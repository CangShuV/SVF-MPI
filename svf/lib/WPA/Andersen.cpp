//===- Andersen.cpp -- Field-sensitive Andersen's analysis-------------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013-2017>  <Yulei Sui>
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.

// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===----------------------------------------------------------------------===//

/*
 * Andersen.cpp
 *
 *  Created on: Nov 12, 2013
 *      Author: Yulei Sui
 */

#include "Util/Options.h"
#include "Graphs/CHG.h"
#include "Util/SVFUtil.h"
#include "MemoryModel/PointsTo.h"
#include "WPA/Andersen.h"

#include <queue>
#include <utility>

#include "WPA/Steensgaard.h"
#include <glog/logging.h>

using namespace SVF;
using namespace SVFUtil;
using namespace std;


u32_t AndersenBase::numOfProcessedAddr = 0;
u32_t AndersenBase::numOfProcessedCopy = 0;
u32_t AndersenBase::numOfProcessedGep = 0;
u32_t AndersenBase::numOfProcessedLoad = 0;
u32_t AndersenBase::numOfProcessedStore = 0;
u32_t AndersenBase::numOfSfrs = 0;
u32_t AndersenBase::numOfFieldExpand = 0;

u32_t AndersenBase::numOfSCCDetection = 0;
double AndersenBase::timeOfSCCDetection = 0;
double AndersenBase::timeOfSCCMerges = 0;
double AndersenBase::timeOfCollapse = 0;

u32_t AndersenBase::AveragePointsToSetSize = 0;
u32_t AndersenBase::MaxPointsToSetSize = 0;
double AndersenBase::timeOfProcessCopyGep = 0;
double AndersenBase::timeOfProcessLoadStore = 0;
double AndersenBase::timeOfUpdateCallGraph = 0;

std::pair<int, std::string> Monitor::parse(std::string inst_info)
{
    // 定义一个辅助函数，用于提取 "ln" 对应的数字
    auto extractLnValue = [](const std::string& str) -> int {
        // 查找 "ln": 的位置
        size_t pos = str.find(R"("ln":)");
        if (pos == std::string::npos) {
            return -1; // 如果找不到 "ln":，返回 -1
        }

        // 跳过 "ln": 和空格
        pos += 5; // "ln": 的长度是 5
        while (pos < str.size() && std::isspace(str[pos])) {
            pos++;
        }

        // 提取数字部分
        int lnValue = 0;
        while (pos < str.size() && std::isdigit(str[pos])) {
            lnValue = lnValue * 10 + (str[pos] - '0');
            pos++;
        }

        return lnValue;
    };

    // 定义一个辅助函数，用于提取 "fl" 对应的字符串
    auto extractFlValue = [](const std::string& str) -> std::string {
        // 查找 "fl": 的位置
        size_t pos = str.find(R"("fl":)");
        if (pos == std::string::npos) {
            return ""; // 如果找不到 "fl":，返回空字符串
        }

        // 跳过 "fl": 和空格
        pos += 5; // "fl": 的长度是 5
        while (pos < str.size() && std::isspace(str[pos])) {
            pos++;
        }

        // 提取字符串部分（假设字符串用双引号包裹）
        if (pos < str.size() && str[pos] == '"') {
            pos++; // 跳过开头的双引号
            size_t endPos = str.find('"', pos); // 找到结尾的双引号
            if (endPos != std::string::npos) {
                return str.substr(pos, endPos - pos);
            }
        }
        return ""; // 如果格式不正确，返回空字符串
    };

    // 从 inst_info 字符串中提取 "ln" 对应的数字和 "fl" 对应的字符串
    int instLnValue = extractLnValue(inst_info);
    std::string instFlValue = extractFlValue(inst_info);

    // if (callLnValue != -1) {
    //     LOG(INFO) << "Call ln: " << callLnValue ;
    // } else {
    //     LOG(INFO) << "Call ln not found!" ;
    // }
    //
    // if (!callFlValue.empty()) {
    //     LOG(INFO) << "Call fl: " << callFlValue ;
    // } else {
    //     LOG(INFO) << "Call fl not found!" ;
    // }

    return make_pair(instLnValue, instFlValue);
}

void Monitor::parseRecord(std::string call, std::string access, BufferType buf_type, StmtType stmt_type,
                          unsigned long long IRStmtsSum, std::multiset<unsigned long long>* pathIRStmtSum)
{
    auto[callLnValue, callFlValue] = parse(std::move(call));
    auto[accessLnValue, accessFlValue] = parse(std::move(access));

    if(accessLnValue > 0  && callLnValue > 0)
    {
        MonitorLogData callLog = {callLnValue, callFlValue, static_cast<int>(buf_type), 0, nullptr};
        MonitorLogData accessLog = {accessLnValue, accessFlValue, static_cast<int>(stmt_type), IRStmtsSum, pathIRStmtSum};
        log[callLog].insert(accessLog);
        // stmtLog.insert(accessLog);
    }
}

/*!
 * Destructor
 */
AndersenBase::~AndersenBase()
{
    delete consCG;
    consCG = nullptr;
}

/*!
 * Initialize analysis
 */
void AndersenBase::initialize()
{
    /// Build SVFIR
    PointerAnalysis::initialize();
    /// Create statistic class
    stat = new AndersenStat(this);
    /// Build Constraint Graph
    consCG = new ConstraintGraph(pag);
    setGraph(consCG);
    if (Options::ConsCGDotGraph())
        consCG->dump("consCG_initial");
}

/*!
 * Finalize analysis
 */
void AndersenBase::finalize()
{
    /// dump constraint graph if PAGDotGraph flag is enabled
    if (Options::ConsCGDotGraph())
        consCG->dump("consCG_final");

    if (Options::PrintCGGraph())
        consCG->print();
    BVDataPTAImpl::finalize();
}

void AndersenBase::solveConstraints()
{
    // Start solving constraints
    DBOUT(DGENERAL, outs() << SVFUtil::pasMsg("Start Solving Constraints\n"));

    bool limitTimerSet = SVFUtil::startAnalysisLimitTimer(Options::AnderTimeLimit());

    initWorklist();
    do
    {
        numOfIteration++;
        if (0 == numOfIteration % iterationForPrintStat)
            printStat();

        reanalyze = false;

        solveWorklist();

        if (updateCallGraph(getIndirectCallsites()))
            reanalyze = true;

    }
    while (reanalyze);

    // Analysis is finished, reset the alarm if we set it.
    SVFUtil::stopAnalysisLimitTimer(limitTimerSet);

    DBOUT(DGENERAL, outs() << SVFUtil::pasMsg("Finish Solving Constraints\n"));
}



const ICFGNode* AndersenBase::findFuncRetNode(const ICFGNode* call_node)
{
    auto *callNode = dyn_cast<CallICFGNode>(call_node);
    if (!callNode)
    {
        // LOG(FATAL) << "[findFuncRetNode] " << callNode << " is not CallNode!!";
        return nullptr;
    }

    const auto retNode = callNode->getRetICFGNode();
    return retNode;
}

const ICFGNode* AndersenBase::findFuncCallNode(const ICFGNode* ret_node)
{
    auto *retNode = dyn_cast<RetICFGNode>(ret_node);
    if (!retNode)
    {
        // LOG(FATAL) << "[findFuncCallNode] " << retNode << " is not RetNode!!";
        return nullptr;
    }

    const auto callNode = retNode->getCallICFGNode();
    return callNode;
}

constexpr unsigned long long AndersenBase::getIRStmtSum(const ICFGNode* node)
{
    return node->getSVFStmts().size();
}

/// [Deprecated]
// void AndersenBase::calculateIRStmtSum(Monitor& monitor)
// {
//     unordered_map<int, std::unordered_set<const ICFGNode*>> visited;
//
//     struct State {
//         const ICFGNode* currentNode;
//         unsigned long long accumulatedSum;
//         int visitedId;
//         const ICFGNode* retNode;
//
//         State(const ICFGNode* node, unsigned long long sum, int visitedId, const ICFGNode* retNode):
//             currentNode(node), accumulatedSum(sum), visitedId(visitedId), retNode(retNode)
//         {}
//     };
//
//     // <hashCode, vid>
//     unordered_map<int, int> visitedHashCode;
//
//     for (auto& buf : monitor.buffers)
//     {
//         LOG(INFO) << "[calculateIRStmtSum, buffer] " << &buf;
//
//         visited.clear();
//         int vidCounter = 1;
//         long long hashConflictCounter = 0;
//
//         std::stack<State, std::vector<State>> stack;
//         stack.emplace(buf.node, 0 ,0, nullptr);
//
//         while (!stack.empty()) {
//             auto [currentNode, currentSum, vid, retNode] = stack.top();
//             stack.pop();
//
//             LOG(INFO) << "[calculateIRStmtSum] " << currentNode->getId() << " , vid: " << vid;
//
//             if (visited[vid].find(currentNode) != visited[vid].end())
//             {
//                 // TODO: 处理环. method: abandon visited, using visited_hash.
//                 continue;
//             }
//             visited[vid].insert(currentNode);
//
//             unsigned long long newSum = currentSum + getIRStmtSum(currentNode);
//             std::vector<State> pushList;
//
//             // if currentNode is access point:
//             for (auto stmt: currentNode->getSVFStmts())
//             {
//                 if (monitor.bufferAccess[&buf].find(stmt) != monitor.bufferAccess[&buf].end())
//                 {
//                     monitor.bufferAccess[&buf][stmt].insertPathInfo(newSum);
//                     goto nextLoop;
//                 }
//             }
//
//             // 遍历所有出边，分裂新的状态
//             for (const auto& edge : currentNode->getOutEdges()) {
//                 ICFGNode* nextNode = edge->getDstNode();
//                 // 仅处理未在当前路径访问过的节点
//                 if (visited[vid].find(nextNode) == visited[vid].end())
//                 {
//                     // if (!retNode)
//                     //     stack.emplace(nextNode, newSum, vidCounter++, findFuncRetNode(nextNode));
//                     // else if (retNode == nextNode)
//                     // {
//                     stack.emplace(nextNode, newSum, vidCounter++, nullptr);
//                     //     break;
//                     // }
//                 }
//             }
//
//             // recycle one vid.
//             if (!pushList.empty())
//             {
//                 auto [nextNode, newSum, newVId, retNode] = pushList.back();
//                 stack.emplace(nextNode, newSum, vid, retNode);
//                 pushList.pop_back();
//                 --vidCounter;
//             }
//
//             for (auto it : pushList)
//             {
//                 stack.push(it);
//                 // copy a new copy.
//                 visited[it.visitedId] = visited[vid];
//             }
//
//             nextLoop:;
//         }
//     }
// }


int AndersenBase::detectAccessNodes(const ICFGNode* node, Monitor& monitor, Buffer& buf)
{
    /// if node is loop's unsafeNode (include continue, break, goto, return), do not process.
    if (monitor.bufferAccess[&buf].find(node->getSVFStmts().back()) != monitor.bufferAccess[&buf].end())
        return -1;

    if (auto* intraNode = dyn_cast<IntraICFGNode>(node))
    {
        auto stmts = intraNode->getSVFStmts();
        for (auto stmt : stmts)
        {
            if (auto* loadStmt = dyn_cast<LoadStmt>(stmt))
            {
                if (buf.type == SEND_BUFFER)
                    continue;

                // monitor.stmts.push_back(stmt);  // 将相关指令添加到 stmts 中
                if (alias(buf.buf, loadStmt->getRHSVar()->getValue()))
                {
                    // LOG(INFO) << "trigger!";
                    // LOG(INFO) <<buf.callInst->getSourceLoc();
                    // LOG(INFO) <<loadStmt->getInst()->getSourceLoc();
                    monitor.bufferAccess[&buf][stmt] = Monitor::IRStmtSumInfo(LOAD_STMT);
                }
            }
            else if (auto* storeStmt = dyn_cast<StoreStmt>(stmt))
            {
                if (buf.type == RECV_BUFFER)
                    continue;

                // monitor.stmts.push_back(stmt);  // 将相关指令添加到 stmts 中
                if (alias(buf.buf, storeStmt->getLHSVar()->getValue()))
                {
                    // LOG(INFO) << "trigger!";
                    // LOG(INFO) <<buf.callInst->getSourceLoc();
                    // LOG(INFO) <<storeStmt->getInst()->getSourceLoc();

                    // 查询最内层循环
                    // const SVFLoop* loop = getInnermostSVFLoop(intraNode);
                    monitor.bufferAccess[&buf][stmt] = Monitor::IRStmtSumInfo(STORE_STMT);
                }
            }
        }
        return 1;
    }

    if (auto *callNode = dyn_cast<CallICFGNode>(node))
    {
        /// 获取调用的函数
        auto *callInst = callNode->getCallSite();
        auto callSite = getSVFCallSite(callInst);

        /// 检查是否是 MPI 相关函数
        if (specialFunctions.count(callSite.getCalledFunction()->getName()))
        {
            StmtType stmtType;
            auto &calledFunctionName = callSite.getCalledFunction()->getName();
            if (calledFunctionName == "MPI_Send") {
                // if (buf.type == SEND_BUFFER)
                //     return 0;

                stmtType = LOAD_STMT;
            } else if (calledFunctionName == "MPI_Recv") {
                // if (buf.type == RECV_BUFFER)
                //     return 0;

                stmtType = STORE_STMT;
            } else if (calledFunctionName == "MPI_Bcast") {
                stmtType = LOAD_AND_STORE_STMT;
            } else {
                stmtType = UNKNOWN_STMT;
            }

            auto bufArg0 = callSite.getArgument(0); // 获取第一个缓冲区参数

            // buf.node != node: omit itself.
            if (buf.node != node && alias(buf.buf, bufArg0))
            {
                //         // LOG(INFO) << "trigger!";
                //         // LOG(INFO) << i.buf->getSourceLoc();
                //         // LOG(INFO) << callinst->getSourceLoc();
                monitor.bufferAccess[&buf][node->getSVFStmts().back()] = Monitor::IRStmtSumInfo(stmtType);
            }

            return 2;
        }
    }
    return 0;
}

void AndersenBase::detectBufferNodes(const ICFGNode* node, Monitor& monitor)
{
    // LOG(INFO) << node->toString();
    /// 判断是否是函数调用节点
    if (auto *callNode = dyn_cast<CallICFGNode>(node)) {
        /// 获取调用的函数
        auto *callInst = callNode->getCallSite();
        auto callSite = getSVFCallSite(callInst);

        /// 检查是否是 MPI 相关函数
        if (specialFunctions.count(callSite.getCalledFunction()->getName())) {
            // TODO: 有些函数有多个缓冲区参数。这里只用了第一个。
            auto buf = callSite.getArgument(0); // 获取第一个缓冲区参数

            /*!
             * 根据函数名判断是发送缓冲区还是接收缓冲区
             * 对应的函数通常会有一个输入参数，用于区分是发送还是接收
             */
            BufferType bufferType;
            auto &calledFunctionName = callSite.getCalledFunction()->getName();
            if (calledFunctionName == "MPI_Send") {
                bufferType = SEND_BUFFER;
            } else if (calledFunctionName == "MPI_Recv") {
                bufferType = RECV_BUFFER;
            } else if (calledFunctionName == "MPI_Bcast") {
                bufferType = SEND_AND_RECV_BUFFER;
            } else {
                bufferType = UNKNOWN_BUFFER;
            }

            /// 创建一个新的缓冲区并添加到 monitor
            Buffer buffer(callInst, buf, node, bufferType);
            monitor.buffers.push_back(buffer);
            LOG(INFO) << "trigger!";
        }
    }
}

/// for test.
void AndersenBase::testICFGLoops()
{
    auto pagICFG = pag->getICFG();
    // assert(!pagICFG->getIcfgNodeToSVFLoopVec().empty());
    for (const auto& [it, jt]: pagICFG->getIcfgNodeToSVFLoopVec())
    {
        LOG(INFO) << it->getId();
        // LOG(FATAL)<< "TRIGGER!";
        for (auto sth : jt)
        {
            auto loop = const_cast<SVFLoop*>(sth);
            for (auto entryEdge = loop->entryICFGEdgesBegin(); entryEdge != loop->entryICFGEdgesEnd(); ++entryEdge){
                LOG(INFO) << (*entryEdge)->getSrcNode()->getId();
                LOG(INFO) << (*entryEdge)->getDstNode()->getId();
            }
            for (auto backEdge = loop->backICFGEdgesBegin(); backEdge != loop->backICFGEdgesEnd(); ++backEdge){
                LOG(INFO) << (*backEdge)->getSrcNode()->getId();
                LOG(INFO) << (*backEdge)->getDstNode()->getId();
            }
            for (auto entryEdge = loop->inEdgesBegin(); entryEdge != loop->inEdgesEnd(); ++entryEdge){
                LOG(INFO) << (*entryEdge)->getSrcNode()->getId();
                LOG(INFO) << (*entryEdge)->getDstNode()->getId();
            }
            for (auto backEdge = loop->outICFGEdgesBegin(); backEdge != loop->outICFGEdgesEnd(); ++backEdge){
                LOG(INFO) << (*backEdge)->getSrcNode()->getId();
                LOG(INFO) << (*backEdge)->getDstNode()->getId();
            }
        }
    }

    LOG(FATAL) << "stop.";
    LOG(INFO) << "[findICFGLoops END]";
}

/// [Deprecated.]
// void AndersenBase::findICFGLoops(const ICFGNode* globalNode, Monitor& monitor)
// {
//     // LOG(INFO) << "[trigger!]";
//     std::unordered_set<const ICFGNode*> visited;
//     std::stack<const ICFGNode*, std::vector<const ICFGNode*>> stack;
//     stack.push(globalNode);
//
//     // 1st DFS, find all loops, and br stmts.
//     while (!stack.empty())
//     {
//         const ICFGNode* currentNode = stack.top();
//         stack.pop();
//
//         // if (visited.find(currentNode) != visited.end())
//
//         // // skip specialFunctions loops.
//         // if (specialFunctions.count(currentNode->getFun()->getName()))
//         //     continue;
//
//         LOG(INFO) << currentNode->getId();
//
//         // int handleTag = 0;
//         ICFGNode* lastNode = nullptr;
//         for (auto edge : currentNode->getInEdges())
//         {
//             // TODO: Used string.find() to discriminating statement. Should be changed to type conversion.
//             lastNode = edge->getSrcNode();
//             // omit FuncNode. (Call, Ret, Exit)
//             if (lastNode->getSVFStmts().empty())
//                 continue;
//
//             const string& lastStmtStr = lastNode->getSVFStmts().back()->toString();
//
//             // record continue & circulation end stmt.
//             // noted: this method will record first call, which means logs need cleaning.
//             // if (lastStmtStr.find("br label %") != std::string::npos
//             //         && (lastStmtStr.find(".cond") != std::string::npos
//             //         // || lastStmtStr.find(".inc") != std::string::npos
//             //         )
//             //     )
//             if (lastStmtStr.find("!llvm.loop") != std::string::npos)
//             {
//                 // // check do-while stmt.
//                 // if (auto* intraEdge = dyn_cast<IntraCFGEdge>(edge))
//                 //     if (intraEdge->getCondition())
//                 //         if (!intraEdge->getSuccessorCondValue())
//                 //             goto nextCase;
//
//                 LOG(INFO) << "[PATH]\n[FROM]\n" << lastNode->toString() << "\n[TO]\n" << currentNode->toString()
//                           << "\n[TYPE]\n" << stmtTypeToString(CIRCULATION_END_STMT);
//                 monitor.loops[currentNode].insert(lastNode);
//                 monitor.backEdges.insert({lastNode, currentNode, CIRCULATION_END_STMT});
//             // nextCase:;
//             }
//             // record return stmt.
//             // ',' is important.
//             else if (lastStmtStr.find("br label %return,") != std::string::npos)
//             {
//                 LOG(INFO) << "[PATH]\n[FROM]\n" << lastNode->toString() << "\n[TO]\n" << currentNode->toString()
//                           << "\n[TYPE]\n" << stmtTypeToString(RETURN_STMT);
//                 monitor.backEdges.insert({lastNode, currentNode, RETURN_STMT});
//             }
//             // record break stmt.
//             else if (lastStmtStr.find("br label %") != std::string::npos
//                     && lastStmtStr.find(".end") != std::string::npos
//                     )
//             {
//                 // omit circulation core Node. only handle "break" stmt.
//                 if (lastNode->getOutEdges().size() == 1)
//                 {
//                     LOG(INFO) << "[PATH]\n[FROM]\n" << lastNode->toString() << "\n[TO]\n" << currentNode->toString()
//                           << "\n[TYPE]\n" << stmtTypeToString(BREAK_STMT);
//                     monitor.backEdges.insert({lastNode, currentNode, BREAK_STMT});
//                 }
//             }
//             else if (lastStmtStr.find("br label %") != std::string::npos &&
//                 lastStmtStr.find("label %if.") == std::string::npos &&
//                 lastStmtStr.find("label %sw.") == std::string::npos &&
//                 lastStmtStr.find("label %for.") == std::string::npos &&
//                 lastStmtStr.find("label %while.") == std::string::npos &&
//                 lastStmtStr.find("label %do.") == std::string::npos)
//             {
//                 LOG(INFO) << "[PATH]\n[FROM]\n" << lastNode->toString() << "\n[TO]\n" << currentNode->toString()
//                           << "\n[TYPE]\n" << stmtTypeToString(UNSAFE_BRANCH_STMT);
//                 monitor.backEdges.insert({lastNode, currentNode, UNSAFE_BRANCH_STMT});
//             }
//         }
//
//         if (visited.find(currentNode) != visited.end())
//             continue; // 已经访问过，跳过
//
//         visited.insert(currentNode);
//
//         // LOG(INFO) << "[PATH]" << currentNode->toString();
//
//         // 遍历所有出边
//         std::vector<ICFGEdge*> trueEdges, falseEdges;
//         for (auto edge : currentNode->getOutEdges())
//         {
//             if (auto* intraEdge = dyn_cast<IntraCFGEdge>(edge))
//             {
//                 if (intraEdge->getCondition())
//                 {
//                     (intraEdge->getSuccessorCondValue() ? falseEdges : trueEdges).push_back(intraEdge);
//                 }
//                 else
//                     falseEdges.push_back(intraEdge);
//             }
//             else
//                 falseEdges.push_back(edge);
//         }
//
//         // 优先处理真边（循环体）
//         for (const auto& edge : trueEdges) {
//             stack.push(edge->getDstNode());
//         }
//         // 再处理假边（退出分支）
//         for (const auto& edge : falseEdges) {
//             stack.push(edge->getDstNode());
//         }
//
//         // LOG(INFO) << trueEdges.size() << ' ' << falseEdges.size();
//     }
//
//     // 2nd DFS, try to clean up loops logs.
//     std::unordered_set<const ICFGNode*> loopsVisited;
//
//     // std::unordered_map<const ICFGNode*, std::unordered_set<const ICFGNode*>> loopsVisited;
//     // // entryNode, backNode, like monitor.loops
//     // std::vector<tuple<const ICFGNode*, const ICFGNode*>> deleteList;
//     // for (auto &[entryNode, backNode]: monitor.loops)
//     // {
//     //     if (loopsVisited.find(entryNode) != loopsVisited.end())
//     //     {
//     //         if (loopsVisited[entryNode].find(backNode) == loopsVisited[entryNode].end())
//     //             deleteList.emplace_back(entryNode, backNode);
//     //         continue;
//     //     }
//
//     visited.clear();
//     while (!stack.empty()) stack.pop();
//
//     std::unordered_set<const ICFGNode*> specialGotoVisited;
//     std::stack<const ICFGNode*, std::vector<const ICFGNode*>> gotoStack;
//
//     // Prepare a Loop stack for each function
//     std::map<std::string, std::stack<const ICFGNode*, std::vector<const ICFGNode*>>> loopStack;
//
//     // stack.push(entryNode);
//     stack.push(globalNode);
//     std::unordered_set<const ICFGNode*> backNodesSet;
//
//     while (!stack.empty())
//     {
//         const ICFGNode* currentNode = stack.top();
//         stack.pop();
//         if (stack.empty() && !gotoStack.empty())
//         {
//             stack.push(gotoStack.top());
//             gotoStack.pop();
//         }
//
//         LOG(INFO) << "[PATH]" << currentNode->getId();
//
//         if (dyn_cast<FunExitICFGNode>(currentNode))
//             continue;
//
//         // only allow last inEdge to search. design for if, switch, etc.
//         if (!dyn_cast<RetICFGNode>(currentNode))
//         {
//             int continueTag = 0;
//             for (auto inEdge : currentNode->getInEdges())
//             {
//                 auto srcNode = inEdge->getSrcNode();
//                 // not visited && not backEdge && not callNode
//                 if (
//                     visited.find(srcNode) == visited.end() &&
//                     !get<0>(monitor.findNodeInBackEdges(srcNode)) &&
//                     !dyn_cast<CallICFGNode>(srcNode)
//                 )
//                 {
//                     LOG(INFO) << currentNode->getId() << " [skipped] " << srcNode->getId();
//                     continueTag = 1;
//                 }
//             }
//             if (continueTag) continue;
//         }
//
//         if (visited.find(currentNode) != visited.end())
//         {
//             LOG(WARNING) << "[findICFGBuffers] Repeated access node!\n" << currentNode->toString();
//             continue; // 已经访问过，跳过
//         }
//         visited.insert(currentNode);
//
//         // 处理当前节点
//         // if currentNode is backNode.
//         if (auto entryNode = monitor.findNodeInLoops(get<1>(monitor.findNodeInBackEdges(currentNode))))
//         {
//             if (loopsVisited.find(entryNode) == loopsVisited.end())
//             {
//                 loopsVisited.insert(entryNode);
//                 // delete first visited "backNode".
//                 monitor.loops[entryNode].erase(currentNode);
//                 assert(get<2>(monitor.findNodeInBackEdges(currentNode)) == CIRCULATION_END_STMT);
//                 monitor.backEdges.erase({currentNode, entryNode, CIRCULATION_END_STMT});
//             }
//         }
//
//         // traverse all outEdges. except goto stmt. Allow last goto node inEdge to search, to avoid special goto node.
//         // But, push it must after searched all the points in current stack.
//         if (get<2>(monitor.findNodeInBackEdges(currentNode)) == UNSAFE_BRANCH_STMT)
//         {
//             LOG(INFO) << "[findLastGoto] " << currentNode->getId();
//             // only push goto_dstNode once.
//             assert(currentNode->getOutEdges().size() == 1); // make sure it is goto stmt.
//             auto dstNode = (*currentNode->getOutEdges().begin())->getDstNode();
//             // for (auto inEdge : dstNode->getInEdges())
//             if (specialGotoVisited.find(dstNode) == specialGotoVisited.end())
//             {
//                 specialGotoVisited.insert(dstNode);
//                 gotoStack.push(dstNode);
//                 LOG(INFO) << "[findLastGotoDstNode:FOUND!] " << dstNode->getId();
//
//                 if (stack.empty() && !gotoStack.empty())
//                 {
//                     stack.push(gotoStack.top());
//                     // specialGotoVisited.insert(currentNode);
//                     gotoStack.pop();
//                 }
//             }
//             continue;
//             // }
//         }
//
//         std::vector<ICFGEdge*> trueEdges, falseEdges;
//         for (auto edge : currentNode->getOutEdges())
//         {
//             if (auto* intraEdge = dyn_cast<IntraCFGEdge>(edge))
//             {
//                 if (intraEdge->getCondition())
//                 {
//                     (intraEdge->getSuccessorCondValue() ? falseEdges : trueEdges).push_back(intraEdge);
//                 }
//                 else
//                     falseEdges.push_back(intraEdge);
//             }
//             else
//                 falseEdges.push_back(edge);
//         }
//
//         // 优先处理真边（循环体）
//         for (const auto& edge : trueEdges)
//         {
//             stack.push(edge->getDstNode());
//         }
//         // 再处理假边（退出分支）
//         for (const auto& edge : falseEdges)
//         {
//             stack.push(edge->getDstNode());
//         }
//
//         if (auto retNode = findFuncRetNode(currentNode))
//         {
//             stack.push(retNode);
//         }
//     }
//
//     //     if (backNodesSet.find(backNode) == backNodesSet.end())
//     //         deleteList.emplace_back(entryNode, backNode);
//     //
//     //     loopsVisited.insert({entryNode, backNodesSet});
//     // }
//
//     // 3rd DFS, find all nodes belongs loop.
//     visited.clear();
//     specialGotoVisited.clear();
//     while (!gotoStack.empty()) gotoStack.pop();
//     loopStack.clear();
//     while (!stack.empty()) stack.pop();
//
//     // std::unordered_set<const ICFGNode*> specialGotoVisited;
//     // std::stack<const ICFGNode*, std::vector<const ICFGNode*>> gotoStack;
//
//     // Prepare a Loop stack for each function
//     // std::map<std::string, std::stack<const ICFGNode*, std::vector<const ICFGNode*>>> loopStack;
//
//     stack.push(globalNode);
//
//     while (!stack.empty())
//     {
//         const ICFGNode* currentNode = stack.top();
//         stack.pop();
//         if (stack.empty() && !gotoStack.empty())
//         {
//             stack.push(gotoStack.top());
//             // specialGotoVisited.insert(currentNode);
//             gotoStack.pop();
//         }
//
//         LOG(INFO) << "[PATH]" << currentNode->getId();
//
//         if (dyn_cast<FunExitICFGNode>(currentNode))
//             continue;
//
//         // only allow last inEdge to search. design for if, switch, etc.
//         // if (!dyn_cast<RetICFGNode>(currentNode))
//         {
//             int continueTag = 0;
//             for (auto inEdge : currentNode->getInEdges())
//             {
//                 auto srcNode = inEdge->getSrcNode();
//                 // // not visited && not backEdge && not callNode && not do-while
//                 // if (
//                 //     visited.find(srcNode) == visited.end() &&
//                 //     !get<0>(monitor.findNodeInBackEdges(srcNode)) &&
//                 //     !dyn_cast<CallICFGNode>(srcNode) &&
//                 //     srcNode->getSVFStmts().back()->toString().find("label %do.body") == std::string::npos
//                 // )
//                 if (srcNode->getSVFStmts().empty())
//                     continue;
//
//                 auto srcNodeBackStmtString = srcNode->getSVFStmts().back()->toString();
//                 if (srcNodeBackStmtString.find("label %if.") != std::string::npos
//                     || srcNodeBackStmtString.find("label %sw.") != std::string::npos
//                 )
//                 {
//                     LOG(INFO) << currentNode->getId() << " [waiting, for skipped] " << srcNode->getId();
//                     continueTag = 1;
//                 }
//             }
//             if (continueTag) continue;
//         }
//
//         if (visited.find(currentNode) != visited.end())
//         {
//             LOG(WARNING) << "[findICFGBuffers] Repeated access node!\n" << currentNode->toString();
//             continue; // 已经访问过，跳过
//         }
//         visited.insert(currentNode);
//
//         // 处理当前节点
//         // avoid globalNode.
//         if (const auto currentFunc = currentNode->getFun())
//         {
//             const auto& funcName = currentFunc->getName();
//             if (!specialFunctions.count(funcName))
//             {
//                 // LOG(INFO) << "trigger!";
//                 // if it is entryNode, push
//                 if (monitor.findNodeInLoops(currentNode))
//                 {
//                     loopStack[funcName].push(currentNode);
//                 }
//
//                 monitor.nodeBelongLoop[currentNode] = {
//                     monitor.findNodeInLoops(loopStack[funcName].empty() ? nullptr : loopStack[funcName].top())
//                 };
//                 LOG(INFO) << "[nodeBelongLoop, 2nd dfs.] " << currentNode->getId() << " [belong] " << (loopStack[funcName].empty() ? 0 : loopStack[funcName].top()->getId());
//
//                 // if it is backNode, pop
//                 if (get<2>(monitor.findNodeInBackEdges(currentNode)) == CIRCULATION_END_STMT)
//                 {
//                     if (loopStack[funcName].empty())
//                         LOG(FATAL) << "[findICFGLoops, 2nd dfs] loopStack[" << funcName << "] try to pop, but it's empty!!\n"
//                                    << "[Node] " << currentNode->getId();
//                     if (auto entryPartner = get<1>(monitor.findNodeInBackEdges(currentNode)); entryPartner != loopStack[funcName].top())
//                         LOG(FATAL) << "[findICFGLoops, 2nd dfs] loopStack[" << funcName << "] try to pop, but top() is not currentNode's EntryNode!!\n"
//                                    << "[<CurrentNode, EntryNode>] " << entryPartner->getId() << " " << loopStack[funcName].top()->getId();
//                     loopStack[funcName].pop();
//                 }
//             }
//         }
//
//         // traverse all outEdges. except goto stmt. Allow last goto node inEdge to search, to avoid special goto node.
//         // But, push it must after searched all the points in current stack.
//         if (get<2>(monitor.findNodeInBackEdges(currentNode)) == UNSAFE_BRANCH_STMT)
//         {
//             LOG(INFO) << "[findLastGoto] " << currentNode->getId();
//             // only push goto_dstNode once.
//             assert(currentNode->getOutEdges().size() == 1);
//             auto dstNode = (*currentNode->getOutEdges().begin())->getDstNode();
//             // for (auto inEdge : dstNode->getInEdges())
//             if (specialGotoVisited.find(dstNode) == specialGotoVisited.end())
//             {
//                 specialGotoVisited.insert(dstNode);
//                 gotoStack.push(dstNode);
//                 LOG(INFO) << "[findLastGotoDstNode:FOUND!] " << dstNode->getId();
//
//                 if (stack.empty() && !gotoStack.empty())
//                 {
//                     stack.push(gotoStack.top());
//                     // specialGotoVisited.insert(currentNode);
//                     gotoStack.pop();
//                 }
//             }
//             continue;
//             // }
//         }
//
//         std::vector<ICFGEdge*> trueEdges, falseEdges;
//         for (auto edge : currentNode->getOutEdges())
//         {
//             if (auto* intraEdge = dyn_cast<IntraCFGEdge>(edge))
//             {
//                 if (intraEdge->getCondition())
//                 {
//                     (intraEdge->getSuccessorCondValue() ? falseEdges : trueEdges).push_back(intraEdge);
//                 }
//                 else
//                     falseEdges.push_back(intraEdge);
//             }
//             else
//                 falseEdges.push_back(edge);
//         }
//
//         // 优先处理真边（循环体）
//         for (const auto& edge : trueEdges)
//         {
//             stack.push(edge->getDstNode());
//         }
//         // 再处理假边（退出分支）
//         for (const auto& edge : falseEdges)
//         {
//             stack.push(edge->getDstNode());
//         }
//
//
//         if (auto retNode = findFuncRetNode(currentNode))
//         {
//             stack.push(retNode);
//         }
//
//     }
//
//     LOG(INFO) << "[findICFGLoops END]";
// }

void AndersenBase::findICFGBuffers(const ICFGNode* globalNode, Monitor& monitor)
{
    std::unordered_set<const ICFGNode*> visited;
    std::stack<const ICFGNode*, std::vector<const ICFGNode*>> stack;

    stack.push(globalNode);

    while (!stack.empty())
    {
        const ICFGNode* currentNode = stack.top();
        stack.pop();

        if (visited.find(currentNode) != visited.end())
        {
            // LOG(INFO) << "[findICFGBuffers] Repeated access node!\n" << currentNode->toString();
            continue; // 已经访问过，跳过
        }
        visited.insert(currentNode);

        // LOG(INFO) << "[PATH]" << currentNode->toString();

        /// 处理当前节点
        detectBufferNodes(currentNode, monitor);

        /// 遍历所有出边
        for (auto edge : currentNode->getOutEdges())
        {
            ICFGNode* nextNode = edge->getDstNode();
            stack.push(nextNode);
        }
    }

    /// [deprecated] pre-process buffers circulation_end
    // for (auto& buf: monitor.buffers)
    // {
    //     auto &[entryNode, backNode] = monitor.nodeBelongLoop[buf.node];
    //     buf.loopEntryNode = entryNode;
    //     buf.loopBackNode = backNode;
    //     if (backNode)
    //     {
    //         LOG(INFO) << "[findICFGBuffers] trigger! \n[buf.node] " << buf.node->getId() << "\n[backNode] " << backNode->getId();
    //         monitor.bufferAccess[&buf].insert({backNode->getSVFStmts().back(), CIRCULATION_END_STMT});
    //     }
    // }


    // [2nd dfs, deprecated] can not solving function multi-call
    // for (auto& buf : monitor.buffers)
    // {
    //     visited.clear();
    //     while (!stack.empty()) stack.pop();
    //
    //     for (auto edge : buf.node->getInEdges())
    //     {
    //         ICFGNode* frontNode = edge->getSrcNode();
    //         stack.push(frontNode);
    //     }
    //
    //     while (!stack.empty())
    //     {
    //         const ICFGNode* currentNode = stack.top();
    //         stack.pop();
    //
    //         if (visited.find(currentNode) != visited.end())
    //         {
    //             // LOG(INFO) << "[findICFGBuffers] Repeated access node!\n" << currentNode->toString();
    //             continue; // 已经访问过，跳过
    //         }
    //         visited.insert(currentNode);
    //
    //         // LOG(INFO) << "[PATH]" << currentNode->toString();
    //
    //         // if it is loopEntryNode
    //         if (get<0>(monitor.findNodeInLoops(currentNode)))
    //         {
    //             if (buf.loopEntryNode)
    //             {
    //                 LOG(FATAL) << "[findICFGBuffers, 2nd DFS] buf.loopEntryNode already exist!!\n[buf.loopEntryNode] "
    //                     << buf.loopEntryNode->getId() << "\n[currentNode] " << currentNode->getId() << "\n[buf.node] "
    //                     << buf.node->getId();
    //             }
    //             // LOG(INFO) << "[findICFGBuffers]";
    //             buf.loopEntryNode = currentNode;
    //         }
    //         else
    //         {
    //             // traverse all inEdges, retrace.
    //             for (auto edge : currentNode->getInEdges())
    //             {
    //                 ICFGNode* nextNode = edge->getSrcNode();
    //                 stack.push(nextNode);
    //             }
    //         }
    //     }
    // }
}

void AndersenBase::traverseICFG(Monitor& monitor)
{
    auto pagICFG = pag->getICFG();
    auto SVFLoopMap = pagICFG->getIcfgNodeToSVFLoopVec();

    /// handle loop's info.
    for (auto& buf : monitor.buffers)
    {
        if (SVFLoopMap.find(buf.node) != SVFLoopMap.end())
        {
            LOG(INFO) << "buf.node: " << buf.node->getId() << " LoopsSize: " << SVFLoopMap[buf.node].size();
            for (auto jt : SVFLoopMap[buf.node])
            {
                auto loop = const_cast<SVFLoop*>(jt);
                for (auto sth = loop->entryICFGEdgesBegin(); sth != loop->entryICFGEdgesEnd(); ++sth)
                    LOG(INFO) << (*sth)->getDstNode()->getId();
            }
            /// getInnerMostLoop.
            auto loop = const_cast<SVFLoop*>(SVFLoopMap[buf.node].back());
            for (auto backEdge = loop->backICFGEdgesBegin(); backEdge != loop->backICFGEdgesEnd(); ++backEdge)
            {
                LOG(INFO) << (*backEdge)->getSrcNode()->getId();
                LOG(INFO) << (*backEdge)->getDstNode()->getId();
                monitor.bufferAccess[&buf][(*backEdge)->getSrcNode()->getSVFStmts().back()] = Monitor::IRStmtSumInfo(
                    CIRCULATION_END_STMT);
            }
            for (auto outEdge = loop->outICFGEdgesBegin(); outEdge != loop->outICFGEdgesEnd(); ++outEdge)
            {
                LOG(INFO) << (*outEdge)->getSrcNode()->getId();
                LOG(INFO) << (*outEdge)->getDstNode()->getId();
                // for (auto entryEdge = loop->entryICFGEdgesBegin(); entryEdge != loop->entryICFGEdgesEnd(); ++entryEdge)
                // {
                //     LOG(INFO) << (*entryEdge)->getSrcNode()->getId();
                //     LOG(INFO) << (*entryEdge)->getDstNode()->getId();
                //     if ((*entryEdge)->getDstNode() == (*outEdge)->getSrcNode())
                //         goto nextLoop;
                // }
                /// if it is not simple br stmt's Node.
                if ((*outEdge)->getSrcNode()->getOutEdges().size() != 1)
                    continue;

                LOG(INFO) << "[Trigger! Break recorded.]";
                monitor.bufferAccess[&buf][(*outEdge)->getSrcNode()->getSVFStmts().back()] = Monitor::IRStmtSumInfo(
                    BREAK_STMT);
            // nextLoop:;
            }
        }
    }

    for (auto& buf : monitor.buffers)
    {
        std::unordered_set<const ICFGNode*> visited;
        std::stack<const ICFGNode*, std::vector<const ICFGNode*>> stack;

        /// starting search with buffer.node.RetNode
        for (auto edge : findFuncRetNode(buf.node)->getOutEdges())
        {
            ICFGNode* nextNode = edge->getDstNode();
            stack.push(nextNode);
        }

        LOG(INFO) << "[TEST] " << stack.size();

        while (!stack.empty())
        {
            const ICFGNode* currentNode = stack.top();
            stack.pop();

            if (visited.find(currentNode) != visited.end())
            {
                // LOG(WARNING) << "[traverseICFG] Repeated access node!\n" << currentNode->toString();
                continue; /// 已经访问过，跳过
            }
            visited.insert(currentNode);

            // LOG(INFO) << "[PATH]" << currentNode->toString();

            int processResult = -1;

            /// 处理当前节点
            /// Do not search for special function nodes.
            if (!specialFunctions.count(currentNode->getFun()->getName()))
                processResult = detectAccessNodes(currentNode, monitor, buf);

            /// 遍历所有出边
            /// omit -1 & -2, unsafe br stmts.
            if (processResult >= 0)
            {
                std::vector<ICFGEdge*> trueEdges, falseEdges;
                for (auto edge : currentNode->getOutEdges())
                {
                    if (auto* intraEdge = dyn_cast<IntraCFGEdge>(edge))
                    {
                        if (intraEdge->getCondition())
                        {
                            (intraEdge->getSuccessorCondValue() ? falseEdges : trueEdges).push_back(intraEdge);
                        }
                        else
                            falseEdges.push_back(intraEdge);
                    }
                    else
                        falseEdges.push_back(edge);
                }

                /// 优先处理真边（循环体）
                for (const auto& edge : trueEdges) {
                    stack.push(edge->getDstNode());
                }
                /// 再处理假边（退出分支）
                for (const auto& edge : falseEdges) {
                    stack.push(edge->getDstNode());
                }
            }

            if (auto retNode = findFuncRetNode(currentNode))
            {
                stack.push(retNode);
            }
        }
    }
}

void AndersenBase::calculateIRStmtsSumV2(const ICFGNode* globalNode, Monitor& monitor)
{
    unordered_set<const ICFGNode*> bufferNodeVisited;
    unordered_set<const ICFGNode*> accessNodeVisited;
    std::stack<const ICFGNode*, std::vector<const ICFGNode*>> stack;

    /// calculate functions IRStmtSum.
    auto &visited = bufferNodeVisited;
    stack.push(globalNode);

    while (!stack.empty())
    {
        const ICFGNode* currentNode = stack.top();
        stack.pop();

        if (visited.find(currentNode) != visited.end())
            continue; /// 已经访问过，跳过
        visited.insert(currentNode);

        if (auto *funEntryNode = dyn_cast<FunEntryICFGNode>(currentNode))
        {
            auto &visited2 = accessNodeVisited;
            visited2.clear();

            std::stack<const ICFGNode*, std::vector<const ICFGNode*>> stack2;
            stack2.push(currentNode);

            while (!stack2.empty())
            {
                const ICFGNode* currentNode2 = stack2.top();
                stack2.pop();

                if (visited2.find(currentNode2) != visited2.end())
                    continue; /// 已经访问过，跳过
                visited2.insert(currentNode2);

                if (!dyn_cast<FunExitICFGNode>(currentNode2))
                    for (auto edge : currentNode2->getOutEdges())
                    {
                        ICFGNode* nextNode = edge->getDstNode();
                        stack2.push(nextNode);
                    }
            }

            for (auto it: visited2)
            {
                monitor.functionsIRSum[currentNode] += getIRStmtSum(it);
            }
            LOG(INFO) << "[functionsIRSum] currentNode: " << currentNode->getId() << "  " << monitor.functionsIRSum[currentNode];
        }

        for (auto edge : currentNode->getOutEdges())
        {
            ICFGNode* nextNode = edge->getDstNode();
            stack.push(nextNode);
        }
    }


    for (auto& buf : monitor.buffers)
    {
        bufferNodeVisited.clear();
        while (!stack.empty()) stack.pop();

        stack.push(buf.node);

        // [1st dfs] calculate buffer's reachable nodes
        while (!stack.empty())
        {
            const ICFGNode* currentNode = stack.top();
            stack.pop();

            if (bufferNodeVisited.find(currentNode) != bufferNodeVisited.end())
                continue; // 已经访问过，跳过
            bufferNodeVisited.insert(currentNode);

            // LOG(INFO) << "[PATH]" << currentNode->toString();

            // if searched accessNodes, stop.
            for (auto &it : currentNode->getSVFStmts())
            {
                if (monitor.bufferAccess[&buf].find(it) != monitor.bufferAccess[&buf].end())
                    goto nextLoop;
            }

            if (!findFuncRetNode(currentNode))
            {
                for (auto edge : currentNode->getOutEdges())
                {
                    ICFGNode* nextNode = edge->getDstNode();
                    stack.push(nextNode);
                }
            }
            // jump functions.
            else
            {
                auto retNode = findFuncRetNode(currentNode);
                stack.push(retNode);
            }

            nextLoop:;
        }

        // LOG(INFO) << "[buffer] " << buf.node->getId();
        // for (auto canReachedNode: bufferNodeVisited)
        // {
        //     LOG(INFO) << canReachedNode->getId();
        // }

        // [2nd dfs] calculate access's inversion reachable nodes
        for (auto& it: monitor.bufferAccess[&buf])
        {
            auto accessStmt = it.first;
            auto startNode = accessStmt->getICFGNode();
            accessNodeVisited.clear();
            /// insert itself!
            accessNodeVisited.insert(startNode);

            while (!stack.empty()) stack.pop();
            stack.push(startNode);
            if (!findFuncCallNode(startNode))
            {
                for (auto edge : startNode->getInEdges())
                {
                    ICFGNode* nextNode = edge->getSrcNode();
                    stack.push(nextNode);
                }
            }
            // jump functions.
            else
            {
                auto callNode = findFuncCallNode(startNode);
                stack.push(callNode);
            }

            while (!stack.empty())
            {
                const ICFGNode* currentNode = stack.top();
                stack.pop();

                /// if searched accessNodes, stop.
                for (auto &currentNodeStmt : currentNode->getSVFStmts())
                {
                    for (auto &buffer: monitor.buffers)
                    {
                        if (monitor.bufferAccess[&buffer].find(currentNodeStmt) != monitor.bufferAccess[&buffer].end())
                            goto nextLoop2nd;
                    }
                }

                /// record.
                if (accessNodeVisited.find(currentNode) != accessNodeVisited.end())
                    continue; // 已经访问过，跳过
                accessNodeVisited.insert(currentNode);

                // LOG(INFO) << "[PATH]" << currentNode->toString();

                /// if searched bufferNodes, stop.
                if (currentNode == buf.node)
                    goto nextLoop2nd;

                if (!findFuncCallNode(currentNode))
                {
                    for (auto edge : currentNode->getInEdges())
                    {
                        ICFGNode* nextNode = edge->getSrcNode();
                        stack.push(nextNode);
                    }
                }
                // jump functions.
                else
                {
                    auto callNode = findFuncCallNode(currentNode);
                    stack.push(callNode);
                }

                nextLoop2nd:;
            }

            // calculate.
            unsigned long long sum = 0;
            for (auto canReachedNode: bufferNodeVisited)
            {
                if (accessNodeVisited.find(canReachedNode) != accessNodeVisited.end())
                {
                    sum += getIRStmtSum(canReachedNode);
                    if (dyn_cast<CallICFGNode>(canReachedNode))
                    {
                        assert(canReachedNode->getOutEdges().size() == 1);
                        for (auto edge : canReachedNode->getOutEdges())
                            sum += monitor.functionsIRSum[edge->getDstNode()];
                    }
                }
            }

            // LOG(INFO) << "[Access] " << accessStmt->getICFGNode()->getId();
            // for (auto sth: accessNodeVisited)
            //     LOG(INFO) << sth->getId();

            monitor.bufferAccess[&buf][accessStmt].insertPathInfo(sum);
        }
    }
}

void AndersenBase::ptsMatch()
{

    Monitor monitor;
    auto *node = pag->getICFG()->getGlobalICFGNode();

    // findICFGLoops(node, monitor);
    findICFGBuffers(node, monitor);

    traverseICFG(monitor);
    // monitor.cleanupLog();

    // calculateIRStmtSum(monitor);
    calculateIRStmtsSumV2(node, monitor);

    for (auto& [buf, stmtMap] : monitor.bufferAccess)
    {
        for (auto& [stmt, IRStmtSumInfo] : stmtMap)
        {
            /// erase Accesses which impossible to reach.
            if (IRStmtSumInfo.allIRSum == 0)
            {
                LOG(INFO) << "\n[impossible to reach access]\n" << "buffer: " << buf->node->getId() << "  access: " <<
                    stmt->getICFGNode()->getId() << "  access type: " << stmtTypeToString(IRStmtSumInfo.type);
            }
            else
                monitor.parseRecord(buf->callInst->getSourceLoc(), stmt->getInst()->getSourceLoc(),
                                    buf->type, IRStmtSumInfo.type, IRStmtSumInfo.allIRSum, &IRStmtSumInfo.pathIRSum);
        }

    }

    /*
     * TODO:Add another traverse to check if load/store/call(noted that
     *      mpi_comm_call will also access memory) inst
     *      triggers any buffer.
     */

    /// print all logs in monitor
    for(const auto& [bufLog, stmtLogSet] : monitor.log)
    {
        LOG(INFO) << "[Buffer]";
        LOG(INFO) << "ln: " << bufLog.lines_index << ", fl: " << bufLog.file_name <<
                     ", Buffer type: " << bufferTypeToString(BufferType(bufLog.type));
        LOG(INFO) << "    [Accesses]";
        for (const auto& stmtLog : stmtLogSet)
        {
            LOG(INFO) << "    ln: " << stmtLog.lines_index << ", fl: " << stmtLog.file_name
                      << ", Access type: " << stmtTypeToString(StmtType(stmtLog.type)) << ", Sum: " << stmtLog.allIRSum;
            // LOG(INFO) << "      [Paths]";
            // int pathSumId = 0;
            // for (auto pathSum: *stmtLog.pathIRSum)
            // {
            //     LOG(INFO) << "      " << pathSumId++ << ": " << pathSum;
            // }
        }
    }
}

/*!
 * Andersen analysis
 */
void AndersenBase::analyze()
{
    if(!Options::ReadAnder().empty())
    {
        readPtsFromFile(Options::ReadAnder());
    }
    else
    {
        if(Options::WriteAnder().empty())
        {
            initialize();
            solveConstraints();
            finalize();
            ptsMatch();
        }
        else
        {
            solveAndwritePtsToFile(Options::WriteAnder());
        }
    }
}

/*!
 * Andersen analysis: read pointer analysis result from file
 */
void AndersenBase::readPtsFromFile(const std::string& filename)
{
    initialize();
    if (!filename.empty())
        this->readFromFile(filename);
    finalize();
}

/*!
 * Andersen analysis: solve constraints and write pointer analysis result to file
 */
void AndersenBase:: solveAndwritePtsToFile(const std::string& filename)
{
    /// Initialization for the Solver
    initialize();
    if (!filename.empty())
        this->writeObjVarToFile(filename);
    solveConstraints();
    if (!filename.empty())
        this->writeToFile(filename);
    finalize();
}

void AndersenBase::cleanConsCG(NodeID id)
{
    consCG->resetSubs(consCG->getRep(id));
    for (NodeID sub: consCG->getSubs(id))
        consCG->resetRep(sub);
    consCG->resetSubs(id);
    consCG->resetRep(id);
    assert(!consCG->hasGNode(id) && "this is either a rep nodeid or a sub nodeid should have already been merged to its field-insensitive base! ");
}

void AndersenBase::normalizePointsTo()
{
    SVFIR::MemObjToFieldsMap &memToFieldsMap = pag->getMemToFieldsMap();
    SVFIR::NodeOffsetMap &GepObjVarMap = pag->getGepObjNodeMap();

    // clear GepObjVarMap/memToFieldsMap/nodeToSubsMap/nodeToRepMap
    // for redundant gepnodes and remove those nodes from pag
    for (NodeID n: redundantGepNodes)
    {
        NodeID base = pag->getBaseObjVar(n);
        GepObjVar *gepNode = SVFUtil::dyn_cast<GepObjVar>(pag->getGNode(n));
        assert(gepNode && "Not a gep node in redundantGepNodes set");
        const APOffset apOffset = gepNode->getConstantFieldIdx();
        GepObjVarMap.erase(std::make_pair(base, apOffset));
        memToFieldsMap[base].reset(n);
        cleanConsCG(n);

        pag->removeGNode(gepNode);
    }
}

/*!
 * Initialize analysis
 */
void Andersen::initialize()
{
    resetData();
    AndersenBase::initialize();

    if (Options::ClusterAnder()) cluster();

    /// Initialize worklist
    processAllAddr();
}

/*!
 * Finalize analysis
 */
void Andersen::finalize()
{
    // TODO: check -stat too.
    // TODO: broken
    if (Options::ClusterAnder())
    {
        Map<std::string, std::string> stats;
        const PTDataTy *ptd = getPTDataTy();
        // TODO: should we use liveOnly?
        // TODO: parameterise final arg.
        NodeIDAllocator::Clusterer::evaluate(*PointsTo::getCurrentBestNodeMapping(), ptd->getAllPts(true), stats, true);
        NodeIDAllocator::Clusterer::printStats("post-main", stats);
    }

    /// sanitize field insensitive obj
    /// TODO: Fields has been collapsed during Andersen::collapseField().
    //	sanitizePts();
    AndersenBase::finalize();
}

/*!
 * Start constraint solving
 */
void Andersen::processNode(NodeID nodeId)
{
    // sub nodes do not need to be processed
    if (sccRepNode(nodeId) != nodeId)
        return;

    ConstraintNode* node = consCG->getConstraintNode(nodeId);
    double insertStart = stat->getClk();
    handleLoadStore(node);
    double insertEnd = stat->getClk();
    timeOfProcessLoadStore += (insertEnd - insertStart) / TIMEINTERVAL;

    double propStart = stat->getClk();
    handleCopyGep(node);
    double propEnd = stat->getClk();
    timeOfProcessCopyGep += (propEnd - propStart) / TIMEINTERVAL;
}

/*!
 * Process copy and gep edges
 */
void Andersen::handleCopyGep(ConstraintNode* node)
{
    NodeID nodeId = node->getId();
    computeDiffPts(nodeId);

    if (!getDiffPts(nodeId).empty())
    {
        for (ConstraintEdge* edge : node->getCopyOutEdges())
            processCopy(nodeId, edge);
        for (ConstraintEdge* edge : node->getGepOutEdges())
        {
            if (GepCGEdge* gepEdge = SVFUtil::dyn_cast<GepCGEdge>(edge))
                processGep(nodeId, gepEdge);
        }
    }
}

/*!
 * Process load and store edges
 */
void Andersen::handleLoadStore(ConstraintNode *node)
{
    NodeID nodeId = node->getId();
    for (PointsTo::iterator piter = getPts(nodeId).begin(), epiter =
                getPts(nodeId).end(); piter != epiter; ++piter)
    {
        NodeID ptd = *piter;
        // handle load
        for (ConstraintNode::const_iterator it = node->outgoingLoadsBegin(),
                eit = node->outgoingLoadsEnd(); it != eit; ++it)
        {
            if (processLoad(ptd, *it))
                pushIntoWorklist(ptd);
        }

        // handle store
        for (ConstraintNode::const_iterator it = node->incomingStoresBegin(),
                eit = node->incomingStoresEnd(); it != eit; ++it)
        {
            if (processStore(ptd, *it))
                pushIntoWorklist((*it)->getSrcID());
        }
    }
}

/*!
 * Process address edges
 */
void Andersen::processAllAddr()
{
    for (ConstraintGraph::const_iterator nodeIt = consCG->begin(), nodeEit = consCG->end(); nodeIt != nodeEit; nodeIt++)
    {
        ConstraintNode * cgNode = nodeIt->second;
        for (ConstraintNode::const_iterator it = cgNode->incomingAddrsBegin(), eit = cgNode->incomingAddrsEnd();
                it != eit; ++it)
            processAddr(SVFUtil::cast<AddrCGEdge>(*it));
    }
}

/*!
 * Process address edges
 */
void Andersen::processAddr(const AddrCGEdge* addr)
{
    numOfProcessedAddr++;

    NodeID dst = addr->getDstID();
    NodeID src = addr->getSrcID();
    if(addPts(dst,src))
        pushIntoWorklist(dst);
}

/*!
 * Process load edges
 *	src --load--> dst,
 *	node \in pts(src) ==>  node--copy-->dst
 */
bool Andersen::processLoad(NodeID node, const ConstraintEdge* load)
{
    /// TODO: New copy edges are also added for black hole obj node to
    ///       make gcc in spec 2000 pass the flow-sensitive analysis.
    ///       Try to handle black hole obj in an appropriate way.
//	if (pag->isBlkObjOrConstantObj(node))
    if (pag->isConstantObj(node) || pag->getGNode(load->getDstID())->isPointer() == false)
        return false;

    numOfProcessedLoad++;

    NodeID dst = load->getDstID();
    return addCopyEdge(node, dst);
}

/*!
 * Process store edges
 *	src --store--> dst,
 *	node \in pts(dst) ==>  src--copy-->node
 */
bool Andersen::processStore(NodeID node, const ConstraintEdge* store)
{
    /// TODO: New copy edges are also added for black hole obj node to
    ///       make gcc in spec 2000 pass the flow-sensitive analysis.
    ///       Try to handle black hole obj in an appropriate way
//	if (pag->isBlkObjOrConstantObj(node))
    if (pag->isConstantObj(node) || pag->getGNode(store->getSrcID())->isPointer() == false)
        return false;

    numOfProcessedStore++;

    NodeID src = store->getSrcID();
    return addCopyEdge(src, node);
}

/*!
 * Process copy edges
 *	src --copy--> dst,
 *	union pts(dst) with pts(src)
 */
bool Andersen::processCopy(NodeID node, const ConstraintEdge* edge)
{
    numOfProcessedCopy++;

    assert((SVFUtil::isa<CopyCGEdge>(edge)) && "not copy/call/ret ??");
    NodeID dst = edge->getDstID();
    const PointsTo& srcPts = getDiffPts(node);

    bool changed = unionPts(dst, srcPts);
    if (changed)
        pushIntoWorklist(dst);
    return changed;
}

/*!
 * Process gep edges
 *	src --gep--> dst,
 *	for each srcPtdNode \in pts(src) ==> add fieldSrcPtdNode into tmpDstPts
 *		union pts(dst) with tmpDstPts
 */
bool Andersen::processGep(NodeID, const GepCGEdge* edge)
{
    const PointsTo& srcPts = getDiffPts(edge->getSrcID());
    return processGepPts(srcPts, edge);
}

/*!
 * Compute points-to for gep edges
 */
bool Andersen::processGepPts(const PointsTo& pts, const GepCGEdge* edge)
{
    numOfProcessedGep++;

    PointsTo tmpDstPts;
    if (SVFUtil::isa<VariantGepCGEdge>(edge))
    {
        // If a pointer is connected by a variant gep edge,
        // then set this memory object to be field insensitive,
        // unless the object is a black hole/constant.
        for (NodeID o : pts)
        {
            if (consCG->isBlkObjOrConstantObj(o))
            {
                tmpDstPts.set(o);
                continue;
            }

            if (!isFieldInsensitive(o))
            {
                setObjFieldInsensitive(o);
                consCG->addNodeToBeCollapsed(consCG->getBaseObjVar(o));
            }

            // Add the field-insensitive node into pts.
            NodeID baseId = consCG->getFIObjVar(o);
            tmpDstPts.set(baseId);
        }
    }
    else if (const NormalGepCGEdge* normalGepEdge = SVFUtil::dyn_cast<NormalGepCGEdge>(edge))
    {
        // TODO: after the node is set to field insensitive, handling invariant
        // gep edge may lose precision because offsets here are ignored, and the
        // base object is always returned.
        for (NodeID o : pts)
        {
            if (consCG->isBlkObjOrConstantObj(o) || isFieldInsensitive(o))
            {
                tmpDstPts.set(o);
                continue;
            }

            NodeID fieldSrcPtdNode = consCG->getGepObjVar(o, normalGepEdge->getAccessPath().getConstantStructFldIdx());
            tmpDstPts.set(fieldSrcPtdNode);
        }
    }
    else
    {
        assert(false && "Andersen::processGepPts: New type GEP edge type?");
    }

    NodeID dstId = edge->getDstID();
    if (unionPts(dstId, tmpDstPts))
    {
        pushIntoWorklist(dstId);
        return true;
    }

    return false;
}

/**
 * Detect and collapse PWC nodes produced by processing gep edges, under the constraint of field limit.
 */
inline void Andersen::collapsePWCNode(NodeID nodeId)
{
    // If a node is a PWC node, collapse all its points-to target.
    // collapseNodePts() may change the points-to set of the nodes which have been processed
    // before, in this case, we may need to re-do the analysis.
    if (consCG->isPWCNode(nodeId) && collapseNodePts(nodeId))
        reanalyze = true;
}

inline void Andersen::collapseFields()
{
    while (consCG->hasNodesToBeCollapsed())
    {
        NodeID node = consCG->getNextCollapseNode();
        // collapseField() may change the points-to set of the nodes which have been processed
        // before, in this case, we may need to re-do the analysis.
        if (collapseField(node))
            reanalyze = true;
    }
}

/*
 * Merge constraint graph nodes based on SCC cycle detected.
 */
void Andersen::mergeSccCycle()
{
    NodeStack revTopoOrder;
    NodeStack & topoOrder = getSCCDetector()->topoNodeStack();
    while (!topoOrder.empty())
    {
        NodeID repNodeId = topoOrder.top();
        topoOrder.pop();
        revTopoOrder.push(repNodeId);
        const NodeBS& subNodes = getSCCDetector()->subNodes(repNodeId);
        // merge sub nodes to rep node
        mergeSccNodes(repNodeId, subNodes);
    }

    // restore the topological order for later solving.
    while (!revTopoOrder.empty())
    {
        NodeID nodeId = revTopoOrder.top();
        revTopoOrder.pop();
        topoOrder.push(nodeId);
    }
}


/**
 * Union points-to of subscc nodes into its rep nodes
 * Move incoming/outgoing direct edges of sub node to rep node
 */
void Andersen::mergeSccNodes(NodeID repNodeId, const NodeBS& subNodes)
{
    for (NodeBS::iterator nodeIt = subNodes.begin(); nodeIt != subNodes.end(); nodeIt++)
    {
        NodeID subNodeId = *nodeIt;
        if (subNodeId != repNodeId)
        {
            mergeNodeToRep(subNodeId, repNodeId);
        }
    }
}

/**
 * Collapse node's points-to set. Change all points-to elements into field-insensitive.
 */
bool Andersen::collapseNodePts(NodeID nodeId)
{
    bool changed = false;
    const PointsTo& nodePts = getPts(nodeId);
    /// Points to set may be changed during collapse, so use a clone instead.
    PointsTo ptsClone = nodePts;
    for (PointsTo::iterator ptsIt = ptsClone.begin(), ptsEit = ptsClone.end(); ptsIt != ptsEit; ptsIt++)
    {
        if (isFieldInsensitive(*ptsIt))
            continue;

        if (collapseField(*ptsIt))
            changed = true;
    }
    return changed;
}

/**
 * Collapse field. make struct with the same base as nodeId become field-insensitive.
 */
bool Andersen::collapseField(NodeID nodeId)
{
    /// Black hole doesn't have structures, no collapse is needed.
    /// In later versions, instead of using base node to represent the struct,
    /// we'll create new field-insensitive node. To avoid creating a new "black hole"
    /// node, do not collapse field for black hole node.
    if (consCG->isBlkObjOrConstantObj(nodeId))
        return false;

    bool changed = false;

    double start = stat->getClk();

    // set base node field-insensitive.
    setObjFieldInsensitive(nodeId);

    // replace all occurrences of each field with the field-insensitive node
    NodeID baseId = consCG->getFIObjVar(nodeId);
    NodeID baseRepNodeId = consCG->sccRepNode(baseId);
    NodeBS & allFields = consCG->getAllFieldsObjVars(baseId);
    for (NodeBS::iterator fieldIt = allFields.begin(), fieldEit = allFields.end(); fieldIt != fieldEit; fieldIt++)
    {
        NodeID fieldId = *fieldIt;
        if (fieldId != baseId)
        {
            // use the reverse pts of this field node to find all pointers point to it
            const NodeSet revPts = getRevPts(fieldId);
            for (const NodeID o : revPts)
            {
                // change the points-to target from field to base node
                clearPts(o, fieldId);
                addPts(o, baseId);
                pushIntoWorklist(o);

                changed = true;
            }
            // merge field node into base node, including edges and pts.
            NodeID fieldRepNodeId = consCG->sccRepNode(fieldId);
            mergeNodeToRep(fieldRepNodeId, baseRepNodeId);
            if (fieldId != baseRepNodeId)
            {
                // gep node fieldId becomes redundant if it is merged to its base node who is set as field-insensitive
                // two node IDs should be different otherwise this field is actually the base and should not be removed.
                redundantGepNodes.set(fieldId);
            }
        }
    }

    if (consCG->isPWCNode(baseRepNodeId))
        if (collapseNodePts(baseRepNodeId))
            changed = true;

    double end = stat->getClk();
    timeOfCollapse += (end - start) / TIMEINTERVAL;

    return changed;
}

/*!
 * SCC detection on constraint graph
 */
NodeStack& Andersen::SCCDetect()
{
    numOfSCCDetection++;

    double sccStart = stat->getClk();
    WPAConstraintSolver::SCCDetect();
    double sccEnd = stat->getClk();

    timeOfSCCDetection +=  (sccEnd - sccStart)/TIMEINTERVAL;

    double mergeStart = stat->getClk();

    mergeSccCycle();

    double mergeEnd = stat->getClk();

    timeOfSCCMerges +=  (mergeEnd - mergeStart)/TIMEINTERVAL;

    return getSCCDetector()->topoNodeStack();
}

/*!
 * Update call graph for the input indirect callsites
 */
bool Andersen::updateCallGraph(const CallSiteToFunPtrMap& callsites)
{

    double cgUpdateStart = stat->getClk();

    CallEdgeMap newEdges;
    onTheFlyCallGraphSolve(callsites,newEdges);
    NodePairSet cpySrcNodes;	/// nodes as a src of a generated new copy edge
    for(CallEdgeMap::iterator it = newEdges.begin(), eit = newEdges.end(); it!=eit; ++it )
    {
        CallSite cs = SVFUtil::getSVFCallSite(it->first->getCallSite());
        for(FunctionSet::iterator cit = it->second.begin(), ecit = it->second.end(); cit!=ecit; ++cit)
        {
            connectCaller2CalleeParams(cs,*cit,cpySrcNodes);
        }
    }
    for(NodePairSet::iterator it = cpySrcNodes.begin(), eit = cpySrcNodes.end(); it!=eit; ++it)
    {
        pushIntoWorklist(it->first);
    }

    double cgUpdateEnd = stat->getClk();
    timeOfUpdateCallGraph += (cgUpdateEnd - cgUpdateStart) / TIMEINTERVAL;

    return (!newEdges.empty());
}

void Andersen::heapAllocatorViaIndCall(CallSite cs, NodePairSet &cpySrcNodes)
{
    assert(SVFUtil::getCallee(cs) == nullptr && "not an indirect callsite?");
    RetICFGNode* retBlockNode = pag->getICFG()->getRetICFGNode(cs.getInstruction());
    const PAGNode* cs_return = pag->getCallSiteRet(retBlockNode);
    NodeID srcret;
    CallSite2DummyValPN::const_iterator it = callsite2DummyValPN.find(cs);
    if(it != callsite2DummyValPN.end())
    {
        srcret = sccRepNode(it->second);
    }
    else
    {
        NodeID valNode = pag->addDummyValNode();
        NodeID objNode = pag->addDummyObjNode(cs.getType());
        addPts(valNode,objNode);
        callsite2DummyValPN.insert(std::make_pair(cs,valNode));
        consCG->addConstraintNode(new ConstraintNode(valNode),valNode);
        consCG->addConstraintNode(new ConstraintNode(objNode),objNode);
        srcret = valNode;
    }

    NodeID dstrec = sccRepNode(cs_return->getId());
    if(addCopyEdge(srcret, dstrec))
        cpySrcNodes.insert(std::make_pair(srcret,dstrec));
}

/*!
 * Connect formal and actual parameters for indirect callsites
 */
void Andersen::connectCaller2CalleeParams(CallSite cs, const SVFFunction* F, NodePairSet &cpySrcNodes)
{
    assert(F);

    DBOUT(DAndersen, outs() << "connect parameters from indirect callsite " << cs.getInstruction()->toString() << " to callee " << *F << "\n");

    CallICFGNode* callBlockNode = pag->getICFG()->getCallICFGNode(cs.getInstruction());
    RetICFGNode* retBlockNode = pag->getICFG()->getRetICFGNode(cs.getInstruction());

    if(SVFUtil::isHeapAllocExtFunViaRet(F) && pag->callsiteHasRet(retBlockNode))
    {
        heapAllocatorViaIndCall(cs,cpySrcNodes);
    }

    if (pag->funHasRet(F) && pag->callsiteHasRet(retBlockNode))
    {
        const PAGNode* cs_return = pag->getCallSiteRet(retBlockNode);
        const PAGNode* fun_return = pag->getFunRet(F);
        if (cs_return->isPointer() && fun_return->isPointer())
        {
            NodeID dstrec = sccRepNode(cs_return->getId());
            NodeID srcret = sccRepNode(fun_return->getId());
            if(addCopyEdge(srcret, dstrec))
            {
                cpySrcNodes.insert(std::make_pair(srcret,dstrec));
            }
        }
        else
        {
            DBOUT(DAndersen, outs() << "not a pointer ignored\n");
        }
    }

    if (pag->hasCallSiteArgsMap(callBlockNode) && pag->hasFunArgsList(F))
    {

        // connect actual and formal param
        const SVFIR::SVFVarList& csArgList = pag->getCallSiteArgsList(callBlockNode);
        const SVFIR::SVFVarList& funArgList = pag->getFunArgsList(F);
        //Go through the fixed parameters.
        DBOUT(DPAGBuild, outs() << "      args:");
        SVFIR::SVFVarList::const_iterator funArgIt = funArgList.begin(), funArgEit = funArgList.end();
        SVFIR::SVFVarList::const_iterator csArgIt  = csArgList.begin(), csArgEit = csArgList.end();
        for (; funArgIt != funArgEit; ++csArgIt, ++funArgIt)
        {
            //Some programs (e.g. Linux kernel) leave unneeded parameters empty.
            if (csArgIt  == csArgEit)
            {
                DBOUT(DAndersen, outs() << " !! not enough args\n");
                break;
            }
            const PAGNode *cs_arg = *csArgIt ;
            const PAGNode *fun_arg = *funArgIt;

            if (cs_arg->isPointer() && fun_arg->isPointer())
            {
                DBOUT(DAndersen, outs() << "process actual parm  " << cs_arg->toString() << " \n");
                NodeID srcAA = sccRepNode(cs_arg->getId());
                NodeID dstFA = sccRepNode(fun_arg->getId());
                if(addCopyEdge(srcAA, dstFA))
                {
                    cpySrcNodes.insert(std::make_pair(srcAA,dstFA));
                }
            }
        }

        //Any remaining actual args must be varargs.
        if (F->isVarArg())
        {
            NodeID vaF = sccRepNode(pag->getVarargNode(F));
            DBOUT(DPAGBuild, outs() << "\n      varargs:");
            for (; csArgIt != csArgEit; ++csArgIt)
            {
                const PAGNode *cs_arg = *csArgIt;
                if (cs_arg->isPointer())
                {
                    NodeID vnAA = sccRepNode(cs_arg->getId());
                    if (addCopyEdge(vnAA,vaF))
                    {
                        cpySrcNodes.insert(std::make_pair(vnAA,vaF));
                    }
                }
            }
        }
        if(csArgIt != csArgEit)
        {
            writeWrnMsg("too many args to non-vararg func.");
            writeWrnMsg("(" + cs.getInstruction()->getSourceLoc() + ")");
        }
    }
}

/*!
 * merge nodeId to newRepId. Return true if the newRepId is a PWC node
 */
bool Andersen::mergeSrcToTgt(NodeID nodeId, NodeID newRepId)
{

    if(nodeId==newRepId)
        return false;

    /// union pts of node to rep
    updatePropaPts(newRepId, nodeId);
    unionPts(newRepId,nodeId);

    /// move the edges from node to rep, and remove the node
    ConstraintNode* node = consCG->getConstraintNode(nodeId);
    bool pwc = consCG->moveEdgesToRepNode(node, consCG->getConstraintNode(newRepId));

    /// 1. if find gep edges inside SCC cycle, the rep node will become a PWC node and
    /// its pts should be collapsed later.
    /// 2. if the node to be merged is already a PWC node, the rep node will also become
    /// a PWC node as it will have a self-cycle gep edge.
    if(node->isPWCNode())
        pwc = true;

    /// set rep and sub relations
    updateNodeRepAndSubs(node->getId(),newRepId);

    consCG->removeConstraintNode(node);

    return pwc;
}
/*
 * Merge a node to its rep node based on SCC detection
 */
void Andersen::mergeNodeToRep(NodeID nodeId,NodeID newRepId)
{

    if (mergeSrcToTgt(nodeId,newRepId))
        consCG->setPWCNode(newRepId);
}

/*
 * Updates subnodes of its rep, and rep node of its subs
 */
void Andersen::updateNodeRepAndSubs(NodeID nodeId, NodeID newRepId)
{
    consCG->setRep(nodeId,newRepId);
    NodeBS repSubs;
    repSubs.set(nodeId);
    /// update nodeToRepMap, for each subs of current node updates its rep to newRepId
    //  update nodeToSubsMap, union its subs with its rep Subs
    NodeBS& nodeSubs = consCG->sccSubNodes(nodeId);
    for(NodeBS::iterator sit = nodeSubs.begin(), esit = nodeSubs.end(); sit!=esit; ++sit)
    {
        NodeID subId = *sit;
        consCG->setRep(subId,newRepId);
    }
    repSubs |= nodeSubs;
    consCG->setSubs(newRepId,repSubs);
    consCG->resetSubs(nodeId);
}

void Andersen::cluster(void) const
{
    assert(Options::MaxFieldLimit() == 0 && "Andersen::cluster: clustering for Andersen's is currently only supported in field-insensitive analysis");
    Steensgaard *steens = Steensgaard::createSteensgaard(pag);
    std::vector<std::pair<unsigned, unsigned>> keys;
    for (SVFIR::iterator pit = pag->begin(); pit != pag->end(); ++pit)
    {
        keys.push_back(std::make_pair(pit->first, 1));
    }

    std::vector<std::pair<hclust_fast_methods, std::vector<NodeID>>> candidates;
    PointsTo::MappingPtr nodeMapping =
        std::make_shared<std::vector<NodeID>>(NodeIDAllocator::Clusterer::cluster(steens, keys, candidates, "aux-steens"));
    PointsTo::MappingPtr reverseNodeMapping =
        std::make_shared<std::vector<NodeID>>(NodeIDAllocator::Clusterer::getReverseNodeMapping(*nodeMapping));

    PointsTo::setCurrentBestNodeMapping(nodeMapping, reverseNodeMapping);
}

/*!
 * Print pag nodes' pts by an ascending order
 */
void Andersen::dumpTopLevelPtsTo()
{
    for (OrderedNodeSet::iterator nIter = this->getAllValidPtrs().begin();
            nIter != this->getAllValidPtrs().end(); ++nIter)
    {
        const PAGNode* node = getPAG()->getGNode(*nIter);
        if (getPAG()->isValidTopLevelPtr(node))
        {
            const PointsTo& pts = this->getPts(node->getId());
            outs() << "\nNodeID " << node->getId() << " ";

            if (pts.empty())
            {
                outs() << "\t\tPointsTo: {empty}\n";
            }
            else
            {
                outs() << "\t\tPointsTo: { ";

                multiset<u32_t> line;
                for (PointsTo::iterator it = pts.begin(), eit = pts.end();
                        it != eit; ++it)
                {
                    line.insert(*it);
                }
                for (multiset<u32_t>::const_iterator it = line.begin(); it != line.end(); ++it)
                {
                    if(Options::PrintFieldWithBasePrefix())
                        if (auto gepNode = SVFUtil::dyn_cast<GepObjVar>(pag->getGNode(*it)))
                            outs() << gepNode->getBaseNode() << "_" << gepNode->getConstantFieldIdx() << " ";
                        else
                            outs() << *it << " ";
                    else
                        outs() << *it << " ";
                }
                outs() << "}\n";
            }
        }
    }

    outs().flush();
}

