//===- Andersen.h -- Field-sensitive Andersen's pointer analysis-------------//
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
 * Andersen.h
 *
 *  Created on: Nov 12, 2013
 *      Author: Yulei Sui
 *
 * The field-sensitive implementation is improved based on
 *
 * Yuxiang Lei and Yulei Sui. "Fast and Precise Handling of Positive Weight Cycles for Field-sensitive Pointer Analysis".
 * 26th International Static Analysis Symposium (SAS'19)
 */

#ifndef INCLUDE_WPA_ANDERSEN_H_
#define INCLUDE_WPA_ANDERSEN_H_

#include "MemoryModel/PointerAnalysisImpl.h"
#include "WPA/WPAStat.h"
#include "WPA/WPASolver.h"
#include "SVFIR/SVFIR.h"
#include "Graphs/ConsG.h"
#include "Util/Options.h"
#include <glog/logging.h>

namespace SVF
{
    enum BufferType : int
    {
        UNKNOWN_BUFFER = 0, // unsafe: ALL
        SEND_BUFFER, // unsafe: STORE
        RECV_BUFFER, // unsafe: LOAD
        SEND_AND_RECV_BUFFER, // unsafe: LOAD & STORE
        INVALID_BUFFER,
    };

    enum StmtType : int
    {
        UNKNOWN_STMT = 0,
        LOAD_STMT,
        STORE_STMT,
        LOAD_AND_STORE_STMT,
        CALL_STMT,
        CIRCULATION_END_STMT,
        UNSAFE_BRANCH_STMT,
        BREAK_STMT,
        RETURN_STMT,
        INVALID_STMT
    };


    inline const char* bufferTypeToString(BufferType type)
    {
        switch (type)
        {
        case SEND_BUFFER: return "Send Buffer";
        case RECV_BUFFER: return "Recv Buffer";
        case SEND_AND_RECV_BUFFER: return "Send & Recv Buffer";
        case UNKNOWN_BUFFER: return "Unknown Buffer";
        default: return "Invalid Buffer";
        }
    }

    inline const char* stmtTypeToString(StmtType type)
    {
        switch (type)
        {
        case LOAD_STMT: return "Load";
        case STORE_STMT: return "Store";
        case LOAD_AND_STORE_STMT: return "Load & Store";
        case CALL_STMT: return "Call";
        case CIRCULATION_END_STMT: return "Circulation End";
        case UNSAFE_BRANCH_STMT: return "Unsafe Branch";
        case RETURN_STMT: return "Return";
        case BREAK_STMT: return "Break";
        case UNKNOWN_STMT: return "Unknown";
        default: return "Invalid";
        }
    }


    class Buffer
    {
    public:
        const SVFInstruction* callInst;
        const SVFValue* buf;
        const ICFGNode* node;
        const BufferType type;
        const ICFGNode* loopEntryNode;
        const ICFGNode* loopBackNode;

        Buffer(const SVFInstruction* call_inst, const SVFValue* buf, const ICFGNode* node,
               const BufferType& type, const ICFGNode* loopEntryNode = nullptr, const ICFGNode* loopBackNode = nullptr)
            : callInst(call_inst), buf(buf), node(node), type(type), loopEntryNode(loopEntryNode),
              loopBackNode(loopBackNode)
        {
        }
    };

    class Monitor{
    public:
        std::vector<Buffer> buffers;
        // std::vector<const SVFStmt*> stmts;

        struct MonitorLogData
        {
            int lines_index;
            std::string file_name;
            int type;
            unsigned long long allIRSum;
            std::multiset<unsigned long long>* pathIRSum;

            bool operator<(const MonitorLogData &x2) const {
                if (lines_index != x2.lines_index) {
                    return lines_index < x2.lines_index;
                } else {
                    return file_name < x2.file_name;
                }
            }

            /// for test.
            MonitorLogData():
                lines_index(0), file_name("null"), type(INVALID_BUFFER), allIRSum(0), pathIRSum(nullptr)
            {}

            MonitorLogData(int lines, std::string &fl_name, int type, unsigned long long sum,
                           std::multiset<unsigned long long>* pathIRSum):
                lines_index(lines), file_name(fl_name), type(type), allIRSum(sum), pathIRSum(pathIRSum)
            {}
        };

        std::set<MonitorLogData> stmtLog;

        // enum LoopHandledTag : int
        // {
        //     UNHANDLED_LOOP = 0,
        //     SAFE_LOOP,
        //     UNSAFE_LOOP,
        //     UNKNOWN_LOOP
        // };

        struct IRStmtSumInfo
        {
            StmtType type;
            unsigned long long allIRSum;
            std::multiset<unsigned long long> pathIRSum;

            explicit IRStmtSumInfo(StmtType type = INVALID_STMT, unsigned long long sum = 0):
                type(type), allIRSum(sum)
            {}

            /// Currently, only accept allIRSum
            void insertPathInfo(unsigned long long sum)
            {
                allIRSum = sum;
            }
        };

        std::map<const ICFGNode*, unsigned long long> functionsIRSum;

        /// final result. <buffer, <unsafe_stmt, {IRStmtSumInfo}>>
        std::map<Buffer*, std::map<const SVFStmt*, IRStmtSumInfo>> bufferAccess;

        /// final log. <[buffer], {accesses}>
        std::map<MonitorLogData, std::set<MonitorLogData>> log;

        /// [<lines, file_name>], {Nodes}
        std::map<std::pair<int, std::string>, std::set<const ICFGNode*>> locToNode;

        /// include loop's entry, out Node. (Unsafe Nodes).
        std::set<const ICFGNode*> loopInfo;

        // <entry, back>
        // std::map<const ICFGNode*, std::set<const ICFGNode*>> loops;
        // /// inv of loops, included goto & return nodes. <back, entry, type>
        // std::set<std::tuple<const ICFGNode*, const ICFGNode*, StmtType>> backEdges;
        // /// [node], loopEntryNode. If node doesn't in loop, will filled by nullptr.
        // std::map<const ICFGNode*, std::set<const ICFGNode*>> nodeBelongLoop;

        // /// <entry>, return key. if not find, return nullptr
        // const ICFGNode* findNodeInLoops(const ICFGNode* entryNode,
        //            const ICFGNode* backNode = nullptr);

        // /// inv of loops, included goto & return nodes. <back, entry, type>. if not find, return {}
        // std::tuple<const ICFGNode*, const ICFGNode*, StmtType>  findNodeInBackEdges(const ICFGNode* entryNode,
        //            const ICFGNode* backNode = nullptr, StmtType type = static_cast<StmtType>(0));
        // /// 记录 SVFLoop* 中有哪些语句, 包括循环体末尾; <Loop, <bufferLog, {accessLogs}>>;
        // std::map<const SVFLoop*, std::map<MonitorLogData, std::set<MonitorLogData>>> loopInfoLog;

        static std::pair<int, std::string> parse(std::string inst_info);

        void parseRecord(std::string call, std::string access,
                         BufferType buf_type = INVALID_BUFFER,
                         StmtType stmt_type = INVALID_STMT,
                         unsigned long long IRStmtsSum = 0,
                         std::multiset<unsigned long long>* pathIRStmtSum = nullptr
        );
    };

class SVFModule;

/*!
 * Abstract class of inclusion-based Pointer Analysis
 */
typedef WPASolver<ConstraintGraph*> WPAConstraintSolver;

class AndersenBase:  public WPAConstraintSolver, public BVDataPTAImpl
{
public:

    // add by bz
    void traverseICFG(Monitor& monitor);
    void ptsMatch();

    // add by zsz
    /// input CallNode, return RetNode. if no CallSite, return nullptr.
    static const ICFGNode* findFuncRetNode(const ICFGNode* callNode);
    static const ICFGNode* findFuncCallNode(const ICFGNode* retNode);
    static constexpr unsigned long long getIRStmtSum(const ICFGNode* node);

    // /// DFS.
    // void findICFGLoops(const ICFGNode* startNode, Monitor& monitor);
    /// Just for test.
    static void testICFGLoops();
    void findICFGBuffers(const ICFGNode* startNode, Monitor& monitor);

    /// void calculateIRStmtSum(Monitor& monitor);
    void calculateIRStmtsSumV2(const ICFGNode* globalNode, Monitor& monitor);
    /// Ignore goto. Keep searching until return to entry or find back.
    // void traverseICFGLoopVer1(const ICFGNode* startNode, Monitor& monitor);

    /// Keep searching until return to entryNode or find backNode/goto/return.
    // void traverseICFGLoopVer2(const ICFGNode* startNode, Monitor& monitor);

    void detectBufferNodes(const ICFGNode* node, Monitor& monitor);
    int detectAccessNodes(const ICFGNode* node, Monitor& monitor, Buffer& buf);

    static void queryIRStmtsSumInit(const ICFGNode* globalNode, Monitor& monitor);
    unsigned long long queryIRStmtsSum(int srcLine, int dstLine, std::string& srcFileName, std::string& dstFileName, Monitor& monitor);

    // void AndersenBase::processFuncNodes(const ICFGNode* node);

    const std::set<std::string> specialFunctions = {
        "foo",         "MPI_Send",     "MPI_Recv",      "MPI_Bcast",
        "MPI_Scatter", "MPI_Gather",   "MPI_Allgather", "MPI_Alltoall",
        "MPI_Reduce",  "MPI_Allreduce"
    };

    // void cleanupBufferAccess(Monitor& monitor);

    // const ICFGNode* findNodeInLoops();
    // std::tuple<const ICFGNode*, const ICFGNode*, StmtType>  findNodeInBackEdges();


    /// Constructor
    AndersenBase(SVFIR* _pag, PTATY type = Andersen_BASE, bool alias_check = true)
        :  BVDataPTAImpl(_pag, type, alias_check), consCG(nullptr)
    {
        iterationForPrintStat = OnTheFlyIterBudgetForStat;
    }

    /// Destructor
    ~AndersenBase() override;

    /// Andersen analysis
    virtual void analyze() override;

    virtual void solveAndwritePtsToFile(const std::string& filename);

    virtual void readPtsFromFile(const std::string& filename);

    virtual void solveConstraints();

    /// Initialize analysis
    virtual void initialize() override;

    /// Finalize analysis
    virtual void finalize() override;

    /// Implement it in child class to update call graph
    virtual inline bool updateCallGraph(const CallSiteToFunPtrMap&) override
    {
        return false;
    }

    /// Methods for support type inquiry through isa, cast, and dyn_cast:
    //@{
    static inline bool classof(const AndersenBase *)
    {
        return true;
    }
    static inline bool classof(const PointerAnalysis *pta)
    {
        return ( pta->getAnalysisTy() == Andersen_BASE
                 || pta->getAnalysisTy() == Andersen_WPA
                 || pta->getAnalysisTy() == AndersenWaveDiff_WPA
                 || pta->getAnalysisTy() == AndersenSCD_WPA
                 || pta->getAnalysisTy() == AndersenSFR_WPA
                 || pta->getAnalysisTy() == TypeCPP_WPA
                 || pta->getAnalysisTy() == Steensgaard_WPA);
    }
    //@}

    /// Get constraint graph
    ConstraintGraph* getConstraintGraph()
    {
        return consCG;
    }

    /// SCC methods
    //@{
    inline NodeID sccRepNode(NodeID id) const override
    {
        return consCG->sccRepNode(id);
    }
    inline NodeBS& sccSubNodes(NodeID repId)
    {
        return consCG->sccSubNodes(repId);
    }
    //@}

    /// dump statistics
    inline void printStat()
    {
        PointerAnalysis::dumpStat();
    }

    virtual void normalizePointsTo() override;

    /// remove redundant gepnodes in constraint graph
    void cleanConsCG(NodeID id);

    NodeBS redundantGepNodes;

    /// Statistics
    //@{
    static u32_t numOfProcessedAddr;   /// Number of processed Addr edge
    static u32_t numOfProcessedCopy;   /// Number of processed Copy edge
    static u32_t numOfProcessedGep;    /// Number of processed Gep edge
    static u32_t numOfProcessedLoad;   /// Number of processed Load edge
    static u32_t numOfProcessedStore;  /// Number of processed Store edge
    static u32_t numOfSfrs;
    static u32_t numOfFieldExpand;

    static u32_t numOfSCCDetection;
    static double timeOfSCCDetection;
    static double timeOfSCCMerges;
    static double timeOfCollapse;
    static u32_t AveragePointsToSetSize;
    static u32_t MaxPointsToSetSize;
    static double timeOfProcessCopyGep;
    static double timeOfProcessLoadStore;
    static double timeOfUpdateCallGraph;
    //@}

protected:
    /// Constraint Graph
    ConstraintGraph* consCG;
};

/*!
 * Inclusion-based Pointer Analysis
 */
class Andersen:  public AndersenBase
{


public:
    typedef SCCDetection<ConstraintGraph*> CGSCC;
    typedef OrderedMap<CallSite, NodeID> CallSite2DummyValPN;

    /// Constructor
    Andersen(SVFIR* _pag, PTATY type = Andersen_WPA, bool alias_check = true)
        :  AndersenBase(_pag, type, alias_check)
    {
    }

    /// Destructor
    virtual ~Andersen()
    {

    }

    /// Initialize analysis
    virtual void initialize();

    /// Finalize analysis
    virtual void finalize();

    /// Reset data
    inline void resetData()
    {
        AveragePointsToSetSize = 0;
        MaxPointsToSetSize = 0;
        timeOfProcessCopyGep = 0;
        timeOfProcessLoadStore = 0;
    }

    /// Methods for support type inquiry through isa, cast, and dyn_cast:
    //@{
    static inline bool classof(const Andersen *)
    {
        return true;
    }
    static inline bool classof(const PointerAnalysis *pta)
    {
        return (pta->getAnalysisTy() == Andersen_WPA
                || pta->getAnalysisTy() == AndersenWaveDiff_WPA
                || pta->getAnalysisTy() == AndersenSCD_WPA
                || pta->getAnalysisTy() == AndersenSFR_WPA);
    }
    //@}

    /// Operation of points-to set
    virtual inline const PointsTo& getPts(NodeID id)
    {
        return getPTDataTy()->getPts(sccRepNode(id));
    }
    virtual inline bool unionPts(NodeID id, const PointsTo& target)
    {
        id = sccRepNode(id);
        return getPTDataTy()->unionPts(id, target);
    }
    virtual inline bool unionPts(NodeID id, NodeID ptd)
    {
        id = sccRepNode(id);
        ptd = sccRepNode(ptd);
        return getPTDataTy()->unionPts(id,ptd);
    }


    void dumpTopLevelPtsTo();

    void setDetectPWC(bool flag)
    {
        Options::DetectPWC.setValue(flag);
    }

protected:

    CallSite2DummyValPN callsite2DummyValPN;        ///< Map an instruction to a dummy obj which created at an indirect callsite, which invokes a heap allocator
    void heapAllocatorViaIndCall(CallSite cs,NodePairSet &cpySrcNodes);

    /// Handle diff points-to set.
    virtual inline void computeDiffPts(NodeID id)
    {
        if (Options::DiffPts())
        {
            NodeID rep = sccRepNode(id);
            getDiffPTDataTy()->computeDiffPts(rep, getDiffPTDataTy()->getPts(rep));
        }
    }
    virtual inline const PointsTo& getDiffPts(NodeID id)
    {
        NodeID rep = sccRepNode(id);
        if (Options::DiffPts())
            return getDiffPTDataTy()->getDiffPts(rep);
        else
            return getPTDataTy()->getPts(rep);
    }

    /// Handle propagated points-to set.
    inline void updatePropaPts(NodeID dstId, NodeID srcId)
    {
        if (!Options::DiffPts())
            return;
        NodeID srcRep = sccRepNode(srcId);
        NodeID dstRep = sccRepNode(dstId);
        getDiffPTDataTy()->updatePropaPtsMap(srcRep, dstRep);
    }
    inline void clearPropaPts(NodeID src)
    {
        if (Options::DiffPts())
        {
            NodeID rep = sccRepNode(src);
            getDiffPTDataTy()->clearPropaPts(rep);
        }
    }

    virtual void initWorklist() {}

    /// Override WPASolver function in order to use the default solver
    virtual void processNode(NodeID nodeId);

    /// handling various constraints
    //@{
    void processAllAddr();

    virtual bool processLoad(NodeID node, const ConstraintEdge* load);
    virtual bool processStore(NodeID node, const ConstraintEdge* load);
    virtual bool processCopy(NodeID node, const ConstraintEdge* edge);
    virtual bool processGep(NodeID node, const GepCGEdge* edge);
    virtual void handleCopyGep(ConstraintNode* node);
    virtual void handleLoadStore(ConstraintNode* node);
    virtual void processAddr(const AddrCGEdge* addr);
    virtual bool processGepPts(const PointsTo& pts, const GepCGEdge* edge);
    //@}

    /// Add copy edge on constraint graph
    virtual inline bool addCopyEdge(NodeID src, NodeID dst)
    {
        if (consCG->addCopyCGEdge(src, dst))
        {
            updatePropaPts(src, dst);
            return true;
        }
        return false;
    }

    /// Update call graph for the input indirect callsites
    virtual bool updateCallGraph(const CallSiteToFunPtrMap& callsites);

    /// Connect formal and actual parameters for indirect callsites
    void connectCaller2CalleeParams(CallSite cs, const SVFFunction* F, NodePairSet& cpySrcNodes);

    /// Merge sub node to its rep
    virtual void mergeNodeToRep(NodeID nodeId,NodeID newRepId);

    virtual bool mergeSrcToTgt(NodeID srcId,NodeID tgtId);

    /// Merge sub node in a SCC cycle to their rep node
    //@{
    void mergeSccNodes(NodeID repNodeId, const NodeBS& subNodes);
    void mergeSccCycle();
    //@}
    /// Collapse a field object into its base for field insensitive analysis
    //@{
    virtual void collapsePWCNode(NodeID nodeId);
    void collapseFields();
    bool collapseNodePts(NodeID nodeId);
    bool collapseField(NodeID nodeId);
    //@}

    /// Updates subnodes of its rep, and rep node of its subs
    void updateNodeRepAndSubs(NodeID nodeId,NodeID newRepId);

    /// SCC detection
    virtual NodeStack& SCCDetect();



    /// Sanitize pts for field insensitive objects
    void sanitizePts()
    {
        for(ConstraintGraph::iterator it = consCG->begin(), eit = consCG->end(); it!=eit; ++it)
        {
            const PointsTo& pts = getPts(it->first);
            NodeBS fldInsenObjs;

            for (NodeID o : pts)
            {
                if(isFieldInsensitive(o))
                    fldInsenObjs.set(o);
            }

            for (NodeID o : fldInsenObjs)
            {
                const NodeBS &allFields = consCG->getAllFieldsObjVars(o);
                for (NodeID f : allFields) addPts(it->first, f);
            }
        }
    }

    /// Get PTA name
    virtual const std::string PTAName() const
    {
        return "AndersenWPA";
    }

    /// Runs a Steensgaard analysis and performs clustering based on those
    /// results set the global best mapping.
    virtual void cluster(void) const;
};



/**
 * Wave propagation with diff points-to set.
 */
class AndersenWaveDiff : public Andersen
{

private:

    static AndersenWaveDiff* diffWave; // static instance

public:
    AndersenWaveDiff(SVFIR* _pag, PTATY type = AndersenWaveDiff_WPA, bool alias_check = true): Andersen(_pag, type, alias_check) {}

    /// Create an singleton instance directly instead of invoking llvm pass manager
    static AndersenWaveDiff* createAndersenWaveDiff(SVFIR* _pag)
    {
        if(diffWave==nullptr)
        {
            diffWave = new AndersenWaveDiff(_pag, AndersenWaveDiff_WPA, false);
            diffWave->analyze();
            return diffWave;
        }
        return diffWave;
    }
    static void releaseAndersenWaveDiff()
    {
        if (diffWave)
            delete diffWave;
        diffWave = nullptr;
    }

    virtual void initialize();
    virtual void solveWorklist();
    virtual void processNode(NodeID nodeId);
    virtual void postProcessNode(NodeID nodeId);
    virtual bool handleLoad(NodeID id, const ConstraintEdge* load);
    virtual bool handleStore(NodeID id, const ConstraintEdge* store);
};

} // End namespace SVF

#endif /* INCLUDE_WPA_ANDERSEN_H_ */
