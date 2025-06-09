# 基于静态值流分析的 MPI 程序自动性能优化关键技术研究

## 项目简介
本项目通过拓展基于 LLVM 开发的静态值流分析工具 SVF，针对 MPI 程序的阻塞通信性能瓶颈，使用静态分析技术检测阻塞操作的最早数据依赖点，并自动转换为非阻塞通信模式，优化程序执行效率。核心技术路径包括指针分析拓展、数据依赖追踪及非阻塞转换策略设计。


## 主要工作内容
1. **技术拓展与算法实现**
    - 拓展 SVF 工具的 Andersen 指针分析算法模块，实现对 MPI 阻塞通信中指令访问缓冲区行为的精准检测。
    - 基于过程间控制流图（ICFG），设计规则表驱动的代码插入点搜索机制，定位非阻塞通信转换的最优位置。
2. **代码工程与维护**
    - 负责项目代码仓库的开发、迭代及测试，确保分析框架与 MPI 程序的兼容性和稳定性。


## 关于这个仓库
- 本仓库为国防科技大学科研项目的部分技术实现载体，由作者 CangShuV 开发、测试及维护，集中展示 MPI 程序静态分析与性能优化的核心代码。
- 仓库结构包含 SVF 基础框架拓展模块、MPI 通信分析组件、测试用Benchmarks及构建脚本，完整复现了从指针分析到非阻塞转换的全流程。


## 环境配置与运行指南
1. **克隆仓库**
```
git clone https://github.com/CangShuV/SVF-MPI.git
cd SVF-MPI
```
2. **环境准备**
    - 参考`setup.sh`脚本完成依赖安装（LLVM-16.0.0、Glog、MPI 开发环境等）。
    - 如需快速部署，可通过`Dockerfile`构建容器化环境。
    - 详细安装说明请参考文档：[SVF Setup Guide](https://github.com/svf-tools/SVF/wiki/Setup-Guide#getting-started)

3. **运行与测试**
    - 构建项目：`source build.sh`
    - 详细测试说明请查阅文档：[run/User Guide (zh).md](https://github.com/CangShuV/SVF-MPI/blob/main/run/User%20Guide%20(zh).md)，内含 MPI 程序分析流程、参数配置及使用选项示例。


## 技术亮点
- **跨领域分析能力**：结合静态值流分析（SVF）与 MPI 通信模型，实现数据依赖与通信行为的联合分析。
- **自动化优化流程**：从依赖检测到代码转换的全流程自动化，减少人工优化成本。


## References

1. Alexis Lescouet, Élisabeth Brunet, François Trahay, Gaël Thomas. "Transparent Overlapping of Blocking Communication in MPI Applications." *2020 IEEE International Conference on High-Performance Computing and Communications (HPCC)*, Dec 2020, Yanuca Island (online), Fiji. [DOI: 10.1109/HPCC-SmartCity-DSS50907.2020.00097](https://doi.org/10.1109/HPCC-SmartCity-DSS50907.2020.00097).

2. Van-Man Nguyen, Emmanuelle Saillard, Julien Jaeger, Denis Barthou, Patrick Carribault. "Automatic Code Motion to Extend MPI Nonblocking Overlap Window." *C3PO’20 Workshop - First Workshop on Compiler-Assisted Correctness Checking and Performance Optimization for HPC*, Jun 2020, Frankfurt / Virtual, Germany. [DOI: 10.1007/978-3-030-59851-8_4](https://doi.org/10.1007/978-3-030-59851-8_4).

3. Van-Man Nguyen, Emmanuelle Saillard, Julien Jaeger, Denis Barthou, Patrick Carribault. "PARCOACH Extension for Static MPI Nonblocking and Persistent Communication Validation." *2020 IEEE/ACM 4th International Workshop on Software Correctness for HPC Applications (Correctness)*, Nov 2020, Atlanta / Virtual, United States. [DOI: 10.1109/Correctness51934.2020.00009](https://doi.org/10.1109/Correctness51934.2020.00009).

4. Van Man Nguyen. "Compile-time Validation and Optimization of MPI Nonblocking Communications." *2022*. Thesis presented for obtaining the grade of Doctor of the University of Bordeaux.

5. H. Ahmed, A. Skjellum, and P. Pirkelbauer, “Petal tool for analyzing and transforming legacy MPI applications,” in _Proceedings of the 28th International Workshop on Languages and Compilers for Parallel Computing_, LCPC 2015, New York, NY, USA, 2016. [DOI: 10.1007/978-3-319-44932-5_11](https://doi.org/10.1007/978-3-319-44932-5_11).

6. H. Ahmed, A. Skjellum, P. Bangalore, and P. Pirkelbauer, “Transforming Blocking MPI Collectives to Non-blocking and Persistent Operations,” in _Proceedings of EuroMPI/USA ’17_, Chicago, IL, USA, Sep. 2017. [DOI: 10.1145/3127024.3127033](https://doi.org/10.1145/3127024.3127033).

7. A. Danalis, L. Pollock, J. Cavazos, and M. Swany, “MPI-aware Compiler Optimizations for Improving Communication-Computation Overlap,” in _Proceedings of the 23rd International Conference on Supercomputing_, ICS ’09, Yorktown Heights, NY, USA, Jun. 2009. [DOI: 10.1145/1542275.1542321](https://doi.org/10.1145/1542275.1542321).

8. S. Stattelmann, “Function Pointer Analysis for C Programs,” Bachelor’s Thesis, Saarland University, Saarbrücken, Germany, Aug. 2008.

9. Yulei Sui and Jingling Xue. "SVF: Interprocedural Static Value-Flow Analysis in LLVM." In _Proceedings of the 25th International Conference on Compiler Construction_, pp. 265–266. ACM, 2016.

10. Yulei Sui, Ding Ye, and Jingling Xue. "Detecting Memory Leaks Statically with Full-Sparse Value-Flow Analysis." _IEEE Transactions on Software Engineering_, 40(2): 107–122, 2014.


## 联系方式
如有任何问题或建议，请通过以下方式联系我们：
- GitHub Issues: [https://github.com/CangShuV/SVF-MPI/issues](https://github.com/CangShuV/SVF-MPI/issues)
- Email: [CangShuV@outlook.com](CangShuV@outlook.com)

**备注**：本仓库代码及文档仅用于计算机专业推免材料展示，如需完整技术文档或项目报告，可进一步沟通提供。
