## 1. DT编译方法简述
### 1.1 修改config/make.def，第108行：

1. 在终端运行:
``` bash
mpicc -show
```
2. 将得到的参数接到第108行代码后：
``` Makefile
CLANG_BC = clang -O0 -g -fno-discard-value-names
```

示例：
在终端运行：
``` bash
root@cang-virtual-machine:/home/cang/Documents/SVF-MPI/run/NPB3.4.3/NPB3.4-MPI/DT# mpicc -show
gcc -Wl,-Bsymbolic-functions -flto=auto -ffat-lto-objects -flto=auto -Wl,-z,relro -I/usr/include/x86_64-linux-gnu/mpich -L/usr/lib/x86_64-linux-gnu -lmpich
```
将"gcc"后的内容接长到108行后：
``` Makefile
CLANG_BC = clang -O0 -g -fno-discard-value-names -Wl,-Bsymbolic-functions -flto=auto -ffat-lto-objects -flto=auto -Wl,-z,relro -I/usr/include/x86_64-linux-gnu/mpich -L/usr/lib/x86_64-linux-gnu -lmpich
```

### 1.2 make
1. cd到DT目录，make clean：
``` bash
make clean
```
2. 指定参数，make DT
``` bash
sudo make NPROCS=4 CLASS=A
```
3. make 可执行文件
``` bash
sudo make test_exe
```
它预期将在每个源文件目录下生成其对应的.bc文件，并在DT目录下生成一个集成了所有.bc文件的"test.bc"。
sudo make test_exe后，将使用test.bc，在DT目录下编译出test_exe可执行文件。
### 1.3 running
使用该命令运行：
``` bash
mpirun ./test_exe
```
输出会提示使用选项：
``` bash
** Usage: mpirun -np N ../bin/dt.S GraphName
** Where 
   - N is integer number of MPI processes
   - S is the class S, W, or A 
   - GraphName is the communication graph name BH, WH, or SH.
   - the number of MPI processes N should not be be less than 
     the number of nodes in the graph
```

示例：
``` bash
root@cang-virtual-machine:/home/cang/Documents/SVF-MPI/run/NPB3.4.3/NPB3.4-MPI/DT# mpirun -np 21 ./test_exe BH
```
### 1.4 更改wpa参数
1. 点击"wpa"字样旁下拉窗口，点击Edit Configurations...
2. 修改wpa的Program arguments:
```
-steens -dump-icfg -dump-pag -dump-callgraph -print-pts test.bc
```
3. 修改wpa的Working directory至DT所在目录:
   示例目录：
```
/home/cang/Documents/SVF-MPI/run/NPB3.4.3/NPB3.4-MPI/DT
```
4. 点击运行即可构建。

## 2. miniAMR编译方法简述
### 2.1 修改openmp/Makefile第21行CLANG_BC，方法同DT。
### 2.2 make
1. cd到openmp目录，make clean：
``` bash
make clean
```
2. make all
``` bash
sudo make all
```
它预期将在每个源文件目录下生成其对应的.o和.bc文件，并在openmp目录下生成一个集成了所有.bc文件的"test.bc"，以及对应的可执行文件test_exe。
### 2.3 running
使用该命令运行：
``` bash
mpirun ./test_exe
```

### 2.4 更改wpa参数
1. 点击"wpa"字样旁下拉窗口，点击Edit Configurations...
2. 修改wpa的Program arguments:
```
-steens -dump-icfg -dump-pag -dump-callgraph -print-pts test.bc
```
3. 修改wpa的Working directory至openmp所在目录:
   示例目录：
```
/home/cang/Documents/SVF-MPI/run/miniAMR-master/openmp
```
4. 点击运行即可构建。

## 3. adept-kernel-mpi编译方法简述
### 3.1 修改Makefile第33行CLANG_BC，方法同DT。
### 3.2 make
1. cd到openmp目录，make clean：
``` bash
make clean
```
2. make all
``` bash
sudo make all
```
它预期将在每个源文件目录下生成其对应的.o和.bc文件，并在根目录下生成一个集成了所有.bc文件的"test.bc"，以及对应的可执行文件test_exe。
### 3.3 running
使用该命令运行：
``` bash
mpirun ./test_exe
```

### 3.4 更改wpa参数
1. 点击"wpa"字样旁下拉窗口，点击Edit Configurations...
2. 修改wpa的Program arguments:
```
-steens -dump-icfg -dump-pag -dump-callgraph -print-pts test.bc
```
3. 修改wpa的Working directory至所在目录:
   示例目录：
```
/home/cang/Documents/SVF-MPI/run/adept-kernel-mpi-master
```
4. 点击运行即可构建。

如果要暂时禁用寻找IR指令和的功能，需要将"const bool calculateIRStmtSum"字段设为false.
## 4. 目前方法存在的问题
1. DT部分中，running时输出的"Compile options"不完全准确。在该方法中，使用的实际是$CLANG_BC而非mpicc。（这不是一个错误，但需要注意。）
2. 不能处理的情况：当buffer是某个结构体或类的成员，而访问是该结构体或类本身或其他部分时，不能分辨是否是不安全访问。目前检查认为是alias方法部分出现了问题，也许可以通过给alias包括了更大域的SVFValue解决这个问题。
   示例（目前在DT测试集中发现的情况）：
``` Cpp {.line-numbers}
561 MPI_Recv(feat->val,feat->len,MPI_DOUBLE,tail>address,tag,MPI_COMM_WORLD,&status);
562 resfeat=WindowFilter(resfeat,feat,nd->id);
```
在这个情况中，561行MPI_Recv的buffer无法检测到562行调用函数传入指针feat对该buffer来说是不安全访问。
一种解决方法是，将buffer认定为该指针对应的整个结构体或类的域（在该例中为记录"feat"指针而非feat->val部分）。这样alias可以找到562行对buffer的访问是不安全的。