# 基础配置（保留原有核心变量）
SHELL = /bin/sh
CC    = mpicc
LD    = mpicc
CPPFLAGS = -I.
CFLAGS   = -O3 -fopenmp
LDFLAGS  =
LDLIBS   = -lm -lgomp -lmpich

# 核心目标定义
EXEC      = miniAMR.x
BC_TARGET = test.bc
BC_EXEC   = test_exe

# 源文件列表（保留原有OBJS结构）
OBJS = block.o check_sum.o comm_block.o comm.o comm_parent.o comm_refine.o \
       comm_util.o driver.o init.o main.o move.o pack.o plot.o profile.o \
       rcb.o refine.o sfc.o stencil.o util.o

# Bitcode生成配置（关键修改点）
CLANG_BC = clang -O0 -g -fno-discard-value-names -fopenmp -I/usr/include/x86_64-linux-gnu/mpich
BC_OBJS  = $(OBJS:.o=.bc)

# 主构建目标（兼容原有逻辑）
all: $(EXEC) $(BC_EXEC)

# 原有可执行文件构建规则
$(EXEC): $(OBJS)
	$(LD) $(LDFLAGS) -o $@ $(OBJS) $(LDLIBS)

# 新增：生成合并的test.bc
$(BC_TARGET): $(BC_OBJS)
	llvm-link $^ -o $@

# 新增：从test.bc生成最终可执行文件（仿示例test_exe逻辑）
$(BC_EXEC): $(BC_TARGET)
	$(CLANG_BC) -fopenmp -O3 $< -o $@ $(LDLIBS)

# Bitcode生成规则（关键修改点）
%.bc: %.c
	$(CLANG_BC) -emit-llvm $(CPPFLAGS) -c $< -o $@

# 原有.o文件生成规则
%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

# 清理规则
clean:
	rm -f *.o *.bc $(EXEC) $(BC_TARGET) $(BC_EXEC)

# 依赖关系（保留原有结构）
block.o: block.h proto.h comm.h timer.h
check_sum.o: block.h comm.h proto.h timer.h
comm_block.o: block.h comm.h proto.h
comm.o: block.h comm.h proto.h timer.h
comm_parent.o: block.h comm.h proto.h
comm_refine.o: block.h comm.h proto.h
comm_util.o: block.h comm.h proto.h
driver.o: block.h comm.h proto.h timer.h
init.o: block.h proto.h comm.h
main.o: block.h comm.h proto.h param.h timer.h
move.o: block.h comm.h proto.h
pack.o: block.h comm.h proto.h
plot.o: block.h comm.h proto.h
profile.o: block.h comm.h proto.h timer.h
rcb.o: block.h comm.h proto.h timer.h
refine.o: block.h comm.h proto.h timer.h
sfc.o: block.h comm.h proto.h timer.h
stencil.o: block.h comm.h proto.h
util.o: block.h comm.h proto.h timer.h