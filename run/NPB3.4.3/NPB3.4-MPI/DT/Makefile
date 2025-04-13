SHELL=/bin/sh
BENCHMARK=dt
BENCHMARKU=DT

include ../config/make.def

include ../sys/make.common
#Override PROGRAM
DTPROGRAM  = test.bc

OBJS = dt.bc DGraph.bc \
	${COMMON}/c_print_results.o ${COMMON}/c_timers.o ${COMMON}/c_randdp.o

${PROGRAM}: config ${OBJS}
	llvm-link dt.bc DGraph.bc -o ${DTPROGRAM}

# 新增目标：生成可执行文件
test_exe: test.bc ${COMMON}/c_print_results.o ${COMMON}/c_timers.o ${COMMON}/c_randdp.o
	$(CLANG_BC) $< ${COMMON}/c_print_results.o ${COMMON}/c_timers.o ${COMMON}/c_randdp.o $(CMPI_LIB) -o $@

# 生成.bc文件的规则
%.bc: %.c
	$(CLANG_BC) -emit-llvm -c $(CFLAGS) $(CMPI_INC) $(CONVERTFLAG) $< -o $@

dt.bc:             dt.c  npbparams.h
DGraph.bc:	DGraph.c DGraph.h

clean:
	- rm -f *.o *.bc *~ mputil*
	- rm -f dt npbparams.h core