SHELL=/bin/sh
BENCHMARK=dt
BENCHMARKU=DT

include ../config/make.def

include ../sys/make.common
#Override PROGRAM
DTPROGRAM  = test.bc

COMMON_BC = ${COMMON}/c_print_results.bc ${COMMON}/c_timers.bc ${COMMON}/c_randdp.bc
OBJS = dt.bc DGraph.bc $(COMMON_BC)

${PROGRAM}: config ${OBJS}
	llvm-link dt.bc DGraph.bc ${COMMON}/c_print_results.bc ${COMMON}/c_timers.bc ${COMMON}/c_randdp.bc -o ${DTPROGRAM}

# 新增目标：生成可执行文件
test_exe: test.bc
	$(CLANG_BC) $< $(CMPI_LIB) -o $@

# 生成.bc文件的规则
%.bc: %.c
	$(CLANG_BC) -emit-llvm -c $(CFLAGS) $(CMPI_INC) $(CONVERTFLAG) $< -o $@

${COMMON}/c_print_results.bc: ${COMMON}/c_print_results.c
	$(CLANG_BC) -emit-llvm -c $(CFLAGS) $(CMPI_INC) $(CONVERTFLAG) $< -o $@

${COMMON}/c_timers.bc: ${COMMON}/c_timers.c
	$(CLANG_BC) -emit-llvm -c $(CFLAGS) $(CMPI_INC) $(CONVERTFLAG) $< -o $@

${COMMON}/c_randdp.bc: ${COMMON}/randdp.c
	$(CLANG_BC) -emit-llvm -c $(CFLAGS) $(CMPI_INC) $(CONVERTFLAG) $< -o $@

dt.bc:             dt.c  npbparams.h
DGraph.bc:	DGraph.c DGraph.h

clean:
	- rm -f *.o *.bc *~ mputil*
	- rm -f dt npbparams.h core
	- rm -f $(COMMON_BC)  # 清理 COMMON 的 .bc 文件