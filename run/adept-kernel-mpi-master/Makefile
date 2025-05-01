# Copyright (c) 2015 The University of Edinburgh.
# 
# This software was developed as part of the                       
# EC FP7 funded project Adept (Project ID: 610490)                 
#     www.adept-project.eu                                            
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Default to gcc but allong setting CC in the shell (or via cmd line) to another compiler
ifndef $CC
  CC = mpicc
endif

#set OPT=debug to compile with -g -O0
ifndef $OPT
  OPT = opt
endif

ifndef $ARCH
  ARCH=generic
endif

CLANG_BC = clang -O0 -g -fno-discard-value-names -fopenmp -I/usr/include/x86_64-linux-gnu/mpich

include platform_inc/${ARCH}_${CC}_${OPT}.inc

SOURCES = main.c level1.c blas_op.c utils.c stencil.c fileparse.c matrix_utils.c cg.c
LDFLAGS += -lm
EXE = kernel

CFLAGS += -ffunction-sections -fdata-sections
LDFLAGS += -Wl,--gc-sections

LDLIBS = -lmpich -lm -L/usr/lib/x86_64-linux-gnu

BC_TARGET = test.bc
BC_EXEC   = test_exe
BC_OBJS  = $(SOURCES:.c=.bc)

#all: $(EXE)
all: $(EXE) $(BC_EXEC)

$(BC_TARGET): $(BC_OBJS)
	llvm-link $^ -o $@

# 新增：从test.bc生成最终可执行文件（仿示例test_exe逻辑）
$(BC_EXEC): $(BC_TARGET)
	$(CLANG_BC) -fopenmp $< -o $@ $(LDLIBS)

# Bitcode生成规则（关键修改点）
%.bc: %.c
	$(CLANG_BC) -emit-llvm -c $(CFLAGS) $(CMPI_INC) $(CONVERTFLAG) $< -o $@

$(EXE): $(SOURCES)
	$(CC) $(CFLAGS) -o $(EXE) $(SOURCES) $(DMACROS) $(LDFLAGS)

clean:
	rm -rf *~ *.o $(EXE)
	rm -rf *~ *.bc
