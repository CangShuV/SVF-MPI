#define CLASS 'A'
/*
   This file is generated automatically by the setparams utility.
   It sets the number of processors and the class of the NPB
   in this directory. Do not modify it by hand.   */
   
#define NUM_SAMPLES 110592
#define STD_DEVIATION 512
#define NUM_SOURCES 16
#define COMPILETIME "01 May 2025"
#define NPBVERSION "3.4.3"
#define MPICC "mpicc"
#define CFLAGS "-O3"
#define CLINK "$(MPICC)"
#define CLINKFLAGS "$(CFLAGS)"
#define CMPI_LIB "$(if $(MPI_LIB),-L$(MPI_LIB)) -lmpi"
#define CMPI_INC "$(if $(MPI_INC),-I$(MPI_INC))"
