#include <stdio.h>

int mpi_comm(int *x, int val) {
    return val;
}

int mpi_comm(int *send, int*recv, int val){
    return val;
}

int main() {
    int send_buf = 0;
    int recv_buf = 0;
    for (int i = 0; i < 10; i++) {
        int*p = &send_buf;
        mpi_comm(p, 1);
        *p=1;
        mpi_comm(&send_buf, &recv_buf, 2);
        printf("%d", recv_buf);
        printf("body");
    }
    return 0;
}
