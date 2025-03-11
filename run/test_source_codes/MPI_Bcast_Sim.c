#include <stdio.h>

#define MPI_COMM_WORLD 0
int thread_rank = 0;

int MPI_Bcast(void *buf, int count, int datatype, int root, int comm) {
    if (root == thread_rank) {
        // 广播
        for (int i = 0; i < count; i++) {
            printf("Data[%d]: %d\n", i, ((int *)buf)[i]);
        }
    } else {
        for (int i = 0; i < count; i++) {
            ((int *)buf)[i] = i + 1;
        }
    }
    return 0;
}

int main() {
    int send_buffer[5] = {1, 2, 3, 4, 5};
    int recv_buffer[5] = {0};

    thread_rank = 0;
    MPI_Bcast(send_buffer, 5, sizeof(int), 0, MPI_COMM_WORLD); // 根进程广播数据

    thread_rank = 1;
    MPI_Bcast(recv_buffer, 5, sizeof(int), 0, MPI_COMM_WORLD); // 接收进程接收广播的数据

    return 0;
}
