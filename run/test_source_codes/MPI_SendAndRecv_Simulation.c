#include <stdio.h>

#define MPI_COMM_WORLD 0

int MPI_Send(const void *buf, int count, int datatype, int dest, int tag, int comm) {
    for (int i = 0; i < count; i++) {
        printf("%d ", ((int*)buf)[i]);
    }
    return 0;
}

int MPI_Recv(void *buf, int count, int datatype, int source, int tag, int comm, int *status) {
    for (int i = 0; i < count; i++) {
        ((int*)buf)[i] = i + 1;
    }
    return 0;
}

int main() {
//    int send_buffer[5] = {1, 2, 3, 4, 5};  // 发送缓冲区
//    int recv_buffer[5];  // 接收缓冲区
    int send_buffer = 1;
    int recv_buffer = 0;

    MPI_Send(&send_buffer, 1, sizeof(int), 1, 0, MPI_COMM_WORLD);

    MPI_Recv(&recv_buffer, 1, sizeof(int), 0, 0, MPI_COMM_WORLD, NULL);

//    for (int i = 0; i < 5; i++) {
//        printf("%d ", recv_buffer[i]);
//    }
    printf("%d \n", recv_buffer);

    return 0;
}
