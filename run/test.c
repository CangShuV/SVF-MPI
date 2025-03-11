#include <stdio.h>

#define MPI_COMM_WORLD 0
int thread_rank = 0;

int MPI_Send(const void *buf, int count, int datatype, int dest, int tag, int comm) {
    printf("Sending data to process %d\n", dest);
    printf("Data: ");
    for (int i = 0; i < count; i++) {
        printf("%d ", ((int*)buf)[i]);
    }
    printf("\n");
    return 0;
}

int MPI_Recv(void *buf, int count, int datatype, int source, int tag, int comm, int *status) {
    printf("Receiving data from process %d\n", source);
    for (int i = 0; i < count; i++) {
        ((int*)buf)[i] = i + 1;
    }
    return 0;
}

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
    int recv_buffer[5];
    int *p_send = send_buffer;
    int p = 0; // 无关变量

    for (int i = 0; i < 10; i++) {
        MPI_Send(&send_buffer, 5, sizeof(int), 1, 0, MPI_COMM_WORLD);

        p = 1;
        printf("%d \n", p);

        *p_send = 1;
        MPI_Recv(&recv_buffer, 5, sizeof(int), 0, 0, MPI_COMM_WORLD, NULL);

        thread_rank = 0;
        MPI_Bcast(send_buffer, 5, sizeof(int), 0, MPI_COMM_WORLD); // 根进程广播数据

        thread_rank = 1;
        MPI_Bcast(recv_buffer, 5, sizeof(int), 0, MPI_COMM_WORLD); // 接收进程接收广播的数据

        for (int j = 0; j < 5; j++) {
            printf("%d ", recv_buffer[j]);
        }
    }

    return 0;
}
