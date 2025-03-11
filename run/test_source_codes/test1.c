#include <stdio.h>

#define MPI_COMM_WORLD 0

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

int main() {
    //    int send_buffer[5] = {1, 2, 3, 4, 5};
    //    int recv_buffer[5];
    int send_buffer = 1;
    int recv_buffer = 0;
    int *p_send = &send_buffer;
    int p = 0;

    for (int i = 0; i < 10; i++) {
        MPI_Send(&send_buffer, 1, sizeof(int), 1, 0, MPI_COMM_WORLD);

        p = 1;
        printf("%d \n", p);

        * p_send = 1;
        MPI_Recv(&recv_buffer, 1, sizeof(int), 0, 0, MPI_COMM_WORLD, NULL);

        //    for (int i = 0; i < 5; i++) {
        //        printf("%d ", recv_buffer[i]);
        //    }
        printf("%d \n", recv_buffer);
    }

    return 0;
}
