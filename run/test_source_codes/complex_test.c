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

// buffer1: Load & Store; buffer2: Load.
int mpi_comm_call(int* buffer1, int buffer2){
    *buffer1 = buffer2;
    return 0;
}

int main() {
    int send_buffer[5] = {1, 2, 3, 4, 5};
    int recv_buffer[5];
    int bcast_buffer[5] = {1, 2, 3, 4, 5};
    int *p_send = send_buffer;
    int ignore = 0; // 无关变量

    for (int i = 0; i < 10; i++) {
        MPI_Send(send_buffer, 5, sizeof(int), 1, 0, MPI_COMM_WORLD);

        printf("%d \n", ignore);

        *p_send = 1;
        MPI_Recv(recv_buffer, 5, sizeof(int), 0, 0, MPI_COMM_WORLD, NULL);

        thread_rank = 0;
        MPI_Bcast(bcast_buffer, 5, sizeof(int), 0, MPI_COMM_WORLD); // 根进程广播数据

        for (int ii = 0; ii < 5; ii++) {
            for (int jj = 0; jj < 5; jj++) {
                MPI_Recv(recv_buffer, 5, sizeof(int), 0, 0, MPI_COMM_WORLD, NULL);
            }
        }

        printf("%d \n", bcast_buffer[0]);
        mpi_comm_call(&bcast_buffer[0], send_buffer[1]);

        thread_rank = 1;
        MPI_Bcast(bcast_buffer, 5, sizeof(int), 0, MPI_COMM_WORLD); // 接收进程接收广播的数据

        for (int ii = 0; ii < 5; ii++) {
            for (int jj = 0; jj < 5; jj++) {
                MPI_Recv(recv_buffer, 5, sizeof(int), 0, 0, MPI_COMM_WORLD, NULL);
            }
        }

        for (int ii = 0; ii < 5; ii++) {
            for (int jj = 0; jj < 5; jj++) {  // 存疑：这个循环对应的ICFG是两条goto语句。也就是说，不存在指回循环开始的语句。具体解释请看附图。
                goto returnbreakfor;
            }
        }

        returnbreakfor:;
        ignore = 6; // 无关变量
        while(ignore){
            ignore -= ignore & -ignore; // -= lowbit
        }
        ignore = 1;

        goto_tag:
        if (ignore & 1)
            for (int j = 0; j < 5; j++) {
                printf("%d ", recv_buffer[j]);
            }

        if (i == 3){
            printf("%d \n", ignore);
        }
        else{
            printf("%d \n", ignore);
        }

        switch (i) {
            case 1:  printf("%d \n", ignore); break;
            case 2:  printf("%d \n", ignore & 1);
            case 3:  printf("%d \n", ignore & 2); break;
            default: printf("%d \n", ignore & 4);
        }

        if (ignore > 0) {
            ignore = 0;
            goto goto_tag;
        }

        if (ignore == -1)
            return 0;

        for (int j = 0; j < 5; j++) {
            printf("%d ", recv_buffer[j]);;
        }

        MPI_Recv(recv_buffer, 5, sizeof(int), 0, 0, MPI_COMM_WORLD, NULL);

        for (int testi = 0; testi < 5; testi++) {
            for (int testj = 0; testj < 5; testj++) {
                if(testi & testj) {
                    ignore = -1;
                    goto goto_tag;
                }
            }
        }

        printf("%d ", recv_buffer[1]);
    }

    *p_send = 1;
    MPI_Send(send_buffer, 5, sizeof(int), 1, 0, MPI_COMM_WORLD);

    return 0;
}
