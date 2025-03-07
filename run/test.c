int* mpi_receive(int* x, int val){
    return x;
}
int main(){
int a = 0;
int buf = 0;
for(int i = 0; i < a; i++){
int *p = &buf;
*p = 1;
mpi_receive(p, 1);
int *q = &buf;
printf("%d", *q);
}
return 0;
}
