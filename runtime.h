typedef long int* ptr;

long int read_int();
void initialize();
ptr collect(long int bytes_requested, ptr rootstack_ptr);

ptr fromspace_begin;
ptr fromspace_end;

ptr rootstack_begin;
ptr rootstack_end;
