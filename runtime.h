typedef long int* ptr;

long int read_int();
void print_int(long int x);
void initialize();
ptr debug_collect(long int bytes_requested)
ptr collect(long int bytes_requested, ptr rootstack_ptr);
ptr alloc(long int bytes_requested);
//ptr alloc(long int bytes_requested, ptr rootstack_ptr);

ptr free_ptr;

ptr fromspace_begin;
ptr fromspace_end;

ptr rootstack_begin;
ptr rootstack_end;
