typedef long int* ptr;

long int read_int();
void print_int(long int x);
void print_bool(int x);

void initialize(long int rootstack_length, long int heap_length);
ptr debug_collect(ptr rootstack_ptr, long int bytes_requested);
void collect(ptr rootstack_ptr, long int bytes_requested);

ptr free_ptr;

ptr fromspace_begin;
ptr fromspace_end;

ptr rootstack_begin;
ptr rootstack_end;
