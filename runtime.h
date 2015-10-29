typedef long int* ptr;

long int read_int();
void initialize();
ptr collect(long int bytes_requested, ptr rootstack_ptr);
void copy_vector(ptr* vec, ptr* free_ptr);
void process_vector(ptr* scan_ptr, ptr* free_ptr);
int is_forwarding(long int tag);
long int six_ones();

ptr fromspace_begin;
ptr fromspace_end;

ptr rootstack_begin;
ptr rootstack_end;
