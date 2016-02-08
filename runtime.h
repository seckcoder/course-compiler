#include <stdint.h>

/* 
   A ptr (also known as a boxed immediate) is conceptually a datum
   that may be pointing to some other ptr(s). Since we rely on
   metainformation to determine if a ptr is a pointer or not we should
   consider it as data and cast to ptr* once we know it is a pointer.
   
   For that reason the following type def is slightly misleading.
   ptrs are defined as a pointer type to ensure compatibility with
   pointer types, they *must* be the same width as the system pointer
   type. Throughout the compiler we assume that pointers are 64bits
   in width, so int64_t is simply a reminder of this. Concretely this
   may be seen in our metainformation tagging scheme.
*/
typedef int64_t ptr;

/* 
   Fromspace is our heap which is conceptually an array of ptr
   unless meta informations tells us they are ptr* themeselves.
*/
ptr* fromspace_begin;
ptr* fromspace_end;

/* 
   The free_ptr is the pointer into the heap were the next free
   quadword is located.
*/
ptr* free_ptr;

/* 
   The root stack is an array of pointers into the heap which
   is conceptually an array of quad word integers. 
*/
ptr** rootstack_begin;
ptr** rootstack_end;

// Initialize the memory of the runtime with a fixed
// rootstack size and initial heap size.
void initialize(long int rootstack_size, long int heap_size);

// Collect garbage data making room for a requested amount
// of memory.
void collect(ptr** rootstack_ptr, long int bytes_requested);

long int read_int();
void print_int(long int x);
void print_bool(int x);



