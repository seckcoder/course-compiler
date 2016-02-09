#include <stdlib.h>
#include <stdio.h>
#include "runtime.h"
#define DEBUG_MODE 1

// Often misunderstood static global variables in C are not
// accessible to code outside of the module.
// No one besides the collector ever needs to know tospace exists.
static int64_t* tospace_begin;
static int64_t* tospace_end;

// initialized it set during initialization of the heap, and can be
// checked in order to ensure that initialization has occurred.
static int initialized = 0;


/*
  Object Tag (64 bits)
  #b|- 7 bit unused -|- 50 bit field [50, 0] -| 6 bits lenght -| 1 bit isForwarding Pointer  
  * If the bottom-most bit is zero, the tag is really a forwarding pointer.
  * Otherwise, its an object. In that case, the next 
    6 bits give the length of the object (max of 50 64-bit words).
    The next 50 bits say where there are pointers.
    A '1' is a pointer, a '0' is not a pointer.
*/
static const int TAG_IS_NOT_FORWARD_MASK = 1;
static const int TAG_LENGTH_MASK = 126;
static const int TAG_LENGTH_RSHIFT = 1;
static const int TAG_PTR_BITFIELD_RSHIFT = 7;

// Check to see if a tag is actually a forwarding pointer.
static inline int is_forwarding(int64_t tag) {
  return !(tag & TAG_IS_NOT_FORWARD_MASK);
}

// Get the length field out of a tag.
static inline int get_length(int64_t tag){
  return (tag & TAG_LENGTH_MASK) >> TAG_LENGTH_RSHIFT;
}

// Get the "is pointer bitfield" out of a tag.
static inline int64_t get_ptr_bitfield(int64_t tag){
  return tag >> TAG_PTR_BITFIELD_RSHIFT;
}

// initialize the state of the collector so that allocations can occur
void initialize(int64_t rootstack_size, int64_t heap_size)
{
  // 1. Check to make sure that our assumptions about the world are correct.
  if (DEBUG_MODE){
    if (sizeof(int64_t) != sizeof(int64_t*)){
      printf("The runtime was compiler on an incompatible plaform");
      exit(-1);
    }
    
    if ((heap_size % 8) != 0){
      printf("invalid heap size %lld\n", heap_size);
      exit(-1);
    }
    
    if ((rootstack_size % 8) != 0) {
      printf("invalid rootstack size %lld\n", rootstack_size);
      exit(-1);
    }
  }
  
  // 2. Allocate memory (You should always check if malloc gave you memory)
  if (!(fromspace_begin = malloc(heap_size))) {
      printf("Failed to malloc %lld byte fromspace\n", heap_size);
      exit(-1);
  }

  if (!(tospace_begin = malloc(heap_size))) {
      printf("Failed to malloc %lld byte tospace\n", heap_size);
      exit(-1);
  }

  if (!(rootstack_begin = malloc(rootstack_size))) {
    printf("Failed to malloc %lld byte rootstack", rootstack_size);
    exit(-1);
  }
  
  // 2.5 Calculate the ends memory we are using.
  // Note: the pointers are for a half open interval [begin, end)
  fromspace_end = fromspace_begin + (heap_size / 8);
  tospace_end = tospace_begin + (heap_size / 8);
  rootstack_end = rootstack_begin + (rootstack_size / 8);

  // 3 Initialize the global free pointer 
  free_ptr = fromspace_begin;
  
  // Useful for debugging
  initialized = 1;

}

// cheney implements cheney's copying collection algorithm
// There is a stub and explaination below.
static void cheney(int64_t** rootstack_ptr);

void collect(int64_t** rootstack_ptr, int64_t bytes_requested)
{
  // 1. Check our assumptions about the world
  if (DEBUG_MODE) {
    if (!initialized){
      printf("Collection tried with uninitialized runtime\n");
      exit(-1);
    }
  
    if (rootstack_ptr < rootstack_begin){
      printf("rootstack_ptr = %p < %p = rootstack_begin\n",
             rootstack_ptr, rootstack_begin);
      exit(-1);
    }

    if (rootstack_ptr > rootstack_end){
      printf("rootstack_ptr = %p > %p = rootstack_end\n",
             rootstack_ptr, rootstack_end);
      exit(-1);
    }

    for(int i = 0; rootstack_begin + i < rootstack_ptr; i++){
      int64_t* a_root = rootstack_begin[i];
      if (!(fromspace_begin <= a_root && a_root < fromspace_end)) {
        printf("rootstack contains non fromspace pointer\n");
        exit(-1);
      }
    }
  }

  
  // 2. Perform collection
  cheney(rootstack_ptr);
  
  // 3. Check if collection freed enough space in order to allocate
  if (sizeof(int64_t) * (fromspace_end - free_ptr) < bytes_requested){
    /* 
       If there is not enough room left for the bytes_requested,
       allocate larger tospace and fromspace.
       
       In order to determine the new size of the heap double the
       heap size until it is bigger than the occupied portion of
       the heap plus the bytes requested.
       
       This covers the corner case of heaps objects that are
       more than half the size of the heap. No a very likely
       scenario but slightly more robust.
     
       One corner case that isn't handled is if the heap is size
       zero. My thought is that malloc probably wouldn't give
       back a pointer if you asked for 0 bytes. Thus initialize
       would fail, but our runtime-config.rkt file has a contract
       on the heap_size parameter that the code generator uses
       to determine initial heap size to this is a non-issue
       in reality.
    */
    
    long occupied_bytes = (free_ptr - fromspace_begin) * 8;
    long needed_bytes = occupied_bytes + bytes_requested;
    long old_len = fromspace_end - fromspace_begin;
    long old_bytes = old_len * sizeof(int64_t);
    long new_bytes = old_bytes;
    
    while (new_bytes < needed_bytes) new_bytes = 2 * new_bytes;

    // Free and allocate a new tospace of size new_bytes
    free(tospace_begin);

    if (!(tospace_begin = malloc(new_bytes))) {
      printf("failed to malloc %ld byte fromspace", new_bytes);
      exit(-1);
    }
    
    tospace_end = tospace_begin + new_bytes / (sizeof(int64_t));

    // The pointers on the stack and in the heap must be updated,
    // so this cannot be just a memcopy of the heap.
    // Performing cheney's algorithm again will have the correct
    // effect, and we have already implemented it.
    cheney(rootstack_ptr);

    
    // Cheney flips tospace and fromspace. Thus, we allocate another 
    // tospace not fromspace as we might expect.
    free(tospace_begin);

    if (!(tospace_begin = malloc(new_bytes))) {
      printf("failed to malloc %ld byte tospace", new_bytes);
      exit(-1);
    }

    tospace_end = tospace_begin + new_bytes / (sizeof(int64_t));
    
  }
}

// copy_vector is responsible for doing a pointer oblivious
// move of vector data and updating the vector pointer with
// the new address of the data.
// There is a stub and explaination for copy_vector below.
static void copy_vector(int64_t** vector_ptr_loc);

/*
  The cheney algorithm takes a pointer to the top of the rootstack.
  It resets the free pointer to be at the begining of tospace, copies
  (or reallocates) the data pointed to by the roots into tospace and
  replaces the pointers in the rootset with pointers to the
  copies. (See the description of copy_vector below).
  
  While this initial copying of root vectors is occuring the free_ptr
  has been maintained to remain at the next free memory location in
  tospace. Cheney's algorithm then scans a vector at a time until it
  reaches the free_ptr.

  At each vector we use the meta information stored in the vector tag
  to find the length of the vector and tell which fields inside the
  vector are vector pointers. Each new vector pointer must have its
  data copied and every vector pointer must be updated to to point to
  the copied data. (The description of copy_vector will help keep this
  organized.

  This process is a breadth first graph traversal. Copying a vector
  places its contents at the end of a Fifo queue and scanning a vector
  removes it. Eventually the graph traversal will run out of unseen
  nodes "catch up" to the free pointer. When this occurs we know that
  all live data in the program is contained by tospace, and that
  everything left in fromspace is unreachable by the program.

  After this point the free pointer will be pointing into what until
  now we considered tospace. This means the program will allocate
  object here. In order to keep track of the we "flip" fromspace and
  tospace by making the fromspace pointers point to tospace and vice
  versa.
*/

void cheney(int64_t** rootstack_ptr)
{
  
}


/* 
 copy_vector takes a pointer, (`location`) to a vector pointer,
 copies the vector data from fromspace into tospace, and updates the
 vector pointer so that it points to the the data's new address in
 tospace.

  Precondition:
    *  original vector pointer location
    |
    V
   [*] old vector pointer
    |
    +-> [tag or forwarding pointer | ? | ? | ? | ...] old vector data
        
 Postcondition:
    * original vector pointer location
    |
    V
   [*] new vector pointer
    |
    |   [ * forwarding pointer | ? | ? | ? | ...] old vector data
    |     |     
    |     V
    +---->[tag | ? | ? | ? | ...] new vector data
 
 Since multiple pointers to the same vector can exist within the
 memory of the program this may or may not be the first time
 we called `copy_vector` on a location that contains this old vector
 pointer. In order to tell if we have copied the old vector data previously we
 check the vector information tag (`tag = old_vector_pointer[0]`).

 If the forwarding bit is set, then is_forwarding(tag) will return
 false and we know we haven't already copied the data. In order to
 figure out how much data to copy we can inspect the tag's length
 field. The length field indicates the number of 64-bit words the
 array is storing for the user, so we need to copy `length + 1` words
 in total, including the tag. After performing the
 copy we need to leave a forwarding pointer in old data's tag field
 to indicate the new address to subsequent copy_vector calls for this
 vector pointer. Furthermore, we need to store the new vector's pointer
 at the location where where we found the old vector pointer.
 
 If the tag is a forwarding pointer, the `is_forwarding(tag) will return
 true and we need to update the location storing the old vector pointer to
 point to the new data instead).
 
 As a side note any time you are allocating new data you must maintain
 the invariant that the free_ptr points to the next free memory address.

*/
void copy_vector(int64_t** vector_ptr_loc)
{
  
}



// Read an integer from stdin
int64_t read_int() {
  int64_t i;
  scanf("%lld", &i);
  return i;
}

// print an integer to stdout
void print_int(int64_t x) {
  printf("%lld", x);
}

// print a bool to stdout
void print_bool(int64_t x) {
  if (x){
    printf("#t");
  } else {
    printf("#f");
  }
}
