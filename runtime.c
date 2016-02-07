#include <stdlib.h>
#include <stdio.h>
#include "runtime.h"

long int read_int() {
  long int i;
  scanf("%ld", &i);
  return i;
}


void print_int(long x) {
  printf("%ld", x);
}

void print_bool(int x) {
  if (x) 
    printf("#t");
  else printf("#f");
}


static void copy_vector(ptr* vec, ptr* free_ptr);
static void process_vector(ptr* scan_ptr, ptr* free_ptr);

/*
  Garbage collection via copying collection.

  Entities:

  * root stack
        local variables that are pointers into the heap (e.g., vectors)

  * fromspace: the current heap

  * tospace: to old, unused heap

  Interface to the generated code:

  * Root Stack Pointer, a register 
    Allocate at the beginning of a procedure by checking for room
    then moving this pointer forward and initialize with zeroes.

  * global variable for the end of the root stack
     (exit the program if you run out of space on the root stack)

  * Allocation Pointer: register pointing to the next opening in the fromspace.
    allocate by checking for room then moving this pointer forward.

  * Allocation End Pointer: register pointing to the end of the fromspace.

  * Vectors start with a bitfield that says which elements are pointers
    or that indicates that the vector has just been copied to tospace
    and the first element is now a forwarding pointer.

  * initialize function
    Allocate the fromspace, tospace, and rootstack. Return the address of
    the start and end of the fromspace and the start of the rootstack.

  * collect function
    Call this when there is not enough room in the fromspace.
    Returns the address of the next allocation and end of the new fromspace.

    Do a breadth-first traversal of the fromspace, starting with
    the root stack. The queue for the BFS is stored in the tospace.

    Maintain two pointers into the tospace. 
    * free pointer: points to the next available slot in the tospace,
      which also represents the end of the BFS queue.

    * scan pointer: points to the front of the queue. The items
      in the queue may have pointers into the fromspace and those
      objects need to get copied over to the tospace.
      
    Forwarding pointers: the graph of pointers in fromspace may
      include multiple pointers to the same object, so we need
      to make sure to only copy each object once, and to maintain
      the original aliasing. This is accomplished by placing
      a forwarding pointer in the fromspace object
      after it is copied to tospace. Also, the tag at the beginning of
      the object is changed to say that there is a forwarding pointer.

    What to do if there is not enough room after collection for the new
    allocation? Allocate a new tospace and fromspace that is twice
    as large as before.

  Object Tag (64 bits)
  #b|- 7 bit unused -|- 50 bit field [50, 0] -| 6 bits lenght -| 1 bit isForwarding Pointer  
  * If the bottom-most bit is zero, the tag is really a forwarding pointer.
  * Otherwise, its an object. In that case, the next 
    6 bits give the length of the object (max of 50 64-bit words).
    The next 50 bits say where there are pointers.
    A '1' is a pointer, a '0' is not a pointer.

 */

static ptr tospace_begin;
static ptr tospace_end;

ptr free_ptr;

ptr fromspace_begin;
ptr fromspace_end;

ptr rootstack_begin;
ptr rootstack_end;

int initialized = 0;

void initialize(long int rootstack_size, long int heap_size)
{
  if (0 != (heap_size % 8)){
    printf("invalid heap size %ld\n", heap_size);
    exit(-1);
  }
  
  if (0 != (rootstack_size % 8)) {
    printf("invalid rootstack size %ld\n", rootstack_size);
    exit(-1);
  }
  
  if (!(fromspace_begin = malloc(heap_size)))
    {
      printf("Failed to malloc %ld byte fromspace\n", heap_size);
      exit(-1);
    }
  
  fromspace_end = fromspace_begin + (heap_size / 8);
  free_ptr = fromspace_begin;
  
  if (!(tospace_begin = malloc(heap_size)))
    {
      printf("Failed to malloc %ld byte tospace\n", heap_size);
      exit(-1);
    }
  
  tospace_end = tospace_begin + (heap_size / 8);

  if (!(rootstack_begin = malloc(rootstack_size)))
    {
      printf("Failed to malloc %ld byte rootstack", rootstack_size);
      exit(-1);
    }
  
  rootstack_end = rootstack_begin + (rootstack_size / 8);
  initialized = 1;

  return;
}

ptr alloc(long int bytes_requested)
{
  if (!initialized) {
    //allocations must be in full words
    printf("Initialization didn't run");
    exit(-1);
  }
  
  if (bytes_requested % 8 != 0){
    //allocations must be in full words
    printf("Can't allocate fractions of a ptr");
    exit(-1);
  }

  if (bytes_requested > (fromspace_end - free_ptr) * 8){
    //collect(bytes_requested, rootstack_ptr);
    printf("Collection not yet implemented\n");
    exit(-1);
  }

  ptr new_ptr = free_ptr;
  free_ptr = free_ptr + (bytes_requested / 8);
  return new_ptr;
}

ptr debug_collect(ptr rootstack_ptr, long int bytes_requested){
  printf("Collection not yet implemented\n");
  exit(-1);
}

void cheney(ptr rootstack_ptr)
{
  ptr scan_ptr = tospace_begin;
  free_ptr = tospace_begin;
  
  /* traverse the root set to create the initial queue */
  for (ptr root = rootstack_begin; root != rootstack_ptr; ++root) {
    copy_vector(&root, &free_ptr);
  }
  
  /* conduct the breadth-first search */
  while (scan_ptr != free_ptr) {
    process_vector(&scan_ptr, &free_ptr);
  }

  /* swap the tospace and fromspace */
  ptr tmp_begin = tospace_begin; 
  ptr tmp_end = tospace_end;
  tospace_begin = fromspace_begin;
  tospace_end = fromspace_end;
  fromspace_begin = tmp_begin;
  fromspace_end = tmp_end;
}

void collect(ptr rootstack_ptr, long int bytes_requested)
{
  
  cheney(rootstack_ptr);
  
  /* if there is not enough room left for the bytes_requested,
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
     would fail.
  */

  if (8 * (fromspace_end - free_ptr) < bytes_requested){
    long int occupied_bytes = (free_ptr - fromspace_begin) * 8;
    long int needed_bytes = occupied_bytes + bytes_requested;
    long int old_len = fromspace_end - fromspace_begin;
    long int old_bytes = 8 * old_len;
    long int new_bytes = 2 * old_bytes;
    
    while (new_bytes < needed_bytes) new_bytes = 2 * new_bytes;
                                           
    free(tospace_begin);

    if (!(tospace_begin = malloc(new_bytes))) {
      printf("failed to malloc %ld byte fromspace", new_bytes);
      exit(-1);
    }
    
    tospace_end = tospace_begin + new_bytes / 8;

    /* 
       The pointers on the stack and in the heap must be updated,
       so this cannot be just a memcopy of the heap.
       Performing cheney's algorithm again will have the correct
       effect, and we have already implemented it.
    */

    cheney(rootstack_ptr);

    /*
      Cheney has flips tospace and fromspace once again now we
      allocate a new tospace once again.
    */

    free(tospace_begin);

    if (!(tospace_begin = malloc(new_bytes))) {
      printf("failed to malloc %ld byte tospace", new_bytes);
      exit(-1);
    }

    tospace_end = tospace_begin + new_bytes / 8;
    
  } /* end if */

}

static inline int is_forwarding(long int tag) {
  return (tag & 1) == 0;
}

static inline long int six_ones() {
  long int all_ones = ~0;
  long int six_zeroes = all_ones << 6;
  return ~six_zeroes;
}

/* Copy vector from fromspace into the tospace */
void copy_vector(ptr* vec, ptr* free_ptr)
{
  long int tag = **vec;
  if (is_forwarding(tag)) {
    /* update vec to the forwarded address */
    *vec = (ptr)**vec;
  } else {
    tag = tag >> 1;
    int len = (tag & six_ones());
    ptr current = *vec;
    ptr new_vec = *free_ptr;

    /* copy the tag into the new vector */
    **free_ptr = *current;
    current = current + 1;
    *free_ptr = *free_ptr + 1;
    /* copy the rest of the vector */
    for (int i = 0; i != len; ++i) {
      current = current + 1;
      *free_ptr = *free_ptr + 1;      
    }
    /* set the forwarding pointer */
    **vec = (long int)new_vec;
    /* update vec to the new location in tospace */
    *vec = (ptr)**vec;
  }
}

void process_vector(ptr* scan_ptr, ptr* free_ptr)
{
  long int tag = **scan_ptr;
  // Clear the forwarding pointer
  tag = tag >> 1;
  // Extract length from the tag
  int len = (tag & six_ones());
  // Each bit low to high says if the next index is a ptr
  tag = tag >> 6;
  
  /* advance past the tag */
  *scan_ptr = *scan_ptr + 1;

  for (int i = 0; i != len; ++i) {
    if ((tag & 1) == 1) {
      copy_vector(scan_ptr, free_ptr);
    }
    tag = tag >> 1;
    *scan_ptr = *scan_ptr + 1;
  }
}
