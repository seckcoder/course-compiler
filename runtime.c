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

void initialize(long int rootstack_length, long int heap_length)
{

  long int space_length = heap_length / 2;
  
  if (!(fromspace_begin = malloc(8 * space_length)))
    {
      printf("Failed to malloc %ld byte fromspace\n", 8 * space_length);
      exit(-1);
    }
  
  fromspace_end = fromspace_begin + space_length;
  free_ptr = fromspace_begin;
  
  if (!(tospace_begin = malloc(8 * space_length)))
    {
      printf("Failed to malloc %ld byte tospace\n", 8 * space_length);
      exit(-1);
    }
  
  tospace_end = tospace_begin + space_length;

  if (!(rootstack_begin = malloc(8 * rootstack_length)))
    {
      printf("Failed to malloc %ld byte rootstack", 8 * rootstack_length);
      exit(-1);
    }
  
  rootstack_end = rootstack_begin + initial_len;
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
  free_ptr = free_ptr + (bytes_requested / sizeof(char));
  return new_ptr;
}

ptr debug_collect(ptr rootstack_ptr, long int bytes_requested){
  printf("Collection not yet implemented\n");
  exit(-1);
}

ptr collect(ptr rootstack_ptr, long int bytes_requested)
{
  //ptr free_ptr;
  ptr scan_ptr;

  free_ptr = tospace_begin;
  scan_ptr = tospace_begin;

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
  
  /* if there is not enough room left for the bytes_requested,
     allocate larger tospace and fromspace */
  
  if (sizeof(char) * (fromspace_end - free_ptr) < bytes_requested) {
    long int old_len = fromspace_end - fromspace_begin;
    long int old_bytes = 8 * old_len;

    free(tospace_begin);
    tospace_begin = malloc(2 * old_bytes);
    tospace_end = tospace_begin + 2 * old_len;

    ptr from = malloc(2 * old_bytes);
    ptr new_free_ptr = from;
    for (ptr p = fromspace_begin; p != free_ptr; ++p) {
      *new_free_ptr = *p;
      ++new_free_ptr;
    }
    free(fromspace_begin);
    fromspace_begin = from;
    fromspace_end = fromspace_begin + 2 * old_len;
    free_ptr = new_free_ptr;
  } /* end if */

  return free_ptr;
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
