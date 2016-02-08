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

//Object tags constants
static const int TAG_IS_NOT_FORWARD_MASK = 1;
static const int TAG_LENGTH_MASK = 126;
static const int TAG_LENGTH_RSHIFT = 1;
static const int TAG_PTR_BITFIELD_RSHIFT = 7;

static inline int is_forwarding(ptr tag) {
  return !(tag & TAG_IS_NOT_FORWARD_MASK);
}

static inline int get_length(ptr tag){
  return (tag & TAG_LENGTH_MASK) >> TAG_LENGTH_RSHIFT;
}

static inline ptr get_ptr_bitfield(ptr tag){
  return tag >> TAG_PTR_BITFIELD_RSHIFT;
}


static ptr* tospace_begin;
static ptr* tospace_end;

ptr* free_ptr;

ptr* fromspace_begin;
ptr* fromspace_end;

ptr** rootstack_begin;
ptr** rootstack_end;

int initialized = 0;

// cheney implements cheney's copying collection algorithm
static void cheney(ptr** rootstack_ptr);

static void copy_vector(ptr** vector_loc);
//static void process_vector(ptr* scan_ptr);

void initialize(long int rootstack_size, long int heap_size)
{
  if (sizeof(int64_t) != sizeof(ptr)){
    printf("The runtime was compiler with an incompatible pointer size");
    exit(-1);
  }
  
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

void collect(ptr** rootstack_ptr, long int bytes_requested)
{
  
  cheney(rootstack_ptr);
  
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
     would fail.
  */

  if (sizeof(ptr) * (fromspace_end - free_ptr) < bytes_requested){
    long int occupied_bytes = (free_ptr - fromspace_begin) * 8;
    long int needed_bytes = occupied_bytes + bytes_requested;
    long int old_len = fromspace_end - fromspace_begin;
    long int old_bytes = old_len * sizeof(long int);
    long int new_bytes = 2 * old_bytes;
    
    while (new_bytes < needed_bytes) new_bytes = 2 * new_bytes;
                                           
    free(tospace_begin);

    if (!(tospace_begin = malloc(new_bytes))) {
      printf("failed to malloc %ld byte fromspace", new_bytes);
      exit(-1);
    }
    
    tospace_end = tospace_begin + new_bytes / (sizeof(ptr));

    /* 
       The pointers on the stack and in the heap must be updated,
       so this cannot be just a memcopy of the heap.
       Performing cheney's algorithm again will have the correct
       effect, and we have already implemented it.
    */

    cheney(rootstack_ptr);

    /*
      Cheney flips tospace and fromspace. Thus, we allocate another 
      tospace not fromspace as we might expect.
    */

    free(tospace_begin);

    if (!(tospace_begin = malloc(new_bytes))) {
      printf("failed to malloc %ld byte tospace", new_bytes);
      exit(-1);
    }

    tospace_end = tospace_begin + new_bytes / (sizeof(ptr));
    
  } /* end if */

}





void cheney(ptr** rootstack_ptr)
{
  ptr* scan_ptr = tospace_begin;
  free_ptr = tospace_begin;
  
  /* traverse the root set to create the initial queue */
  for (ptr** root = rootstack_begin; root != rootstack_ptr; ++root) {
    /*
      We pass copy vector the pointer to the pointer to the vector.
      This is because we need to be able to rewrite the pointer after
      the object has been moved.
    */
    copy_vector(root);
  }
  
  /* 
     Here we need to scan tospace until we reach the free_ptr pointer.
     This will end up being a breadth first search of the pointers in
     from space.
  */
  while (scan_ptr != free_ptr) {
    /* 
       I inlined this to leave maniuplation of scan_ptr to a single
       function. This can be accomplished by passing the location
       of the pointer into helper, but let's not make reasoning
       through the algorithm any harder.
    
       The invarient of the outer loop is that scan_ptr is either
       at the front of a vector, or == to free_ptr.
    */
    
    // Since this tag is already in tospace we know that it isn't
    // a forwarding pointer.
    ptr tag = *scan_ptr;
    
    // the length of the vector is contained in bits [1,6]
    int len = get_length(tag);

    // Find the next vector or the next free_ptr;
    // with is len + 1 away from the current;
    ptr* next_ptr = scan_ptr + len + 1;
    
    // each bit low to high says if the next index is a ptr
    int64_t isPointerBits = get_ptr_bitfield(tag);

    // Advance the scan_ptr then check to
    // see if we have arrived at the beginning of the next array.
    scan_ptr += 1;
    while(scan_ptr != next_ptr){
      if ((isPointerBits & 1) == 1) {
        // since the tag says that the scan ptr in question is a
        // ptr* we known that scan_ptr currently points to a ptr*
        // and must be a ptr** itself.
        copy_vector((ptr**)scan_ptr);
      }
      // Advance the tag so the next check is for the next scan ptr
      isPointerBits = isPointerBits >> 1;
      scan_ptr += 1;
    }

    //scan_ptr == next_ptr 

    // todo delete this.
    /*
    for (int i = 0; i != len; ++i) {
      if ((tag & 1) == 1) {
        copy_vector(scan_ptr, free_ptr);
      }
      tag = tag >> 1;
      *scan_ptr = *scan_ptr + 1;
    }
    */
    
  }

  /* swap the tospace and fromspace */
  ptr* tmp_begin = tospace_begin; 
  ptr* tmp_end = tospace_end;
  tospace_begin = fromspace_begin;
  tospace_end = fromspace_end;
  fromspace_begin = tmp_begin;
  fromspace_end = tmp_end;
}


/* Copy vector from fromspace into the tospace */
void copy_vector(ptr** vector_loc)
{
  
  ptr* old_vector = *vector_loc;
  ptr tag = old_vector[0];
   
  // If our search has already moved the vector then we
  //  would have left a forwarding pointer.

  if (is_forwarding(tag)) {
    // Since we left a forwarding pointer the we have already
    // moved this vector. All we need to do is update the pointer
    // that was pointing to the old vector. To point we the
    // forwarding pointer says the new copy is.
    *vector_loc = (ptr*) tag;
    
  } else {
    // This is the first time we have followed this pointer.
    
    // Since we are about to jumble all the pointers around lets
    // set up some structure to the world.

    // The tag we grabbed earlier contains some usefull info for
    // forwarding copying the vector.
    int len = get_length(tag);
    
    // The new vector is going to be where the free ptr pointer
    // currently points.
    ptr* new_vector = free_ptr;

    // Just perform a straight forward copy from old to new.
    // The length is a bit of a lie because includeing the
    // meta information the actual length is len + 1;
    for (int i = 0; i < len + 1; i++){
      new_vector[i] = old_vector[i];
    }
        
    // the free ptr can be updated to point to the next free ptr.
    free_ptr = free_ptr + len + 1;    

    // We need to set the forwarding pointer in the old_vector
    old_vector[0] = (ptr) new_vector;

    // And where we found the old vector we need to update the
    // pointer to point to the new vector
    *vector_loc = new_vector;

    //TODO delete this block once the code works
    /*
    //and each subsequent bit tells us whether the ptr pointed
    //by current is a pointer.
    ptr current = *vec;
    ptr new_vec = *free_ptr;

    // copy the tag into the new vector
    **free_ptr = *current;
    current = current + 1;
    *free_ptr = *free_ptr + 1;
    //copy the rest of the vector
    for (int i = 0; i != len; ++i) {
      current = current + 1;
      *free_ptr = *free_ptr + 1;      
    }
    
    //set the forwarding pointer
    **vec = (long int)new_vec;
    // update vec to the new location in tospace
    *vec = (ptr)**vec;
    */
  }
}

void process_vector(ptr* scan_ptr)
{
  
  ptr tag = *scan_ptr;
  // Clear the forwarding pointer
  tag = tag >> 1;
  // Extract length from the tag
  int len = get_length(tag);
  // Each bit low to high says if the next index is a ptr
  tag = tag >> 6;
  
  /* advance past the tag */
  *scan_ptr = *scan_ptr + 1;

  for (int i = 0; i != len; ++i) {
    if ((tag & 1) == 1) {
      copy_vector((ptr**) scan_ptr);
    }
    tag = tag >> 1;
    *scan_ptr = *scan_ptr + 1;
  }
}
