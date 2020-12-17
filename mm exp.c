/*
 * mm.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>
#include "mm.h"
#include "memlib.h"

/*
 * If you want debugging output, uncomment the following.  Be sure not
 * to have debugging enabled in your final submission
 */
//#define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__) 
#define dbg_checkheap(...) mm_checkheap(__VA_ARGS__)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#define dbg_requires(...)
#define dbg_ensures(...)
#define dbg_checkheap(...)
#define dbg_printheap(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* What is the correct alignment? */
#define ALIGNMENT 16

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word, header, footer size (bytes)
static const size_t dsize = 2*wsize;          // double word size (bytes)
static const size_t min_block_size = 2*dsize; // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    /*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
    union data
    {
        /* data */
        char payload[0];
        struct block *ptrArr[2];
    } d;
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
} block_t;


/* Global variables */
/* Pointer to first block */
static block_t *heap_listp = NULL;
static block_t *freeListStart = NULL;
//static block_t *startSrch = NULL;

/* Function prototypes for internal helper routines */
static block_t *insert_free_block (block_t *block);
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);
static bool in_heap(const void *p);
static size_t align(size_t x);
static bool aligned(const void *p);
static void removeBlock (block_t *block);

bool mm_checkheap(int lineno);

/*
 * mm_init: initializes the heap; it is run once when heap_start == NULL.
 *          prior to any extend_heap operation, this is the heap:
 *              start            start+8           start+16
 *          INIT: | PROLOGUE_FOOTER | EPILOGUE_HEADER |
 * heap_listp ends up pointing to the epilogue header.
 */
bool mm_init(void) 
{
    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1) 
    {
        return false;
    }

    start[0] = pack(0, true); // Prologue footer
    start[1] = pack(0, true); // Epilogue header
    // Heap starts with first block header (epilogue)
    heap_listp = (block_t *) &(start[1]);

    // Extend the empty heap with a free block of chunksize bytes
    block_t *newBlock = extend_heap (chunksize);
    if (newBlock == NULL)
    {
        return false;
    }
    insert_free_block (newBlock);
    return true;
}

/*
 * malloc: allocates a block with size at least (size + dsize), rounded up to
 *         the nearest 16 bytes, with a minimum of 2*dsize. Seeks a
 *         sufficiently-large unallocated block on the heap to be allocated.
 *         If no such block is found, extends heap by the maximum between
 *         chunksize and (size + dsize) rounded up to the nearest 16 bytes,
 *         and then attempts to allocate all, or a part of, that memory.
 *         Returns NULL on failure, otherwise returns a pointer to such block.
 *         The allocated block will not be used for further allocations until
 *         freed.
 */
void *malloc(size_t size) 
{
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_listp == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
	dbg_printf("Malloc(%zd) --> %p\n", size, bp);
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = align (size) + dsize;

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {  
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
	        dbg_printf("Malloc(%zd) --> %p\n", size, bp);
            return bp;
        }
    }
    else
    {
        removeBlock (block);
    }
    place(block, asize);
    bp = header_to_payload(block);
    dbg_printf("Malloc(%zd) --> %p\n", size, bp);
    return bp;
} 

/*
 * free: Frees the block such that it is no longer allocated while still
 *       maintaining its size. Block will be available for use on malloc.
 */
void free(void *bp)
{
    block_t *newBlock;
    if (bp == NULL)
    {
        return;
    }
    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    write_header(block, size, false);
    write_footer(block, size, false);

    newBlock = coalesce(block);
    insert_free_block (newBlock);
    dbg_printf("Completed free(%p)\n", bp);
    return;
}

/*
 * realloc: returns a pointer to an allocated region of at least size bytes:
 *          if ptrv is NULL, then call malloc(size);
 *          if size == 0, then call free(ptr) and returns NULL;
 *          else allocates new region of memory, copies old data to new memory,
 *          and then free old block. Returns old block if realloc fails or
 *          returns new pointer on success.
 */
void *realloc(void *ptr, size_t size)
{
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (!newptr)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * calloc: Allocates a block with size at least (elements * size + dsize)
 *         through malloc, then initializes all bits in allocated memory to 0.
 *         Returns NULL on failure.
 */
void *calloc(size_t nmemb, size_t size)
{
    void *bp;
    size_t asize = nmemb * size;

    if (asize/nmemb != size)
	// Multiplication overflowed
	return NULL;
    
    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/
/*
 * insert_free_block: Inserts a free block at the start of the explicit list
 *                    for free blocks and returns a pointer to the newly inserted 
 *                    free block
 */
static block_t *insert_free_block (block_t *block)
{
    dbg_requires (block != NULL);
    if (freeListStart == NULL)
    {
        (block -> d).ptrArr[0] = NULL;
        (block -> d).ptrArr[1] = NULL;
        freeListStart = block;
    }
    else
    {
        (block -> d).ptrArr[1] = freeListStart;
        dbg_printf("next ptr changed at line 328 to %p\n", (block -> d).ptrArr[1]);
        (block -> d).ptrArr[0] = NULL;
        dbg_requires (freeListStart != NULL);
        (freeListStart -> d).ptrArr[0] = block;
        freeListStart = block;
    }
    dbg_ensures (freeListStart != NULL);
    return (freeListStart);
}

static void removeBlock (block_t *block)
{
    dbg_requires (!(get_alloc (block)));
    dbg_requires (block != NULL);

    if (((block -> d).ptrArr[0] == NULL) && ((block -> d).ptrArr[1] == NULL))
    {
        freeListStart = NULL;
    }
    else if (((block -> d).ptrArr[0] == NULL) && ((block -> d).ptrArr[1] != NULL))
    {
        freeListStart = (block -> d).ptrArr[1];
        dbg_requires (freeListStart != NULL);
        (freeListStart -> d).ptrArr[0] = NULL;
    }
    else if (((block -> d).ptrArr[0] != NULL) && ((block -> d).ptrArr[1] == NULL))
    {
        (((block -> d).ptrArr[0]) -> d).ptrArr[1] = NULL;
        dbg_printf("next ptr changed at line 356 to %p\n", (((block -> d).ptrArr[0]) -> d).ptrArr[1]);

    }
    else
    {
        (((block -> d).ptrArr[0]) -> d).ptrArr[1] = (block -> d).ptrArr[1];
        dbg_printf("next ptr changed at line 360 to %p\n", (((block -> d).ptrArr[0]) -> d).ptrArr[1]);
        (((block -> d).ptrArr[1]) -> d).ptrArr[0] = (block -> d).ptrArr[0];
    }
    return;
}



/*
 * extend_heap: Extends the heap with the requested number of bytes, and
 *              recreates epilogue header. Returns a pointer to the result of
 *              coalescing the newly-created block with previous free block, if
 *              applicable, or NULL in failure.
 */
static block_t *extend_heap(size_t size) 
{
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = align(size);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);
    write_header(block, size, false);
    write_footer(block, size, false);
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true);

    // Coalesce in case the previous block was free
    return coalesce(block);
}

/* Coalesce: Coalesces current block with previous and next blocks if
 *           either or both are unallocated; otherwise the block is not
 *           modified. Then, insert coalesced block into the segregated list.
 *           Returns pointer to the coalesced block. After coalescing, the
 *           immediate contiguous previous and next blocks must be allocated.
 */
static block_t *coalesce(block_t * block) 
{
    block_t *block_next = find_next(block);
    block_t *block_prev = find_prev(block);

    bool prev_alloc = extract_alloc(*(find_prev_footer(block)));
    bool next_alloc = get_alloc(block_next);
    size_t size = get_size(block);

    if (prev_alloc && next_alloc)              // Case 1
    {
        return block;
    }

    else if (prev_alloc && !next_alloc)        // Case 2
    {
        size += get_size(block_next);
        removeBlock (block_next);
        write_header(block, size, false);
        write_footer(block, size, false);
    }

    else if (!prev_alloc && next_alloc)        // Case 3
    {
        size += get_size(block_prev);
        removeBlock (block_prev);
        write_header(block_prev, size, false);
        write_footer(block_prev, size, false);
        block = block_prev;
    }

    else                                        // Case 4
    {
        size += get_size(block_next) + get_size(block_prev);
        removeBlock (block_next);
        removeBlock (block_prev);
        write_header(block_prev, size, false);
        write_footer(block_prev, size, false);
        block = block_prev;
    }
    return block;
}

/*
 * place: Places block with size of asize at the start of bp. If the remaining
 *        size is at least the minimum block size, then split the block to the
 *        the allocated block and the remaining block as free, which is then
 *        inserted into the segregated list. Requires that the block is
 *        initially unallocated.
 */
static void place(block_t *block, size_t asize)
{
    dbg_requires (! (get_alloc (block)));
    size_t csize = get_size(block);

    if ((csize - asize) >= min_block_size)
    {
	block_t *block_next;
        write_header(block, asize, true);
        write_footer(block, asize, true);

        block_next = find_next(block);
        write_header(block_next, csize-asize, false);
        write_footer(block_next, csize-asize, false);
        insert_free_block (block_next);
    }

    else
    { 
        write_header(block, csize, true);
        write_footer(block, csize, true);
    }
}

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x) {
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

/*
 * find_fit: Looks for a free block with at least asize bytes with
 *           first-fit policy. Returns NULL if none is found.
 */
static block_t *find_fit(size_t asize)
{
    block_t *iter; 
    for (iter = freeListStart; (iter != NULL);
                             iter = (iter -> d).ptrArr[1])
    {
        if ((iter != NULL) && (!(get_alloc(iter))) && (asize <= get_size(iter)))
        {
            dbg_requires (iter != NULL);
            return iter;
        }
    }
    /*
    if (startSrch == NULL)
    {
        dbg_requires (freeListStart != NULL);
        for (iter = freeListStart; (iter != NULL);
                             iter = (iter -> d).ptrArr[1])
        {
            dbg_printf("iter is %p\n", iter);
            if ((iter != NULL) && (!(get_alloc(iter))) && (asize <= get_size(iter)))
            {
                dbg_requires (iter != NULL);
                startSrch = (iter -> d).ptrArr[1];
                dbg_printf("start srch = %p normal search\n", startSrch);
                return iter;
            }
        }
    }
    else
    {
        for (iter = startSrch; (iter != NULL);
                             iter = (iter -> d).ptrArr[1])
        {
            dbg_printf("iter is %p from startsrch\n", iter);
            if (!(get_alloc(iter)) && (asize <= get_size(iter)))
            {
                dbg_requires (iter != NULL);
                startSrch = (iter -> d).ptrArr[1];
                dbg_printf("start srch = %p start search\n", startSrch);
                return iter;
            }
        }
        dbg_requires (freeListStart != NULL);
        for (iter = freeListStart; (iter != NULL) && (iter != startSrch);
                             iter = (iter -> d).ptrArr[1])
        {
            dbg_printf("iter is %p not startsrch\n", iter);
            if (!(get_alloc(iter)) && (asize <= get_size(iter)))
            {
                dbg_requires (iter != NULL);
                startSrch = (iter -> d).ptrArr[1];
                dbg_printf("start srch = %p restart\n", startSrch);
                return iter;
            }
        }
    }*/
    return NULL; // no fit found
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}


/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc)
{
    return alloc ? (size | 1) : size;
}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & ~(word_t) 0xF);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    dbg_requires (block != NULL);
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - dsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & 0x1);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    dbg_requires (block != NULL);
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
    dbg_requires (block != NULL);
    block->header = pack(size, alloc);
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)(((char *)(block) + get_size(block)) - wsize);
    *footerp = pack(size, alloc);
}


/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    return (block_t *)(((char *)block) + get_size(block));
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    dbg_requires (block != NULL);
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, d.payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    dbg_requires (block != NULL);
    return (void *)((block -> d).payload);
}

/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void *p) {
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/* mm_checkheap: checks the heap for correctness; returns true if
 *               the heap is correct, and false otherwise.
 *               can call this function using mm_checkheap(__LINE__);
 *               to identify the line number of the call site.
 */
bool mm_checkheap(int lineno)  
{ 
    /* you will need to write the heap checker yourself. As a filler:
     * one guacamole is equal to 6.02214086 x 10**23 guacas.
     * one might even call it
     * the avocado's number.
     *
     * Internal use only: If you mix guacamole on your bibimbap, 
     * do you eat it with a pair of chopsticks, or with a spoon? 
     */
    block_t *block;
    block_t *prevBlock;
    int freeBlocks = 0;
    int freeBlocksList = 0;
    /* Checking epilogue and prologue blocks*/


    /* Checking each block address alignment */
    for (block = heap_listp; get_size(block) > 0;
                             block = find_next(block))
    {
        if (! (aligned ((block -> d).payload)))
        {
            dbg_printf ("Block not aligned. Error on line number %d.\n", lineno);
            return false;
        }
        if (get_size (block) < min_block_size)
        {
            dbg_printf ("Block size not correct. Error on line number %d.\n", lineno);
            return false;
        }
        if (block -> header != (word_t)*((char *)block + get_size(block) - 8))
        {
            dbg_printf ("Block Header and footer do not agree. Error on line number %d.\n", lineno);
            return false;
        }
        if (! get_alloc (block))
        {
            if (! get_alloc (find_prev (block)) || ! get_alloc (find_next (block)))
            {
                dbg_printf ("2 contiguous free blocks. Error on line number %d.\n", lineno);
                return false;
            }
            freeBlocks ++;
        }
    }
    /* Checking explicit free list */
    for (block = freeListStart; ((block != NULL) && (((block -> d).ptrArr[1]) != NULL)); 
                                block = (block -> d).ptrArr[1])
    {
        prevBlock = (((block -> d).ptrArr[1]) -> d).ptrArr[0];
        
        if (prevBlock != block)
        {
            dbg_printf ("Free block ptrs not conssitent. Error on line number %d.\n", lineno);
            return false;
        }
        if (! (in_heap (block)))
        {
            dbg_printf ("Free ptrs not between heap hi and lo. Error on line number %d.\n", lineno);
            return false;
        }
        freeBlocksList ++;
    }
    freeBlocksList ++;

    if (freeBlocksList != freeBlocks)
    {
        dbg_printf ("Number of free blocks not equal. Error on line number %d.\n", lineno);
        return false;
    }
    return true;
}


