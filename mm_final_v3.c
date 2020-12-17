/*Name : Mohammad Shaheer
Andrew Id : mshaheer*/

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>
#include <math.h>
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

/* Pointer to last block in heap */
static block_t *last_block = NULL;


/* List of pointers to segregated list */
static block_t **freeListPtr = NULL;
static block_t **startIndex = NULL;


/* Function prototypes for internal helper routines */
static void insert_free_block (block_t *block);
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);
static int find_free_list (size_t size);
static size_t max(size_t x, size_t y);
static word_t pack(size_t size, bool alloc, bool prev_alloc);
static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);
static bool extract_alloc(word_t header);
static bool extract_prev_alloc(word_t header);
static bool get_alloc(block_t *block);
static bool get_prev_alloc(block_t *block);
static void write_header(block_t *block, size_t size, bool alloc, bool prev_alloc);
static void write_footer(block_t *block, size_t size, bool alloc, bool prev_alloc);
static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);
static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);
static bool in_heap(const void *p);
static size_t align(size_t x);
static bool aligned(const void *p);
static void remove_block (block_t *block);
static bool is_acyclic (block_t *block);
bool mm_checkheap(int lineno);
static void change_alloc_next_block (block_t *block, bool alloc);

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
    word_t *start = (word_t *)(mem_sbrk(24 * wsize));

    if (start == (void *)-1) 
    {
        return false;
    }

    start[22] = pack(0, true, true); // Prologue footer
    start[23] = pack(0, true, true); // Epilogue header
    // Heap starts with first block header (epilogue)
    last_block = (block_t *) &(start[22]);
    heap_listp = (block_t *) &(start[23]);

    freeListPtr = (block_t **) &(start[0]);
    startIndex = (block_t **) &(start[11]);


    /* Initialising array of ptrs to segregated list*/
    for (int i = 0; i < 11; i ++)
    {
        *(freeListPtr + i) = NULL;
        *(startIndex + i) = NULL;
    }

    // Extend the empty heap with a free block of chunksize bytes
    block_t *newBlock = extend_heap (chunksize);
    if (newBlock == NULL)
    {
        return false;
    }

    /* Setting the allocation status of the previous block in the current block*/
    //newBlock -> header = (newBlock -> header) | (0x2);
    //word_t *footerp = (word_t *)(((char *)(newBlock) + get_size(newBlock)) - wsize);
    //*footerp = newBlock -> header;
    //start[1] = pack (0, true, false);
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
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    //(max operator)
    asize = max (32, align (size - wsize) + dsize);
    /*if (size <= wsize)
    {
        asize = 32;
    }
    else
    {
        asize = align (size - wsize) + dsize;
    }*/
    

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {  
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }
        //change_alloc_next_block (block, true);
    }
    else
    {
        remove_block (block);
        change_alloc_next_block (block, true);
    }
    place(block, asize);
    bp = header_to_payload(block);
    //dbg_printf("Malloc(%zd) --> %p\n", size, bp);
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

    write_header(block, size, false, get_prev_alloc (block));
    write_footer(block, size, false, get_prev_alloc (block));

    newBlock = coalesce(block);
    change_alloc_next_block (newBlock, false);
    insert_free_block (newBlock);
    //dbg_printf("Completed free(%p)\n", bp);
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
 * find_free_list: This function finds the segregated list according
 *                 to the size based on powers of 2. It then returns
 *                 the index
 */

static int find_free_list (size_t size) //remove extra checks
{
    if (size <= 64)
    {
        return 0;
    }
    else if (size <= 128)
    {
        return 1;
    }
    else if (size <= 256)
    {
        return 2;
    }
    else if (size <= 512)
    {
        return 3;
    }
    else if (size <= 1024)
    {
        return 4;
    }
    else if (size <= 2048)
    {
        return 5;
    }
    else if (size <= 4096)
    {
        return 6;
    }
    else if (size <= 8192)
    {
        return 7;
    }
    else if (size <= 16384)
    {
        return 8;
    }
    else if (size <= 32768)
    {
        return 9;
    }
    else
    {
        return 10;
    }
}

/*
 * insert_free_block: This function first determines the index
 *                    of the segregated list into which the block
 *                    should be inserted. It then inserts the block at the start
 *                    of the list
 */
static void insert_free_block (block_t *block)
{
    dbg_requires (block != NULL);
    size_t size = get_size (block);
    int ind = find_free_list (size);
    /* If nothing is present in the segregated list */
    if (*(freeListPtr + ind) == NULL)
    {
        (block -> d).ptrArr[0] = NULL;
        (block -> d).ptrArr[1] = NULL;
        *(freeListPtr + ind) = block;
    }

    /* If the segregated list is not empty */
    else
    {
        (block -> d).ptrArr[1] = *(freeListPtr + ind);
        (block -> d).ptrArr[0] = NULL;
        ((*(freeListPtr + ind)) -> d).ptrArr[0] = block;
        *(freeListPtr + ind) = block;
    }
    dbg_ensures (*(freeListPtr + ind) != NULL);
    return;
}

/*
 * remove_block: This function removes the block from a particular
 *               segregated list while making sure the linking is not
 *               destroyed
 */
static void remove_block (block_t *block)
{
    dbg_requires (!(get_alloc (block)));
    dbg_requires (block != NULL);
    size_t size = get_size (block);
    int ind = find_free_list (size);
    block_t *freeListStart = *(freeListPtr + ind);

    /* If the block to be deleted is the sole block in the list */
    if (((block -> d).ptrArr[0] == NULL) && ((block -> d).ptrArr[1] == NULL))
    {
        freeListStart = NULL;
    }

    /* If the block to be deleted is at the start of the segregated list*/
    else if (((block -> d).ptrArr[0] == NULL) && ((block -> d).ptrArr[1] != NULL))
    {
        freeListStart = (block -> d).ptrArr[1];
        (freeListStart -> d).ptrArr[0] = NULL;
    }

    /* If the block to be deleted is at the end of the segregated list */
    else if (((block -> d).ptrArr[0] != NULL) && ((block -> d).ptrArr[1] == NULL))
    {
        (((block -> d).ptrArr[0]) -> d).ptrArr[1] = NULL;
    }

    /* If the block to be deleted is at the middle of the segregated list */
    else
    {
        (((block -> d).ptrArr[0]) -> d).ptrArr[1] = (block -> d).ptrArr[1];
        (((block -> d).ptrArr[1]) -> d).ptrArr[0] = (block -> d).ptrArr[0];
    }
    *(freeListPtr + ind) = freeListStart;
    if (*(startIndex + ind) == block)
    {
        if (((block -> d).ptrArr[1]) != NULL)
        {
            *(startIndex + ind) = (block -> d).ptrArr[1];
        }
        else
        {
            *(startIndex + ind) = *(freeListPtr + ind);
        }
        
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
    write_header(block, size, false, get_alloc (last_block));
    write_footer(block, size, false, get_alloc (last_block));
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true, false);
    last_block = block;
    // Coalesce in case the previous block was free
    block_t *finalBlock = coalesce (block);
    return finalBlock;
}

/* Coalesce: Coalesces current block with previous and next blocks if
 *           either or both are unallocated; otherwise the block is not
 *           modified. Then, insert coalesced block into the segregated list.
 *           Returns pointer to the coalesced block. After coalescing, the
 *           immediate contiguous previous and next blocks must be allocated.
 */
static block_t *coalesce(block_t * block) 
{
    block_t *block_prev;
    block_t *block_next = find_next(block);
    bool prev_alloc = get_prev_alloc (block);
    bool next_alloc = get_alloc(block_next);
    size_t size = get_size(block);

    if (prev_alloc && next_alloc)              // Case 1
    {
        return block;
    }

    else if (prev_alloc && !next_alloc)        // Case 2
    {
        size += get_size(block_next);
        if (block_next == last_block)
        {
            last_block = block;
        }
        remove_block (block_next);
        write_header(block, size, false, true);
        write_footer(block, size, false, true);
    }

    else if (!prev_alloc && next_alloc)        // Case 3
    {
        block_prev = find_prev (block);
        size += get_size(block_prev);
        if (block == last_block)
        {
            last_block = block_prev;
        }
        remove_block (block_prev);
        write_header(block_prev, size, false, get_prev_alloc (block_prev));
        write_footer(block_prev, size, false, get_prev_alloc (block_prev));
        block = block_prev;
    }

    else                                        // Case 4
    {
        block_prev = find_prev (block);
        size += get_size(block_next) + get_size(block_prev);
        if (block_next == last_block)
        {
            last_block = block_prev;
        }
        remove_block (block_next);
        remove_block (block_prev);
        write_header(block_prev, size, false, get_prev_alloc (block_prev));
        write_footer(block_prev, size, false, get_prev_alloc (block_prev));
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
static void 
place(block_t *block, size_t asize)
{
    dbg_requires (! (get_alloc (block)));
    size_t csize = get_size(block);

    if ((csize - asize) >= min_block_size)
    {
	    block_t *block_next;
        write_header(block, asize, true, get_prev_alloc (block));

        block_next = find_next(block);
        write_header(block_next, csize-asize, false, true);
        write_footer(block_next, csize-asize, false, true);
        change_alloc_next_block (block_next, false);
        if (block == last_block)
        {
            last_block = block_next;
        }
        insert_free_block (block_next);
    }
    else
    { 
        write_header(block, csize, true, get_prev_alloc (block));
    }
}

static void change_alloc_next_block (block_t *block, bool alloc)
/*dont need to change footer*/
{
    block_t *nextBlock = find_next (block);
    nextBlock -> header = (alloc) ? ((nextBlock -> header) | (0x2)) : ((nextBlock -> header) & (0xFFFFFFFFFFFFFFFD));
    /*if (alloc)
    {
        if (get_alloc (nextBlock))
        {
            nextBlock -> header = (nextBlock -> header) | (0x2);
        }
        else
        {
            nextBlock -> header = (nextBlock -> header) | (0x2);
            word_t *footerp = (word_t *)(((char *)(nextBlock) + get_size(nextBlock)) - wsize);
            *footerp = nextBlock -> header;
        }
    }
    else
    {
        if (get_alloc (nextBlock))
        {
            nextBlock -> header = (nextBlock -> header) & (0xFFFFFFFFFFFFFFFD);
        }
        else
        {
            nextBlock -> header = (nextBlock -> header)  & (0xFFFFFFFFFFFFFFFD);
            word_t *footerp = (word_t *)(((char *)(nextBlock) + get_size(nextBlock)) - wsize);
            *footerp = nextBlock -> header;
        }
    }*/
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
    int ind = find_free_list (asize);
    for (int i = ind; i < 11; i ++)
    {
        for (iter = (*(startIndex + i) != NULL) ? (*(startIndex + i)) : *(freeListPtr + i); (iter != NULL);
                             iter = (iter -> d).ptrArr[1])
        {
            if (asize <= get_size(iter))
            {
                *(startIndex + i) = (iter -> d).ptrArr[1];
                return iter;
            }
        }
    }
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
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc, bool prev_alloc)
/*terary operator*/
{
    if (alloc)
    {
        size = size | (0x1);
    }
    if (prev_alloc)
    {
        size = size | (0x2);
    }
    return size;
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
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - wsize;
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
 * extract_prev_alloc: returns the allocation status of the previous block
 */
static bool extract_prev_alloc(word_t word)
{
    return (bool)((word & 0x2) >> 1);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * get_prev_alloc: returns true when the previous block is allocated based on the
 *                 block header's second lowest bit, and false otherwise.
 */
static bool get_prev_alloc(block_t *block)
{
    return extract_prev_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc, bool prev_alloc)
{
    block->header = pack(size, alloc, prev_alloc);
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc, bool prev_alloc)
{
    word_t *footerp = (word_t *)(((char *)(block) + get_size(block)) - wsize);
    *footerp = pack(size, alloc, prev_alloc);
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

/* This algorith detects cycles in a linked list */
static bool is_acyclic (block_t *block)
{
    if (block == NULL)
    {
        return true;
    }
    block_t *tort = block; // tortoise
    block_t *hare = (block -> d).ptrArr[1]; // hare
    while (hare != tort) 
    {
        if (hare == NULL || (hare -> d).ptrArr[1] == NULL)
        {
            return true;
        } 
        tort = (tort -> d).ptrArr[1]; // tortoise moves by 1 step
        hare = (((hare -> d).ptrArr[1]) -> d).ptrArr[1]; // hare moves by 2 steps
    }
    return false;
}

/* mm_checkheap: checks the heap for correctness; returns true if
 *               the heap is correct, and false otherwise.
 *               can call this function using mm_checkheap(__LINE__);
 *               to identify the line number of the call site.
 */
bool mm_checkheap(int lineno)  
{ 
    block_t *block;
    block_t *prevBlock;
    int freeBlocks = 0;
    int freeBlocksList = 0;
    block_t *footer = (block_t *)((char *)heap_listp - wsize);
    block_t *header = (block_t *)((char *)(mem_heap_hi ()) - (wsize - 1));

    /* Checking epilogue and prologue blocks*/
    if (get_size (footer) != 0 || ! (get_alloc (footer)))
    {
        dbg_printf ("Error in prologue footer. Error on line number %d.\n", lineno);
        return false;
    }
    if (get_size (header) != 0 || ! (get_alloc (header)))
    {
        dbg_printf ("Error in epilogue header. Error on line number %d.\n", lineno);
        return false;
    }
    if (last_block != header && last_block != footer)
    {
        if (find_next (last_block) != header)
        {
            dbg_printf ("Pointer to last block is not correct. Error on line number %d.\n", lineno);
            return false;
        }
        if (get_alloc (last_block) != get_prev_alloc (header))
        {
            dbg_printf ("Epilogue header does not correctly store the alloc status of last block. Error on line number %d.\n", lineno);
            return false;
        }
    }
    
    /* Checking each block address alignment */
    for (block = heap_listp; get_size(block) > 0;
                             block = find_next(block))
    {
        if (!(aligned ((block -> d).payload)))
        {
            dbg_printf ("Block not aligned. Error on line number %d.\n", lineno);
            return false;
        }
        if (get_size (block) < min_block_size)
        {
            dbg_printf ("Block size not correct. Error on line number %d.\n", lineno);
            return false;
        }
        if (get_prev_alloc (find_next (block)) != get_alloc (block))
        {
            dbg_printf ("Next block does not hold alloc status of prev block. Error on line number %d.\n", lineno);
            return false;
        }
        if (! get_alloc (block))
        {
            if ((!get_alloc (find_next (block))) && ((find_next (block) != header)))
            {
                dbg_printf ("2 contiguous free blocks. Block add is %p. Error on line number %d.\n", block, lineno);
                return false;
            }
            if (block -> header != *(word_t *)(((char *)(block) + get_size(block)) - wsize))
            {
                dbg_printf ("Block Header and footer do not agree. Error on line number %d.\n", lineno);
                return false;
            }
            freeBlocks ++;
        }
    }
    /* Checking explicit free list */
    for (int i = 0; i < 11; i ++)
    {
        if (! is_acyclic (freeListPtr[i]))
        {
            dbg_printf ("Cycles present in linked list. Error on line number %d.\n", lineno);
            return false;
        }
        for (block = *(freeListPtr + i); (block != NULL); 
                                block = (block -> d).ptrArr[1])
        {
            if ((block -> d).ptrArr[1] != NULL)
            {
                prevBlock = (((block -> d).ptrArr[1]) -> d).ptrArr[0];
                if (prevBlock != block)
                {
                    dbg_printf ("Free block ptrs not consistent. Error on line number %d.\n", lineno);
                    return false;
                }
            }
            if (! (in_heap (block)))
            {
                dbg_printf ("Free ptrs not between heap hi and lo. Error on line number %d.\n", lineno);
                return false;
            }
            if (get_alloc (block))
            {
                dbg_printf ("Block not free. Error on line number %d.\n", lineno);
                return false;

            }
            if ((i == 0) && (get_size (block) > pow (2, i + 6)))
            {
                dbg_printf ("Free blocks not within segregated list size. i is %d. Block is %p Error on line number %d.\n", i, block, lineno);
                return false;
            }
            else if ((i != 0 && i != 10) && (get_size (block) > pow (2, i + 6) || get_size (block) <= pow (2, i + 5)))
            {
                dbg_printf ("Free blocks not within segregated list size. i is %d. Error on line number %d.\n", i, lineno);
                return false;
            }
            else if ((i == 10) && (get_size (block) <= pow (2, i + 5)))
            {
                dbg_printf ("Free blocks not within segregated list size. i is %d. Error on line number %d.\n", i, lineno);
                return false;
            }
            freeBlocksList ++;
        }
    }
    if (freeBlocksList != freeBlocks)
    {
        dbg_printf ("Number of free blocks not equal. Error on line number %d.\n", lineno);
        return false;
    }
    return true;
}


