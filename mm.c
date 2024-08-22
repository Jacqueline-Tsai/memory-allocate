/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * This file implements a dynamic memory allocator for a heap using an implicit
 *free list with block coalescing. It includes functions for initializing the
 *heap, allocating memory, freeing memory, and reallocating memory blocks. The
 *allocator is designed to manage memory efficiently while maintaining
 *alignment, minimizing fragmentation, and maximizing throughput.
 *
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Jacqueline Tsai <yunhsuat@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printf(...) ((void)printf(__VA_ARGS__))
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, these should emit no code whatsoever,
 * not even from evaluation of argument expressions.  However,
 * argument expressions should still be syntax-checked and should
 * count as uses of any variables involved.  This used to use a
 * straightforward hack involving sizeof(), but that can sometimes
 * provoke warnings about misuse of sizeof().  I _hope_ that this
 * newer, less straightforward hack will be more robust.
 * Hat tip to Stack Overflow poster chqrlie (see
 * https://stackoverflow.com/questions/72647780).
 */
#define dbg_discard_expr_(...) ((void)((0) && printf(__VA_ARGS__)))
#define dbg_requires(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_assert(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_ensures(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_printf(...) dbg_discard_expr_(__VA_ARGS__)
#define dbg_printheap(...) ((void)((0) && print_heap(__VA_ARGS__)))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = 2 * dsize;

/**
 * @brief The minimum chunk size to extend the heap (bytes).
 *
 * Chunksize is used to extend the heap when more memory is needed.
 * Require at least Chunksize to avoid segmentation.
 * It must be a multiple of the double word size to maintain alignment.
 */
static const size_t chunksize = (1 << 12);

/** @brief Mask to extract the allocation bit from a block header. */
static const word_t alloc_mask = 0x1;

/** @brief Mask to extract the allocation bit of previos block from a block
 * header. */
static const word_t prev_alloc_mask = 0x2;

/** @brief Mask to extract the size of a block from its header. */
static const word_t size_mask = ~(word_t)0xF;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;

    /**
     * @brief A pointer to the block payload.
     */
    union {
        struct {
            struct block *next;
            struct block *prev;
        } free_neighbor;
        char payload[0];
    } info;
} block_t;

/* Global variables */
/** @brief Declare no more than 128 bytes of writable global variablesp */
#define LIST_COUNT 15

/** @brief 20% of the requested size. Determines how close the block size should be to the requested size to be considered a good fit. */
#define THRESHOLD 0.3

/** @brief Maximum number of blocks to scan before selecting the best candidate found so far. */
#define SEARCH_LIMIT 30

/** @brief Segregated list of pointers to first free blocks of different ranges
 * of size */
static block_t *free_list_start[LIST_COUNT] = {NULL};

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds size up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the size and alloc of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool prev_alloc, bool alloc) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }
    if (prev_alloc) {
        word |= prev_alloc_mask;
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static bool get_prev_alloc(block_t *block) {
    // dbg_printf("get_prev_alloc %d\n", (bool)((block->header) &
    // prev_alloc_mask) >> 1);
    return (bool)(((block->header) & prev_alloc_mask) >> 1);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Computes the index in the free list array based on the block size.
 *
 * The index is determined by the block size. Larger blocks are assigned higher
 * indices, with a maximum index of 14.
 *
 * @param[in] size The size of the block
 * @return The index in the free list array
 */
static int get_list_index(size_t size) {
    if (size <= 16)
        return 0;
    if (size <= 32)
        return 1;
    if (size <= 64)
        return 2;
    if (size <= 128)
        return 3;
    if (size <= 256)
        return 4;
    if (size <= 512)
        return 5;
    if (size <= 1024)
        return 6;
    if (size <= 2048)
        return 7;
    if (size <= 4096)
        return 8;
    if (size <= 8192)
        return 9;
    if (size <= 16384)
        return 10;
    if (size <= 32768)
        return 11;
    if (size <= 65536)
        return 12;
    if (size <= 131072)
        return 13;
    return 14;
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, info.payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->info.payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->info.payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 *
 * The header is found by subtracting the block size from
 * the footer and adding back wsize.
 *
 * If the prologue is given, then the footer is return as the block.
 *
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    if (size == 0) {
        return (block_t *)footer;
    }
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    if (get_alloc(block)) {
        return asize - wsize;
    }
    return asize - dsize;
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == (char *)mem_heap_hi() - 7);
    block->header = pack(0, false, true);
}

/**
 * @brief Writes the previous allocation bit in the header of the given block.
 *
 * This function updates the header of the block to reflect whether the 
 * previous block is allocated or not.
 *
 * @param[out] block The block whose header needs to be updated
 * @param[in] prev_alloc The allocation status of the previous block
 */
static void write_prev_alloc_bit(block_t *block, bool prev_alloc) {
    dbg_requires(block != NULL);
    block->header = (block->header & (~prev_alloc_mask));
    if (prev_alloc) {
        block->header |= prev_alloc_mask;
    }
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");

    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 * @pre The block is not the prologue
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_prev on the first block in the heap");

    word_t *footerp = find_prev_footer(block);
    return footer_to_header(footerp);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool alloc) {
    dbg_printf("write block\n");
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    bool prev_alloc = get_prev_alloc(block);

    block->header = pack(size, prev_alloc, alloc);
    if (!alloc) {
        word_t *footerp = header_to_footer(block);
        *footerp = pack(size, prev_alloc, alloc);
    }
    write_prev_alloc_bit(find_next(block), alloc);
}

/**
 * @brief Gets the previous block in the free list.
 *
 * @param[in] block A block in the heap
 * @return The previous block in the free list
 * @pre The block must be valid and not the first block in the heap
 */
static block_t *get_linked_prev(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called get_linked_prev on the first block in the heap");
    return block->info.free_neighbor.prev;
}

/**
 * @brief Gets the next block in the free list.
 *
 * @param[in] block A block in the heap
 * @return The next block in the free list
 * @pre The block must be valid and not the last block in the heap
 */
static block_t *get_linked_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called get_linked_next on the last block in the heap");
    return block->info.free_neighbor.next;
}

/**
 * @brief Removes a block from the segregated free list.
 *
 * This function removes the specified block from the appropriate 
 * segregated free list, maintaining the doubly linked list structure.
 *
 * @param[in] block The block to be removed from the free list
 * @pre The block must be valid and present in the free list
 */
static void eliminate_from_linked(block_t *block) {
    int n_bits = get_list_index(get_size(block));
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called eliminate_from_linked on the last block in the heap");

    dbg_printf("eliminate from link, pointer %p, bits %d\n", (void *)block,
               n_bits);
    if (get_linked_prev(block) == NULL && get_linked_next(block) == NULL) {
        free_list_start[n_bits] = NULL;
    } else if (get_linked_next(block) == NULL) {
        get_linked_prev(block)->info.free_neighbor.next = NULL;
    } else if (get_linked_prev(block) == NULL) {
        get_linked_next(block)->info.free_neighbor.prev = NULL;
        free_list_start[n_bits] = get_linked_next(block);
    } else {
        get_linked_prev(block)->info.free_neighbor.next =
            get_linked_next(block);
        get_linked_next(block)->info.free_neighbor.prev =
            get_linked_prev(block);
    }
    dbg_printf("Exit eliminate from link\n");
}

/**
 * @brief Inserts a block into the segregated free list.
 *
 * This function inserts the specified block into the appropriate 
 * segregated free list, maintaining the doubly linked list structure.
 *
 * @param[in] block The block to be inserted into the free list
 * @pre The block must be valid and not already present in the free list
 */
static void insert_into_linked(block_t *block) {
    int n_bits = get_list_index(get_size(block));
    dbg_printf("insert into link, pointer %p, bits %d\n", (void *)block,
               n_bits);

    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called insert_into_linked on the last block in the heap");
    dbg_requires(block != free_list_start[n_bits]);

    block->info.free_neighbor.prev = NULL;
    block->info.free_neighbor.next = free_list_start[n_bits];
    if (free_list_start[n_bits] != NULL) {
        free_list_start[n_bits]->info.free_neighbor.prev = block;
    }
    free_list_start[n_bits] = block;
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

/**
 * @brief Coalesces a free block with its neighbors if they are free.
 *
 * This function merges adjacent free blocks to form a larger free block,
 * reducing fragmentation. The block is first removed from the free list, then
 * merged with any adjacent free blocks, and finally the new coalesced block is
 * returned.
 *
 * @param[in] block The block to be coalesced
 * @return The coalesced block
 * @pre The block must be valid and not allocated
 * @post The block is coalesced with its neighbors if they are free
 */
static block_t *coalesce_block(block_t *block) {
    dbg_printf("coalesce block\n");

    if (get_size(block) == 0) {
        return block;
    }
    size_t new_size = get_size(block);

    block_t *block_next = find_next(block);
    eliminate_from_linked(block);
    if (!get_alloc(block_next)) {
        new_size += get_size(block_next);
        eliminate_from_linked(block_next);
    }

    if (!get_prev_alloc(block)) {
        block_t *block_prev = find_prev(block);
        dbg_printf("prev block %p, heap start %p\n", (void *)block_prev,
                   (void *)heap_start);
        dbg_printf("prev block size %d %zu\n", get_alloc(block_prev),
                   get_size(block_prev));
        new_size += get_size(block_prev);
        block = block_prev;
        eliminate_from_linked(block_prev);
    }
    write_block(block, new_size, false);
    dbg_printf("Exit coalesce_block\n");
    return block;
}

/**
 * @brief Extends the heap with a new free block of the specified size.
 *
 * This function increases the size of the heap by the specified size,
 * initializing a new free block and the new epilogue header.
 *
 * @param[in] size The size to extend the heap by
 * @return The newly allocated block
 * @pre The size must be a multiple of the double word size
 * @post The heap is extended, and a new free block is initialized
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    dbg_printf("extend heap\n");

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk((intptr_t)size)) == (void *)-1) {
        return NULL;
    }

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_block(block, size, false);
    block->info.free_neighbor.prev = NULL;
    block->info.free_neighbor.next = NULL;

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next);

    // Coalesce in case the previous block was free
    return coalesce_block(block);
}

/**
 * @brief Splits a block into two blocks if the size difference is large enough.
 *
 * This function checks if a block can be split into two smaller blocks. If so,
 * it updates the headers and footers accordingly.
 *
 * @param[in] block The block to be split
 * @param[in] asize The desired size of the first block after splitting
 * @pre The block must be valid and allocated
 * @post The block is split into two blocks if possible
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));

    dbg_printf("split block, pointer %p, split %d\n", (void *)block,
               (get_size(block) - asize) >= min_block_size);

    size_t block_size = get_size(block);

    if ((block_size - asize) >= min_block_size) {
        write_block(block, asize, true);
        block_t *block_next = find_next(block);
        write_block(block_next, block_size - asize, false);
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief Finds a free block that fits the requested size.
 *
 * This function searches the segregated free lists for a block that is large
 * enough to satisfy the allocation request.
 *
 * @param[in] asize The size of the block to allocate
 * @return A pointer to a suitable block, or NULL if no suitable block is found
 * @pre The size must be a valid block size
 * @post A suitable block is found and returned, or NULL if no suitable block is
 * found
 */
static block_t *find_fit(size_t asize) {
    dbg_printf("find fit, bits %d\n", get_list_index(asize));
    block_t *block;
    block_t *best_block = NULL;
    size_t best_size_difference = SIZE_MAX;
    size_t threshold_size_difference = (size_t)((double)asize * THRESHOLD);

    int search_count = 0;

    for (int i = get_list_index(asize); i < LIST_COUNT; i++) {
        for (block = free_list_start[i]; block != NULL;
             block = block->info.free_neighbor.next) {
            size_t block_size = get_size(block);

            if (asize <= block_size) {
                size_t size_difference = block_size - asize;

                // Check if the block is within the threshold
                if (size_difference <= threshold_size_difference) {
                    if (size_difference < best_size_difference) {
                        best_block = block;
                        best_size_difference = size_difference;
                    }
                    search_count++;
                }

                // If perfect fit is found, allocate immediately
                if (size_difference == 0) {
                    return block;
                }

                if (search_count >= SEARCH_LIMIT) {
                    return best_block;
                }
            }
        }

        if (best_block != NULL) {
            return best_block;
        }
    }

    // Fall back to First Fit if no suitable block found within search limit
    for (int i = get_list_index(asize); i < LIST_COUNT; i++) {
        for (block = free_list_start[i]; block != NULL;
             block = block->info.free_neighbor.next) {
            if (asize <= get_size(block)) {
                return block;
            }
        }
    }

    dbg_printf("not found\n");
    return NULL; // no fit found
}

/**
 * @brief Checks the consistency of the heap.
 *
 * This function verifies the consistency and correctness of the heap structure,
 * including block sizes, alignment, free/allocated status, and the integrity of
 * the free lists.
 *
 * @param[in] line The line number from which this function was called
 * @return true if the heap is consistent, false otherwise
 * @pre The heap must be initialized
 * @post The heap is checked for consistency, and any inconsistencies are
 * reported
 */
bool mm_checkheap(int line) {
    // Check for prologue block
    if (heap_start == NULL) {
        dbg_printf("Heap start is NULL (called at line %d)\n", line);
        return false;
    }

    // Check if the first block is the prologue and is correctly marked as
    // allocated
    block_t *block = find_prev(heap_start);
    if (get_size(block) != 0 || !get_alloc(block)) {
        dbg_printf("Prologue block is incorrect. Block size is %lu. Alloc is "
                   "%d (called at line %d)\n",
                   get_size(block), get_alloc(block), line);
        return false;
    }

    // Traverse the entire heap to check for correctness
    block_t *prev_block = NULL;
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
        // Check block alignment
        if (((uintptr_t)block - (uintptr_t)heap_start) % dsize != 0) {
            dbg_printf("Block at %p is not aligned. Start point: %p. (called "
                       "at line %d)\n",
                       (void *)block, (void *)heap_start, line);
            return false;
        }

        // Check block size is at least the minimum block size
        if (get_size(block) < min_block_size) {
            dbg_printf("Block at %p is smaller than minimum block size (called "
                       "at line %d)\n",
                       (void *)block, line);
            return false;
        }

        // Check if block is within heap boundaries
        if ((char *)block < (char *)mem_heap_lo() ||
            (char *)block >= (char *)mem_heap_hi()) {
            dbg_printf(
                "Block at %p is out of heap boundaries (called at line %d)\n",
                (void *)block, line);
            return false;
        }

        // Check if header and footer match
        if (!get_alloc(block)) {
            word_t *footer = header_to_footer(block);
            if (block->header != *footer) {
                dbg_printf("Header and footer do not match for block at %p "
                           "(called at line %d)\n",
                           (void *)block, line);
                return false;
            }
        }

        // Check for consecutive free blocks
        if (prev_block && !get_alloc(prev_block) && !get_alloc(block)) {
            dbg_printf(
                "Consecutive free blocks at %p and %p (called at line %d)\n",
                (void *)prev_block, (void *)block, line);
            return false;
        }

        // Check prev alloc bit
        if (prev_block && get_alloc(prev_block) != get_prev_alloc(block)) {
            dbg_printf("Prev alloc bit (%d) at block %p is different from "
                       "alloc bit (%d) at block %p (called at line %d)\n",
                       get_alloc(prev_block), (void *)prev_block,
                       get_prev_alloc(block), (void *)block, line);
            return false;
        }

        prev_block = block;
    }

    // Check for epilogue block
    if (get_size(block) != 0 || !get_alloc(block)) {
        dbg_printf("Epilogue block is incorrect (called at line %d)\n", line);
        return false;
    }

    // Traverse the free list to check for correctness
    for (int i = 0; i < LIST_COUNT; i++) {
        for (block = free_list_start[i]; block != NULL && get_size(block) > 0;
             block = get_linked_next(block)) {
            if (get_alloc(block)) {
                dbg_printf("Free block at %p in list %d is allocated (called "
                           "at line %d)\n",
                           (void *)block, i, line);
                return false;
            }
            if (get_list_index(get_size(block)) != i) {
                dbg_printf("Free block at %p in list %d is not in correct "
                           "list. Should be in list %d (called at line %d)\n",
                           (void *)block, i, get_list_index(get_size(block)),
                           line);
                return false;
            }
        }
    }

    // tmp
    dbg_printf("\n");
    int i = 0;
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
        dbg_printf("block %d %p %zu %d -> ", i, (void *)block, get_size(block),
                   get_alloc(block));
        i++;
    }
    dbg_printf("\n");

    return true;
}

/**
 * @brief Initializes the memory allocator.
 *
 * This function sets up the initial empty heap, including creating the prologue
 * and epilogue blocks. It also extends the heap by the initial chunk size.
 *
 * @return true if successful, false otherwise
 * @post The heap is initialized and ready for memory allocations
 */
bool mm_init(void) {
    dbg_printf("Enter init\n");
    for (size_t i = 0; i < LIST_COUNT; i++) {
        free_list_start[i] = NULL;
    }

    // Create special regions of memory for small, fixed-size blocks
    // mem_sbrk(1000 * dsize);

    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    start[0] = pack(0, true, true); // Heap prologue (block footer)
    start[1] = pack(0, true, true); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);

    // Extend the empty heap with a free block of chunksize bytes
    block_t *new_block = extend_heap(chunksize);
    if (new_block == NULL) {
        return false;
    }
    insert_into_linked(new_block);

    return true;
}

/**
 * @brief Allocates a block of memory of the specified size.
 *
 * This function searches the free list for a suitable block. If no suitable
 * block is found, it extends the heap and allocates a new block.
 *
 * @param[in] size The size of the block to allocate
 * @return A pointer to the allocated block, or NULL if the allocation fails
 * @pre The size must be greater than 0
 * @post A block of memory is allocated and returned
 */
void *malloc(size_t size) {
    dbg_printf("\nMalloc %zu\n", size);
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        if (!(mm_init())) {
            dbg_printf("Problem initializing heap. Likely due to sbrk");
            return NULL;
        }
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = max(min_block_size, round_up(size + wsize, dsize));

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    } else {
        eliminate_from_linked(block);
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Mark block as allocated
    size_t block_size = get_size(block);
    write_block(block, block_size, true);

    // Try to split the block if too large
    split_block(block, asize);

    block_t *block_next = find_next(block);

    // eliminate_from_linked(block);
    if (!get_alloc(block_next)) {
        insert_into_linked(block_next);
    }

    bp = header_to_payload(block);

    dbg_printf("Exiting malloc with pointer %p\n", bp);
    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief Frees a previously allocated block of memory.
 *
 * This function marks a block as free and coalesces it with neighboring free
 * blocks if possible.
 *
 * @param[in] bp The pointer to the block to free
 * @pre The block must be valid and previously allocated
 * @post The block is marked as free and coalesced with neighboring blocks if
 * possible
 */
void free(void *bp) {
    dbg_printf("\nFree %p\n", bp);
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_block(block, size, false);

    insert_into_linked(block);

    // Try to coalesce the block with its neighbors
    block_t *new_block = coalesce_block(block);
    insert_into_linked(new_block);

    dbg_ensures(mm_checkheap(__LINE__));
    dbg_printf("\nExiting free with pointer %p\n", bp);
}

/**
 * @brief Reallocates a block of memory to a new size.
 *
 * This function reallocates a block to a new size, copying the existing data to
 * the new block. If the new size is smaller, the data is truncated. If the new
 * size is larger, additional memory is allocated.
 *
 * @param[in] ptr The pointer to the existing block of memory
 * @param[in] size The new size of the block
 * @return A pointer to the reallocated block, or NULL if the reallocation fails
 */
void *realloc(void *ptr, size_t size) {
    dbg_printf("\nRealloc %p %zu\n", ptr, size);

    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief Allocates a block of memory for an array, initializing it to zero.
 *
 * This function allocates memory for an array of elements, each of the
 * specified size, and initializes all bytes in the allocated memory to zero.
 *
 * @param[in] elements The number of elements in the array
 * @param[in] size The size of each element
 * @return A pointer to the allocated and initialized memory, or NULL if the
 * allocation fails
 */
void *calloc(size_t elements, size_t size) {
    dbg_printf("\nCalloc %zu %zu\n", elements, size);
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
