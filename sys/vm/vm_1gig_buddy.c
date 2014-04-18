
#include <sys/param.h>
#include <sys/systm.h>
#include <sys/kernel.h>		/* for ticks and hz */
#include <sys/eventhandler.h>
#include <sys/lock.h>
#include <sys/mutex.h>
#include <sys/proc.h>
#include <sys/malloc.h>

#include <sys/sbuf.h>
#include <sys/sysctl.h>

#include <vm/vm.h>
#include <vm/vm_kern.h>
#include <vm/vm_param.h>
#include <vm/pmap.h>
#include <vm/vm_map.h>
#include <vm/vm_object.h>
#include <vm/vm_page.h>
#include <vm/vm_pageout.h>
#include <vm/vm_phys.h>
#include <vm/vm_extern.h>
#include <vm/uma.h>


//
// Memory in the 1 gig page is tracked in power-of-2 sized chunks, logically
// arranged in a binary tree.  At the top is a single 1 GB chunk, on the next
// level down are two 512 MB chunks, then four 256 MB chunks, etc.
//
// Each level in this tree has an "in-use" bitmap that tracks which of the nodes
// at that level are free.  If a node's in-use bit is cleared, that means that
// the node is unused and is available for allocation.  If a node's in-use bit
// is set, it means the node is not available for allocation (because it's
// already been allocated by somebody else, or because one of the smaller chunks
// under it has been allocated).
//


#define KMEM_1GIG_NUM_LEVELS 19  // log2(1GB/4kB) + 1

#define KMEM_1GIG_LEFT_IN_USE  0x1 // left half has been allocated
#define KMEM_1GIG_RIGHT_IN_USE 0x2 // right half has been allocated

#define KMEM_1GIG_IN_USE (KMEM_1GIG_LEFT_IN_USE | KMEM_1GIG_RIGHT_IN_USE)

#define NODE_IS_FREE(n) ((n->va & KMEM_1GIG_IN_USE) == 0)
#define NODE_IS_ALLOCATED(n) ((n->va & KMEM_1GIG_IN_USE) == KMEM_1GIG_IN_USE)

#define NODE_IS_LEAF(n) ((n->left_child == NULL) && (n->right_child == NULL))

#define NODE_HAS_BOTH_CHILDREN(n)  \
    ((n->left_child != NULL) && (n->right_child != NULL))


//
// This struct tracks a 1 gig page that the kmem low-level allocator is
// currently using to satisfy allocation requests made by the rest of the
// kernel (including uma slabs).
//
struct kmem_1gig_page {
    // list of 1 gig pages used by the allocator
    TAILQ_ENTRY(kmem_1gig_page) list;

    // This is an array of bitmaps, one for each level in the tree.
    // in_use_bitmap[0] points to an array containing a single bit, which is the
    // in-use bit for the whole 1 gig.
    // in_use_bitmap[1] points to an array of 2 bits, the least significant bit
    // tracks the first 512 MB chunk of the page and the most significant bit
    // tracks the second 512 MB chunk.
    // The smallest tracked chunk in 4 kB, so there are 18 levels.
    uint64_t *in_use_bitmap[KMEM_1GIG_NUM_LEVELS];

    vm_offset_t va;
    vm_paddr_t pa;

    uint64_t bytes_free;
    uint64_t bytes_allocated;    // how much did our users ask for?
    // how much did we actually give our users?  (it'll probably be more
    // than bytes_allocated because we round up to a power of 2)
    uint64_t bytes_handed_out;
};


static int vm_1gig_fetching_another_page = 0;

TAILQ_HEAD(kmem_1gig_page_list, kmem_1gig_page) kmem_1gig_pages =
	TAILQ_HEAD_INITIALIZER(kmem_1gig_pages);

static struct mtx kmem_1gig_mutex;
MTX_SYSINIT(kmem_1gig_mutex, &kmem_1gig_mutex, "kmem 1gig mutex", MTX_DEF);

#define KASSERT_MTX_OWNED()                                   \
    do {                                                      \
        KASSERT(                                              \
            cold || mtx_owned(&kmem_1gig_mutex),              \
            ("%s: kmem 1gig mutex not owned!", __FUNCTION__)  \
        );                                                    \
    } while(0)


#define LOCK() do { \
    if (!cold) { \
        mtx_lock(&kmem_1gig_mutex); \
    } \
} while(0)


#define UNLOCK() do { \
    if (!cold) { \
        mtx_unlock(&kmem_1gig_mutex); \
    } \
} while(0)


#define WAKEUP() do { \
    if (!cold) { \
        wakeup(&vm_1gig_fetching_another_page); \
    } \
} while(0)


#define KASSERT_MTX_OWNED()                                   \
    do {                                                      \
        KASSERT(                                              \
            cold || mtx_owned(&kmem_1gig_mutex),              \
            ("%s: kmem 1gig mutex not owned!", __FUNCTION__)  \
        );                                                    \
    } while(0)


#define KASSERT_MTX_NOT_OWNED()                               \
    do {                                                      \
        KASSERT(                                              \
            cold || !mtx_owned(&kmem_1gig_mutex),              \
            ("%s: kmem 1gig mutex owned when it sholdnt be!", __FUNCTION__)  \
        );                                                    \
    } while(0)


static inline uint64_t round_up_to_power_of_2(uint64_t x) {
    // 4096 is the minimum power of 2 we'll return
    if (x < 4096) {
        return 4096;
    }

    x--;
    x |= x >> 1;  // handle  2 bit numbers
    x |= x >> 2;  // handle  4 bit numbers
    x |= x >> 4;  // handle  8 bit numbers
    x |= x >> 8;  // handle 16 bit numbers
    x |= x >> 16; // handle 32 bit numbers
    x |= x >> 32; // handle 64 bit numbers
    x++;

    return x;
}


//
// Helper functions to work with the in-use bitmaps.
//

static inline int
kmem_1gig_find_level(vm_size_t node_size)
{
    int level = 0;
    vm_size_t level_size = 1024 * 1024 * 1024;

    while (level_size > node_size) {
        level_size >>= 1;
        level ++;
    }

    return level;
}


static inline vm_size_t
kmem_1gig_node_size_at_level(int level)
{
    vm_size_t node_size = 1024 * 1024 * 1024;
    KASSERT(
        (level >= 0) && (level < KMEM_1GIG_NUM_LEVELS),
        ("%s: invalid level %d", __FUNCTION__, level)
    );
    return node_size >> level;
}


static inline int
kmem_1gig_num_nodes_at_level(int level)
{
    int num_nodes = 1;
    return num_nodes << level;
}


static inline int
kmem_1gig_node_in_use(struct kmem_1gig_page *p, int level, int node)
{
    int word = node / 64;
    int bit = node % 64;
    KASSERT_MTX_OWNED();
    KASSERT(
        (level >= 0) && (level < KMEM_1GIG_NUM_LEVELS),
        ("%s: invalid level %d", __FUNCTION__, level)
    );
    KASSERT(
        (node >= 0) && (node < kmem_1gig_num_nodes_at_level(level)),
        (
            "%s: invalid node %d at level %d (%d nodes)",
            __FUNCTION__,
            node,
            level,
            kmem_1gig_num_nodes_at_level(level)
        )
    );
    return (0 != (p->in_use_bitmap[level][word] & (1ULL << bit)));
}


static inline void
kmem_1gig_mark_node_in_use(struct kmem_1gig_page *p, int level, int node)
{
    int word = node / 64;
    int bit = node % 64;
    KASSERT_MTX_OWNED();
    KASSERT(
        (level >= 0) && (level < KMEM_1GIG_NUM_LEVELS),
        ("%s: invalid level %d", __FUNCTION__, level)
    );
    KASSERT(
        (node >= 0) && (node < kmem_1gig_num_nodes_at_level(level)),
        (
            "%s: invalid node %d at level %d (%d nodes)",
            __FUNCTION__,
            node,
            level,
            kmem_1gig_num_nodes_at_level(level)
        )
    );
    p->in_use_bitmap[level][word] |= (1ULL << bit);
}

// Lifted and modified from sys/bitstring
#define	_bit_qword(bit) ((bit) >> 6)

				/* clear bits start ... stop in bitstring */
static inline void
bit_nclear64(uint64_t *bits, int start, int stop)
{
	int startword = _bit_qword(start);
	int stopword = _bit_qword(stop);
	// NOTE: shift twice to ensure no shift is all 64 bits, which is
	// undefined
	if (startword == stopword) {
		bits[startword] &= (((UINT64_MAX >> (63 - (start&63)))>>1) |
				      ((UINT64_MAX << (stop&63)) << 1));
	} else {
		bits[startword] &= (UINT64_MAX >> (63 - (start&63))) >> 1;
		while (++startword < stopword)
			bits[startword] = 0;
		bits[stopword] &= (UINT64_MAX << (stop&63)) << 1;
	}
}

static inline void
bit_nset64(uint64_t *bits, int start, int stop)
{
	int startword = _bit_qword(start);
	int stopword = _bit_qword(stop);
	if (startword == stopword) {
		bits[startword] |= ((UINT64_MAX << (start&63)) &
				      (UINT64_MAX >> (63 - (stop&63))));
	} else {
		bits[startword] |= UINT64_MAX << (start&63);
		while (++startword < stopword)
			bits[startword] = UINT64_MAX;
		bits[stopword] |= UINT64_MAX >> (63 - (stop&63));
	}
}

static inline void
kmem_1gig_mark_nodes_in_use(struct kmem_1gig_page *p, int level, int first, int last)
{
    KASSERT_MTX_OWNED();
    MPASS(first <= last);
    MPASS((level >= 0) && (level < KMEM_1GIG_NUM_LEVELS));
    MPASS(first >= 0 && (first < kmem_1gig_num_nodes_at_level(level)));
    MPASS(last >= 0 && (last < kmem_1gig_num_nodes_at_level(level)));
    bit_nset64(p->in_use_bitmap[level], first, last);
}

static inline void
kmem_1gig_mark_nodes_free(struct kmem_1gig_page *p, int level, int first, int last)
{
    KASSERT_MTX_OWNED();
    MPASS(first <= last);
    MPASS((level >= 0) && (level < KMEM_1GIG_NUM_LEVELS));
    MPASS(first >= 0 && (first < kmem_1gig_num_nodes_at_level(level)));
    MPASS(last >= 0 && (last < kmem_1gig_num_nodes_at_level(level)));
    bit_nclear64(p->in_use_bitmap[level], first, last);
}


static inline void
kmem_1gig_mark_node_free(struct kmem_1gig_page *p, int level, int node)
{
    int word = node / 64;
    int bit = node % 64;
    KASSERT_MTX_OWNED();
    KASSERT(
        (level >= 0) && (level < KMEM_1GIG_NUM_LEVELS),
        ("%s: invalid level %d", __FUNCTION__, level)
    );
    KASSERT(
        (node >= 0) && (node < kmem_1gig_num_nodes_at_level(level)),
        (
            "%s: invalid node %d at level %d (%d nodes)",
            __FUNCTION__,
            node,
            level,
            kmem_1gig_num_nodes_at_level(level)
        )
    );
    p->in_use_bitmap[level][word] &= ~(1ULL << bit);
}


static inline int
kmem_1gig_va_to_node(struct kmem_1gig_page *p, int level, vm_offset_t va) {
    int node;
    KASSERT(
        (va >= p->va) && (va < (p->va + (1024 * 1024 * 1024))),
        ("%s: va=0x%lx is not on page at va=0x%lx!", __FUNCTION__, va, p->va)
    );
    node =  (va - p->va) / kmem_1gig_node_size_at_level(level);
    KASSERT(
        (p->va + (node * kmem_1gig_node_size_at_level(level)) == va),
        (
            "%s: va=0x%lx is not on a node boundary (p->va=0x%lx, "
            "node=%d, node_size=0x%lx, node va=0x%lx)",
            __FUNCTION__, va, p->va, node,
            kmem_1gig_node_size_at_level(level),
            p->va + (node * kmem_1gig_node_size_at_level(level))
        )
    );
    return node;
}


static inline int
kmem_1gig_sibling_node(int node) {
    if (node & 1) {
        return node - 1;
    } else {
        return node + 1;
    }
}




//
// Sysctl stats book keeping functions
//

static inline void kmem_1gig_alloc_bookkeeping(
    struct kmem_1gig_page *p,
    vm_size_t size
) {
    uint64_t node_size;

    KASSERT_MTX_OWNED();
    KASSERT(p != NULL, ("%s: got NULL page!\n", __FUNCTION__));

    node_size = round_up_to_power_of_2(size);
    p->bytes_free -= node_size;
    p->bytes_allocated += size;
    p->bytes_handed_out += node_size;
}


static inline void kmem_1gig_free_bookkeeping(
    struct kmem_1gig_page *p,
    vm_size_t size
) {
    uint64_t node_size;

    KASSERT_MTX_OWNED();
    KASSERT(p != NULL, ("kmem_1gig_free_bookkeeping: got NULL page!\n"));

    node_size = round_up_to_power_of_2(size);
    p->bytes_free += node_size;
    p->bytes_allocated -= size;
    p->bytes_handed_out -= node_size;
}




//
// Misc helper functions
//

static void kmem_1gig_sort_page_list(struct kmem_1gig_page *p) {
    KASSERT_MTX_OWNED();
    do {
        struct kmem_1gig_page *prev, *next;

        prev = TAILQ_PREV(p, kmem_1gig_page_list, list);
        next = TAILQ_NEXT(p, list);

#if 0
        printf(
            "1gig alloc: should sort pages, prev->bytes_free=%ld, p->bytes_free=%ld, next->bytes_free=%ld\n",
            (prev != NULL ? prev->bytes_free : -1),
            p->bytes_free,
            (next != NULL ? next->bytes_free : -1)
        );
#endif


        if (prev == NULL) {
            // p is the head of the list
            if (next == NULL) {
                break;
            }
            if (p->bytes_free > next->bytes_free) {
                // move P to be after Next, and sort again
                TAILQ_REMOVE(&kmem_1gig_pages, p, list);
                TAILQ_INSERT_AFTER(&kmem_1gig_pages, next, p, list);
                continue;
            } else {
                break;
            }

        } else if (next == NULL) {
            // p is the tail of the list
            // prev is not NULL
            if (p->bytes_free < prev->bytes_free) {
                // move P to be before Prev, and sort again
                TAILQ_REMOVE(&kmem_1gig_pages, p, list);
                TAILQ_INSERT_BEFORE(prev, p, list);
                continue;
            } else {
                break;
            }

        } else {
            // p is somewhere in the middle of the list
            if (p->bytes_free < prev->bytes_free) {
                // move P to be before Prev, and sort again
                TAILQ_REMOVE(&kmem_1gig_pages, p, list);
                TAILQ_INSERT_BEFORE(prev, p, list);
                continue;

            } else if (p->bytes_free > next->bytes_free) {
                // move P to be after Next, and sort again
                TAILQ_REMOVE(&kmem_1gig_pages, p, list);
                TAILQ_INSERT_AFTER(&kmem_1gig_pages, next, p, list);
                continue;
            }

            // p is where it belongs
            break;
        }
    } while (1);
}

static inline int
bit_ffc_64(uint64_t *bits, int nbits)
{
    uint64_t *cur = bits;
    uint64_t *over = cur + ((nbits - 1)/64) + 1;
    int bit=-1;
    if (nbits <= 0) {
        return (-1);
    }
    for (; cur < over; cur++) {
        int ls = ffsl(~(*cur));
        if (ls > 0) {
            bit = (ls-1) + (64 * (cur - bits));
            break;
        }
    }

    if (bit >= nbits) {
        bit = -1;
    }
    return bit;
}


//
// See if there's a free chunk of the requested size on this 1 gig page.
//
static vm_offset_t
kmem_1gig_find_free(struct kmem_1gig_page *p, vm_size_t size)
{
    vm_offset_t va;
    vm_size_t node_size;
    uint64_t num_nodes;
    int level;
    int node;  // index of the free node

    KASSERT_MTX_OWNED();
    KASSERT(p != NULL, ("%s: NULL page passed in!", __FUNCTION__));

    if (size > p->bytes_free) return 0;

    node_size = round_up_to_power_of_2(size);
    KASSERT(
        node_size >= 4096,
        (
            "%s: round_up_to_power_of_2(%lu) "
            " returned %lu, expected 4096\n",
            __FUNCTION__,
            size,
            node_size
        )
    );

    level = kmem_1gig_find_level(node_size);
    num_nodes = kmem_1gig_num_nodes_at_level(level);
    node = bit_ffc_64(p->in_use_bitmap[level], num_nodes);
    if ( node < 0 ) {
        return 0;
    }
    MPASS(!kmem_1gig_node_in_use(p, level, node));

    va = p->va + (node * node_size);

    // mark this node as in use
    kmem_1gig_mark_node_in_use(p, level, node);

    // mark all the children as in-use
    {
        int first_child_node = node;
        int child_level;
        for (
            child_level = level + 1;
            child_level < KMEM_1GIG_NUM_LEVELS;
            child_level ++
        ) {
            int num_child_nodes = 1 << (child_level - level);
            first_child_node <<= 1;
	    kmem_1gig_mark_nodes_in_use(p, child_level,
		first_child_node, first_child_node + num_child_nodes - 1);
        }
    }

    // mark all the ancestors as in-use
    {
        int ancestor_node = node;
        int ancestor_level;
        for (
            ancestor_level = level - 1;
            ancestor_level >= 0;
            ancestor_level --
        ) {
            ancestor_node >>= 1;
            // we don't assert that the ancestors are not in use here, because
            // our sibling might be in use, in which case our ancestors would
            // be in use too
            kmem_1gig_mark_node_in_use(p, ancestor_level, ancestor_node);
        }
    }

    return va;
}


// Allocate and initialize another 1 gig page, but don't insert it into the
// list.  Return it instead, the caller will take the 1 gig lock and insert the
// page.
static struct kmem_1gig_page *
kmem_1gig_add_page(void)
{
    struct kmem_1gig_page *p;
    vm_offset_t va;
    int level;

    KASSERT_MTX_NOT_OWNED();
    KASSERT(vm_1gig_fetching_another_page, ("%s: fetching another 1 gig page "
            "without advertising that fact...", __FUNCTION__));

    va = kmem_malloc_1gig_page(kmem_arena, M_NOWAIT);
    if (va == 0) {
        static int complained_once = 0;
        if (!complained_once) {
            printf("kmem_1gig_add_page: failed to allocate another gig\n");
            complained_once = 1;
        }
        goto fail0;
    }

    p = (void*)kmem_malloc_real(
        kmem_arena,
        sizeof(struct kmem_1gig_page),
        M_NOWAIT
    );
    if (p == NULL) {
        goto fail1;
    }

    bzero(p->in_use_bitmap, sizeof(p->in_use_bitmap));

    for (level = 0; level < KMEM_1GIG_NUM_LEVELS; level ++) {
        int num_bytes = ((kmem_1gig_num_nodes_at_level(level) / 64) + 1) * 8;
        p->in_use_bitmap[level] = (uint64_t*)kmem_malloc_real(
            kmem_arena,
            num_bytes,
            M_NOWAIT | M_ZERO
        );
        if (p->in_use_bitmap[level] == NULL) {
            goto fail2;
        }
    }

    p->va = va;
    p->pa = pmap_extract(kernel_pmap, p->va);
    p->bytes_free = 1024 * 1024 * 1024;
    p->bytes_allocated = 0;
    p->bytes_handed_out = 0;

    return p;

fail2:
    for (level = 0; level < KMEM_1GIG_NUM_LEVELS; level ++) {
        int num_bytes = (kmem_1gig_num_nodes_at_level(level) / 8) + 1;
        if (p->in_use_bitmap[level] == NULL) {
            break;
        }
        kmem_free_real(kmem_arena, (vm_offset_t)p->in_use_bitmap[level], num_bytes);
    }

    kmem_free_real(kmem_arena, (vm_offset_t)p, sizeof(struct kmem_1gig_page));

fail1:
    kmem_free_real(kmem_arena, va, 1024*1024*1024);

fail0:
    return NULL;
}


static vm_offset_t
kmem_alloc_1gig_internal(
    struct vmem *vmem, vm_size_t size, int flags, vm_paddr_t low,
    vm_paddr_t high, unsigned long alignment, unsigned long boundary,
    vm_memattr_t memattr, int contig)
{
    vm_offset_t va;
    struct kmem_1gig_page *p;
    static int complained_once = 0;

    size = ulmax(size, alignment);

    if (size > 1024*1024*1024) {
        printf("%s: request too big, using the real allocator\n", __FUNCTION__);
        goto punt;
    }

    if (vmem != kmem_arena) {
        goto punt;
    }

    LOCK();

retry:
    KASSERT_MTX_OWNED();

    // do we have a 1 gig page with a big enough free chunk?
    TAILQ_FOREACH(p, &kmem_1gig_pages, list) {
        if ((p->pa < low) || ((p->pa + (1<<30)) > high)) {
            continue;
        }
        va = kmem_1gig_find_free(p, size);
        if (va != 0) {
            // found one, return it quick!
            kmem_1gig_alloc_bookkeeping(p, size);
            kmem_1gig_sort_page_list(p);
            UNLOCK();
            if (flags & M_ZERO) {
                bzero((void*)va, size);
            }
            return va;
        }
    }

    // Didn't find a page with free space for this allocation.
    // Set the indicator flag that says to other threads calling the 1 gig
    // buddy allocator "a thread is trying to add another page, have
    // patience".  We set this indicator while holding the 1 gig buddy
    // lock, so only one thread at a time tries to add memory.

    if (vm_1gig_fetching_another_page) {
        // some other thread is trying to fetch another page
        KASSERT(!cold, ("%s: multiple threads in 1 gig buddy allocator while "
                    "system is cold!", __FUNCTION__));

        if (flags & M_NOWAIT) {
            UNLOCK();
            DELAY(10);
            LOCK();
        } else {
            msleep(
                &vm_1gig_fetching_another_page,
                &kmem_1gig_mutex,
                0,
                "1gig page",
                0
            );
        }
        goto retry;
    }

    // we're the lucky thread that gets to fetch more memory
    vm_1gig_fetching_another_page = 1;
    UNLOCK();
    p = kmem_1gig_add_page();
    LOCK();
    vm_1gig_fetching_another_page = 0;
    WAKEUP();
    if (p == NULL) {
        // failed to get another gig, fall back to the real allocator
        if (!complained_once) {
            printf("%s: failed, using the real allocator\n", __FUNCTION__);
            complained_once = 1;
        }
        UNLOCK();
        goto punt;
    }

    // got another gig!
    TAILQ_INSERT_TAIL(&kmem_1gig_pages, p, list);

    if ((p->pa < low) || ((p->pa + (1<<30)) > high)) {
        goto punt;
    }

    va = kmem_1gig_find_free(p, size);
    if (va != 0) {
        // found one, return it quick!
        kmem_1gig_alloc_bookkeeping(p, size);
        kmem_1gig_sort_page_list(p);
        UNLOCK();
        if (flags & M_ZERO) {
            bzero((void*)va, size);
        }
        return va;
    }

    if (!complained_once) {
        printf("%s: failed, using the real allocator\n", __FUNCTION__);
        complained_once = 1;
    }

    UNLOCK();

punt:
    if (contig) {
        return kmem_alloc_contig_real(vmem, size, flags, low, high,
            alignment, boundary, memattr);
    } else {
        return kmem_malloc_real(vmem, size, flags);
    }
}


vm_offset_t
kmem_malloc_1gig(struct vmem *vmem, vm_size_t size, int flags)
{
    return kmem_alloc_1gig_internal(
        vmem, size, flags,
        0,            // low phys addr
        UINTPTR_MAX,  // high phys addr
        0x1,          // alignment
        0,            // boundary
        0,            // memattr, not used for non-contig
        0             // *not* contig
    );
}

vm_offset_t
kmem_alloc_contig_1gig(struct vmem *vmem, vm_size_t size, int flags, vm_paddr_t low,
    vm_paddr_t high, unsigned long alignment, unsigned long boundary,
    vm_memattr_t memattr)
{
    return kmem_alloc_1gig_internal(
        vmem, size, flags,
        low, high, alignment,
        boundary, memattr,
        1 // contig
    );
}


static void
kmem_free_1gig_to_page(
    struct kmem_1gig_page *p,
    vm_offset_t addr,
    vm_size_t size
) {
    vm_size_t node_size;  // size of the node we're freeing this chunk to
    int node;
    int level;

    KASSERT_MTX_OWNED();

    //
    // We're freeing a chunk with a given virtual address and size.
    //
    // Round the size up to the next higher power of two, because that's
    // the size increment that the buddy allocator uses.
    //

    node_size = round_up_to_power_of_2(size);
    KASSERT(
        node_size >= 4096,
        (
            "%s: round_up_to_power_of_2(%lu) "
            " returned %lu, expected 4096\n",
            __FUNCTION__,
            size,
            node_size
        )
    );

    // the node size gives us the level
    level = kmem_1gig_find_level(node_size);

    // the level and address give us the node index
    node = kmem_1gig_va_to_node(p, level, addr);
    KASSERT(
        (node >= 0) && (node < kmem_1gig_num_nodes_at_level(level)),
        (
            "%s: got invalid node number (p->va=0x%lx, level=%d, addr=0x%lx)",
            __FUNCTION__,
            p->va,
            level,
            addr
        )
    );

    if (!kmem_1gig_node_in_use(p, level, node)) {
        // this should never happen
        return;
    }

    // mark this node as free
    kmem_1gig_mark_node_free(p, level, node);

    // mark all the children as free
    {
        int first_child_node = node;
        int child_level;
        for (
            child_level = level + 1;
            child_level < KMEM_1GIG_NUM_LEVELS;
            child_level ++
        ) {
            int num_child_nodes = 1 << (child_level - level);
            first_child_node <<= 1;

	    kmem_1gig_mark_nodes_free(p, child_level,
		first_child_node, first_child_node + num_child_nodes -1);
        }
    }

    // This node is free now, if the sibling is also free then mark the parent
    // free.
    while (level > 0) {
        int sibling_node = kmem_1gig_sibling_node(node);
        if (kmem_1gig_node_in_use(p, level, sibling_node)) {
            // sibling is in use, so this is where we stop
            break;
        }

        level --;
        node >>= 1;
        KASSERT(
            kmem_1gig_node_in_use(p, level, node),
            ("%s: ancestor node not in use!", __FUNCTION__)
        );
        kmem_1gig_mark_node_free(p, level, node);
    }
}


void
kmem_free_1gig(struct vmem *vmem, vm_offset_t addr, vm_size_t size)
{
    struct kmem_1gig_page *p;

    if (vmem != kmem_arena) {
        // printf("1gig alloc: not kmem_arena, punting to old free (va=0x%016lx, size=%lu)\n", addr, size);
        kmem_free_real(vmem, addr, size);
        return;
    }

    LOCK();

    // find the 1 gig page that has this va
    TAILQ_FOREACH(p, &kmem_1gig_pages, list) {
        if ((addr & ~((1024UL*1024*1024)-1)) == p->va) {
            // free this memory back to this page
            kmem_free_1gig_to_page(p, addr, size);
            kmem_1gig_free_bookkeeping(p, size);
            kmem_1gig_sort_page_list(p);
            UNLOCK();
            return;
        }
    }

    UNLOCK();

    // couldnt find a page for that VA, must be from the regular allocator
    kmem_free_real(vmem, addr, size);
}


static int
kmem_1gig_count_free_chunks(struct kmem_1gig_page *p, vm_size_t size)
{
    int level;
    int num_nodes;
    int num_free_chunks;
    int node;

    KASSERT_MTX_OWNED();

    level = kmem_1gig_find_level(size);
    num_nodes = kmem_1gig_num_nodes_at_level(level);
    num_free_chunks = 0;

    for (node = 0; node < num_nodes; node ++) {
        if (!kmem_1gig_node_in_use(p, level, node)) {
            num_free_chunks ++;
        }
    }

    return num_free_chunks;
}


//
// sysctls for 1 gig buddy allocator
//

// tunable to enable the 1 gig buddy allocator
int vm_1gig_buddy_enable = 1;
SYSCTL_INT(_vm, OID_AUTO, vm_1gig_buddy_enable, CTLFLAG_RDTUN,
	&vm_1gig_buddy_enable, 0, "enable the 1 gig buddy allocator");
TUNABLE_INT("vm.vm_1gig_buddy_enable", &vm_1gig_buddy_enable);

// Set this one to a positive value to allocate that much memory in the first
// available allocation slot.  Set it to a negative value to free the
// allocation slot.
static int sysctl_1gig_buddy_alloc(SYSCTL_HANDLER_ARGS);
SYSCTL_PROC(
    _debug,
    OID_AUTO,
    kmem_1gig_buddy_alloc,
    CTLTYPE_LONG | CTLFLAG_WR,
    NULL,
    0,
    sysctl_1gig_buddy_alloc,
    "L",
    "Allocate or free memory from the 1 gig buddy allocator."
);

// read this to see the allocation slots
static int sysctl_1gig_buddy_alloc_state(SYSCTL_HANDLER_ARGS);
SYSCTL_PROC(
    _debug,
    OID_AUTO,
    kmem_1gig_buddy_alloc_state,
    CTLTYPE_STRING | CTLFLAG_RD,
    NULL,
    0,
    sysctl_1gig_buddy_alloc_state,
    "A",
    "Show allocation slots for 1 gig buddy tester"
);


static struct {
    vm_offset_t va;
    vm_size_t size;
} kmem_1gig_allocations[1000] = {
    { -1, 0 },
    { 0, 0 },
    { 0, 0 },
    { 0, 0 },
    { 0, 0 },
    { 0, 0 },
    { 0, 0 },
    { 0, 0 },
    { 0, 0 },
    { 0, 0 }
};


static int sysctl_1gig_buddy_alloc(SYSCTL_HANDLER_ARGS) {
    long alloc;
    int error;
    int num_alloc_slots = sizeof(kmem_1gig_allocations) /
        sizeof(kmem_1gig_allocations[0]);
    int i;

    alloc = -99999;
    error = sysctl_handle_long(oidp, &alloc, 0, req);
    if (error) {
        return error;
    }
    if (alloc == -99999) {
        return 0;
    }

    if (alloc < 0) {
        alloc *= -1;
        if (alloc < num_alloc_slots) {
            kmem_free_1gig(
                kmem_arena,
                kmem_1gig_allocations[alloc].va,
                kmem_1gig_allocations[alloc].size
            );
            kmem_1gig_allocations[alloc].va = 0;
            kmem_1gig_allocations[alloc].size = 0;
        }
        return 0;
    }

    for (i = 0; i < num_alloc_slots; i ++) {
        if (kmem_1gig_allocations[i].va == 0) {
            kmem_1gig_allocations[i].va = kmem_malloc_1gig(kmem_arena, alloc, 0);
            if (kmem_1gig_allocations[i].va != 0) {
                kmem_1gig_allocations[i].size = alloc;
            }
            break;
        }
    }
    return 0;
}


static int sysctl_1gig_buddy_alloc_state(SYSCTL_HANDLER_ARGS) {
    struct sbuf *sb;
    int error;
    int num_alloc_slots = sizeof(kmem_1gig_allocations) /
        sizeof(kmem_1gig_allocations[0]);
    int i;
    struct kmem_1gig_page *p;

    sb = sbuf_new(NULL, NULL, 20 * 1024, SBUF_FIXEDLEN);
    if (sb == NULL) {
        printf("out of memory in 1gig_buddy_alloc_state sysctl\n");
        return ENOMEM;
    }

    sbuf_printf(sb, "1 gig buddy allocator tester allocation slots:\n");
    for (i = 0; i < num_alloc_slots; i ++) {
        if (kmem_1gig_allocations[i].va == 0) {
            continue;
        }
        sbuf_printf(
            sb,
            "    %3d: %ld bytes at va 0x%016lx\n",
            i,
            kmem_1gig_allocations[i].size,
            kmem_1gig_allocations[i].va
        );
    }

    sbuf_printf(sb, "1 gig buddy allocator pages:\n");
    LOCK();
    TAILQ_FOREACH(p, &kmem_1gig_pages, list) {
        vm_size_t size;

        sbuf_printf(sb, "    page at va 0x%016lx:\n", p->va);

        sbuf_printf(
            sb,
            "        space free: %lu (%lu kB, %lu MB)\n",
            p->bytes_free,
            (p->bytes_free/1024),
            (p->bytes_free/(1024*1024))
        );

        sbuf_printf(
            sb,
            "        space allocated: %lu (%lu kB, %lu MB)\n",
            p->bytes_allocated,
            (p->bytes_allocated/1024),
            (p->bytes_allocated/(1024*1024))
        );

        sbuf_printf(
            sb,
            "        space handed out: %lu (%lu kB, %lu MB)\n",
            p->bytes_handed_out,
            (p->bytes_handed_out/1024),
            (p->bytes_handed_out/(1024*1024))
        );

        for (size = 1024*1024*1024; size >= PAGE_SIZE; size /= 2) {
            sbuf_printf(
                sb,
                "        %10ld-byte free chunks: %d\n",
                size,
                kmem_1gig_count_free_chunks(p, size)
            );
        }
    }
    UNLOCK();

    sbuf_finish(sb);
    error = SYSCTL_OUT(req, sbuf_data(sb), sbuf_len(sb) + 1);
    sbuf_delete(sb);
    return error;
}

