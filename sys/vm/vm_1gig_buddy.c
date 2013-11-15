
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
// This struct is a node in a binary tree of power-of-2-sized memory
// regions backed by a 1 gig page.  The binary tree uses these nodes to
// track free and allocated memory chunks.  Children are half the size of
// their parent.  Siblings track adjacent, aligned memory areas.
//
// Allocation:
//
//     When a memory allocation request is made of this allocator, the
//     allocator searches the tree for the smallest usable free chunk
//     (the smallest free chunk that's not too small), splits it until it
//     can't split it any more, marks the final node as allocated (by
//     setting the 'in-use' flag in the node's VA), and returns it.
//
//     Splitting a node consists of allocating two new nodes and hanging
//     them off the current node's child pointers.
//
//     If both a parent's children are marked as allocated (with the
//     in-use flag in the VA), the parent is marked as allocated.
//
// Freeing:
//
//     When memory is freed back to this allocator, the VA of the memory
//     is used to find the node representing the memory chunk.  The node
//     is marked free (by clearing the in-use bit in its VA).
//
//     Free nodes get "collapsed" up the tree.  If two siblings are both
//     free they are removed, their node data structures are freed and
//     the child pointers in their parent are NULLed out, making the
//     parent into a leaf node.  The two free memory areas that the
//     children used to track are coalesced into one and tracked by the
//     parent.  Thus an entirely free gig of memory is tracked by a
//     single node.
//
// Data structure invariants:
//
//     The tree has a node for every allocated chunk, and a node for every
//     free chunk.
//
//     A node has either 0 or 2 children.  In other words, every node
//     (except the root node) has a sibling.
//
//     If a node is marked as in-use (by having the in-use flag set in
//     its VA), and it has children, then the children are also marked as
//     in-use.
//
//     A node never has two free children.  When a user frees a node that
//     has a free sibling, the node and its sibling are both removed from
//     the tree, making the parent node into a leaf-node.  This is called
//     'consolidation'.
//

struct kmem_1gig_node {
    vm_offset_t va;
    size_t size;
    struct kmem_1gig_node *parent;
    struct kmem_1gig_node *left_child;
    struct kmem_1gig_node *right_child;
};

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
    // root of the free-node tree
    struct kmem_1gig_node *root;
    vm_offset_t va;
    uint64_t bytes_free;
    uint64_t bytes_allocated;    // how much did our users ask for?
    // how much did we actually give our users?  (it'll probably be more
    // than bytes_allocated because we round up to a power of 2)
    uint64_t bytes_handed_out;
};


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


//
// Walk a free node tree and return the node that should be used to satisfy
// the allocation, or NULL if no appropriate node was found.
//
static struct kmem_1gig_node *
kmem_1gig_find_free_node(struct kmem_1gig_node *root, vm_size_t size)
{
    struct kmem_1gig_node *node_from_left_child;
    struct kmem_1gig_node *node_from_right_child;

    KASSERT_MTX_OWNED();
    KASSERT(root != NULL, ("%s: NULL root node passed in", __FUNCTION__));

    if (root->size < size) {
        // this entire (sub-)tree, even if it was all free, is too small
        return NULL;
    }

    if (NODE_IS_ALLOCATED(root)) {
        // no free memory at or below this node
        return NULL;
    }

    if (NODE_IS_LEAF(root)) {
        // this is a leaf node, so this is the one to use!
        // the caller will split the node, if appropriate
        return root;
    }

    KASSERT(
        NODE_HAS_BOTH_CHILDREN(root),
        ("%s: passed-in root node has only one child", __FUNCTION__)
    );

    if (root->size/2 < size) {
        // this node is not all free (it's not a leaf node),
        // and the children are too small for this request
        return NULL;
    }

    if ((root->va & KMEM_1GIG_LEFT_IN_USE) == 0) {
        node_from_left_child =
            kmem_1gig_find_free_node(root->left_child, size);
    } else {
        node_from_left_child = NULL;
    }

    if ((root->va & KMEM_1GIG_RIGHT_IN_USE) == 0) {
        node_from_right_child =
            kmem_1gig_find_free_node(root->right_child, size);
    } else {
        node_from_right_child = NULL;
    }

    if (node_from_left_child == NULL) {
        return node_from_right_child;
    }

    if (node_from_right_child == NULL) {
        return node_from_left_child;
    }

    // return the smaller of the two nodes
    if (node_from_left_child->size < node_from_right_child->size) {
        return node_from_left_child;
    }
    return node_from_right_child;
}


//
// See if there's a free chunk of the requested size on this 1 gig page.
//
// We do this by finding the smallest leaf node that's at least 'size' big,
// splitting any extra memory off the end it, and returning the offset of
// the beginning of the chunk.
//
static vm_offset_t
kmem_1gig_find_free(struct kmem_1gig_page *p, vm_size_t size)
{
    struct kmem_1gig_node *n;
    vm_offset_t va;

    KASSERT_MTX_OWNED();

    if (size > p->bytes_free) return 0;

    // find the best free node to use for this allocation
    n = kmem_1gig_find_free_node(p->root, size);
    if (n == NULL) {
        // there is no suitable free chunk in this 1 gig page
        return 0;
    }

    KASSERT(
        NODE_IS_FREE(n),
        (
            "%s: kmem_1gig_find_free_node() returned an in-use node!",
            __FUNCTION__
        )
    );
    KASSERT(
        NODE_IS_LEAF(n),
        (
            "%s: kmem_1gig_find_free_node() returned a non leaf node!",
            __FUNCTION__
        )
    );

    // n is the free leaf-node we should use to satisfy the allocation

    // split the node, if possible
    while ((n->size > PAGE_SIZE) && (n->size/2 >= size)) {
        n->left_child = (void*)kmem_malloc_real(
            kmem_arena,
            sizeof(struct kmem_1gig_node),
            M_NOWAIT
        );
        if (n->left_child == NULL) {
            printf("%s: out of memory while splitting node\n", __FUNCTION__);
            // oh well, let's just use this node even though it's too big
            break;
        }

        n->right_child = (void*)kmem_malloc_real(
            kmem_arena,
            sizeof(struct kmem_1gig_node),
            M_NOWAIT
        );
        if (n->right_child == NULL) {
            kmem_free_real(
                kmem_arena,
                (vm_offset_t)n->left_child,
                sizeof(struct kmem_1gig_node)
            );
            // oh well, let's just use this node even though it's too big
            break;
        }

        n->left_child->size = n->size / 2;
        n->left_child->va = n->va;
        n->left_child->parent = n;
        n->left_child->left_child = NULL;
        n->left_child->right_child = NULL;

        n->right_child->size = n->size / 2;
        n->right_child->va = n->va + n->left_child->size;
        n->right_child->parent = n;
        n->right_child->left_child = NULL;
        n->right_child->right_child = NULL;

        // try to split one of the newly created child nodes
        n = n->left_child;
    }

    // here, n is the node we're going to actually give to the user

    va = n->va;
    n->va |= KMEM_1GIG_IN_USE;

    // propagate the in-use flag up the tree
    while ((n->parent != NULL) && NODE_IS_ALLOCATED(n)) {
        n = n->parent;
        KASSERT(
            NODE_HAS_BOTH_CHILDREN(n),
            ("%s: parent lacks children!", __FUNCTION__)
        );
        if (NODE_IS_ALLOCATED(n->left_child)) {
            n->va |= KMEM_1GIG_LEFT_IN_USE;
        }
        if (NODE_IS_ALLOCATED(n->right_child)) {
            n->va |= KMEM_1GIG_RIGHT_IN_USE;
        }
    }

    return va;
}


static struct kmem_1gig_page *
kmem_1gig_add_page(void)
{
    struct kmem_1gig_page *p;
    struct kmem_1gig_node *n;
    vm_offset_t va;
    long one_gig = 1024 * 1024 * 1024;

    KASSERT_MTX_OWNED();

    va = kmem_malloc_1gig_page(kmem_arena, M_NOWAIT);
    if (va == 0) {
        static int complained_once = 0;
        if (!complained_once) {
            printf("kmem_1gig_add_page: failed to allocate another gig\n");
            complained_once = 1;
        }
        return NULL;
    }

    n = (void*)kmem_malloc_real(
        kmem_arena,
        sizeof(struct kmem_1gig_node),
        M_NOWAIT
    );
    if (n == NULL) {
        kmem_free_real(kmem_arena, va, one_gig);
        return NULL;
    }

    p = (void*)kmem_malloc_real(
        kmem_arena,
        sizeof(struct kmem_1gig_page),
        M_NOWAIT
    );
    if (p == NULL) {
        kmem_free_real(
            kmem_arena,
            (vm_offset_t)n,
            sizeof(struct kmem_1gig_node)
        );
        kmem_free_real(kmem_arena, va, one_gig);
        return NULL;
    }

    n->va = va;
    n->size = 1024*1024*1024;
    n->parent = NULL;
    n->left_child = NULL;
    n->right_child = NULL;

    p->root = n;
    p->va = n->va;
    p->bytes_free = n->size;
    p->bytes_allocated = 0;
    p->bytes_handed_out = 0;

    TAILQ_INSERT_TAIL(&kmem_1gig_pages, p, list);

    return p;
}


vm_offset_t
kmem_malloc_1gig(struct vmem *vmem, vm_size_t size, int flags)
{
    vm_offset_t va;
    struct kmem_1gig_page *p;
    static int complained_once = 0;

    if (vmem != kmem_arena) {
        // printf("%s: not kmem_arena, punting to old malloc (size=%lu)\n", __func__, size);
        return kmem_malloc_real(vmem, size, flags);
    }

    if (size > 1024*1024*1024) {
        // punt
        printf("kmem_malloc_1gig: request too big, using the real allocator\n");
        return kmem_malloc_real(vmem, size, flags);
    }

    if (!cold) {
        mtx_lock(&kmem_1gig_mutex);
    }

    // do we have a 1 gig page with a big enough free chunk?
    TAILQ_FOREACH(p, &kmem_1gig_pages, list) {
        va = kmem_1gig_find_free(p, size);
        if (va != 0) {
            // found one, return it quick!
            kmem_1gig_alloc_bookkeeping(p, size);
            kmem_1gig_sort_page_list(p);
            if (!cold) {
                mtx_unlock(&kmem_1gig_mutex);
            }
            if (flags & M_ZERO) {
                bzero((void*)va, size);
            }
            return va;
        }
    }

    // didn't find a page with free space for this allocation
    p = kmem_1gig_add_page();
    if (p != NULL) {
        // we got a new 1gig page!
        va = kmem_1gig_find_free(p, size);
        if (va != 0) {
            // found one, return it quick!
            kmem_1gig_alloc_bookkeeping(p, size);
            kmem_1gig_sort_page_list(p);
            if (!cold) {
                mtx_unlock(&kmem_1gig_mutex);
            }
            if (flags & M_ZERO) {
                bzero((void*)va, size);
            }
            return va;
        }
    }

    // fall back to the real allocator
    if (!cold) {
        mtx_unlock(&kmem_1gig_mutex);
    }

    if (!complained_once) {
        printf("kmem_malloc_1gig: failed, using the real allocator\n");
        complained_once = 1;
    }

    return kmem_malloc_real(vmem, size, flags);
}


//
// This function gets called when node n just became entirely free.
// It should check with its parent if its sibling is also fully free, and
// if so, merge with its sibling into its parent (and recurse).
//

static void
kmem_1gig_coalesce(struct kmem_1gig_node *n)
{
    KASSERT_MTX_OWNED();

    do {
        struct kmem_1gig_node *parent;
        struct kmem_1gig_node *sibling;

        KASSERT(n != NULL, ("%s: got NULL node!\n", __FUNCTION__));
        KASSERT(NODE_IS_FREE(n), ("%s: node is in use!\n", __FUNCTION__));
        KASSERT(NODE_IS_LEAF(n), ("%s: got a non leaf node!\n", __FUNCTION__));

        parent = n->parent;
        if (parent == NULL) {
            // the current node n is the top of the tree, cannot coalesce
            // further
            KASSERT(
                n->size == 1024*1024*1024,
                (
                    "%s: node lacks parent, but size is %lu (not 1 gig)\n",
                    __FUNCTION__,
                    n->size
                )
            );
            return;
        }
        // since this node is free, the parent can't be *fully* allocated
        KASSERT(
            0 == NODE_IS_ALLOCATED(parent),
            ("%s: parent is marked in-use\n", __FUNCTION__)
        );

        if (n == parent->left_child) {
            sibling = parent->right_child;
        } else if (n == parent->right_child) {
            sibling = parent->left_child;
        } else {
            panic(
                "%s: node at %p has parent which doesnt have this node "
                "as a child\n",
                __FUNCTION__,
                n
            );
        }

        KASSERT(
            sibling != NULL,
            ("%s: sibling of passed-in node is NULL!", __FUNCTION__)
        );

        if (!NODE_IS_LEAF(sibling)) {
            // sibling is not a leaf-node, we can not coalesce
            return;
        }

        if (!NODE_IS_FREE(sibling)) {
            // sibling is at least partially in use, we can not coalesce
            return;
        }

        // the passed-in node's sibling is a free leaf node, we can coalesce

        kmem_free_real(
            kmem_arena,
            (vm_offset_t)n,
            sizeof(struct kmem_1gig_node)
        );
        kmem_free_real(
            kmem_arena,
            (vm_offset_t)sibling,
            sizeof(struct kmem_1gig_node)
        );

        parent->left_child = NULL;
        parent->right_child = NULL;

        n = parent;
    } while (1);
}


static void
kmem_free_1gig_to_page(
    struct kmem_1gig_page *p,
    vm_offset_t addr,
    vm_size_t size
) {
    vm_size_t node_size;  // size of the node we're freeing this chunk to
    struct kmem_1gig_node *n;

    KASSERT_MTX_OWNED();
    KASSERT(
        p->root != NULL,
        ("%s: kmem 1gig page without a root node!", __FUNCTION__)
    );

    n = p->root;

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

    // walk the tree down to the leaf node that tracks this chunk of memory,
    // clearing the 'in-use' bit as we go
    while (!NODE_IS_LEAF(n) && (n->size > node_size)) {
        KASSERT(
            NODE_HAS_BOTH_CHILDREN(n),
            (
                "%s: freeing VA %p led to an internal node %p "
                "with missing child",
                __FUNCTION__,
                (void*)addr,
                (void*)n
            )
        );

        if (addr < ((n->va & ~KMEM_1GIG_IN_USE) + (n->size / 2))) {
            // the chunk we're freeing is in the left tree of the current node
            n->va &= ~KMEM_1GIG_LEFT_IN_USE;
            n = n->left_child;
        } else {
            // the chunk we're freeing is in the right tree of the current node
            n->va &= ~KMEM_1GIG_RIGHT_IN_USE;
            n = n->right_child;
        }
    }

    // n is the node that tracks this chunk of memory!

    KASSERT(
        NODE_IS_ALLOCATED(n),
        (
            "%s: va=%p, size=%luk, found the node { va=%p, size=%luk, l=%d, "
            "r=%d } but it's not marked in-use\n",
            __FUNCTION__,
            (void*)addr,
            size/1024,
            (void*)n->va,
            n->size/1024,
            (n->va & KMEM_1GIG_LEFT_IN_USE) ? 1 : 0,
            (n->va & KMEM_1GIG_RIGHT_IN_USE) ? 1 : 0
        )
    );
    KASSERT(
        NODE_IS_LEAF(n),
        (
            "%s: va=%p, size=%luk, found the node { va=%p, size=%luk, l=%d, "
            "r=%d }, but it's not a leaf\n",
            __FUNCTION__,
            (void*)addr,
            size/1024,
            (void*)n->va,
            n->size/1024,
            (n->va & KMEM_1GIG_LEFT_IN_USE) ? 1 : 0,
            (n->va & KMEM_1GIG_RIGHT_IN_USE) ? 1 : 0
        )
    );
    KASSERT(
        n->va == (addr | KMEM_1GIG_IN_USE),
        (
            "%s: va=%p, size=%luk, found the node { va=%p, size=%luk, l=%d, "
            "r=%d }, but the VA is wrong\n",
            __FUNCTION__,
            (void*)addr,
            size/1024,
            (void*)n->va,
            n->size/1024,
            (n->va & KMEM_1GIG_LEFT_IN_USE) ? 1 : 0,
            (n->va & KMEM_1GIG_RIGHT_IN_USE) ? 1 : 0
        )
    );
    KASSERT(
        n->size >= node_size,
        (
            "%s: va=%p, size=%luk, found the node { va=%p, size=%luk, l=%d, "
            "r=%d }, but the size is too small\n",
            __FUNCTION__,
            (void*)addr,
            size/1024,
            (void*)n->va,
            n->size/1024,
            (n->va & KMEM_1GIG_LEFT_IN_USE) ? 1 : 0,
            (n->va & KMEM_1GIG_RIGHT_IN_USE) ? 1 : 0
        )
    );

    // mark the node as not in use
    n->va &= ~KMEM_1GIG_IN_USE;

    // try to merge this node with its buddy, and on up the tree
    kmem_1gig_coalesce(n);
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

    if (!cold) {
        mtx_lock(&kmem_1gig_mutex);
    }

    // find the 1 gig page that has this va
    TAILQ_FOREACH(p, &kmem_1gig_pages, list) {
        if ((addr & ~((1024UL*1024*1024)-1)) == p->va) {
            // free this memory back to this page
            kmem_free_1gig_to_page(p, addr, size);
            kmem_1gig_free_bookkeeping(p, size);
            kmem_1gig_sort_page_list(p);
            if (!cold) {
                mtx_unlock(&kmem_1gig_mutex);
            }
            return;
        }
    }

    if (!cold) {
        mtx_unlock(&kmem_1gig_mutex);
    }

    // couldnt find a page for that VA, must be from the regular allocator
    kmem_free_real(vmem, addr, size);
}


static int
kmem_1gig_count_free_chunks(struct kmem_1gig_node *n, vm_size_t size)
{
    KASSERT_MTX_OWNED();

    if (n == NULL) {
        return 0;
    }

    if (n->size < size) {
        return 0;
    }

    // no free memory at or below this node
    if (NODE_IS_ALLOCATED(n)) {
        return 0;
    }

    if (n->size == size) {
        if (!NODE_IS_FREE(n)) {
            // this node has the right size, but it's not free
            return 0;
        }
        return 1;
    }

    // this node is too big, ask both children
    return kmem_1gig_count_free_chunks(n->left_child, size) +
        kmem_1gig_count_free_chunks(n->right_child, size);
}


//
// debug sysctls for 1 gig buddy allocator
//

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
    if (!cold) {
        mtx_lock(&kmem_1gig_mutex);
    }
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
                kmem_1gig_count_free_chunks(p->root, size)
            );
        }
    }
    if (!cold) {
        mtx_unlock(&kmem_1gig_mutex);
    }

    sbuf_finish(sb);
    error = SYSCTL_OUT(req, sbuf_data(sb), sbuf_len(sb) + 1);
    sbuf_delete(sb);
    return error;
}

