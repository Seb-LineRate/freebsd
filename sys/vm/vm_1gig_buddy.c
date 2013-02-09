
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
// regions backed by a 1 gig page.
//
// If a node has no children (both left_child and right_child are NULL), it
// means the whole node is free.
//
// If a node has one or two children, it means that the memory tracked by
// the node is partially free and partially in use.  In this case, a
// missing child (a child pointer that is NULL), indicates that the missing
// child is fully allocated.  A child pointer that is not NULL points to a
// node that is not fully allocated, ie it is at least partially free.
//

struct kmem_1gig_free_node {
    vm_offset_t va;
    size_t size;
    struct kmem_1gig_free_node *parent;
    struct kmem_1gig_free_node *left_child;
    struct kmem_1gig_free_node *right_child;
};


//
// This struct tracks a 1 gig page that the kmem low-level allocator is
// currently using to satisfy allocation requests made by the rest of the
// kernel (including uma slabs).
//
struct kmem_1gig_page {
    TAILQ_ENTRY(kmem_1gig_page) list;   // list of 1 gig pages used by the allocator
    struct kmem_1gig_free_node *root;         // root of the free-node tree
    vm_offset_t va;
    uint64_t bytes_free;
    uint64_t bytes_allocated;    // how much did our users ask for?
    uint64_t bytes_handed_out;   // how much did we actually give our users?  (it'll probably be more than bytes_allocated because we round up to a power of 2)
};



TAILQ_HEAD(kmem_1gig_page_list, kmem_1gig_page) kmem_1gig_pages = TAILQ_HEAD_INITIALIZER(kmem_1gig_pages);

static struct mtx kmem_1gig_mutex;
MTX_SYSINIT(kmem_1gig_mutex, &kmem_1gig_mutex, "kmem 1gig mutex", MTX_DEF);


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


static inline void kmem_1gig_alloc_bookkeeping(struct kmem_1gig_page *p, vm_size_t size) {
    uint64_t node_size;

    KASSERT(p != NULL, ("kmem_1gig_alloc_bookkeeping: got NULL page!\n"));

    node_size = round_up_to_power_of_2(size);
    p->bytes_free -= node_size;
    p->bytes_allocated += size;
    p->bytes_handed_out += node_size;

#if 0
    printf(
        "1gig buddy allocator: allocated %ld bytes (%ld bytes handed out) from 1gig page at 0x%016lx, %lu bytes left (%lu kB, %lu MB)\n",
        size,
        node_size,
        p->va,
        p->bytes_free,
        (p->bytes_free / 1024),
        (p->bytes_free / (1024*1024))
    );
#endif
}


static inline void kmem_1gig_free_bookkeeping(struct kmem_1gig_page *p, vm_size_t size) {
    uint64_t node_size;

    KASSERT(p != NULL, ("kmem_1gig_free_bookkeeping: got NULL page!\n"));

    node_size = round_up_to_power_of_2(size);
    p->bytes_free += node_size;
    p->bytes_allocated -= size;
    p->bytes_handed_out -= node_size;

#if 0
    printf(
        "1gig buddy allocator: freed %ld bytes (%ld bytes returned) to 1gig page at 0x%016lx, now has %lu bytes free (%lu kB, %lu MB)\n",
        size,
        node_size,
        p->va,
        p->bytes_free,
        (p->bytes_free / 1024),
        (p->bytes_free / (1024*1024))
    );
#endif
}


static void kmem_1gig_sort_page_list(struct kmem_1gig_page *p) {
    do {
        struct kmem_1gig_page *prev, *next;

        prev = TAILQ_PREV(p, kmem_1gig_page_list, list);
        next = TAILQ_NEXT(p, list);

#if 0
        {
            struct kmem_1gig_page *tmp;
            printf("starting sorting pages:\n");
            TAILQ_FOREACH(tmp, &kmem_1gig_pages, list) {
                if (tmp == p) {
                    printf("{ *** va=0x%016lx, bytes_free=%ld *** }  ", tmp->va, tmp->bytes_free);
                } else {
                    printf("{ va=0x%016lx, bytes_free=%ld }  ", tmp->va, tmp->bytes_free);
                }
            }
            printf("\n");
        }
#endif

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

#if 0
    // debuggingly print out the list of 1 gig pages
    // printf("finished sorting pages:\n");
    TAILQ_FOREACH(p, &kmem_1gig_pages, list) {
        struct kmem_1gig_page *tmp;
        if (tmp == p) {
            printf("{ *** va=0x%016lx, bytes_free=%ld *** }  ", tmp->va, tmp->bytes_free);
        } else {
            printf("{ va=0x%016lx, bytes_free=%ld }  ", tmp->va, tmp->bytes_free);
        }
    }
    printf("\n");
#endif
}


//
// Walk a free node tree and return the node that should be used to satisfy
// the allocation, or NULL if no appropriate node was found.
//
static struct kmem_1gig_free_node *
kmem_1gig_find_free_node(struct kmem_1gig_free_node *root, vm_size_t size)
{
    struct kmem_1gig_free_node *node_from_left_child;
    struct kmem_1gig_free_node *node_from_right_child;

    KASSERT(cold || mtx_owned(&kmem_1gig_mutex), ("%s: kmem 1gig mutex not owned!", __FUNCTION__));

    if (root == NULL) {
        // this entire tree is in use!
        return NULL;
    }

    if (root->size < size) {
        // this entire tree, even if it was all free, is too small
        return NULL;
    }

    if ((root->left_child == NULL) && (root->right_child == NULL)) {
        // there are no nodes below this one, so this is the one to use!
        return root;
    }

    if (root->size/2 < size) {
        // this node is not all free (it's not a leaf node),
        // and each of the children is too small for this request
        return NULL;
    }

    node_from_left_child = kmem_1gig_find_free_node(root->left_child, size);
    node_from_right_child = kmem_1gig_find_free_node(root->right_child, size);

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


// remove the specified node from the specified tree
static void
kmem_1gig_remove_node(struct kmem_1gig_page *p, struct kmem_1gig_free_node *n)
{
    struct kmem_1gig_free_node *parent;

    KASSERT(cold || mtx_owned(&kmem_1gig_mutex), ("%s: kmem 1gig mutex not owned!", __FUNCTION__));

    KASSERT(p != NULL, ("kmem_1gig_remove_node: got NULL 1gig page!\n"));
    KASSERT(n != NULL, ("kmem_1gig_remove_node: got NULL node!\n"));
    KASSERT(n->left_child == NULL, ("%s: got a node with a left child!\n", __FUNCTION__));
    KASSERT(n->right_child == NULL, ("%s: got a node with a right child!\n", __FUNCTION__));

    while ((n->left_child == NULL) && (n->right_child == NULL)) {
        parent = n->parent;

        if (parent == NULL) {
            // the node is the root of the tree
            KASSERT(n == p->root, ("%s: non-root node has NULL parent!\n", __FUNCTION__));
            kmem_free_real(kmem_map, (vm_offset_t)n, sizeof(struct kmem_1gig_free_node));
            p->root = NULL;
            return;
        }

        if (n == parent->left_child) {
            parent->left_child = NULL;
        } else {
            KASSERT(n == parent->right_child, ("%s: node is not its parent's child!\n", __FUNCTION__));
            parent->right_child = NULL;
        }

        kmem_free_real(kmem_map, (vm_offset_t)n, sizeof(struct kmem_1gig_free_node));
        n = parent;
    }
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
    struct kmem_1gig_free_node *n;
    vm_offset_t va;

    KASSERT(cold || mtx_owned(&kmem_1gig_mutex), ("%s: kmem 1gig mutex not owned!", __FUNCTION__));

    if (size > p->bytes_free) return 0;

    // find the best leaf node to use for this allocation
    n = kmem_1gig_find_free_node(p->root, size);
    if (n == NULL) {
        // there is no free chunk in this 1 gig page suitable for this allocation
        return 0;
    }

    KASSERT(n->left_child == NULL, ("%s: kmem_1gig_find_free_node() returned a node with children!", __FUNCTION__));
    KASSERT(n->right_child == NULL, ("%s: kmem_1gig_find_free_node() returned a node with children!", __FUNCTION__));

    // n is the node we should use to satisfy the allocation

    // split the node, if possible
    while ((n->size > PAGE_SIZE) && (n->size/2 >= size)) {
        n->left_child = (void*)kmem_malloc_real(kmem_map, sizeof(struct kmem_1gig_free_node), M_WAITOK);
        if (n->left_child == NULL) {
            printf("kmem_1gig_find_free: out of memory while splitting node\n");
            // oh well, let's just use this node I guess, even though it's too big
            break;
        }

        n->right_child = (void*)kmem_malloc_real(kmem_map, sizeof(struct kmem_1gig_free_node), M_WAITOK);
        if (n->right_child == NULL) {
            kmem_free_real(kmem_map, (vm_offset_t)n->left_child, sizeof(struct kmem_1gig_free_node));
            // oh well, let's just use this node I guess, even though it's too big
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

    // remove the node from the tree, and any of its ancestors that
    // are free after removing this node
    kmem_1gig_remove_node(p, n);

    return va;
}


static struct kmem_1gig_page *
kmem_1gig_add_page(void)
{
    struct kmem_1gig_page *p;
    struct kmem_1gig_free_node *n;
    vm_offset_t va;
    long one_gig = 1024 * 1024 * 1024;

    KASSERT(cold || mtx_owned(&kmem_1gig_mutex), ("%s: kmem 1gig mutex not owned!", __FUNCTION__));

    va = kmem_malloc_1gig_page(kmem_map, M_WAITOK);
    if (va == 0) {
        printf("kmem_1gig_add_page: failed to allocate another gig\n");
        return NULL;
    }

    n = (void*)kmem_malloc_real(kmem_map, sizeof(struct kmem_1gig_free_node), M_WAITOK);
    if (n == NULL) {
        kmem_free_real(kmem_map, va, one_gig);
        return NULL;
    }

    p = (void*)kmem_malloc_real(kmem_map, sizeof(struct kmem_1gig_page), M_WAITOK);
    if (p == NULL) {
        kmem_free_real(kmem_map, (vm_offset_t)n, sizeof(struct kmem_1gig_free_node));
        kmem_free_real(kmem_map, va, one_gig);
        return NULL;
    }

    n->va = va;
    n->size = 1024*1024*1024;
    n->parent = NULL;
    n->left_child = NULL;
    n->right_child = NULL;

    p->root = n;
    p->va = va;
    p->bytes_free = 1024UL * 1024UL * 1024UL;
    p->bytes_allocated = 0;
    p->bytes_handed_out = 0;

    TAILQ_INSERT_TAIL(&kmem_1gig_pages, p, list);

    return p;
}


vm_offset_t
kmem_malloc_1gig(vm_map_t map, vm_size_t size, int flags)
{
    vm_offset_t va;
    struct kmem_1gig_page *p;

    if (map != kmem_map) {
        // printf("1gig alloc: not kmem_map, punting to old malloc (size=%lu)\n", size);
        return kmem_malloc_real(map, size, flags);
    }

    if (size > 1024*1024*1024) {
        // punt
        printf("kmem_malloc_1gig: request is too big, punting to the real allocator\n");
        return kmem_malloc_real(map, size, flags);
    }

    if (!cold) {
        mtx_lock(&kmem_1gig_mutex);
    }

    // do we have a 1 gig page with a free chunk big enough for this allocation request?
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
    printf("kmem_malloc_1gig: everything failed, punting to the real allocator\n");
    return kmem_malloc_real(map, size, flags);
}


//
// This function gets called when node n just became entirely free.
// It should check with its parent if its sibling is also fully free, and
// if so, merge with its sibling into its parent (and recurse).
//

static void
kmem_1gig_coalesce(struct kmem_1gig_page *p, struct kmem_1gig_free_node *n)
{
    struct kmem_1gig_free_node *parent;
    struct kmem_1gig_free_node *sibling;

    KASSERT(cold || mtx_owned(&kmem_1gig_mutex), ("%s: kmem 1gig mutex not owned!", __FUNCTION__));

    KASSERT(p != NULL, ("kmem_1gig_coalesce: got NULL 1gig page!\n"));
    KASSERT(n != NULL, ("kmem_1gig_coalesce: got NULL node!\n"));
    KASSERT(n->left_child == NULL, ("kmem_1gig_coalesce: got a node with a non-NULL left_child!\n"));
    KASSERT(n->right_child == NULL, ("kmem_1gig_coalesce: got a node with a non-NULL right_child!\n"));

    parent = n->parent;
    if (parent == NULL) {
        // we're at the top of the tree
        KASSERT(n->size == 1024*1024*1024, ("kmem_1gig_coalesce: node lacks parent, but size is %lu (not 1 gig)\n", n->size));
        return;
    }

    if (n == parent->left_child) {
        sibling = parent->right_child;
    } else if (n == parent->right_child) {
        sibling = parent->left_child;
    } else {
        panic("kmem_1gig_coalesce: node at %p has parent which doesnt have this node as a child\n", n);
    }

    if (sibling == NULL) {
        // sibling is completely allocated, we can not coalesce
        return;
    }

    if ((sibling->left_child != NULL) || (sibling->right_child != NULL)) {
        // sibling is partially allocated, we can not coalesce
        return;
    }

    // if we get here, then the passed-in node's sibling is free, and we can coalesce

    kmem_free_real(kmem_map, (vm_offset_t)n, sizeof(struct kmem_1gig_free_node));
    kmem_free_real(kmem_map, (vm_offset_t)sibling, sizeof(struct kmem_1gig_free_node));

    parent->left_child = NULL;
    parent->right_child = NULL;

    kmem_1gig_coalesce(p, parent);
}


// we might have to add interior nodes to reach down to the leaf node that will represent this va/size pair
// we might have to coalesce this chunk with its buddy, and recursively up the tree
static void
kmem_free_1gig_to_page(struct kmem_1gig_page *p, vm_offset_t addr, vm_size_t size)
{
    vm_size_t node_size;  // size of the node we're freeing this chunk to
    struct kmem_1gig_free_node *n;

    KASSERT(cold || mtx_owned(&kmem_1gig_mutex), ("%s: kmem 1gig mutex not owned!", __FUNCTION__));

    if (p->root == NULL) {
        p->root = (void*)kmem_malloc_real(kmem_map, sizeof(struct kmem_1gig_free_node), M_WAITOK);
        if (p->root == NULL) {
            printf("kmem_free_1gig_to_page: out of memory!\n");
            return;
        }
        p->root->va = p->va;
        p->root->size = 1024*1024*1024;
        p->root->parent = NULL;
        p->root->left_child = NULL;
        p->root->right_child = NULL;
    }

    n = p->root;


    //
    // We're freeing a chunk with a given virtual address and size.
    //
    // Round the size up to the next higher power of two, because that's
    // the size increment that the buddy allocator uses.
    //

    node_size = round_up_to_power_of_2(size);
    KASSERT(node_size >= 4096, ("kmem_free_1gig_to_page: round_up_to_power_of_2(%lu) returned %lu, expected 4096\n", size, node_size));

    while (node_size < n->size) {
        // The current node is too big for what we're freeing, go down
        // one level (left or right, depending on virtual address).
        if (addr < (n->va + (n->size / 2))) {
            // the chunk we're freeing is in the left tree of the current node
            if (n->left_child == NULL) {
                // allocate the left child, if needed
                n->left_child = (void*)kmem_malloc_real(kmem_map, sizeof(struct kmem_1gig_free_node), M_WAITOK);
                if (n->left_child == NULL) {
                    printf("kmem_free_1gig_to_page: out of memory!\n");
                    return;
                }
                n->left_child->size = n->size / 2;
                n->left_child->va = n->va;
                n->left_child->parent = n;
                n->left_child->left_child = NULL;
                n->left_child->right_child = NULL;
            }
            n = n->left_child;

        } else {
            // the chunk we're freeing is in the right tree of the current node
            if (n->right_child == NULL) {
                n->right_child = (void*)kmem_malloc_real(kmem_map, sizeof(struct kmem_1gig_free_node), M_WAITOK);
                if (n->right_child == NULL) {
                    printf("kmem_free_1gig_to_page: out of memory!\n");
                    return;
                }
                n->right_child->size = n->size / 2;
                n->right_child->va = n->va + n->right_child->size;
                n->right_child->parent = n;
                n->right_child->left_child = NULL;
                n->right_child->right_child = NULL;
            }
            n = n->right_child;
        }
    }

    // If we get here, then the chunk we're freeing belongs on this
    // level, and it better belong exactly to the current node or we're
    // lost in the tree!

    // we found the node where this memory belongs!
    KASSERT(n->va == addr, ("kmem_free_1gig_to_page: found the node, but the va is wrong\n"));
    KASSERT(n->size == node_size, ("kmem_free_1gig_to_page: found the node, but the size is wrong\n"));
    KASSERT(n->left_child == NULL, ("kmem_free_1gig_to_page: found the node, but the left child is not NULL\n"));
    KASSERT(n->right_child == NULL, ("kmem_free_1gig_to_page: found the node, but the right child is not NULL\n"));

    // try to merge this node with its buddy, and recursively up the tree
    kmem_1gig_coalesce(p, n);

    return;
}


void
kmem_free_1gig(vm_map_t map, vm_offset_t addr, vm_size_t size)
{
    struct kmem_1gig_page *p;

    if (map != kmem_map) {
        // printf("1gig alloc: not kmem_map, punting to old free (va=0x%016lx, size=%lu)\n", addr, size);
        kmem_free_real(map, addr, size);
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
    printf("1gig alloc: free punting to old allocator (va=0x%016lx, size=%lu)\n", addr, size);
    kmem_free_real(map, addr, size);
}


static int
kmem_1gig_count_free_chunks(struct kmem_1gig_free_node *n, vm_size_t size)
{
    KASSERT(cold || mtx_owned(&kmem_1gig_mutex), ("%s: kmem 1gig mutex not owned!", __FUNCTION__));

    if (n == NULL) {
        return 0;
    }

    if (n->size < size) {
        return 0;
    }

    if (n->size == size) {
        if (n->left_child || n->right_child) {
            // this node has the right size, but it's not a leaf node so it's not entirely free
            return 0;
        }
        return 1;
    }

    // this node is too big, ask both children
    return kmem_1gig_count_free_chunks(n->left_child, size) + kmem_1gig_count_free_chunks(n->right_child, size);
}


//
// debug sysctls for 1 gig buddy allocator
//

// set this one to a positive value to allocate that much memory in the first available allocation slot
// set it to a negative value to free the allocation slot
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
    int num_alloc_slots = sizeof(kmem_1gig_allocations) / sizeof(kmem_1gig_allocations[0]);
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
            kmem_free_1gig(kmem_map, kmem_1gig_allocations[alloc].va, kmem_1gig_allocations[alloc].size);
            kmem_1gig_allocations[alloc].va = 0;
            kmem_1gig_allocations[alloc].size = 0;
        }
        return 0;
    }

    for (i = 0; i < num_alloc_slots; i ++) {
        if (kmem_1gig_allocations[i].va == 0) {
            kmem_1gig_allocations[i].va = kmem_malloc_1gig(kmem_map, alloc, 0);
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
    int num_alloc_slots = sizeof(kmem_1gig_allocations) / sizeof(kmem_1gig_allocations[0]);
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
            sbuf_printf(sb, "        %10ld-byte free chunks: %d\n", size, kmem_1gig_count_free_chunks(p->root, size));
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

