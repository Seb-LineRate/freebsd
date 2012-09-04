
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
// If a node has no children, it means the whole node is free.
//
// If a node has any children, it means that the memory governed by the
// node is partially in use, ie not wholly free.
//
// If a node is missing (ie if the parent node has a NULL pointer where
// this node would be), then the memory governed by the missing node is allocated.
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
    LIST_ENTRY(kmem_1gig_page) list;   // list of 1 gig pages used by the allocator
    struct kmem_1gig_free_node *root;         // root of the free-node tree
    vm_offset_t va;
};



LIST_HEAD(, kmem_1gig_page) kmem_1gig_pages = LIST_HEAD_INITIALIZER();


//
// Walk a free node tree and return the node that should be used to satisfy
// the allocation, or NULL if no appropriate node was found.
//
static struct kmem_1gig_free_node *
kmem_1gig_find_free_node(struct kmem_1gig_free_node *root, vm_size_t size)
{
    struct kmem_1gig_free_node *node_from_left_child;
    struct kmem_1gig_free_node *node_from_right_child;

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


// remove the specified node from the specified tree (but don't free it)
static void
kmem_1gig_remove_node(struct kmem_1gig_page *p, struct kmem_1gig_free_node *n)
{
    KASSERT(p != NULL, ("kmem_1gig_remove_node: got NULL 1gig page!\n"));
    KASSERT(n != NULL, ("kmem_1gig_remove_node: got NULL node!\n"));

    while ((n->left_child == NULL) && (n->right_child == NULL)) {
        if (n->parent == NULL) {
            // the node is the root of the tree
            p->root = NULL;
            return;
        }

        if (n == n->parent->left_child) {
            n->parent->left_child = NULL;
        } else {
            n->parent->right_child = NULL;
        }

        n = n->parent;
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

    printf("kmem_1gig_find_free: looking for %lu free bytes on 1 gig page at %p\n", size, p);

    // find the best leaf node to use for this allocation
    n = kmem_1gig_find_free_node(p->root, size);
    if (n == NULL) {
        // there is no free chunk in this 1 gig page suitable for this allocation
        printf("kmem_1gig_find_free: no sufficiently large free chunks\n");
        return 0;
    }

    printf("kmem_1gig_find_free: found a sufficiently large free chunk!\n");
    printf("    n->va = 0x%016lx\n", n->va);
    printf("    n->size = %lu\n", n->size);
    printf("    n->parent = %p\n", n->parent);
    printf("    n->left_child = %p\n", n->left_child);
    printf("    n->right_child = %p\n", n->right_child);

    // n is the node we should use to satisfy the allocation

    // split the node, if possible
    while ((n->size > PAGE_SIZE) && (n->size/2 >= size)) {
        printf("kmem_1gig_find_free: splitting node...\n");
        printf("    original node size is %ld\n", n->size);

        n->left_child = (void*)kmem_malloc_real(kmem_map, sizeof(struct kmem_1gig_free_node), M_WAITOK);
        if (n->left_child == NULL) {
            printf("kmem_1gig_find_free: out of memory while splitting node\n");
            // oh well, let's just use this node I guess, even though it's too big
            break;
        }

        n->right_child = (void*)kmem_malloc_real(kmem_map, sizeof(struct kmem_1gig_free_node), M_WAITOK);
        if (n->right_child == NULL) {
            kmem_free(kmem_map, (vm_offset_t)n->left_child, sizeof(struct kmem_1gig_free_node));
            printf("kmem_1gig_find_free: out of memory while splitting node\n");
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
        printf("    new node size is %ld\n", n->size);
    }

    // remove the node from the tree if possible
    kmem_1gig_remove_node(p, n);

    va = n->va;
    kmem_free(kmem_map, (vm_offset_t)n, sizeof(struct kmem_1gig_free_node));
    return va;
}


static struct kmem_1gig_page *
kmem_1gig_add_page(void)
{
    struct kmem_1gig_page *p;
    struct kmem_1gig_free_node *n;
    vm_offset_t va;
    long one_gig = 1024 * 1024 * 1024;

    printf("kmem_1gig_add_page: trying to add another gig\n");

    va = kmem_malloc_1gig_page(kmem_map, M_WAITOK);
    if (va == 0) {
        printf("kmem_1gig_add_page: failed to allocate another gig\n");
        return NULL;
    }

    n = (void*)kmem_malloc_real(kmem_map, sizeof(struct kmem_1gig_free_node), M_WAITOK);
    if (n == NULL) {
        printf("kmem_1gig_add_page: failed to allocate root free node\n");
        kmem_free(kmem_map, va, one_gig);
        return NULL;
    }

    p = (void*)kmem_malloc_real(kmem_map, sizeof(struct kmem_1gig_page), M_WAITOK);
    if (p == NULL) {
        printf("kmem_1gig_add_page: failed to allocate metadata\n");
        kmem_free(kmem_map, (vm_offset_t)n, sizeof(struct kmem_1gig_free_node));
        kmem_free(kmem_map, va, one_gig);
        return NULL;
    }

    n->va = va;
    n->size = 1024*1024*1024;
    n->parent = NULL;
    n->left_child = NULL;
    n->right_child = NULL;

    p->root = n;
    p->va = va;

    LIST_INSERT_HEAD(&kmem_1gig_pages, p, list);

    return p;
}


vm_offset_t
kmem_malloc_1gig(vm_map_t map, vm_size_t size, int flags)
{
    vm_offset_t va;
    struct kmem_1gig_page *p;

    printf("kmem_malloc_1gig: got a request for %lu bytes\n", size);

    if (size > 1024*1024*1024) {
        // punt
        printf("kmem_malloc_1gig: request is too big, punting to the real allocator\n");
        return kmem_malloc_real(map, size, flags);
    }

    // do we have a 1 gig page with a free chunk big enough for this allocation request?
    LIST_FOREACH(p, &kmem_1gig_pages, list) {
        va = kmem_1gig_find_free(p, size);
        if (va != 0) {
            // found one, return it quick!
            printf("kmem_malloc_1gig: request is satisfied, returning VA 0x%016lx\n", va);
            return va;
        }
    }

    // didn't find a page with free space for this allocation
    printf("kmem_malloc_1gig: request could not be satisified from the current list of 1 gig pages, allocating a new one from the real allocator\n");
    p = kmem_1gig_add_page();
    if (p != NULL) {
        // we got some more memory!
        va = kmem_1gig_find_free(p, size);
        if (va != 0) {
            // found one, return it quick!
            printf("kmem_malloc_1gig: request is satisfied from the new page, returning VA 0x%016lx\n", va);
            return va;
        }
    }


    // fall back to the real allocator
    printf("kmem_malloc_1gig: everything failed, punting to the real allocator\n");
    return kmem_malloc_real(map, size, flags);
}


// we might have to add interior nodes to reach down to the leaf node that will represent this va/size pair
// we might have to coalesce this chunk with its buddy, and recursively up the tree
static void
kmem_free_1gig_to_page(struct kmem_1gig_page *p, vm_offset_t addr, vm_size_t size)
{
    struct kmem_1gig_free_node *n;

    printf("kmem_free_1gig_to_page: freeing %ld bytes at va 0x%016lx\n", size, addr);

    if (p->root == NULL) {
        p->root = (void*)kmem_malloc(kmem_map, sizeof(struct kmem_1gig_free_node), M_WAITOK);
        if (p->root == NULL) {
            printf("kmem_free_1gig: out of memory!\n");
            return;
        }
        p->root->va = p->va;
        p->root->size = 1024*1024*1024;
        p->root->parent = NULL;
        p->root->left_child = NULL;
        p->root->right_child = NULL;
    }

    n = p->root;

    while (size != n->size) {
        if (addr < n->va + (n->size / 2)) {
            if (n->left_child == NULL) {
                n->left_child = (void*)kmem_malloc(kmem_map, sizeof(struct kmem_1gig_free_node), M_WAITOK);
                if (n->left_child == NULL) {
                    printf("kmem_free_1gig_to_page: out of memory!\n");
                    return;
                }
                n->left_child->va = p->va;
                n->left_child->size = n->size / 2;
                n->left_child->parent = n;
                n->left_child->left_child = NULL;
                n->left_child->right_child = NULL;
            }
            n = n->left_child;
        } else {
            if (n->right_child == NULL) {
                n->right_child = (void*)kmem_malloc(kmem_map, sizeof(struct kmem_1gig_free_node), M_WAITOK);
                if (n->right_child == NULL) {
                    printf("kmem_free_1gig_to_page: out of memory!\n");
                    return;
                }
                n->right_child->va = p->va;
                n->right_child->size = n->size / 2;
                n->right_child->parent = n;
                n->right_child->left_child = NULL;
                n->right_child->right_child = NULL;
            }
            n = n->right_child;
        }
    }

    // we're done!
    KASSERT(n->va == addr, ("kmem_free_1gig_to_page: found the node, but the va is wrong\n"));
    KASSERT(n->size == size, ("kmem_free_1gig_to_page: found the node, but the size is wrong\n"));
    KASSERT(n->left_child == NULL, ("kmem_free_1gig_to_page: found the node, but the left child is not NULL\n"));
    KASSERT(n->right_child == NULL, ("kmem_free_1gig_to_page: found the node, but the right child is not NULL\n"));

    return;
}


void
kmem_free_1gig(vm_map_t map, vm_offset_t addr, vm_size_t size)
{
    struct kmem_1gig_page *p;

    printf("kmem_free_1gig: map=%p, va=0x%016lx, size=%ld\n", map, addr, size);

    // find the 1 gig page that has this va
    LIST_FOREACH(p, &kmem_1gig_pages, list) {
        if ((addr & ~((1024*1024*1024)-1)) == p->va) {
            // free this memory back to this page
            kmem_free_1gig_to_page(p, addr, size);
        }
    }

    printf("kmem_free_1gig: couldnt find a page for va=%lu, must be from the regular allocator\n", addr);
    kmem_free_real(map, addr, size);
}


static int
kmem_1gig_count_free_chunks(struct kmem_1gig_free_node *n, vm_size_t size)
{
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

    return kmem_1gig_count_free_chunks(n->left_child, size) + kmem_1gig_count_free_chunks(n->right_child, size);
}


//
// debug sysctls for 1 gig buddy allocator
//

// set this one to a positive value to allocate that much memory in the first available allocation slot
// set it to a negative value to free the allocation slot
static int sysctl_1gig_buddy_alloc(SYSCTL_HANDLER_ARGS);
SYSCTL_PROC(
    _lros_debug,
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
    _lros_debug,
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
} kmem_1gig_allocations[10] = {
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

    error = sysctl_handle_long(oidp, &alloc, 0, req);
    if (error) {
        return error;
    }

    printf("sysctl_1gig_buddy_alloc got %ld\n", alloc);
    if (alloc < 0) {
        alloc *= -1;
        if (alloc < num_alloc_slots) {
            printf(
                "    freeing allocation %ld (%ld bytes at va 0x%016lx)\n",
                alloc,
                kmem_1gig_allocations[alloc].size,
                kmem_1gig_allocations[alloc].va
            );
            kmem_free_1gig(kmem_map, kmem_1gig_allocations[alloc].va, kmem_1gig_allocations[alloc].size);
            kmem_1gig_allocations[alloc].va = 0;
            kmem_1gig_allocations[alloc].size = 0;
        } else {
            printf("    allocation free request for invalid slot %ld\n", alloc);
        }
        return 0;
    }

    for (i = 0; i < num_alloc_slots; i ++) {
        if (kmem_1gig_allocations[i].va == 0) {
            printf("    allocate %ld bytes into slot %d\n", alloc, i);
            kmem_1gig_allocations[i].va = kmem_malloc_1gig(kmem_map, alloc, 0);
            if (kmem_1gig_allocations[i].va == 0) {
                printf("    allocation failed!\n");
            } else {
                kmem_1gig_allocations[i].size = alloc;
                printf(
                    "    allocation succeeded, va=0x%016lx, size=%ld!\n",
                    kmem_1gig_allocations[i].va,
                    kmem_1gig_allocations[i].size
                );
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

    sb = sbuf_new(NULL, NULL, 2 * 1024, SBUF_FIXEDLEN);
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
    LIST_FOREACH(p, &kmem_1gig_pages, list) {
        vm_size_t size;
        sbuf_printf(sb, "    page at %p:\n", p);
        for (size = 1024*1024*1024; size >= PAGE_SIZE; size /= 2) {
            sbuf_printf(sb, "        %10ld-byte free chunks: %d\n", size, kmem_1gig_count_free_chunks(p->root, size));
        }
    }

    sbuf_finish(sb);
    error = SYSCTL_OUT(req, sbuf_data(sb), sbuf_len(sb) + 1);
    sbuf_delete(sb);
    return error;
}

