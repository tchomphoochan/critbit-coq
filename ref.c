#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

// Q: why do we do tagging on the pointer instead of the node?
// A: because morally, the "pointer" is really what you think about as the
// "object" in functional programming
// A: an external node should be small

typedef struct {
  enum { internal, external } type;
  void *ptr;
} nodeptr_t;
// this will be replaced with a single void* where the top bit stores type info
// external -> K (null-terminated array of chars)

typedef struct {
  nodeptr_t child[2];
  // byte+otherbits is index_t
  uint32_t byte;
  uint8_t otherbits;
} internal_node_t;

typedef struct {
  nodeptr_t root;
} tree_t;

// representation stuff
// can be optimized using bit tricks e.g. use the top bit to denote childtype_t

bool is_internal_ptr(nodeptr_t p) { return p.type == internal; }
internal_node_t *get_internal_ptr(nodeptr_t p) {
  assert(is_internal_ptr(p));
  return (internal_node_t *)p.ptr;
}
// TODO: external node should be a key-value pair!!
const char *get_external_ptr(nodeptr_t p) {
  assert(!is_internal_ptr(p));
  return (const char *)p.ptr;
}
// an external "node" is actually just a pointer to a string
nodeptr_t allocate_external_node(const char *u) {
  const size_t ulen = strlen(u);
  char *x = malloc(sizeof(char) * (ulen + 1));
  memcpy(x, u, ulen + 1);

  nodeptr_t ret = {external, x};
  return ret;
}
bool is_empty_tree(tree_t *t) { return (t->root.ptr == NULL); }

// this is also tricky, uses bit representation
int choose_direction(internal_node_t *q, const char *u, size_t ulen) {
  // ulen is just strlen(u) precomputed for efficiency
  uint8_t c = 0;
  if (q->byte < ulen)
    c = (uint8_t)u[q->byte];
  const int direction = (1 + (q->otherbits | c)) >> 8;
  return direction;
}

// other higher level functions

nodeptr_t choose_child(nodeptr_t p, const char *u, size_t ulen) {
  // ulen is just strlen(u) precomputed for efficiency
  internal_node_t *q = get_internal_ptr(p);
  return q->child[choose_direction(q, u, ulen)];
}

int contains(tree_t *t, const char *u) {
  if (is_empty_tree(t))
    return 0;

  const size_t ulen = strlen(u);
  nodeptr_t p = t->root;
  while (is_internal_ptr(p)) {
    p = choose_child(p, u, ulen);
  }

  return 0 == strcmp(u, get_external_ptr(p));
}

int insert(tree_t *t, const char *u) {
  if (is_empty_tree(t)) {
    t->root = allocate_external_node(u);
    return 2;
  }

  // traverse down the tree until we reach an external node
  const size_t ulen = strlen(u);
  nodeptr_t p = t->root;
  while (is_internal_ptr(p)) {
    p = choose_child(p, u, ulen);
  }

  // modifying the external node so it becomes an internal node

  // find the critical bit (where the current key differs from the
  // new, to-be-inserted key)
  const char *q = get_external_ptr(p);
  uint32_t newbyte;
  uint32_t newotherbits;
  const uint8_t *ubytes = (void *)u;
  for (newbyte = 0; newbyte < ulen; ++newbyte) {
    if (q[newbyte] != ubytes[newbyte]) {
      newotherbits = q[newbyte] ^ ubytes[newbyte];
      goto different_byte_found;
    }
  }
  if (q[newbyte] != 0) {
    newotherbits = q[newbyte];
    goto different_byte_found;
  }
  return 1;

different_byte_found: // TODO: pls don't use gotos
  newotherbits |= newotherbits >> 1;
  newotherbits |= newotherbits >> 2;
  newotherbits |= newotherbits >> 4;
  newotherbits = (newotherbits & ~(newotherbits >> 1)) ^ 255;
  uint8_t c = q[newbyte];
  int newdirection = (1 + (newotherbits | c)) >> 8; // abstract this??

  // TODO: cancel when malloc runs out of memory
  internal_node_t *newnode =
      malloc(sizeof(internal_node_t)); // TODO: allocate internal node?
  newnode->byte = newbyte;
  newnode->otherbits = newotherbits;
  newnode->child[1 - newdirection] = allocate_external_node(x);

  // TODO: the rest of the algorithm

  //   void **wherep = &t->root;
  //   for (;;) {
  //     uint8_t *p = *wherep;
  //     if (!(1 & (intptr_t)p))
  //       break;
  //     critbit0_node *q = (void *)(p - 1);
  //     if (q->byte > newbyte)
  //       break;
  //     if (q->byte == newbyte && q->otherbits > newotherbits)
  //       break;
  //     uint8_t c = 0;
  //     if (q->byte < ulen)
  //       c = ubytes[q->byte];
  //     const int direction = (1 + (q->otherbits | c)) >> 8;
  //     wherep = q->child + direction;
  //   }

  //   newnode->child[newdirection] = *wherep;
  //   *wherep = (void *)(1 + (char *)newnode);
  // # 262 "./critbit.w"
  // # 177 "./critbit.w"

  //   return 2;
}
