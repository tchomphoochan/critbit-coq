#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

#define BRANCHES 2

typedef const char *key_t; // null-terminate bitstring
typedef bool discrim_t;    // discriminate by bit. has BRANCHES possible result
typedef void *value_t;

typedef struct {
  uint8_t byte;
  uint8_t otherbits;
} index_t;

discrim_t get_ith_discrim(key_t k, index_t idx) {
  return false; // TO BE IMPLEMENTED
}

struct node; // forward decl
typedef struct {
  struct node *child[BRANCHES];
  index_t discrimidx;
} intnode_t;

typedef struct {
  key_t key;
  // value_t value;
} extnode_t;

typedef struct node {
  bool isint;
  union {
    intnode_t intnode;
    extnode_t extnode;
  } data;
} node_t;

typedef struct {
  node_t *root;
} tree_t;
