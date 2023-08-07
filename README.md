# Crit-bit Tree in Coq

This is a formally verified Coq implementation of (very simplified) crit-bit trees as described in [Adam Langley's notes](https://www.imperialviolet.org/binary/critbit.pdf) and [D.J. Bernstein's notes](https://cr.yp.to/critbit.html). We also referenced [QP tries](https://dotat.at/prog/qp/blog-2015-10-04.html) for further inspiration as well.

## Context

This is an **UNCOMPLETED** project, which is a part of my (@tchomphoochan) UROP at MIT in Spring 2023. Unfortunately, because of changes in my priorities, I was not able to complete the implementation and verification. I am leaving the code base open sourced in case it may be useful to anyone (or if someone else ever continues the project). Below is an explanation of how things have been implemented so far. This project was supervised by @samuelgruetter.

## Quick summary of simplified crit-bit tree

Crit-bit tree implements the map/dictionary interface.

The tree consists of two types of nodes, internal nodes, and leaf nodes. Internal node contains an index of the "critical bit" and pointers to left and right trees. Leaf node contains a key-value pair. The critical bit tells you, essentially, an important information to distinguish whether a key-value pair should be found in the left sub-tree or the right subtree. A key is an infinite list of zeros and ones.

For example, consider a tree representing this map:
```
00101 -> 5 (leaf node A)
01100 -> 7 (leaf node B)
01111 -> 10 (leaf node C)
```
The tree will look like this:
```
    1
   / \
  A   3
     / \
    B   C
```

To search for a key in the tree, we start from the root node. The node tells you the index of the "critical bit." That critical bit tells you if you should go left or right. Repeat until you get to the leaf node. Verify, at the leaf node, that the node's key matches what you're looking for.

Suppose you are searching for `01111`. The first node tells you to look at index `1`, which is a `1`, so you go right. The next node tells you to look at index `3`, which is a `1`, so you go right. We have reached final node (C). Notice that we have not looked at index `0`, `2`, or `4` at all. Crit-bit tree allows you to check only as many bits as needed to distinguish between the existing keys. This, however, means, you have to store the full key in (C) to verify that it is indeed the key `01111`, not any key in the form of `?1?1?`.

In Coq, `lookup` implements this search algorithm. It makes use `find_best` which is the described tree-walking algorithm. `find_best` is split into a helper function because it is useful for other operations too.

You can see more examples in the `Examples` section in Coq.

## Key representation

An astute reader may notice that this structure is incapable of representing this map:
```
0 -> A
00 -> B
```
Because there is no critical bit to distinguish between the two! ...Unless we have some sort of "last bit" marker, which is very ugly. (Since that would mean three possibilities rather than two possibilities for each position in the key.)

So, we have decided that a key is conceptually an _infinite_ list of zeros and ones. In Coq, we represent such an infinite list as a finite list that must end with a 1 (see `valid_key`). Infinite zeros are implied to follow that final 1.

This means `0` and `00` are both invalid keys! If they were, they would represent the same key `00000000000...`.

`valid_key` defines a checker for this.

`diff` lets you find the first critical bit among two keys. The implementation of `diff` is a bit tricky because we have to account for these implied infinite zeros at the end.

## Lexicographic order

Another thing to notice. It is useful to maintain that the indices are _increasing_ as you traverse the tree from root to any leaf. This keeps the leaves essentially sorted, allowing for convenient operations like finding the next key in the lexicographic order or iterating through all sorted keys.

To maintain this invariant, we implement `insert` as the following:
- First, to insert a key, we simply search the key as usual first. If the key already exists then we can simply replace that node. Done.
- If the key does not exist, we would end up in a leaf node that's the "best candidate" (hence the naming of `find_best`). We compare the best candidate with the new key to insert to figure out the first critical bit, and insert a branch there.

For example, consider a tree representing this map:
```
00101 -> 5 (leaf node A)
01101 -> 7 (leaf node B)
01111 -> 10 (leaf node C)
```
which looks like this as a crit-bit tree:
```
    1
   / \
  A   3
     / \
    B   C
```
If we want to insert `01011` (D), the first step would lead us to see the best candidate `01111` (C). `diff` tells us the first critical bit is index `2`. Therefore, a branch (with the new leaf node) gets inserted right before we reach index 3, as we traverse down that path:
```
    1
   / \
  A  [2]
     / \
   *D*  3
       / \
      B   C
```
Again, you can see a long, sample sequence of insertions in `Examples` section (Examples with names starting with `map3_`).

## Current proof progress

### Invariant

To prove the correctness of crit-bit trees, we define an inductive predicate `ct` (and `ct_top`) that asserts whether a tree `t` is representative of map `m`.

There's an additional variable in the definition for `ct`: `s`, representing the prefix of all the keys in the tree. Why? Remember, we keep the crit-bit indices increasing from root to leaf. When we traverse down a node, we know that, for all nodes in the entire subtree, all bits up to that index must have the same prefix up to that index. Otherwise, that node would have been stored elsewhere!

You can see examples with names starting with `map3_` and try to prove those examples manually to get a sense of how this definition is applied.

This is not exactly the cleanest invariant.

In particular, note that the prefix `s` is a _finite_ list that may end with either a 0 or a 1. There are no implied infinite zeros! `s` is _not_ a "key," which is conceptually infinite. When reading the definition of `ct`, keep that in mind.

For example, consider a tree with just one leaf node `1->*`. Since the key `1` is actually conceptually `100000...`, it would be valid to say that this tree has prefix `1` or `10` or `100` or `1000` or `10000` and so on, hence `s' = s ++ repeat false n` in the definition.

There are also other sources of inelegance, like the fact that the indices are described using absolute indices rather than relative indices, and also feel quite redundant themselves (see `n = length s`).

### Theorem statements

At least, with this invariant, it's not too hard to state the top-level theorem. For example,
```coq
Theorem lookup_ok : forall t m k r,
  ct_top t m -> valid_key k -> map.get m k = r -> lookup t k = r.
```
simply says, for each tree `t` that represents map `m`, if you're trying to look up a valid key `k` in the tree you would get the same result as looking it up in the represented map.

This theorem has been proven completely, so we can say with some confidence that things are implemented correctly.

`insert_ok` has not been completely proven yet, and other operations like find next in lexicographic order have not been implemented at all.

## Engineering notes

### Map representation

We chose to use a concrete map implementation rather than an abstract one, from the `coqutil` project. The reason is that, it is much easier to reason about equality when doing proofs. It's also computable, so it's convenient for confirming examples. This map implementation has exactly one possible representation for each abstract map (I believe). This avoids the headache that comes with functional maps where the order of insertions changes the representation.

### Refactoring

If anyone ever works on this, I highly suggest working through the existing proofs and seeing if you could come up with a way to clean them up. It was rather painful to make progress on `insert_ok` because of all the unnecessary tedium from bad design decisions, like using `repeat` function instead of `Repeated` predicate (which I defined much later in the process).

This variant is probably fine as is, but as I said, it is not elegant. Perhaps an entirely new invariant may be justified. The entire thing about infinite zeros is very confusing. This refactoring is probably needed to make any meaningful progress on this. In the indefinite future, I might be able to get back to this project.
