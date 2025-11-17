-- Let's just say, we only want full binary trees for now.
inductive BTree (α : Type) : Type
| leaf : BTree α
| node : α → BTree α → BTree α → BTree α -- value, left, right
deriving Repr, DecidableEq

example : BTree Nat :=
  BTree.leaf

example : BTree Nat := -- a tree with one node and two leaves
  BTree.node 1 BTree.leaf BTree.leaf

example : BTree Nat := -- a tree with two nodes and three leaves
  BTree.node 1 (BTree.node 2 BTree.leaf BTree.leaf) BTree.leaf


-- Compute the size of a binary tree
def size {α : Type} : BTree α → Nat
| BTree.leaf => 1
| BTree.node _ left right => 1 + size left + size right

-- Compute the depth of a binary tree
def depth {α : Type} : BTree α → Nat
| BTree.leaf => 1
| BTree.node _ left right => 1 + Nat.max (depth left) (depth right)
