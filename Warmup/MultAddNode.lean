import Std.Data.Array.Basic
open Std

inductive Op where
| AND
| XOR
deriving Repr, DecidableEq

def Op.Eval : Op → Bool → Bool → Bool
| Op.AND, b1, b2 => b1 && b2
| Op.XOR, b1, b2 => b1 != b2

structure NodeOp where
  bit : Bool
  op  : Op
deriving Repr, DecidableEq

inductive BTreeMultAdd where
| leaf : Bool → BTreeMultAdd
| node : NodeOp → BTreeMultAdd → BTreeMultAdd → BTreeMultAdd
deriving Repr, DecidableEq

def depth : BTreeMultAdd → Nat
| BTreeMultAdd.leaf _ => 1
| BTreeMultAdd.node _ left right => 1 + Nat.max (depth left) (depth right)

-- We use a Monad to mimic mutable array
def iterative_eval_ST (tree : BTreeMultAdd) (buf : STArray s Bool) (depth : Nat) : ST s Bool := do
  let buf ← get
  match tree with
  | .leaf b =>
    buf.set! depth b
    pure b
  | .node op left right => do
    buf.set! (depth + 1) iterative_eval_ST left buf (depth + 1)
    buf.set! (depth + 2) iterative_eval_ST right buf (depth + 2)
    buf.set! depth (Op.Eval op.op (buf.get! (depth + 1)) (buf.get! (depth + 2)))
    pure (buf.get! depth)
