import Batteries.Data.List.Basic

namespace Complexity

/- Head movement direction on a tape -/
inductive Move
| L | R | S
deriving Repr, DecidableEq

/-- A single tape, represented by:
    • left  – symbols to the left of the head (nearest first),
    • head  – the current symbol under the head,
    • right – symbols to the right of the head (nearest first).
-/

structure Tape (σ : Type) where
  left  : List σ
  head  : σ
  right : List σ
deriving Repr

namespace Tape

/-- Move the head left or right, updating the tape contents.
    Extends with a blank symbol when moving off the edge. -/

def move {σ : Type} (blank : σ) (mv : Move) (t : Tape σ) : Tape σ :=
  match mv with
  | Move.L =>
    match t.left with
    | [] => { left := [], head := blank, right := t.head :: t.right }
    | h :: ls => { left := ls, head := h, right := t.head :: t.right }
  | Move.R =>
    match t.right with
    | [] => { left := t.head :: t.left, head := blank, right := [] }
    | h :: rs => { left := t.head :: t.left, head := h, right := rs }
  | Move.S => t

/-- Initialize a tape with an input list, head on the first symbol (or blank if empty). -/
def init {σ : Type} (blank : σ) (input : List σ) : Tape σ :=
  match input with
  | [] => { left := [], head := blank, right := [] }
  | h :: rs => { left := [], head := h, right := rs }

end Tape

/-- Transition function type for a k-tape deterministic TM. -/
def TMTransition (k : Nat) (Q σ : Type) :=
  Q × (Fin k → σ) → Q × (Fin k → σ) × (Fin k → Move)

/-- Deterministic multitape Turing machine. -/
structure TM (k : Nat) (Q σ : Type) where
  start : Q
  halt : Q → Bool
  blank : σ
  δ : TMTransition k Q σ

/-- A configuration = current state + k tapes. -/
structure TMConfig (k : Nat) (Q σ : Type) where
  state : Q
  tapes : Fin k → Tape σ

/-- One deterministic step of a multitape TM. -/
def step {k Q σ} (M : TM k Q σ) (c : TMConfig k Q σ) : TMConfig k Q σ :=
  let read (i : Fin k) : σ := (c.tapes i).head
  let (q', writes, moves) := M.δ (c.state, read)
  let tapes' : Fin k → Tape σ :=
    fun i =>
      let t := c.tapes i
      let t' := { t with head := writes i }
      t'.move M.blank (moves i)
  { state := q', tapes := tapes' }

end Complexity
