namespace Catalytic

inductive ThreeReg where
  | R1
  | R2
  | R3
  deriving DecidableEq, Repr

def distinct3 (i j k : ThreeReg) : Prop :=
  i ≠ j ∧ j ≠ k ∧ k ≠ i

abbrev Val := Nat

structure State where
  r1 : Val
  r2 : Val
  r3 : Val
  deriving Repr

-- These are only helpers, useful for defining semantics later
-- DO NOT use them for programming!
def State.read (s : State) (r : ThreeReg) : Val :=
  match r with
  | ThreeReg.R1 => s.r1
  | ThreeReg.R2 => s.r2
  | ThreeReg.R3 => s.r3

def State.write (s : State) (r : ThreeReg) (v : Val) : State :=
  match r with
  | ThreeReg.R1 => { s with r1 := v }
  | ThreeReg.R2 => { s with r2 := v }
  | ThreeReg.R3 => { s with r3 := v }

-- We support three instructions for this catalytic space model
inductive Instr where
  -- Load value x into register dst
  -- For example, "Load 5 R2" would change (r1, r2, r3) into (r1, r2+5, r3)
  | load (x : Val) (dst : ThreeReg)
  | load_rev (x : Val) (dst : ThreeReg)
  -- Add the sum of a register and a const into another register
  -- For example, "add_const R1 a R2" would change (r1, r2, r3) into (r1, r2+r1+a, r3)
  | add_const (src : ThreeReg) (x : Val) (dst : ThreeReg)
  | add_const_rev (src : ThreeReg) (x : Val) (dst : ThreeReg)
  -- Add the sum of two registers into another register
  -- For example, "add_reg R1 R2 R3" would change (r1, r2, r3) into (r1, r2, r3+r1+r2)
  | add_reg (src1 src2 dst : ThreeReg)
  | add_reg_rev (src1 src2 dst : ThreeReg)
  -- Add the product of a register and a const into another register
  -- For example, "mult_const R1 a R2" would change (r1, r2, r3) into (r1, r2+a*r1, r3)
  | mul_const (src : ThreeReg) (x : Val) (dst : ThreeReg)
  | mul_const_rev (src : ThreeReg) (x : Val) (dst : ThreeReg)
  -- Add the product of two registers into another register
  -- For example, "mult_reg R1 R2 R3" would change (r1, r2, r3) into (r1, r2, r3+r1*r2)
  | mul_reg (src1 src2 dst : ThreeReg)
  | mul_reg_rev (src1 src2 dst : ThreeReg)
  deriving Repr

-- Defining big step semantics for Instructions
def Instr.exec (i : Instr) (s : State) : State :=
  match i with
  | .load x dst =>
      let v := s.read dst + x
      s.write dst v
  | .load_rev x dst =>
      let v := s.read dst - x
      s.write dst v
  | .add_const src x dst =>
      let v := s.read dst + s.read src + x
      s.write dst v
  | .add_const_rev src x dst =>
      let v := s.read dst - (s.read src + x)
      s.write dst v
  | .add_reg src1 src2 dst =>
      let v := s.read dst + s.read src1 + s.read src2
      s.write dst v
  | .add_reg_rev src1 src2 dst =>
      let v := s.read dst - (s.read src1 + s.read src2)
      s.write dst v
  | .mul_const src x dst =>
      let v := s.read dst + x * s.read src
      s.write dst v
  | .mul_const_rev src x dst =>
      let v := s.read dst - x * s.read src
      s.write dst v
  | .mul_reg src1 src2 dst =>
      let v := s.read dst + s.read src1 * s.read src2
      s.write dst v
  | .mul_reg_rev src1 src2 dst =>
      let v := s.read dst - s.read src1 * s.read src2
      s.write dst v

def Instr.rev : Instr → Option Instr
  | Instr.load x i => some (Instr.load_rev x i)
  | Instr.load_rev x i => some (Instr.load x i)
  | Instr.add_const src x dst => some (Instr.add_const_rev src x dst)
  | Instr.add_const_rev src x dst => some (Instr.add_const src x dst)
  | Instr.add_reg src1 src2 dst => some (Instr.add_reg_rev src1 src2 dst)
  | Instr.add_reg_rev src1 src2 dst => some (Instr.add_reg src1 src2 dst)
  | Instr.mul_const src x dst => some (Instr.mul_const_rev src x dst)
  | Instr.mul_const_rev src x dst => some (Instr.mul_const src x dst)
  | Instr.mul_reg src1 src2 dst => some (Instr.mul_reg_rev src1 src2 dst)
  | Instr.mul_reg_rev src1 src2 dst => some (Instr.mul_reg src1 src2 dst)

-- A program is simply a list of instructions
abbrev Program := List Instr

-- We can execute this program
def Program.exec (p : Program) (s : State) : State :=
  p.foldl (fun st i => Instr.exec i st) s

-- We will also have a universal way to reverse a program
def Program.rev : Program → Option Program
  | []  => some []
  | instr :: rest =>
    match Program.rev rest, Instr.rev instr with
    | some revRest, some revInstr => some (revInstr :: revRest)
    | _, _ => none

/- Now we start to do some more difficult task
Given two following programs:
- p1 can turn a register ri into ri+x
- p2 can turn a register rj into rj+y
Desired outcome
- A program that can turn a register rk into rk+z
-/
def ADD
  (p1 p2 : Program)
  (i j k : ThreeReg)
  (h : distinct3 i j k ) : Option Program :=
  match p1.rev, p2.rev with
  | some revP1, some revP2 =>
    some (
      p1 ++ [Instr.add_const i 0 k] ++ revP1 ++ [Instr.add_const_rev i 0 k] ++
      p2 ++ [Instr.add_const j 0 k] ++ revP2 ++ [Instr.add_const_rev j 0 k]
    )
  | _, _ => none

end Catalytic
