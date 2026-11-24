-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Matrix
public import Tactics.KernelRfl
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Projection
open PTX

inductive Word where
  | input (reg : Nat)
  | address (base : Nat) (offset : Int)
  | load (ordinal word : Nat)
  | product (ordinal word : Nat)
  | zero
  deriving DecidableEq, Repr

structure Trace where
  registers : List (Nat × Word) := []
  sources : List Word := []
  products : Nat := 0

def Trace.read (t : Trace) (r : Nat) := (t.registers.lookup r).getD (.input r)

def write (rs : List Nat) (tag : Nat → Word) (t : Trace) : Trace :=
  { t with registers := (rs.zipIdx.map fun (r,i) => (r,tag i)) ++ t.registers }

def operands (n : Nat) : List Word :=
  let stage := n / 8
  let tile := n % 8
  let a := 4*stage + tile/2%2
  let b := 4*stage + 2 + tile/4
  (List.range 4).map (.load a) ++ (List.range 2).map (fun i => .load b (2*(tile%2)+i)) ++
    (List.range 4).map (fun i => if stage = 0 then .zero else .product (n-8) i)

def step (t : Trace) : Instr → Option Trace
  | ⟨none,.int ⟨.add, .int .s 32, false, [some d], [.reg r,.imm k]⟩⟩ => do
    let .input base := t.read r | none
    return write [d] (fun _ => .address base k) t
  | ⟨none,.move ⟨.scalar, .int .b 32, [some d], [.imm 0]⟩⟩ =>
    some (write [d] (fun _ => .zero) t)
  | ⟨none,.matrix ⟨.move ⟨false,.m8n8,4,false,.b16⟩,some (.shared .cta),
      some ⟨.reg r 32,0⟩, ds,[]⟩⟩ => do
    guard (ds.length = 4)
    return { write ds (.load t.sources.length) t with sources := t.read r :: t.sources }
  | ⟨none,.matrix ⟨.mma s,none,none,ds,src⟩⟩ => do
    guard (s = Matrix.shape ∧ ds.length = 4)
    let words ← src.mapM fun x => match x with
      | .reg r => some (t.read r)
      | _ => none
    guard (words = operands t.products)
    return { write ds (.product t.products) t with products := t.products+1 }
  | _ => none

def address (i : Nat) : Word :=
  let s := i/4
  match i%4 with
  | 0 => if s = 0 then .input 1158 else .address 1944 (36992 + 512*s : Nat)
  | 1 => .address 1944 (41088 + 512*s : Nat)
  | 2 => .input ([1160,1177,1212,1263,1314,1365,1416,1467].getD s 0)
  | _ => .input ([1161,1737,1767,1797,1827,1857,1887,1916].getD s 0)

def outputRegisters (tile : Nat) : List Nat :=
  let first := [1488,1502,1630,1636,1524,1534,1654,1660].getD tile 0
  (List.range 4).map (first+·)

def summary (t : Trace) :=
  (t.products, t.sources.reverse, (List.range 8).map fun i => (outputRegisters i).map t.read)

set_option maxHeartbeats 0 in
set_option maxRecDepth 60000 in
theorem register_flow : ((Transfers.slice 2193 112).bind (fun xs => xs.foldlM step {})).map summary
    = some (64, (List.range 32).map address,
      (List.range 8).map (fun i => (List.range 4).map (.product (56+i)))) := by kernel_rfl

def partialProduct (a b : Matrix.Tile) (stage : Nat) : Matrix.Tile :=
  fun r j => ((List.range (16*stage)).map (fun k => a r k * b k j)).sum

theorem next_product (a b : Matrix.Tile) (stage : Nat) :
    Matrix.dot (fun r k => a r (16*stage+k)) (fun k j => b (16*stage+k) j)
        (partialProduct a b stage) = partialProduct a b (stage+1) := by
  funext r j
  unfold Matrix.dot partialProduct
  rw [Nat.mul_succ, List.range_add, List.map_append, List.map_map, List.sum_append]
  exact add_comm ..

theorem next_registers (a b : Matrix.Tile) (stage lane : Nat) (hl : lane < 32) :
    let aa := fun r k => a r (16*stage+k)
    let bb := fun k j => b (16*stage+k) j
    mmaRecv [Activation.arithmetic, Activation.approximate] Matrix.shape
      (Matrix.laneBytes aa bb (partialProduct a b stage)) lane =
      .ok ((List.range 4).flatMap fun i => Matrix.bytes (.float .f32
        (partialProduct a b (stage+1) (Matrix.row lane i) (Matrix.col lane i)))) := by
  dsimp only
  rw [Matrix.receive _ _ _ lane hl]
  simp only [Matrix.result, next_product]

end FlashKda.Packed.Projection
