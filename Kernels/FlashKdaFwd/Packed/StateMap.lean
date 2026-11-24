-- SPDX-License-Identifier: Apache-2.0
module
public import Core.Async.Tensor.TensorStore
public import Lemmas.Tensor.TensorSwizzle
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

@[expose] public section
namespace FlashKda.Packed.StateMap
open PTX

def descriptor (base planes : Nat) (allocation : TensorDescriptor.AllocationClass) :
    TensorDescriptor.Descriptor 2 where
  format := .f32
  base := base
  extent := ![128, 128, planes]
  outerStride := ![512, 65536]
  box := ⟨![8, 128, 1], fun _ => 1⟩
  swizzle := .b32
  fill := .zero
  allocationClass := allocation

def strip (base planes plane : Nat) (allocation : TensorDescriptor.AllocationClass)
    (smem : Loc) (i : Fin 16) : TensorStore.Spec where
  outer := 2
  descriptor := descriptor base planes allocation
  origin := ![((8*i.val : Nat) : Int), 0, (plane : Int)]
  sharedBase := { smem with addr := smem.addr + 32768 + 4096*i.val }

section
variable (base planes plane : Nat) (allocation : TensorDescriptor.AllocationClass) (smem : Loc)
local notation "d" => descriptor base planes allocation
local notation "s" => strip base planes plane allocation smem

def slot (col : Fin 8) (row : Fin 128) (byte : Fin 4) : TensorTransfer.Slot d :=
  ⟨⟨col, by simp [descriptor, TensorTile.count, TensorTile.step]⟩,
   ⟨row, by simp [descriptor, TensorTile.rows, TensorTile.rowsOf,
     TensorTile.count, TensorTile.step]⟩, byte⟩

local notation "cell" => slot base planes allocation

theorem byte_count : TensorTransfer.bytes d = 4096 := by
  simp [TensorTransfer.bytes, descriptor, TensorTile.count, TensorTile.rows, TensorTile.rowsOf,
    TensorTile.step, TensorDescriptor.Format.bytes]

theorem coords (i : Fin 16) (col : Fin 8) (row : Fin 128) (byte : Fin 4) :
    TensorTransfer.coord (s i).descriptor (s i).origin (s i).rows (cell col row byte) =
      ![((8*i.val + col.val : Nat) : Int), (row.val : Int), (plane : Int)] := by
  funext axis
  fin_cases axis <;>
    simp [strip, descriptor, slot, TensorTransfer.coord, TensorTransfer.index, TensorTile.coord,
      TensorTile.indexOf, TensorTile.unflatten, TensorTile.count, TensorTile.step, Fin.cases,
      Nat.mod_eq_of_lt row.isLt, Nat.div_eq_of_lt row.isLt] <;> rfl

theorem address (live : plane < planes) (i : Fin 16) (col : Fin 8) (row : Fin 128)
    (byte : Fin 4) : (s i).globalAddress (cell col row byte) = some
      (base + 65536*plane + 512*row.val + 4*(8*i.val + col.val) + byte.val) := by
  unfold TensorBox.globalAddress TensorTransfer.globalAddress TensorAddress.lookup
  rw [coords]
  let c : Fin 3 → Int := ![((8*i.val + col.val : Nat) : Int), (row.val : Int), (plane : Int)]
  have inside (a : Fin 3) :
      0 ≤ c a ∧ c a < (((descriptor base planes allocation).extent a : Nat) : Int) := by
    fin_cases a <;> simp [c, descriptor] <;> omega
  rw [ite_eq_left ⟨inside, byte.isLt⟩]
  congr 1
  simp only [TensorAddress.byteAddress, Fin.sum_univ_succ]
  change base + ((8*i.val + col.val)*4 + (row.val*512 + (plane*65536 + 0))) + byte.val = _
  ring

theorem covers (live : plane < planes) (k v : Fin 128) (b : Fin 4) :
    ∃ (i : Fin 16) (col : Fin 8), (s i).globalAddress (cell col v b) =
      some (base + 65536*plane + 512*v.val + 4*k.val + b.val) := by
  refine ⟨⟨k.val/8, by omega⟩, ⟨k.val%8, by omega⟩, ?_⟩
  rw [address _ _ _ _ _ live]
  congr 1
  dsimp
  omega

theorem unique (p q : Nat) (ip iq : Fin 16) (cp cq : Fin 8) (vp vq : Fin 128)
    (bp bq : Fin 4)
    (same : 65536*p + 512*vp.val + 4*(8*ip.val+cp.val) + bp.val =
      65536*q + 512*vq.val + 4*(8*iq.val+cq.val) + bq.val) :
    p = q ∧ vp = vq ∧ ip = iq ∧ cp = cq ∧ bp = bq := by
  simp only [Fin.ext_iff]
  omega

theorem write_byte (live : plane < planes) (i : Fin 16) (col : Fin 8) (row : Fin 128)
    (byte : Fin 4) (e : TensorStore.Effects (s i)) (ok : TensorStore.CopyOk (s i) e)
    (done_ : e.fullDone = true) :
    let l : Loc := ⟨.global, 0, base + 65536*plane + 512*row.val + 4*(8*i.val+col.val) + byte.val⟩
    TensorStore.destination (s i) (cell col row byte) = some l ∧
      ∃ value, e.read (cell col row byte) = some value ∧
        e.write (cell col row byte) = some value := by
  dsimp only
  have target := address base planes plane allocation smem live i col row byte
  have dest := congrArg (Option.map (fun a => (⟨.global, 0, a⟩ : Loc))) target
  refine ⟨dest, ?_⟩
  obtain ⟨v, hv⟩ := (ok.complete done_).2 _ _ dest
  obtain ⟨_, w, hw, eqv⟩ := ok.writes _ _ hv
  exact ⟨v, eqv rfl ▸ hw, hv⟩

def input (barrier : Loc) (i : Fin 16) : TensorCopy.Spec :=
  { (s i).toTensorBox with mbar := barrier }

theorem shared_slot (i : Fin 16) (col : Fin 8) (row : Fin 128) (byte : Fin 4) :
    let start := smem.addr + 32768 + 4096*i.val
    (s i).sharedLoc (cell col row byte) =
      ⟨smem.space, smem.cta, start + TensorSwizzle.offset .b32 start
        (32*row.val + 4*col.val + byte.val)⟩ := by
  dsimp only
  unfold TensorBox.sharedLoc TensorTile.sharedByte TensorTile.linearByte
  simp only [strip, descriptor, slot, TensorDescriptor.Format.bytes,
    TensorTile.rowBytes, TensorTile.count, TensorTile.step, TensorTile.swizzleWidth]
  simp [Nat.mul_comm]

set_option maxRecDepth 8192 in
theorem read_byte (live : plane < planes) (i : Fin 16) (col : Fin 8) (row : Fin 128)
    (byte : Fin 4) (barrier : Loc)
    (e : TensorCopy.Effects (input base planes plane allocation smem barrier i))
    (ok : TensorCopy.CopyOk _ e) (done_ : e.notified = true) :
    let j := cell col row byte
    TensorCopy.source (input base planes plane allocation smem barrier i) j =
      .global (base + 65536*plane + 512*row.val + 4*(8*i.val+col.val) + byte.val) ∧
      ∃ value, e.read j = some value ∧ e.write j = some (.copied value) := by
  dsimp only
  let j := cell col row byte
  have ha := address base planes plane allocation smem live i col row byte
  have hs : TensorCopy.source (input base planes plane allocation smem barrier i) j =
      .global (base + 65536*plane + 512*row.val + 4*(8*i.val+col.val) + byte.val) := by
    unfold TensorCopy.source
    change (match (s i).globalAddress j with
      | some a => TensorTransfer.Source.global a
      | none => .fill .zero .f32 byte.val) = _
    rw [show (s i).globalAddress j = _ from ha]
  refine ⟨hs, ?_⟩
  obtain ⟨v, hv⟩ := ok.complete done_ j
  have source := ok.writes j v hv
  rw [hs] at source
  obtain ⟨w, read, rfl⟩ := source
  exact ⟨w, read, hv⟩

end
end FlashKda.Packed.StateMap
