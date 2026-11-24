-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.NormalizeIndex
import Core.Async.Tensor.TensorCopy
import Lemmas.Tensor.TensorSwizzle

/-! Byte correspondence of the public query and key tensor maps. The host supplies
the packed allocation length, measured in tokens, including every sequence. -/
namespace FlashKda.InputTile
open PTX
set_option maxRecDepth 8192

def descriptor (base heads tokens : Nat) (allocation : TensorDescriptor.AllocationClass) :
    TensorDescriptor.Descriptor 2 where
  format := .bf16
  base := base
  extent := ![128, tokens, heads]
  outerStride := ![256 * heads, 256]
  box := ⟨![128, 16, 1], fun _ => 1⟩
  swizzle := .none
  fill := .zero
  allocationClass := allocation

theorem byte_count (base heads tokens : Nat) (allocation : TensorDescriptor.AllocationClass) :
    TensorTransfer.bytes (descriptor base heads tokens allocation) = 4096 := by
  simp [TensorTransfer.bytes, descriptor, TensorTile.count, TensorTile.rows, TensorTile.rowsOf,
    TensorTile.step, TensorDescriptor.Format.bytes]

def transfer (base heads tokens first head : Nat) (dst barrier : Loc)
    (allocation : TensorDescriptor.AllocationClass) : TensorCopy.Spec where
  outer := 2
  descriptor := descriptor base heads tokens allocation
  origin := ![0, (first : Int), (head : Int)]
  sharedBase := dst
  mbar := barrier

section
variable (base heads tokens first head : Nat) (dst barrier : Loc)
    (allocation : TensorDescriptor.AllocationClass)
local notation "s" => transfer base heads tokens first head dst barrier allocation

/-- One byte of a thread's sixteen-byte load, grouped into eight bfloat16 elements. -/
def threadSlot (tid : Fin 256) (i : Fin 8) (j : Fin 2) :
    TensorTransfer.Slot (descriptor base heads tokens allocation) :=
  ⟨⟨8 * (tid.val % 16) + i.val, by simp [descriptor, TensorTile.count, TensorTile.step]; omega⟩,
   ⟨tid.val / 16, by
      simp [descriptor, TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step]
      omega⟩, j⟩

local notation "slot" => threadSlot base heads tokens allocation

theorem shared (tid : Fin 256) (i : Fin 8) (j : Fin 2) :
    (s).sharedLoc (slot tid i j) =
      { dst with addr := dst.addr + (tid.val <<< 4) + 2 * i.val + j.val } := by
  unfold TensorBox.sharedLoc TensorTile.sharedByte TensorTile.linearByte
  simp only [transfer, descriptor, threadSlot, TensorDescriptor.Format.bytes,
    TensorTile.rowBytes, TensorTile.count, TensorTile.step, TensorTile.swizzleWidth]
  simp only [Fin.val_zero, ↓reduceIte]
  norm_num
  rw [TensorSwizzle.offset_none, (Normalize.thread_offsets tid).1]
  ring

theorem coordinates (tid : Fin 256) (i : Fin 8) (j : Fin 2) :
    TensorTransfer.coord (s).descriptor (s).origin (s).rows (slot tid i j) =
      ![((8 * (tid.val % 16) + i.val : Nat) : Int), ((first + tid.val / 16 : Nat) : Int),
        (head : Int)] := by
  funext axis
  fin_cases axis <;>
    simp [transfer, descriptor, threadSlot, TensorTransfer.coord, TensorTransfer.index,
      TensorTile.coord, TensorTile.indexOf, TensorTile.unflatten, TensorTile.count,
      TensorTile.step, Fin.cases, Nat.mod_eq_of_lt (show tid.val / 16 < 16 by omega),
      Nat.div_eq_of_lt (show tid.val / 16 < 16 by omega)] <;>
    rfl

/-- The host's token-major, head-minor address, including both the row within
the tile and the byte within the thread's eight-element vector. -/
def address (base heads first head : Nat) (tid : Fin 256) (i : Fin 8) (j : Fin 2) : Nat :=
  base + ((first + tid.val / 16) * heads + head) * 256 +
    (8 * (tid.val % 16) + i.val) * 2 + j.val

theorem global (hh : head < heads) (tid : Fin 256) (i : Fin 8) (j : Fin 2) :
    (s).globalAddress (slot tid i j) =
      if first + tid.val / 16 < tokens then some (address base heads first head tid i j)
      else none := by
  unfold TensorBox.globalAddress TensorTransfer.globalAddress TensorAddress.lookup
  rw [coordinates]
  let coord : Fin 3 → Int := ![((8 * (tid.val % 16) + i.val : Nat) : Int),
    ((first + tid.val / 16 : Nat) : Int), (head : Int)]
  change (if (∀ a, 0 ≤ coord a ∧ coord a < (((s).descriptor.extent a : Nat) : Int)) ∧
      j.val < 2 then some (TensorAddress.byteAddress (TensorDescriptor.geometry (s).descriptor)
      coord j.val) else none) = _
  have bounds : (∀ a, 0 ≤ coord a ∧ coord a < (((s).descriptor.extent a : Nat) : Int)) ↔
      first + tid.val / 16 < tokens := by
    constructor
    · intro h
      have mid := (h 1).2
      change ((first + tid.val / 16 : Nat) : Int) < (tokens : Int) at mid
      exact_mod_cast mid
    · intro live a
      fin_cases a <;> simp [coord, transfer, descriptor] <;> omega
  simp only [bounds, j.isLt, and_true]
  split
  · congr 1
    simp only [TensorAddress.byteAddress, Fin.sum_univ_succ]
    change base + ((8 * (tid.val % 16) + i.val) * 2 +
      ((first + tid.val / 16) * (256 * heads) + (head * 256 + 0))) + j.val = _
    unfold address
    ring
  · rfl

/-- A completed valid transfer with a public, stable source reads and writes
the same byte for each live token. Tail rows beyond the entire allocation
receive zero fill from the descriptor without a global read. -/
theorem completed (hh : head < heads) (tid : Fin 256) (i : Fin 8) (j : Fin 2)
    (memory : Nat → Byte) (effects : TensorCopy.Effects s)
    (ok : TensorCopy.CopyOk s effects) (done_ : effects.notified = true)
    (reads : ∀ cell addr byte, (s).globalAddress cell = some addr →
      effects.read cell = some byte → byte = memory addr) :
    if first + tid.val / 16 < tokens then
      effects.write (slot tid i j) = some (.copied (memory (address base heads first head tid i j)))
    else effects.read (slot tid i j) = none ∧
      effects.write (slot tid i j) = some (.filled .zero .bf16 j.val) := by
  let cell := slot tid i j
  obtain ⟨value, written⟩ := ok.complete done_ cell
  have source := global base heads tokens first head dst barrier allocation hh tid i j
  have content := ok.writes cell value written
  unfold TensorCopy.source at content
  change (s).globalAddress cell = _ at source
  split <;> rename_i live
  · rw [ite_eq_left live] at source
    rw [source] at content
    obtain ⟨byte, read, rfl⟩ := content
    rwa [reads cell _ byte source read] at written
  · rw [ite_eq_right live] at source
    rw [source] at content
    constructor
    · cases h : effects.read cell with
      | none => rfl
      | some b =>
        obtain ⟨_, bad⟩ := ok.reads cell b h
        simp [TensorCopy.source, source] at bad
    · rwa [content] at written

end
end FlashKda.InputTile
