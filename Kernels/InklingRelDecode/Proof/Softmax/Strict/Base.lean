-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.LateHalf
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Machine
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Base
public import Kernels.InklingRelDecode.Gen.TypedLateQt

@[expose] public section

/-! # The strict steps of the softmax's value machine: the shared parts

The lane's invariant is `QTF lateQt` and its fact about a state after an event `TauAll (LateR' L g)`
(`Gen.TypedLateQt.LQ`). `LWf` is what the lane assumes of the events: the words the
`tcgen05.ld`s return are data of four bytes. A span between two sites is a chain of lane
windows (`lw_<window>`), whose facts pass through: `pass_span`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Assumption
open PTX.Kernels.InklingRelDecode.Proof.Iface PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

/-- The events the lane assumes well-formed. -/
structure LWf (e : Event) : Prop where
  tc : ∀ a vals sh, e.pc ∈ tcLdPcs → e.kind = .tc (.ld a vals sh) → ∀ v ∈ vals, Dat32 v
  /-- The warp broadcasts of the pcs 1261 and 2603 return a 32-bit word. -/
  idx : e.pc = 1261 ∨ e.pc = 2603 → ∀ m av bv cv recv ok,
    e.kind = .shfl m av bv cv recv ok → ∃ x, recv = b32 x
  /-- The shared load of the row sums (pc 2252) returns a datum of four bytes. -/
  ld : e.pc = 2252 → ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ Dat32 v
  /-- The loads of the bias words (the preloads and the loop's) return a datum of a word. -/
  bias : e.pc % 2 = 0 → (680 ≤ e.pc ∧ e.pc ≤ 806 ∨ 1124 ≤ e.pc ∧ e.pc ≤ 1250) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v
  /-- The butterfly shuffles of the maxima and the sums return a datum of four bytes. -/
  bfly : e.pc ∈ [1838, 2234, 2242, 2244, 2246, 2248, 2253, 2255] →
    ∀ m av bv cv recv ok, e.kind = .shfl m av bv cv recv ok → Dat32 recv

/-- The pcs `[a, b)` are the data lanes' pcs away from the three single-instruction readings. -/
def rangeOk (a b : Nat) : Bool :=
  (List.range' a (b - a)).all fun pc => lateRange pc && pc != 600 && pc != 807 && pc != 2562

theorem fp3_of {L : Launch} {g a b : Nat} (h : rangeOk a b = true) :
    FloatPlain3 Assumptions.all L g a b := by
  refine floatPlain3 fun pc h1 h2 => ?_
  have := (List.all_eq_true.mp h) pc (List.mem_range'_1.mpr ⟨h1, by omega⟩)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  obtain ⟨⟨⟨hr, h6⟩, h8⟩, h25⟩ := this
  exact ⟨lateRange_emu hr, h25, h6, h8⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
