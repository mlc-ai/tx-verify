-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.LaunchReads

@[expose] public section

/-! # Byte bounds of the kernel's read-only global inputs -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof

open PTX

/-- The entire footprint lies in a global input array. -/
def FitsInput (a : Acc) (base width : Nat) : Prop :=
  a.loc.space = .global ∧ base ≤ a.loc.addr ∧ a.loc.addr + a.size ≤ base + width

/-- The five global input arrays read with the non-coherent proxy. -/
inductive NcInputFootprint (P : Params) (a : Acc) : Prop
  | mainLength {ptr : Nat} : P.topkLenBase = some ptr →
      FitsInput a ptr (4 * P.b) → NcInputFootprint P a
  | extraLength {ptr : Nat} : P.extraTopkLenBase = some ptr →
      FitsInput a ptr (4 * P.b) → NcInputFootprint P a
  | sink {ptr : Nat} : P.sinkBase = some ptr →
      FitsInput a ptr (4 * 64) → NcInputFootprint P a
  | mainIndices : FitsInput a P.indicesBase (4 * P.b * P.s_q * P.topk) → NcInputFootprint P a
  | extraIndices : 0 < P.extra_topk →
      FitsInput a P.extraIndicesBase (4 * P.b * P.s_q * P.extra_topk) → NcInputFootprint P a

/-- A non-coherent event uses an input footprint. -/
def NcInputEvent (P : Params) (e : Event) : Prop :=
  ∀ a bs, e.kind = .nc a bs → NcInputFootprint P a

namespace NcInputEvent

theorem mainLength {P : Params} {e : Event} {ptr row : Nat} {bs : List (Option Byte)}
    (hp : P.topkLenBase = some ptr) (hRow : row < P.b)
    (he : e.kind = .nc {loc := ⟨.global, 0, ptr + 4 * row⟩, size := 4} bs) : NcInputEvent P e := by
  intro a _ hk
  cases (Kind.nc.inj (he.symm.trans hk)).1
  exact .mainLength hp ⟨rfl, by simp, by simp; omega⟩

theorem extraLength {P : Params} {e : Event} {ptr row : Nat} {bs : List (Option Byte)}
    (hp : P.extraTopkLenBase = some ptr) (hRow : row < P.b)
    (he : e.kind = .nc {loc := ⟨.global, 0, ptr + 4 * row⟩, size := 4} bs) : NcInputEvent P e := by
  intro a _ hk
  cases (Kind.nc.inj (he.symm.trans hk)).1
  exact .extraLength hp ⟨rfl, by simp, by simp; omega⟩

theorem sink {P : Params} {e : Event} {ptr row : Nat} {bs : List (Option Byte)}
    (hp : P.sinkBase = some ptr) (hRow : row < 64)
    (he : e.kind = .nc {loc := ⟨.global, 0, ptr + 4 * row⟩, size := 4} bs) : NcInputEvent P e := by
  intro a _ hk
  cases (Kind.nc.inj (he.symm.trans hk)).1
  exact .sink hp ⟨rfl, by simp, by simp; omega⟩

end NcInputEvent
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
