-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.GlobalWrites
public import Kernels.TmlFa4Fwd.Proof.Lib.OutputGeom
public import Kernels.TmlFa4Fwd.Proof.Lib.ScheduleCoords
public import Lemmas.TensorStore.StoreWrite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The global write frame

Every global write is of the O region or of an LSE word, from the output stores' boxes
(`issuedBox`) and the LSE words' addresses (`outputIntentFootprint_of_sites`); so no write is of an
input byte (`OutputIntentFootprint.noInputWrite`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow TensorDescriptor PTX.Kernels.TmlFa4Fwd.Epilogue

noncomputable section

/-- The footprints of pending global output writes obey the same frame. -/
def OutputIntentFootprint (p : Params) (X : Execution) : Prop :=
  ∀ w a loc, X.Intent w a true → a.Covers loc → loc.space = .global →
    p.oRegion.Contains loc ∨
      ∃ q < p.totalQ, ∃ h < p.heads, ∃ k < 4, loc = (p.lseLoc q h).at k

private theorem region_not_both {a b : Region} {loc : Loc} (h : a.Apart b)
    (ha : a.Contains loc) (hb : b.Contains loc) : False := by
  rcases h with h | h
  · exact (Nat.not_lt_of_ge (h.trans hb.2.2.1)) ha.2.2.2
  · exact (Nat.not_lt_of_ge (h.trans ha.2.2.1)) hb.2.2.2

/-- **The write frame excludes the input assumption's undefined behaviour**: every global
write is in the O or LSE region, which every parameter set of the launch keeps apart from its
input arrays. -/
theorem OutputIntentFootprint.noInputWrite {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (h : OutputIntentFootprint p X) :
    ¬ Assumptions.inputReadOnly.ub l m X := by
  rintro ⟨w, a, loc, hw, hc, P, hP, r, hr, hl⟩
  obtain ⟨hO, hL⟩ := outputs_pinned hp hP
  rcases h w a loc hw hc hl.1 with ho | ⟨q, hq, head, hh, k, hk, rfl⟩
  · exact region_not_both (hP.separate.2 r hr).1 (hO ▸ ho) hl
  · exact region_not_both (hP.separate.2 r hr).2 (hL ▸ lseByte_in hq hh hk) hl

/-- Physical output boxes described by the selected work item. -/
def OutputBoxSpec (p : Params) (l : Launch) (X : Execution) : Prop :=
  ∀ i addr s, X.TensorStoreIssue i addr s →
    ∃ batch < p.batch, ∃ head < p.heads, ∃ (tile : Nat) (stage : Fin 2) (box : Fin 4),
      s = Epilogue.writebackStoreSpec p l i.1 batch head tile stage box

/-- Scalar global output writes address a whole LSE word. -/
def LseWriteSpec (p : Params) (X : Execution) : Prop :=
  ∀ i a bytes, X.Writes i a bytes → a.loc.space = .global →
    ∃ row < p.totalQ, ∃ head < p.heads, a.loc = p.lseLoc row head ∧ a.size = 4

private theorem coveredLseByte {p : Params} {a : Acc} {loc : Loc} {q head : Nat}
    (hAt : a.loc = p.lseLoc q head) (hSize : a.size = 4) (hc : a.Covers loc) :
    ∃ k < 4, loc = (p.lseLoc q head).at k := by
  let k := loc.addr - a.loc.addr
  have hk : k < 4 := by
    have hb := hc.2.2.2
    dsimp [k]
    omega
  have heq : loc = a.loc.at k := by
    obtain ⟨sp, cta, addr⟩ := loc
    rcases a with ⟨⟨baseSpace, baseCTA, baseAddr⟩, _, _, _, _, _, _⟩
    obtain ⟨h₁, h₂, h₃, _⟩ := hc
    change Loc.mk sp cta addr = Loc.mk baseSpace baseCTA (baseAddr + k)
    change baseAddr ≤ addr at h₃
    have hK : k = addr - baseAddr := rfl
    rw [Loc.mk.injEq]
    exact ⟨h₁, h₂, by omega⟩
  exact ⟨k, hk, heq.trans (congrArg (fun a => a.at k) hAt)⟩

/-- Each global write covers a word of LSE or individual bytes of O. -/
theorem outputIntentShape {p : Params} {l : Launch} {m : Mem0} {A : List Assumption}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l Decoded.kernel A m X)
    (hLse : LseWriteSpec p X) (hTensor : OutputBoxSpec p l X)
    {w : AsyncCopy.Ref} {a : Acc} (hw : X.Intent w a true) (hs : a.loc.space = .global) :
    (∃ q < p.totalQ, ∃ head < p.heads, a.loc = p.lseLoc q head ∧ a.size = 4) ∨
      (a.size = 1 ∧ p.oRegion.Contains a.loc) := by
  rcases globalWriteIntentSources hX hw hs with
      ⟨i, site, bytes, _, _, he⟩ | ⟨i, x, y, k, site, addr, s, _, _, he, hLoc, hSize⟩
  · exact .inl (hLse i a bytes ⟨site, he⟩ hs)
  · obtain ⟨batch, hb, head, hh, tile, stage, box, rfl⟩ := hTensor i addr s ⟨site, he⟩
    have hDest := writebackWriteLoc hp (g := i.1) (tile := tile) stage box x y k hb hh
    simp only at hDest
    rw [hDest] at hLoc
    by_cases h : x < 32 ∧ y < 128 ∧ k < 4 ∧ Epilogue.stageRow tile stage + y < p.qLength batch
    · rw [ite_eq_left h, Option.some.injEq] at hLoc
      have hRow := packedRow_lt hp hb h.2.2.2
      have hCol : 32 * box.val + x < 128 := by have := box.isLt; omega
      exact .inr ⟨hSize, hLoc ▸ outputByte_in hRow hh hCol h.2.2.1⟩
    · simp [h] at hLoc

/-- The observed output descriptors and LSE addresses determine the global write frame. -/
theorem outputIntentFootprint_of_sites {p : Params} {l : Launch} {m : Mem0} {A : List Assumption}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l Decoded.kernel A m X)
    (hLse : LseWriteSpec p X) (hTensor : OutputBoxSpec p l X) :
    OutputIntentFootprint p X := by
  intro w a loc hw hc hs
  have hSpace : a.loc.space = .global := hc.1.symm.trans hs
  rcases outputIntentShape hp hX hLse hTensor hw hSpace with
    ⟨q, hq, head, hh, hAt, hSize⟩ | ⟨hSize, ho⟩
  · exact .inr ⟨q, hq, head, hh, coveredLseByte hAt hSize hc⟩
  · exact .inl (Acc.loc_of_one hc hSize ▸ ho)

/-- Every output box warp 13 issues is a box of the output of a request and head. -/
theorem issuedBox {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {addr : Nat}
    {spec : TensorStore.Spec} (hw : Prologue.warpIndex l i.1 = 13)
    (hIssue : X.TensorStoreIssue i addr spec) :
    ∃ batch < p.batch, ∃ head < p.heads, ∃ (tile : Nat) (stage : Fin 2) (box : Fin 4),
      spec = writebackStoreSpec p l i.1 batch head tile stage box := by
  obtain ⟨-, b, hb, st, bx, hlo, hhi, rfl⟩ := Proof.Epilogue.store_issue hp hX hw hIssue
  exact ⟨b, hb, _, (Epilogue.assignedCoordinates_valid hp hlo hhi).2, _, st, bx, rfl⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof
