-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global
public import Lemmas.Protocol.RegionOrder

@[expose] public section

/-! # The read-only global memory and local memory

No write is of a global byte outside the O and LSE regions, so the input arrays have no conflict
(`input_ordered`). A local byte is accessed by one thread, so its conflicts are ordered by program
order (`local_ordered`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
  (hFw : Follow p L X)
include hp hX hFw

/-- **The global bytes outside the output and the LSE have no conflict.** -/
theorem input_ordered : ConflictsOrdered L X fun l =>
    l.space = .global ∧ ¬ p.oRegion.Contains l ∧ ¬ p.lseRegion.Contains l :=
  .of_none fun e f a b l hcon ha hb ⟨hs, ho, hl⟩ => by
    obtain ⟨-, we, wf, he, hf, hw, -⟩ := hcon
    rcases hw with rfl | rfl
    · exact (global_write_region hp hX hFw he ha hs).elim ho hl
    · exact (global_write_region hp hX hFw hf hb hs).elim ho hl

/-- A local access is its thread's. -/
theorem local_access (hS : CpSrc p X) {r : Ref} {a : Acc} {w : Bool} {l : Loc}
    (hi : X.Intent r a w) (hc : a.Covers l) (hl : l.space = .local) :
    ∃ k, r = .thread (l.cta, k) ∧ k < (X.tr l.cta).length ∧
      (X.get (l.cta, k)).bind Event.acc = some a := by
  have hs : a.loc.space = .local := hc.1.symm.trans hl
  have hns : a.loc.space ≠ .shared := by rw [hs]; decide
  obtain ⟨g, k, rfl, o, hloc, -⟩ : ∃ g k, r = .thread (g, k) ∧ LocalAt L g a := by
    cases w with
    | true =>
      rcases outside_write hp hX hFw hi hns with h | h
      · rw [hs] at h; cases h
      · exact h
    | false =>
      rcases outside_read hp hX hFw hi hns with ⟨-, h⟩ | h | ⟨i, sp, hcp, rfl⟩ | ⟨-, h⟩
      · rcases h with ⟨_, -, h⟩ | ⟨_, -, h⟩ | ⟨_, -, _, -, h⟩ <;> (rw [h] at hs; cases hs)
      · exact h
      · obtain ⟨_, -, _, -, _, -, _, -, _, -, h | h⟩ := hS i sp l hcp hc <;>
          (rw [h] at hl; cases hl)
      · rcases h with ⟨_, -, _, -, _, -, _, -, h⟩ | ⟨_, -, _, -, _, -, _, -, h⟩ <;>
          (rw [h] at hs; cases hs)
  have hcta : l.cta = g := by rw [hc.2.1, hloc]
  rw [hcta]
  refine ⟨k, rfl, ?_⟩
  rcases hi with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨o', n, pc, he⟩ <;>
    exact ⟨(List.getElem?_eq_some_iff.mp he).1, by rw [he]; rfl⟩

/-- **Local memory is ordered.** -/
theorem local_ordered (hS : CpSrc p X) : ConflictsOrdered L X fun l => l.space = .local := by
  intro e f a b l hcon ha hb hl
  obtain ⟨hne, we, wf, he, hf, -, -⟩ := hcon
  obtain ⟨i, rfl, hil, hia⟩ := local_access hp hX hFw hS he ha hl
  obtain ⟨j, rfl, hjl, hja⟩ := local_access hp hX hFw hS hf hb hl
  rcases Nat.lt_trichotomy i j with h | rfl | h
  · exact .inl (.of_base L (.single (.inl ⟨rfl, h, hjl,
      fun hs => hs.not_overlap rfl h hia hja ⟨l, ha, hb⟩⟩)))
  · exact (hne rfl).elim
  · exact .inr (.of_base L (.single (.inl ⟨rfl, h, hil,
      fun hs => hs.not_overlap rfl h hja hia ⟨l, hb, ha⟩⟩)))

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
