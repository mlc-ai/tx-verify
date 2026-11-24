-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotTensor

@[expose] public section

/-! # The box of a tensor load

A proof tool. A unicast tensor load through a cluster address issues a copy whose box is the
map's descriptor (in the load's mode) at the destination the destination operand resolves to,
with the map's rank, the mode's row coordinates, cluster addressing and the instruction's CTA
group (`fires_cpTensor_box`). -/

namespace PTX.Flow
open PTX

noncomputable section

/-- The copy a tensor load prepares: its shared destination, addressing and group. -/
theorem tensorLoadCopy_box {L : Launch} {g : Nat} {t : TState} {ca grp : Bool} {dst mb : Nat}
    {off moff : Int} {map : Opnd} {cs : List Opnd} {lm : TensorMode} {a : Nat}
    {s : TensorCopy.Spec} (h : tensorLoadCopy L g t ca grp dst off map cs mb moff lm = .ok (a, s)) :
    sharedEffAddr L g t ca dst off = .ok s.sharedBase ∧ s.clusterAddress = ca ∧
      s.group = (if grp then .two else .one) := by
  unfold tensorLoadCopy at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  rcases hm : tensorMap L g t map cs lm with f | ⟨a', outer, d⟩ <;> rw [hm] at h
  · cases h
  rcases hd : sharedEffAddr L g t ca dst off with f | dl <;> simp only [hd] at h
  · cases h
  repeat' (split at h <;> (try (cases h; done)))
  all_goals (cases h; refine ⟨rfl, rfl, ?_⟩; try simp_all)

/-- **A tensor load's box.** A unicast tensor load through a cluster address issues the copy of
the map at the address its map operand evaluates to: the map's rank and descriptor (in the load's
mode), the mode's row coordinates, the destination its operand resolves to, cluster addressing
and the instruction's CTA group. -/
theorem fires_cpTensor_box {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {grp : Bool} {dst mb : Nat} {off moff : Int} {map : Opnd} {cs : List Opnd} {lm : TensorMode}
    {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.cpTensor true grp dst off map cs mb moff none lm)) e
      (some u)) :
    ∃ a s, e = ⟨pc, .tensorIssue a s⟩ ∧ tensorMapAddress L g t map = .ok a ∧
      (∃ d, L.tensorMaps a = some ⟨s.outer, d⟩ ∧ s.descriptor = lm.transfer d) ∧
      (s.rows = none ↔ lm = .tile) ∧
      sharedEffAddr L g t true dst off = .ok s.sharedBase ∧ s.clusterAddress = true ∧
      s.group = (if grp then .two else .one) := by
  have hf' : Fires pc (tensorTmpl L g t (.cpTensor true grp dst off map cs mb moff none lm)) e
      (some u) := hf
  rcases tensorTmpl_cpTensor_unicast (L := L) (g := g) (t := t) (ca := true) (grp := grp)
    (dst := dst) (mb := mb) (off := off) (moff := moff) (map := map) (cs := cs) (lm := lm) with
    ⟨f, hT⟩ | ⟨a, s, hT⟩
  · rw [hT] at hf'
    simp [Fires] at hf'
  · rw [hT] at hf'
    obtain ⟨rfl, -⟩ := hf'
    obtain ⟨hcopy, -⟩ := tensorTmpl_unicast_issue hT
    obtain ⟨hma, -, d, hd, -, hdesc, hrows⟩ := tensorLoadCopy_ok hcopy
    obtain ⟨hdst, hca, hgrp⟩ := tensorLoadCopy_box hcopy
    exact ⟨a, s, rfl, hma, ⟨d, hd, hdesc⟩, hrows, hdst, hca, hgrp⟩

end

end PTX.Flow
