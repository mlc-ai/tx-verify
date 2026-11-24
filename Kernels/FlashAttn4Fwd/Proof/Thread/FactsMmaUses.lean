-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaSteps
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaDesc
public import Kernels.FlashAttn4Fwd.Proof.Interface.MmaUses

@[expose] public section

/-! # The ring uses the MMAs read

An MMA of block `b`, trip `t` and item `i` reads the KV ring use `2 n i + u` of its block (`u` =
0 for the first K's blocks, `2 + 2 t` for the loop's K blocks, `1 + 2 t` for the V blocks), in slot
`(2 n i + u) % 6`. Before it the thread released `2 n i + rv b t` ring uses (`Counts.kvEmpty`),
which is `2 u'` or `2 u' - 1` for a QK MMA of score tile `u'` and `2 u' + 1` for a PV MMA of tile
`u'`: so its commits to its slot's empty barrier count the slot's earlier uses. Before a QK MMA
it committed once per earlier item to each Q stage's empty barrier (`Counts.qEmpty`). With
`n = kvBlocks P` (`kvBlocks_eq`) these are the fields of `MmaUseFacts`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Mma

/-- KV-empty commits (released ring uses) before MMA block `b` of the item (beyond `2 n i`). -/
def rv : Fin 8 → Nat → Nat
  | 0, _ => 0
  | 1, _ => 0
  | 5, t => 2 + 2 * t
  | _, t => 1 + 2 * t

theorem relA_eq (b j : Fin 8) (t : Nat) :
    relA (.mma b j) + 2 * (t * (Site.mma b j).loop) = rv b t := by
  fin_cases b <;> fin_cases j <;>
    simp [relA, rv, Site.after, Site.inTrip, Site.loop, Site.ord, mmaOrd, isPv]

theorem qeA_qk (k : Fin 2) {b : Fin 8} (hp : isPv b = false) (j : Fin 8) :
    qeA k (.mma b j) = 0 := by
  fin_cases k <;> fin_cases b <;> simp [isPv] at hp <;> fin_cases j <;>
    simp [qeA, Site.after, Site.ord, mmaOrd, isPv]

end Mma

namespace MmaSt

variable {g k : Nat} {d : Mma.D} {b j : Fin 8}

/-- The KV-empty commits of slot `s` before it. -/
theorem kvEmpty (h : MmaSt L X g k d b j) (s : Fin 6) :
    ringCommits L X g (.kvEmpty s) k =
      Mma.slots (2 * (Mma.trips L * d.i) + Mma.rv b d.t) s := by
  unfold ringCommits
  rw [show (FBar.kvEmpty s).loc L (ctaOf L g) = Mma.bar L g (.kvEmpty s) from rfl,
    h.counts.kvEmpty h.leadTake s]
  unfold Mma.cnt
  rw [h.site, Nat.add_assoc, Mma.relA_eq]
  ring_nf

/-- The Q-empty commits of stage `st` before a QK MMA. -/
theorem qEmpty (h : MmaSt L X g k d b j) (hp : Mma.isPv b = false) (st : Fin 2) :
    ringCommits L X g (.qEmpty st) k = d.i := by
  unfold ringCommits
  rw [show (FBar.qEmpty st).loc L (ctaOf L g) = Mma.bar L g (.qEmpty st) from rfl,
    h.counts.qEmpty h.leadTake st]
  unfold Mma.cnt
  rw [h.site, Mma.qeA_qk st hp]
  ring

end MmaSt

/-- **The field `MmaUseFacts.qk`.** -/
theorem MmaUseFacts_qk (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {cell : Cell} {st : Nat} (hst : st < 2) (hi : X.MmaIssue i d s acc mask)
    (hc : X.MmaCell i cell) (hS : InS st cell) :
    ∃ sl : Fin 6, sl.val % 2 = 0 ∧
      s.a = kMajorDesc (qStepStart L ⟨st, hst⟩ (qkStep L X i.1 st i.2)) ∧
      s.b = kMajorDesc (kStepStart L sl (qkStep L X i.1 st i.2)) ∧
      ringCommits L X i.1 (.qEmpty ⟨st, hst⟩) i.2 = sCommits L X i.1 st i.2 / kvBlocks P ∧
      6 * ringCommits L X i.1 (.kvEmpty sl) i.2 + sl.val = 2 * sCommits L X i.1 st i.2 := by
  obtain ⟨g, k⟩ := i
  obtain ⟨dd, b, j, h, -, rfl, -, -⟩ := mmaSt_of hpre hX ht hi
  obtain ⟨hp, rfl⟩ := (h.inS_iff hst).mp ⟨cell, hc, hS⟩
  have hfin : (⟨(Mma.mmaStage b).val, hst⟩ : Fin 2) = Mma.mmaStage b := Fin.ext rfl
  rw [hfin, qkStep_eq hpre hX ht h hp, h.qEmpty hp, h.sCommits, kvBlocks_eq hpre]
  have hn := trips_pos hpre
  have hsv := Mma.sv_own_lt hp h.tripAt hn
  refine ⟨Mma.kSlot L dd b, ?_, by simp [Mma.mmaSpec, hp], by simp [Mma.mmaSpec, hp], ?_, ?_⟩
  · unfold Mma.kSlot
    split
    · rw [Mma.slotOf_mod]
    · rw [Mma.slotOf_mod]; omega
  · rw [show Mma.trips L * dd.i + Mma.sv (Mma.mmaStage b) b dd.t =
      Mma.sv (Mma.mmaStage b) b dd.t + Mma.trips L * dd.i by ring,
      Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hsv, Nat.zero_add]
  · rw [h.kvEmpty]
    have htrip := h.tripAt
    unfold Mma.TripAt at htrip
    have hsl : (Mma.kSlot L dd b).val =
        (2 * (Mma.trips L * dd.i) + if b.val < 2 then 0 else 2 + 2 * dd.t) % 6 := by
      unfold Mma.kSlot
      split <;> simp [Mma.slotOf, Mma.kvSlot, Mma.kvUse, Mma.kvBase, Nat.mul_assoc, *]
    unfold Mma.slots
    rw [hsl]
    generalize Mma.trips L * dd.i = m
    fin_cases b <;> simp [Mma.isPv] at hp <;> simp [Mma.rv, Mma.sv, Mma.mmaStage] at htrip ⊢ <;>
      omega

/-- **The field `MmaUseFacts.pv`.** -/
theorem MmaUseFacts_pv (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {cell : Cell} {st : Nat} (_hst : st < 2) (hi : X.MmaIssue i d s acc mask)
    (hc : X.MmaCell i cell) (hO : InO st cell) :
    ∃ sl : Fin 6, sl.val % 2 = 1 ∧
      s.b = mnMajorDesc (vStepStart L sl (pvStep L X i.1 st i.2)) ∧
      6 * ringCommits L X i.1 (.kvEmpty sl) i.2 + sl.val =
        2 * (pPolls L X i.1 st i.2 - 1) + 1 := by
  obtain ⟨g, k⟩ := i
  obtain ⟨dd, b, j, h, -, rfl, -, -⟩ := mmaSt_of hpre hX ht hi
  obtain ⟨hp, rfl⟩ := h.inO_iff.mp ⟨cell, hc, hO⟩
  rw [pvStep_eq hpre hX ht h hp, h.pPolls, Mma.pv_own hp]
  refine ⟨Mma.vSlot L dd, ?_, by simp [Mma.mmaSpec, hp], ?_⟩
  · unfold Mma.vSlot
    rw [Mma.slotOf_mod]
    omega
  · rw [h.kvEmpty]
    have htrip := h.tripAt
    unfold Mma.TripAt at htrip
    have hsl : (Mma.vSlot L dd).val = (2 * (Mma.trips L * dd.i) + (1 + 2 * dd.t)) % 6 := by
      simp [Mma.vSlot, Mma.slotOf, Mma.kvSlot, Mma.kvUse, Mma.kvBase, Nat.mul_assoc]
    unfold Mma.slots
    rw [hsl]
    generalize Mma.trips L * dd.i = m
    fin_cases b <;> simp [Mma.isPv] at hp <;> simp [Mma.rv] at htrip ⊢ <;> omega

/-- **The thread layer's facts of the MMAs' shared-memory descriptors.** -/
theorem mmaSmemFacts (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) : MmaSmemFacts L X where
  qk := MmaSmemFacts_qk hpre hX ht
  pv := MmaSmemFacts_pv hpre hX ht

/-- **The thread layer's facts of the MMAs' K steps.** -/
theorem mmaStepFacts (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) : MmaStepFacts P L X where
  qk_step := MmaStepFacts_qk_step hpre hX ht
  pv_step := MmaStepFacts_pv_step hpre hX ht
  pv_next := MmaStepFacts_pv_next hpre hX ht
  pv_a := MmaStepFacts_pv_a hpre hX ht

/-- **The thread layer's facts of the ring uses the MMAs read.** -/
theorem mmaUseFacts (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) : MmaUseFacts P L X where
  qk := MmaUseFacts_qk hpre hX ht
  pv := MmaUseFacts_pv hpre hX ht

end
end PTX.Kernels.FlashAttn4Fwd.Proof
