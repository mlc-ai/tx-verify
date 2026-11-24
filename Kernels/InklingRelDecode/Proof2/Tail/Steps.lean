-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Tail.Machine
public import Kernels.InklingRelDecode.Proof.Thread.SmDischarge

@[expose] public section

/-! # The steps of the softmax–epilogue fragment

Every state of `Tail.code` meets its step obligation (`stepAt`): a softmax state by the flat
region's `Code.StepAt` (`DComp.smStepAt`, with the score stage's sites and the loop's exit from
`SmDischarge`, whose one launch premise, the row slack, is a field of the entry numbers' `Ent.Ok`),
the event that ends the loop through the bridge (`Br.bridge`) into the epilogue's first state, and
an epilogue state by `Epi.stepAt_all`. -/

namespace PTX.Kernels.InklingRelDecode.Proof2.Tail
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The softmax region's obligations: the row slack is a field of `Ent.Ok`. -/
theorem smOb (g : Nat) : Proof.DComp.SmObligations Q L m g :=
  Proof.DComp.smObligations_of_rest ⟨fun _ _ hi => hi.ok.slack⟩

/-- A state whose local steps reach a dead state is dead. -/
theorem dead_of_rtg {u t : TState}
    (hr : Relation.ReflTransGen (Tau kernel Assumptions.all L g) u t)
    (hd : Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) t) :
    Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) u := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact hd
  | head h _ ih => exact Machine.dead_of_tau h ih

/-- **A softmax state.** -/
theorem stepAt_sm (hpre : Pre Q L m) (d0 d : Proof.Sm.D) : (code L g d0).StepAt (.sm d) where
  site hi := (Proof.DComp.smStepAt hpre (smOb (Q := Q) (m := m) g) d).site hi
  step := by
    intro t e u ins h hi hc hf
    have h' : (Proof.Sm.code Proof.Sm.asms L g d).AtD d t := h
    have hso := smOb (Q := Q) (L := L) (m := m) g
    by_cases hl : Proof.DComp.leaves L g d e
    · obtain ⟨hok, t', hr, ht'⟩ := hso.exit hpre hi h' hc hf hl
      have ht2 : At t' 2560 (Proof.Br.exitFacts (Proof.DComp.exitIn L g d)) := by
        rw [Proof.DComp.exitFacts_eq]
        exact ht'
      obtain ⟨hmain, hdead⟩ := Proof.Br.bridge (L := L) (g := g) (Proof.DComp.exitIn L g d) hok ht2
      by_cases hnf : (Proof.DComp.exitIn L g d).NoFault
      · obtain ⟨t'', hr2, ht''⟩ := hmain hnf
        refine .inl (.inr ⟨.epi (Proof.Epi.D.entry (Proof.Br.prm (Proof.DComp.exitIn L g d))
          (Proof.DComp.exitIn L g d).skip), t'', ?_, hr.trans hr2,
          ⟨ht''.1, ht''.2.1, ht''.2.2.1, ht''.2.2.2.1, ht''.2.2.2.2⟩,
          Proof.Epi.entry_inv _ (Proof.Br.prm_ok _ hok) (Or.inl rfl) _, rfl⟩)
        show next L g (.sm d) e = _
        simp [next, hl, exitNext, hnf]
      · refine .inr ⟨?_, dead_of_rtg hr (hdead hnf)⟩
        show next L g (.sm d) e = none
        simp [next, hl, exitNext, hnf]
    · rcases (Proof.DComp.smStepAt hpre hso d).step ins h' hi hc hf with
        (hn | ⟨d', t', hn, hr, hg'⟩) | ⟨hn, hd⟩
      · refine .inl (.inl ?_)
        have hn' : Proof.Sm.next L g d e = some none := hn
        show next L g (.sm d) e = some none
        simp [next, hl, hn']
      · have hn' : Proof.Sm.next L g d e = some (some d') := hn
        refine .inl (.inr ⟨.sm d', t', ?_, hr, hg'⟩)
        show next L g (.sm d) e = _
        simp [next, hl, hn']
      · refine .inr ⟨?_, hd⟩
        have hn' : Proof.Sm.next L g d e = none := hn
        show next L g (.sm d) e = none
        simp [next, hl, hn']

/-- **An epilogue state.** -/
theorem stepAt_epi (d0 : Proof.Sm.D) (d : Proof.Epi.D) : (code L g d0).StepAt (.epi d) where
  site hi := (Proof.Epi.stepAt_all (L := L) (g := g) d d).site hi
  step := by
    intro t e u ins h hi hc hf
    have h' : (Proof.Epi.code Proof.Epi.asms L g d).AtD d t := h
    rcases (Proof.Epi.stepAt_all (L := L) (g := g) d d).step ins h' hi hc hf with
      (hn | ⟨d', t', hn, hr, hg'⟩) | ⟨hn, hd⟩
    · refine .inl (.inl ?_)
      have hn' : Proof.Epi.next d e = some none := hn
      show next L g (.epi d) e = some none
      simp [next, hn']
    · have hn' : Proof.Epi.next d e = some (some d') := hn
      refine .inl (.inr ⟨.epi d', t', ?_, hr, hg'.1, hg'.2.1, hg'.2.2⟩)
      show next L g (.epi d) e = _
      simp [next, hn']
    · refine .inr ⟨?_, hd⟩
      have hn' : Proof.Epi.next d e = none := hn
      show next L g (.epi d) e = none
      simp [next, hn']

/-- **Every state of the fragment meets its step obligation.** -/
theorem stepAt (hpre : Pre Q L m) (d0 : Proof.Sm.D) (σ : St) : (code L g d0).StepAt σ := by
  cases σ with
  | sm d => exact stepAt_sm hpre d0 d
  | epi d => exact stepAt_epi d0 d

end
end PTX.Kernels.InklingRelDecode.Proof2.Tail
