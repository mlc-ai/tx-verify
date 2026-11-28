-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Site
public import Kernels.InklingRelDecode.Proof.Softmax.StepAt
public import Lemmas.Flow.Determinism

@[expose] public section

/-! # Where the thread stops after an event

The control machine's step says the thread stops at the successor's position (or is dead). A data
step that follows the code by position, whatever the branches, then knows the position of every
stop it reaches. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- **Every stop after the event is at the successor's position**, or the thread is dead. -/
theorem stops_pc {d d' : D} {t u : TState} {ev : Event} {ins : Instr}
    (hat : (code e L g).AtD d t) (hi : (code e L g).inv d)
    (hc : kernel.code[(code e L g).pc d]? = some ins)
    (hf : Fires ((code e L g).pc d) (eventTmpl Assumptions.all L g t ins.op) ev (some u))
    (hn : (code e L g).next d ev = some (some d')) :
    (∀ t'', Relation.ReflTransGen (Tau kernel Assumptions.all L g) u t'' →
      Stops kernel Assumptions.all L g t'' → t''.pc = (code e L g).pc d') ∨
      Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) u := by
  have htc : (Control.code e L g).AtD d.c t :=
    atD_ctl hat
  obtain ⟨c', hnc0, rfl⟩ := succ_inv hn
  have hnc : (Control.code e L g).next d.c ev = some (some c') := hnc0
  rcases (Control.stepAt (e := e) (L := L) (g := g) d.c).step ins htc hi hc hf with
    (hy | ⟨c2, t', hy, hl, hg⟩) | ⟨hy, hd⟩
  · rw [hnc] at hy; cases hy
  · rw [hnc] at hy
    obtain rfl := Option.some.inj (Option.some.inj hy)
    rcases hg with ⟨hat', hinv'⟩ | hd
    · refine .inl fun t'' hr hs => ?_
      have hs' : Stops kernel Assumptions.all L g t' := by
        obtain ⟨_, _, ho⟩ := site_outU (Control.stepAt (e := e) (L := L) (g := g) _)
          ⟨hat', hinv'⟩
        exact ⟨_, ho⟩
      rw [stop_unique hr hl hs hs']
      exact hat'.1
    · obtain ⟨f, hf'⟩ := hd
      exact .inr ⟨t', f, hl, hf'⟩
  · rw [hnc] at hy; cases hy

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
