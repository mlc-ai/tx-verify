-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionAll
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCounts

@[expose] public section

/-! # The end of the correction warps

The end barrier (`bar.arrive 2, 416`) continues at the `ret`, which ends the thread. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- **The end barrier**, then the exit. -/
theorem step_barEnd {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : D} {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hs : d.site = .barEnd) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    Ev L g d e ∧ Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_barArrive_4)
  obtain ⟨rfl, rfl⟩ := fires_barArrive_imm (id := 2) (n := 416) (by decide) (by decide)
    (by decide) (by decide) (by rw [hpre.block]; decide) hf
  refine ⟨⟨rfl, rfl⟩, step_of_run (d' := ⟨.exit, i, tt, aw, a, o⟩) (by simp [next])
    (inv_same (d := ⟨.barEnd, i, tt, aw, a, o⟩) _ hi rfl
      (.inr (.inl (hi.tail rfl (by simp) (by simp) (by simp)))) (by simp [Site.inTrip])
      (by simp [Site.rescale]) (by simp)) rfl ⟨0, ?_⟩⟩
  corr_seg (At.next h) hpre

/-- **The exit**: `ret` ends the thread; no event continues. -/
theorem step_exit {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .exit) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : False := by
  rw [hs] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
  simp [eventTmpl, Fires] at hf

/-- The exit's event is the thread's exit. -/
theorem ev_exit {L : Launch} {g : Nat} {d : D} {t : TState} {e : Event} {ins : Instr}
    {o : Option TState} (hs : d.site = .exit) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) : Ev L g d e := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs hc hf ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
  simp only [eventTmpl, Fires] at hf
  rw [hf.1]
  exact ⟨rfl, rfl⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
