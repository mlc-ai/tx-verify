-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
public import Kernels.InklingRelDecode.Proof.Common.Roles
public import Kernels.InklingRelDecode.Proof.Common.Table
public import Lemmas.Flow.StrictWindow
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import all Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.Sound
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Kernels.InklingRelDecode.Proof.Common.Staged.Early
import Lemmas.Kernel.NoUbStrictLane
import Lemmas.Kernel.FrameU
import Lemmas.Flow.StrictLift

@[expose] public section

/-! # No undefined behaviour in a lane whose states are the startup and a role's

The skeleton `Frame.noUb_strict_lane` on the thread machine, with the startup's states handled
here (strict by the startup's steps, safe by `Startup.safe_site`, live by `Startup.live_site` and
the base word's read) and the states of the rest of the lane's roles supplied by the caller. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- **The first undefined-behaviour event of a lane is not one**: its states are the startup's
or satisfy `Rest`, whose steps are strict, whose templates are safe, and which die only on the
exit. -/
theorem lane_noUb (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) (hg : g < L.threads)
    (he : X.get (g, k) = some e) {Rest : (thread Q L g).D → Prop}
    (hR : ∀ j d, j < k → Frame.stateAt (thread Q L) X g j = some (some d) →
      (∃ s n, d = (.inl s, n)) ∨ Rest d)
    (hRk : ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) → e.pc = (thread Q L g).pc σ →
      (∃ s n, σ = (.inl s, n)) ∨ Rest σ)
    (strict : ∀ j dj ej, Rest dj → X.get (g, j) = some ej →
      Frame.stateAt (thread Q L) X g j = some (some dj) → Frame.NoUbBefore X g (j + 1) →
      (thread Q L g).StepFor dj ej)
    (safe : ∀ σ t ins, Rest σ → Frame.stateAt (thread Q L) X g k = some (some σ) →
      guardedTable Q L g σ → e.pc = (thread Q L g).pc σ → (thread Q L g).Good (some σ) t →
      kernel.code[(thread Q L g).pc σ]? = some ins →
      ∀ f, eventTmpl Assumptions.all L g t ins.op ≠ .ub f)
    (live : ∀ i d v, Rest d → X.get (g, i) = some v →
      Frame.stateAt (thread Q L) X g i = some (some d) → guardedTable Q L g d →
      Frame.NoUbBefore X g (i + 1) → (thread Q L g).next d v = none → v.kind = .exit)
    (f : Fault) : e.kind ≠ .ub f := by
  have hC : ∀ g < L.threads, (thread Q L g).SoundU := fun g hg => thread_sound hp hg
  have hglue : Code.Handoff (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) := by
    apply Code.handoff_gated
    · exact fun d r h _ => stub_at d r h
    · intro d r i t hr hs hat hinv
      exact thread_handoff d r i t hr hs hat hinv
  refine Frame.noUb_strict_lane (C := thread Q L) (J := guardedTable Q L)
    (R := fun d => (∃ s n, d = (Sum.inl s, n)) ∨ Rest d) hC hX (hf g hg) he ?strict ?safe ?live
    hR f
  case strict =>
    rintro j dj ej (⟨s, n, rfl⟩ | hr) hej hd nuj
    · exact Code.counted_stepFor (Code.glue_inl_stepFor (fun hx =>
        (startup_steps hp s (Code.gatedExit_none.mp hx)).stepFor ej) hglue) n
    · exact strict j dj ej hr hej hd nuj
  case safe =>
    intro σ t ins hσ hJ hpc hgood hc f'
    rcases hRk σ hσ hpc with ⟨s, n, rfl⟩ | hr
    · obtain ⟨hat, hinv⟩ := hgood
      have hx : Startup.enterOf s = none := Code.gatedExit_none.mp hinv.2
      exact Startup.safe_site (by rw [hp.block]) (Startup.sharedOk_of_pre hp) hat
        (fun r h => by simp [Startup.enterOf, h] at hx) hc f'
    · exact safe σ t ins hr hσ hJ hpc hgood hc f'
  case live =>
    rintro i d v (⟨s, n, rfl⟩ | hr) hv hd hJ nui hn
    · have hik : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp hv).1
      have nui' : Frame.NoUbBefore X g i := fun u hu => nui u (by omega)
      have hx : Startup.enterOf s = none :=
        Code.gatedExit_none.mp (reached_table hf hg nui' hd).1.2
      have hu : ∀ f, v.kind ≠ .ub f := fun f => nui i (by omega) v hv f
      obtain ⟨t, ins, o, hat, hi, hc, hfi⟩ := Frame.fired_siteU hC hX hv hd hu
      have ev := Startup.shape hp hat hi.1 hc hfi hu
      rw [next_start] at hn
      have hs : Startup.succ L g s v = none := by
        cases h : Startup.succ L g s v with
        | none => rfl
        | some _ => rw [h] at hn; cases hn
      refine absurd hs (Startup.live_site (fun r h => by simp [Startup.enterOf, h] at hx) ev ?_)
      intro hl ac bs hvv hloc hsz
      subst hvv
      exact base hv hloc hsz
    · exact live i d v hr hv hd hJ nui hn

end
end PTX.Kernels.InklingRelDecode.Proof
