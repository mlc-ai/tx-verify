-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Occurs
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Table
import Kernels.InklingRelDecode.Proof.Common.Sound
import Lemmas.Kernel.FrameTrackedU
import Lemmas.Flow.Determinism
import all Kernels.InklingRelDecode.Proof.Common.Follow

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {ev : Event}

/-- **The state that fires an occurring event**, with its instruction and the firing. -/
theorem Occurs.site (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (h : Occurs L X g k ev) (hu : ∀ f, ev.kind ≠ .ub f) :
    ∃ s, Frame.stateAt (thread Q L) X g k = some (some s) ∧ ev.pc = (thread Q L g).pc s ∧
      ∃ t ins o, (thread Q L g).AtD s t ∧ (thread Q L g).inv s ∧
        kernel.code[(thread Q L g).pc s]? = some ins ∧
        Fires ((thread Q L g).pc s) (eventTmpl Assumptions.all L g t ins.op) ev o := by
  rcases h with he | ⟨hg, rfl, nu, t, t1, mm, u, hrun, hl, hout, hfire⟩
  · have hg := Frame.lt_of_get hX he
    obtain ⟨s, hs, _⟩ := Frame.good_stateU (fun g h => thread_sound hp h) hX he
      (fun _ f h => hu f (congrArg Event.kind h)) (hf g hg k)
    obtain ⟨t, ins, u, ht, hI, hc, fire⟩ :=
      Frame.fired_siteU (fun g h => thread_sound hp h) hX he hs hu
    exact ⟨s, hs, Frame.event_pcU (fun g h => thread_sound hp h) hX he hs hu, t, ins, u, ht, hI,
      hc, fire⟩
  · have dead : Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) t → False := by
      rintro ⟨t', f, hl', hout'⟩
      obtain rfl := stop_unique hl hl' ⟨_, hout⟩ ⟨_, hout'⟩
      obtain rfl := Out.ev.inj (hout.symm.trans hout')
      exact hu f (congrArg Event.kind hfire.1)
    cases hst : Frame.stateAt (thread Q L) X g (X.tr g).length with
    | none => exact (dead (Frame.end_deadU (fun g h => thread_sound hp h) hg hrun hst)).elim
    | some o =>
      cases o with
      | none => exact absurd hst (hf g hg _).1
      | some σ =>
        rcases Frame.end_atU (fun g h => thread_sound hp h) hg hrun hst with
          ⟨s, ins, hl', hat, hi, hins, hout'⟩ | hd
        · obtain rfl := stop_unique hl hl' ⟨_, hout⟩ ⟨_, hout'⟩
          obtain rfl := Out.ev.inj (hout.symm.trans hout')
          have hpc : t1.pc = (thread Q L g).pc σ := hat.1
          exact ⟨σ, rfl, hpc ▸ EventFrame.fires_source_pc hfire, _, ins, u, hat, hi, hins,
            hpc ▸ hfire⟩
        · exact (dead hd).elim

end PTX.Kernels.InklingRelDecode.Proof
