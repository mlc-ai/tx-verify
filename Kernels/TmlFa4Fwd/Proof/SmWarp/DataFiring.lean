-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.DataEvent
import Kernels.TmlFa4Fwd.Proof.Common.DataSound

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
open PTX.Flow Softmax

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g i : Nat}

/-- Recover the softmax value state at a live position of its control machine. -/
theorem lift_state (hp : Pre p L m) {d n}
    (hc : Frame.stateAt (thread p L) X g i = some (some (sinj p L g d n)))
    (hl : ∃ σ, Frame.stateAt (threadD p L) X g i = some (some σ)) :
    ∃ v : D, Frame.stateAt (threadD p L) X g i = some (some (.inr ⟨.softmax,v⟩,n)) ∧
      Control.erase v = d := by
  obtain ⟨⟨s,c⟩, hs⟩ := hl
  have eq := Option.some.inj (Option.some.inj ((control_of_data hp hs).symm.trans hc))
  have hn : c = n := congrArg Prod.snd eq
  subst c
  cases s with
  | inl s => cases eq
  | inr a =>
    obtain ⟨r,v⟩ := a
    cases r <;> cases eq
    exact ⟨v,hs,rfl⟩

theorem data_firing (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {d : D} {n e} (he : X.get (g,i) = some e)
    (hs : Frame.stateAt (threadD p L) X g i = some (some (.inr ⟨.softmax,d⟩,n))) :
    ∃ t o, (codeD p L g).AtD d t ∧ Fires d.site.pc ((codeD p L g).tmpl (some d) t) e o := by
  obtain ⟨t, ins, o, hat, _, hc, hf⟩ :=
    Frame.fired_site (fun _ hg => threadD_sound hp hg) hX he hs
  change kernel.code[d.site.pc]? = some ins at hc
  refine ⟨t, o, hat, ?_⟩
  change Fires _ (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op | none => .ub .pcOutOfRange) e o
  rw [hc]
  exact hf

end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
