-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.At574
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
import Kernels.InklingRelDecode.Proof.Common.BaseWord
public import Kernels.InklingRelDecode.Proof.Common.LaunchRounds
import Lemmas.Kernel.FrameU

@[expose] public section

/-! # The state of the lane at its first softmax event

A clean event at position 574 of a data lane is fired at a softmax state of the value machine
(`soft_574`), whose entry has the zero base word (`recorded_zero`) and the launch's request
numbers and bases (`reached_numbers`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem entOk_of {w : Value} {ent : Control.Entry} (hp : Pre Q L m) (zero : ent.base = b32 0)
    (nums : EntryNumbers Q L g w ent) : EntOk ent := by
  obtain ⟨⟨d, rfl⟩, -, -⟩ := nums
  exact ⟨zero, hp.relAlign, hp.oAlign, hp.lseAlign⟩

/-- **The state at the first softmax event**: a softmax state with an entry the window accepts. -/
theorem entry_state (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) {j : Nat} {e1 : Event}
    (he1 : X.get (g, j + 1) = some e1) (clean : ∀ f, e1.kind ≠ .ub f)
    (nu : Frame.NoUbBefore X g (j + 1)) (h574 : e1.pc = 574) :
    ∃ w ent s n, Frame.stateAt (lateThread Q L) X g (j + 1) = some (some (softSt w ent s n)) ∧
      EntOk ent := by
  have hg := Frame.lt_of_get hX he1
  have hC : ∀ g < L.threads, (lateThread Q L g).SoundU := fun g hg => lateThread_sound hp hg
  obtain ⟨dk, hdk, -⟩ := Frame.good_stateU (C := lateThread Q L)
    (J := fun g σ => guardedTable Q L g (lateErase Q L g σ)) hC hX he1
    (fun pc f h => clean f (congrArg Event.kind h)) (lateFollowed hf hg (j + 1))
  have pos := Frame.event_pcU hC hX he1 hdk clean
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_siteU hC hX he1 hdk clean
  obtain ⟨w, ent, s, n, rfl⟩ := soft_574 hinv (pos.symm.trans h574)
  refine ⟨w, ent, s, n, hdk, ?_⟩
  have hk : j + 1 ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he1).1.le
  have hs := Frame.stateAt_map_some lateThread_stepMap hdk
  exact entOk_of hp (recorded_zero hp hX base hk nu hs) (reached_numbers hp hX hg hk hs)

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
