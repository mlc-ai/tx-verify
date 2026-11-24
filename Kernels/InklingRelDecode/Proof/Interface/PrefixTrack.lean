-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.PrefixLocal

@[expose] public section

/-!
# What the induction along a thread proves at an event

`Good e` collects what the induction along each thread (`Interface.weakTracked_of`) proves at an
event `e`: the machine is tracked through `e` (`TT`), and a read of input bytes at `e` returns the
launch's bytes (`LaunchRead`). A machine that left its run never comes back (`someNone_mono`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A read of input bytes at `e` returns the launch's bytes.** -/
def LaunchRead (Q : Params) (mem0 : Mem0) (X : Execution) (e : EvId) : Prop :=
  ∀ (pc : Nat) (a : Acc) (bs : List (Option Byte)), X.get e = some ⟨pc, .rd a bs⟩ →
    a.loc.space = .global → a.loc.cta = 0 → ∀ k < a.size, Q.reads (a.loc.at k).addr →
      ∃ c, mem0 (a.loc.at k) = some (some c) ∧ bs[k]? = some (some c)

/-- **What the induction proves at an event.** -/
structure Good (Q : Params) (L : Launch) (mem0 : Mem0) (X : Execution) (e : EvId) : Prop where
  tt : TT Q L X e
  launch : LaunchRead Q mem0 X e

/-- A machine that left its run (`some none`) never comes back. -/
theorem someNone_mono {g n m : Nat} (h : Frame.stateAt (code L Q) X g n = some none)
    (hnm : n ≤ m) : Frame.stateAt (code L Q) X g m = some none := by
  induction m with
  | zero => rwa [show n = 0 by omega] at h
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hnm with heq | hlt
    · rwa [← heq]
    · have ih' := ih (by omega)
      by_cases hm : m < (X.tr g).length
      · obtain ⟨e, he⟩ : ∃ e, (X.tr g)[m]? = some e := ⟨_, List.getElem?_eq_getElem hm⟩
        rw [Frame.stateAt_succ he, ih']
        rfl
      · rw [Frame.stateAt_of_le (by omega)]
        rwa [Frame.stateAt_of_le (by omega)] at ih'

/-- Tracked through an event is tracked through every earlier event of the thread. -/
theorem TT.mono {g j k : Nat} (hlt : j ≤ k) (h : TT Q L X (g, k)) : TT Q L X (g, j) :=
  fun hn => h (someNone_mono hn (by omega))

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
