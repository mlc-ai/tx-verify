-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingGatePrefix
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueRoleTrace

@[expose] public section

/-! # Exits cannot bypass the prologue gate -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow

theorem dismissal_after_gate {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (hi : i ≤ (X.tr g).length) (hbad : Frame.stateAt (Machine.code P L) X g i = some none) :
    ∃ j, j + 1 < i ∧ X.get (g, j) = some ⟨97, .bar 0 none .sync⟩ ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.prologue .barrier)) := by
  classical
  let Bad := fun k => Frame.stateAt (Machine.code P L) X g k = some none
  have hb : ∃ k, Bad k := ⟨i, hbad⟩
  have hmin := Nat.find_min' hb hbad
  have hzero : ¬ Bad 0 := by unfold Bad; rw [Frame.stateAt_zero]; simp
  obtain ⟨k, hfind⟩ := Nat.exists_eq_succ_of_ne_zero
    (show Nat.find hb ≠ 0 from fun eq => hzero (eq ▸ Nat.find_spec hb))
  have hkbad : Frame.stateAt (Machine.code P L) X g (k + 1) = some none := by
    simpa only [Bad, hfind] using Nat.find_spec hb
  have hklt : k < i := by omega
  have hklen : k < (X.tr g).length := hklt.trans_le hi
  let x := (X.tr g)[k]
  have hx : X.get (g, k) = some x := List.getElem?_eq_getElem hklen
  have hkn := Frame.stateAt_succ (C := Machine.code P L) hx
  rw [hkbad] at hkn
  have hd : ∃ d, Frame.stateAt (Machine.code P L) X g k = some (some d) := by
    cases hp : Frame.stateAt (Machine.code P L) X g k with
    | none => rw [hp] at hkn; cases hkn
    | some q =>
      cases q with
      | none => exact (Nat.find_min hb (show k < Nat.find hb by omega) hp).elim
      | some d => exact ⟨d, rfl⟩
  obtain ⟨d, hd⟩ := hd
  rw [hd] at hkn
  change some none = Machine.next P L g d x at hkn
  have hrole (s : Site) : d ≠ .prologue s := by
    intro h
    rw [h] at hkn hd
    exact PrologueRoleTrace.prologue_next_tracked hpre hX hs hx hd hkn.symm
  obtain ⟨j, hj, he, hst⟩ :=
    gate_in_followed_prefix hX (hs g (Frame.lt_of_get hX hx)) hx hd hrole
  exact ⟨j, hj.trans hklt, he, hst⟩

/-- Every actual exit follows the thread's own real prologue gate, even if the role abstraction
dismissed an earlier event in that thread. -/
theorem exit_follows_gate {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i tag : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (he : X.get (g, i) = some ⟨tag, .exit⟩) :
    ∃ j, j + 1 < i ∧ X.get (g, j) = some ⟨97, .bar 0 none .sync⟩ ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.prologue .barrier)) := by
  have hg := Frame.lt_of_get hX he
  rcases ((hs g hg).produces (hX.thr g hg)).fired he with
    ⟨s, _, hst, hf⟩ | ⟨_, _, _, heq⟩
  · cases s with
    | none => exact dismissal_after_gate hpre hX hs (PTX.len_of_get he).le hst
    | some d =>
      exact gate_in_followed_prefix hX (hs g hg) he hst (RingGateEvents.exit_after_prologue hf rfl)
  · cases heq

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
