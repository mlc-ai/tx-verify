-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingInitControl
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueRoleTrace

@[expose] public section

/-! # Actual initialization events never leave the followed prefix -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow

private theorem role_after_gate {P : Params} {L : Launch} {g : Nat} (d : Machine.ThreadD)
    (hrole : ∀ s, d ≠ .prologue s) : 98 ≤ (Machine.code P L g).pc d := by
  cases d
  case prologue s => exact (hrole s rfl).elim
  case head => change 98 ≤ 1843; decide
  case done => change 98 ≤ 3611; decide
  case idle s =>
    change 98 ≤ s.pc
    cases s <;> decide
  all_goals
    rename_i d
    change 98 ≤ d.site.pc
    cases d.site <;>
      first
      | decide
      | (rename_i a; revert a; decide)
      | (rename_i a b; revert a b; decide)
      | (rename_i a b c; revert a b c; decide)

/-- A real initialization cannot appear after the first dismissed role state. The actual
instruction trace stays beyond the initialization region once a role event has fired. -/
theorem init_state {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {e : Event} {m : Loc} {count : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some e) (hk : e.kind = .mbInit m count) :
    ∃ j, Frame.stateAt (Machine.code P L) X g i = some (some (.prologue (.init j))) ∧
      m = ⟨.shared, g / L.block, L.sharedBase + initOff j⟩ ∧ count = initCount j := by
  classical
  have hn : Frame.stateAt (Machine.code P L) X g i ≠ some none := by
    intro hBad
    let Bad := fun k => Frame.stateAt (Machine.code P L) X g k = some none
    have hb : ∃ k, Bad k := ⟨i, hBad⟩
    have hi := Nat.find_min' hb hBad
    have hzero : ¬ Bad 0 := by unfold Bad; rw [Frame.stateAt_zero]; simp
    obtain ⟨k, hfind⟩ := Nat.exists_eq_succ_of_ne_zero
      (show Nat.find hb ≠ 0 from fun eq => hzero (eq ▸ Nat.find_spec hb))
    have hkbad : Frame.stateAt (Machine.code P L) X g (k + 1) = some none := by
      simpa only [Bad, hfind] using Nat.find_spec hb
    have hklt : k < i := by omega
    have hklen : k < (X.tr g).length := hklt.trans (PTX.len_of_get he)
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
    have hpast (s : Site) : d ≠ .prologue s := by
      intro h
      rw [h] at hkn hd
      exact PrologueRoleTrace.prologue_next_tracked hpre hX (fun a ha => (hs a ha).machine)
        hx hd hkn.symm
    have hpc : 98 ≤ x.pc := by rw [Frame.event_pc hs hX hx hd]; exact role_after_gate d hpast
    have hg := Frame.lt_of_get hX he
    obtain ⟨o, hr⟩ := hX.thr g hg
    have hSplit := List.take_append_drop k (X.tr g)
    rw [List.drop_eq_getElem_cons hklen] at hSplit
    rw [← hSplit] at hr
    have hmem : e ∈ (X.tr g).drop (k + 1) := by
      have hkd : k + 1 ≤ i := hklt
      apply List.mem_of_getElem? (i := i - (k + 1))
      simpa only [List.getElem?_drop, Nat.add_sub_of_le hkd] using
        (show (X.tr g)[i]? = some e from he)
    exact no_init_from_later_event hpc hr e (.tail x hmem) m count hk
  have hg := Frame.lt_of_get hX he
  rcases ((hs g hg).machine.produces (hX.thr g hg)).fired he with
    ⟨s, o, hst, hf⟩ | ⟨_, _, _, rfl⟩
  · cases s with
    | none => exact (hn hst).elim
    | some d =>
      obtain ⟨j, rfl⟩ := RingInitSources.init_site hf hk
      exact ⟨j, hst, Kind.mbInit.inj (hk.symm.trans (RingEvents.barrier_init hpre hf))⟩
  · cases hk

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
