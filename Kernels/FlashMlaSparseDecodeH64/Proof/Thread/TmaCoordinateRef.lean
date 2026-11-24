-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTmaCoordinate

@[expose] public section

/-! # The recorded coordinate words of the TMA role

`Wg1Tma` records every coordinate word it reads and compares it with nothing; `Wg1Tma.Ref`
states that the words of the current block are the index warp's `tma_coord` words. This file
proves `Ref` at every followed state of an actual execution: every coordinate read returns its
published word (`MachineTracking.actual_coordinate_value`), which is `Wg1Tma.Expect`, and
`Wg1Tma.ref_next` carries `Ref` across each step of the thread. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmaCoordinateRef

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A composed state that steps to a TMA state is a TMA state that steps to it, or the step is the
dispatch to the role's first state. -/
private theorem tma_source {g : Nat} {u : Machine.ThreadD} {e : Event} {d : Wg1Tma.D}
    (hn : Machine.next P L g u e = some (some (.tma d))) :
    (∃ d0, u = .tma d0 ∧ Wg1Tma.next P L g d0 e = some (some d)) ∨ d = Wg1Tma.init P L g := by
  cases u
  case tma d0 =>
    left
    refine ⟨d0, rfl, ?_⟩
    simp only [Machine.next] at hn
    split at hn
    · rename_i d' hs
      cases hn
      exact hs
    · split at hn
      · cases hn
      · split at hn <;> cases hn
    · split at hn <;> cases hn
  case head =>
    right
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals try contradiction
    all_goals rename_i heq
    all_goals
      cases hn
      all_goals unfold Machine.headStart at heq
      repeat' split at heq
      all_goals cases heq
      all_goals rfl
  all_goals
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals try cases hn
    all_goals rename_i wg hnext hgroup
    all_goals fin_cases wg <;> cases hn

/-- **The TMA role's recorded words are the index warp's.** At every followed state of an actual
execution, every coordinate word the role has read in its current block is the `tma_coord` word
of its position. -/
theorem ref_at (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) {g n : Nat} {d : Wg1Tma.D}
    (hd : Frame.stateAt (Machine.code P L) X g n = some (some (.tma d))) :
    Wg1Tma.Ref P L g d := by
  induction n generalizing d with
  | zero =>
    rw [Frame.stateAt_zero] at hd
    cases hd
  | succ n ih =>
    by_cases hlen : n < (X.tr g).length
    · obtain ⟨e, he⟩ : ∃ e, X.get (g, n) = some e := ⟨_, List.getElem?_eq_getElem hlen⟩
      have hstep := Frame.stateAt_succ (C := Machine.code P L) he
      rw [hd] at hstep
      cases hu : Frame.stateAt (Machine.code P L) X g n with
      | none => rw [hu] at hstep; cases hstep
      | some o =>
        cases o with
        | none => rw [hu] at hstep; cases hstep
        | some u =>
          rw [hu] at hstep
          rcases tma_source hstep.symm with ⟨d0, rfl, hn⟩ | rfl
          · refine Wg1Tma.ref_next (ih hu) ?_ hn
            intro k j a bs v hSite hk hv
            obtain ⟨a', bs', hk', hr⟩ :=
              MachineTracking.actual_coordinate_value hpre hX hs he hu hSite
            obtain ⟨-, rfl⟩ := Kind.rd.inj (hk'.symm.trans hk)
            exact Except.ok.inj (hv.symm.trans hr)
          · exact Wg1Tma.ref_init P L g
    · have hle : (X.tr g).length ≤ n := by omega
      rw [Frame.stateAt_of_le (by omega), ← Frame.stateAt_of_le hle] at hd
      exact ih hd

/-- The four coordinates of a gather issue are the recorded words of the index warp. -/
theorem issue_words (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) {g n : Nat} {d : Wg1Tma.D} {k : Fin 16}
    (hd : Frame.stateAt (Machine.code P L) X g n = some (some (.tma d)))
    (hSite : d.site = .issue k) (j : Fin 4) :
    d.cw (Wg1Tma.coordPos k.val j.val) =
      b32 (Wg1Tma.coordAt P L g d.block (Wg1Tma.coordPos k.val j.val)) :=
  ref_at hpre hX hs hd _ (by
    rw [hSite]
    have := k.isLt
    have := j.isLt
    simp only [Wg1Tma.readCount, Wg1Tma.coordPos]
    omega)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmaCoordinateRef
