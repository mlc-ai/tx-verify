-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrWarp
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Bar
public import Lemmas.Flow.Final

@[expose] public section

/-! # The correction warps' named barriers: participants and counts at the exit

* A correction thread's named-barrier events are on barrier 2 or on its statistics barriers
  `statsId st (w - 8)`, whose participant warps include its own (`Cross.barMember_corr`, the
  correction part of `Cross.BarMember`).
* At its exit a correction thread has made its two events on barrier 2 and `(n + 1)` syncs per
  item of its cluster on each statistics barrier (`Cross.barExit_corr`, the correction part of
  `Cross.BarNoExit`: a correction lane with fewer events on a barrier has not exited). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem barIs_isBarId {id c : Nat} {m : BarMode} {x : Event} (h : barIs id c m x = true) :
    Execution.isBarId id x = true := by
  obtain ⟨pc, k⟩ := x
  cases k <;> simp only [barIs, Bool.false_eq_true] at h
  rename_i id' cnt m'
  cases cnt <;> simp only [Bool.false_eq_true, decide_eq_true_eq] at h
  obtain ⟨rfl, -, -⟩ := h
  simp [Execution.isBarId]

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **At its exit a correction thread has made all its named-barrier events**: two on barrier 2
and `(n + 1)` per item of its cluster on each statistics barrier. -/
theorem Cross.barExit_corr {g e pc : Nat} (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12)
    (he : X.get (g, e) = some ⟨pc, .exit⟩) :
    (X.tr g).countP (Execution.isBarId 2) = 2 ∧
      ∀ st < 2, (X.tr g).countP (Execution.isBarId (statsId st (warpOf L g - 8))) =
        (Correction.trips L + 1) * Correction.items L g := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, -, hc, hi, hs⟩ := corr_exit_state hpre hX ht hw hw' he
  -- the exit is the trace's last event
  obtain ⟨o, hr⟩ := hX.thr g hg
  have hlast := Run.end_last hr he (.inr rfl)
  have htr : X.tr g = (X.tr g).take e ++ [⟨pc, .exit⟩] := by
    rw [← Option.toList_some, ← he, Execution.get, ← List.take_add_one, hlast, List.take_length]
  have hti := hi.tail (by rw [hs]; rfl) (by rw [hs]; simp) (by rw [hs]; simp)
    (fun _ => by rw [hs]; simp)
  have hkw := corr_kOf hw hw'
  refine ⟨?_, fun st hst => ?_⟩
  · rw [htr, List.countP_append]
    simp only [List.countP_singleton, Execution.isBarId, reduceCtorEq, ite_false, Nat.add_zero]
    -- the events on barrier 2 are the start and end barriers
    have h2 := hc.bar2
    simp only [Correction.bar2Sync, Correction.bar2Arrive, hs] at h2
    have hsplit : ((X.tr g).take e).countP (Execution.isBarId 2) =
        barEvents 2 416 .sync ((X.tr g).take e) + barEvents 2 416 .arrive ((X.tr g).take e) := by
      unfold barEvents
      rw [← countP_or_disj]
      · apply List.countP_congr
        intro x hx
        obtain ⟨j, -, hj⟩ := get_of_mem_take hx
        obtain ⟨xpc, k⟩ := x
        constructor
        · intro h
          cases k <;> simp only [Execution.isBarId, beq_iff_eq, reduceCtorEq] at h
          rename_i id cnt m
          subst h
          rcases corr_bar hpre hX ht hw hw' hj with ⟨-, rfl⟩ | ⟨-, -, st', -, hid⟩
          · cases m <;> simp [barIs]
          · omega
        · intro h
          rcases Bool.or_eq_true _ _ ▸ h with h | h <;> exact barIs_isBarId h
      · intro x _ ⟨h1, h2⟩
        obtain ⟨-, hm⟩ := barIs_both h1 h2
        cases hm
    rw [hsplit, h2.1, h2.2]
  · rw [htr, List.countP_append]
    simp only [List.countP_singleton, Execution.isBarId, reduceCtorEq, ite_false, Nat.add_zero]
    have hid : statsId st (warpOf L g - 8) = Correction.kOf L g + 3 + 4 * st := by
      simp only [statsId]; omega
    rw [hid]
    have hb := corr_barOrd hpre hX ht hw hw' e (id := Correction.kOf L g + 3 + 4 * st) (by omega)
    unfold barOrd at hb
    rw [hb, hc.sync st hst, hti]
    obtain ⟨site, i, tt, aw, a, o'⟩ := d
    simp only at hs ⊢
    subst hs
    simp [Correction.syncPos]

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
