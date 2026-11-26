-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.ProgressState

@[expose] public section

/-!
# The progress contract along one step: barriers and the counted events left

The fields of `Proof/Schedule/Contract.lean: RefProgress` that speak about one step of a
thread's machine, from the followed state `d` before the thread's `k`-th event `e` to the
followed state `d'` after it, for the numbers `nums P L` of `ProgressNums.lean`.

* `barStep_at`, field `barStep`: a barrier event is fired at sub-step 0 and leads to a later
  instruction, at a tile index that is not smaller. For the nine `bar.sync 0` no phase is
  named: the event is the arrival at barrier 0 (`Ref.bar0_event`), so the thread's count of
  `bar.sync 0` grows by one, and that count is `bar0Of` of the state's instruction on both
  sides (`bar0_at`); the tile index is 0 before a barrier up to 1402 and the tile count after
  one from 3113 on. The named barrier at instruction 2913 is the Compute phase's
  (`Compute.barStep_compute`).
* `left_dec_at`, field `left_dec`: every step lowers the counted events left (`leftNum`) by
  the event's count (1, or 0 for a failed poll). Inside a phase this is the phase's own
  statement about its events left; across the border of two phases it is the choice of the
  bases in `leftNum` (the table in `ProgressNums.lean`): the successor is the exit state of the
  phase, whose instruction belongs to the next phase, and the next phase's events left at its
  entry state are bounded (`conv_left_le`, `CarryLoad.leftOf_le`, `loopLeft_entry`; 723 at the
  first instruction of the epilogue).
* `epi_pc_nxt`: in the epilogue the next position of every role is at a later instruction, so
  the distance of the instruction from the end of the program is a bound on the events left.

Everything is in the sub-namespace `Assembly.Progress`; `hub` is as in `ProgressState.lean`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.Progress
open PTX PTX.Proof PTX.Flow PTX.Sched
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Bar uses bar0Pcs ctaTiles)
open PTX.Kernels.FlashKdaFwd.Proof.Progress (siteCls bar0Of)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The events of the Conversion phase left at a state are at most 175 (the phase has
`3 + 4 * 43` events for a compute thread and `3 + 4 * 42` for the others). -/
theorem conv_left_le (g : Nat) (d : D) : Conversion.leftOf g d ≤ 175 := by
  unfold Conversion.leftOf Conversion.len Conversion.pairs Conversion.head
  split_ifs <;> omega

/-- **In the epilogue the next position is at a later instruction**, for every role. -/
theorem epi_pc_nxt (g : Nat) (pos : Epilogue.Pos) (hne : pos ≠ .exit) :
    pos.site.pc < (Epilogue.nxt g pos).site.pc := by
  cases pos with
  | exit => exact absurd rfl hne
  | st j =>
    have hj := j.isLt
    by_cases h1 : j.val + 1 < 128
    · rw [Epilogue.nxt, dite_eq_left h1, Epilogue.st_pc, Epilogue.st_pc]
      simp only
      omega
    · rw [Epilogue.nxt, dite_eq_right h1, Epilogue.st_pc]
      show _ < 3774
      omega
  | ts i =>
    have hi := i.isLt
    by_cases h1 : i.val + 1 < 16
    · rw [Epilogue.nxt, dite_eq_left h1, Epilogue.ts_pc, Epilogue.ts_pc]
      simp only
      omega
    · rw [Epilogue.nxt, dite_eq_right h1, Epilogue.ts_pc]
      show _ < 3832
      omega
  | bar7 => simp only [Epilogue.nxt]; split <;> decide
  | bar8 => simp only [Epilogue.nxt]; split <;> decide
  | _ => simp only [Epilogue.nxt]; decide

/-- The instruction of a state at a position of the Store phase: 1402 at the entry, otherwise
one of the store leader's loop. -/
theorem store_refAt_pc {pos : Store.Pos} {d : D} (hr : Store.RefAt P g pos d) :
    d.site.pc = 1402 ∨ (2944 < d.site.pc ∧ d.site.pc ≤ 3112) := by
  rw [hr.site]
  rcases Store.site_pc pos with ⟨-, h⟩ | ⟨-, h⟩
  · exact .inl h
  · exact .inr h

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads) (hub : ∀ k, NoUb X g k)
include hpre hX hg hub

/-- **Field `barStep`**: a barrier event is made at sub-step 0 and leads to a later
instruction, at a tile index that is not smaller. -/
theorem barStep_at {k pc id : Nat} {cnt : Option Nat} {m : BarMode} {d d' : D}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt m⟩) (hσ : At (code L) X g k d)
    (hσ' : At (code L) X g (k + 1) d') :
    d.site.sub = 0 ∧ d.site.pc < d'.site.pc ∧ tileNum P L g d ≤ tileNum P L g d' := by
  have hklt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨-, hsub, hpcs⟩ := bar_site_pc (sounds hpre) hX he hσ rfl
  have hst := stage hpre hX hg (Nat.le_of_lt hklt) hσ
  rcases hpcs with hb0 | h2913
  · have hev := bar0_event (sounds hpre) hX he hσ hb0
    have h1 := bar0_at hpre hX hg hub (Nat.le_of_lt hklt) hσ
    have h2 := bar0_at hpre hX hg hub (show k + 1 ≤ (X.tr g).length by omega) hσ'
    have h3 := count_snoc (Execution.isBarId 0) he
    have h4 : Execution.isBarId 0 (⟨pc, .bar id cnt m⟩ : Event) = true := by
      rw [hev]
      rfl
    rw [h4] at h3
    simp only [↓reduceIte] at h3
    have hlt : d.site.pc < d'.site.pc := Startup.bar0_lt (by
      unfold bar0Of at h1 h2
      omega)
    refine ⟨hsub, hlt, ?_⟩
    rcases Nat.lt_or_ge 1402 d.site.pc with h1402 | h1402
    · have h3113 : 3113 ≤ d.site.pc := by
        simp only [bar0Pcs, List.mem_cons, List.not_mem_nil, or_false] at hb0
        omega
      rw [tileNum_end h3113, tileNum_end (by omega)]
    · rw [tileNum_start h1402]
      exact Nat.zero_le _
  · obtain ⟨hr, j0, s0, -, -, -, hI⟩ := hst.of_pc_compute (by omega) (by omega)
    obtain ⟨-, hlt, hle, hcase⟩ := Compute.barStep_compute hpre hX hg he hσ hI hσ'
    refine ⟨hsub, hlt, ?_⟩
    rw [tileNum_compute (d := d) (by omega) (by omega) hr]
    rcases hcase with hI' | hO
    · have hp' := Compute.site_compute hI'
      rw [tileNum_compute (d := d') (by omega) (by omega) hr]
      exact hle
    · have hpc' : d'.site.pc = 3113 := by
        rw [hO.1.site]
        rfl
      rw [tileNum_end (d := d') (by omega), tiles_eq hpre]
      exact Compute.tileOf_le P g d

/-- **Field `left_dec`**: every step of a followed thread lowers the counted events left by the
event's count. -/
theorem left_dec_at {k : Nat} {d d' : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : At (code L) X g k d) (hn : Thread.next L g d e = some (some d')) :
    leftNum P g d' + (if e.counts then 1 else 0) ≤ leftNum P g d := by
  have hklt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hσ' : At (code L) X g (k + 1) d' := by
    rw [At, Frame.stateAt_succ he, hσ]
    exact hn
  obtain ⟨c, hc, hc1⟩ : ∃ c, (if e.counts = true then 1 else 0) = c ∧ c ≤ 1 :=
    ⟨_, rfl, by split <;> omega⟩
  rw [hc]
  have hst := stage hpre hX hg (Nat.le_of_lt hklt) hσ
  cases hst with
  | startup hI =>
    have h1 := Startup.left_dec_startup hpre hX hg he hσ hI.inv hn
    rw [hc] at h1
    obtain ⟨s2, hσ2, hnext⟩ := Startup.inv_next hpre hX hg he hσ hI
    obtain rfl : s2 = d' := Option.some.inj (Option.some.inj (hσ2.symm.trans hσ'))
    have hp := pc_startup hI.inv
    rw [leftNum_startup (d := d) (by omega)]
    rcases hnext with h | h
    · have hp' := pc_startup h.inv
      rw [leftNum_startup (d := s2) (by omega)]
      omega
    · have hs : s2.site.pc = 387 := by
        rw [h.1.1.site]
        rfl
      have hE := Startup.leftOf_exit h.1.1
      have hlen := conv_left_le g s2
      rw [leftNum_conversion (d := s2) (by omega) (by omega)]
      omega
  | conversion past hj hI =>
    have hp := pc_conversion hI
    rw [leftNum_conversion (d := d) (by omega) (by omega)]
    rcases Conversion.left_dec_conversion hpre hX hg he hσ hI hn with ⟨hI', h⟩ | ⟨-, hout, h⟩
    · have hp' := pc_conversion hI'
      rw [leftNum_conversion (d := d') (by omega) (by omega)]
      omega
    · have hs' : 622 ≤ d'.site.pc ∧ d'.site.pc < 1402 := by
        rw [hout.1.site]
        split_ifs <;> decide
      have hle := CarryLoad.leftOf_le d'
      rw [leftNum_carry (d := d') hs'.1 hs'.2]
      omega
  | carryLoad past hj hI =>
    have h := CarryLoad.leftOf_dec hpre hX hg he hσ hI hn
    have hp := pc_carryLoad hI
    rw [leftNum_carry (d := d) (by omega) (by omega)]
    rcases CarryLoad.inv_next hpre hX hg he hσ hI hn with hI' | ⟨-, hO⟩
    · have hp' := pc_carryLoad hI'
      rw [leftNum_carry (d := d') (by omega) (by omega)]
      omega
    · have hs' := hO.1.site
      have hpc' : d'.site.pc = 1402 := by
        rw [hs']
        rfl
      have hle := loopLeft_entry (P := P) (g := g) hs'
      have h1 : CarryLoad.leftOf d' = 1 := by
        simp only [CarryLoad.leftOf, hpc']
      rw [leftNum_loop (d := d') (by omega) (by omega)]
      omega
  | compute hr past hj hin hI =>
    have hp := pc_compute hI
    rw [leftNum_loop (d := d) (by omega) (by omega), loopLeft_compute hr]
    obtain ⟨hcase, h⟩ := Compute.leftOf_dec hpre hX hg he hσ hI hn
    rw [hc] at h
    rcases hcase with hI' | hO
    · have hp' := pc_compute hI'
      rw [leftNum_loop (d := d') (by omega) (by omega), loopLeft_compute hr]
      omega
    · have hpc' : d'.site.pc = 3113 := by
        rw [hO.1.site]
        rfl
      rw [leftNum_epilogue (d := d') (by omega), hpc']
      omega
  | producer hr past hj hen hI =>
    have hp := pc_producer hI
    rw [leftNum_loop (d := d) (by omega) (by omega), loopLeft_producer hr]
    rcases Producer.leftOf_dec hpre hX hg hr he hσ hI hn with ⟨hI', h⟩ | ⟨hO, h⟩
    · have hp' := pc_producer hI'
      rw [hc] at h
      rw [leftNum_loop (d := d') (by omega) (by omega), loopLeft_producer hr]
      omega
    · have hpc' : d'.site.pc = 3113 := by
        rw [hO.1.site]
        rfl
      rw [hc] at h
      rw [leftNum_epilogue (d := d') (by omega), hpc']
      omega
  | store hr past hj hin hI hW =>
    have hI := hI (hub k)
    have hp := pc_store_inv hI
    rw [leftNum_loop (d := d) (by omega) (by omega), loopLeft_store hr]
    rcases Store.leftOf_dec hpre hg he hσ hI hn with ⟨⟨pos', hr'⟩, h⟩ | ⟨hE, h⟩
    · have hp' := store_refAt_pc hr'
      rw [hc] at h
      rw [leftNum_loop (d := d') (by omega) (by omega), loopLeft_store hr]
      omega
    · have hpc' : d'.site.pc = 3113 := by
        rw [hE.site]
        rfl
      rw [leftNum_epilogue (d := d') (by omega), hpc']
      omega
  | epilogue past hj hW hI =>
    have hW' := Epilogue.epilogue_weak hpre hX hg past.state past.into
      (show _ ≤ k + 1 by omega) (show k + 1 ≤ (X.tr g).length by omega) hσ'
    have hp := pc_epilogue hW
    have hp' := pc_epilogue hW'
    obtain ⟨pos, hr, hon, hkp, -⟩ := hW
    obtain ⟨pos', hr', hon', hkp', -⟩ := hW'
    have hne : pos ≠ .exit := by
      rintro rfl
      obtain ⟨site, w, p, x⟩ := d
      obtain rfl : site = .exit 0 := hr.site
      rw [Thread.next_exit_0] at hn
      cases hn
    have hpos : pos' = Epilogue.nxt g pos :=
      Epilogue.ord_inj hon' (Epilogue.onPath_nxt hon) (by rw [Epilogue.ord_nxt hon hne]; omega)
    have hlt := epi_pc_nxt g pos hne
    rw [← hpos, ← hr.site, ← hr'.site] at hlt
    rw [leftNum_epilogue (d := d) hp.1, leftNum_epilogue (d := d') hp'.1]
    omega

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.Progress
