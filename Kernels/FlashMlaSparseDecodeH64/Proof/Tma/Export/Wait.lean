-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Elect.Tma
public import Lemmas.Kernel.Progress.NextEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.LastTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaWords
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaWon
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.ObjCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefStep
import Lemmas.Step.ExitLast

@[expose] public section

/-! # The TMA lane's waits

The waiter rows of the TMA lane (`Tma/Export/Time.lean` imports this file publicly and states the
channel table): `tma_slot_wait` (pc 2205), `tma_won_on`, `tma_lastWait`, `tma_crWait`,
`tma_rfWait`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}


/-- The TMA sites at the pcs of the polls. -/
private theorem site_pc {s : Tma.Site} (hl : ∀ i, s ≠ .leave i) {p : Nat} (h : p = s.pc) :
    (p = 2205 → s = .qWait) ∧ (p = 2209 → s = .storeWait) ∧ (p = 2234 → s = .coordWait) ∧
      (p = 2245 → s = .rawWait) := by
  cases s with
  | leave i => exact absurd rfl (hl i)
  | coord0 k | coord1 k | coord2 k | coord3 k =>
    have := k.isLt
    simp only [Tma.Site.pc, Tma.coordPc] at h
    refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_⟩ <;> split_ifs at h <;> omega
  | gather k =>
    have := k.isLt
    simp only [Tma.Site.pc] at h
    refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_⟩ <;> split_ifs at h <;> omega
  | _ => simp only [Tma.Site.pc] at h; subst h; simp

/-- **The TMA lane at its wait on `bar_q_utccp` is at the commit's slot** `qUtccpSlot`. -/
theorem tma_slot_wait (hp : Pre P L m) (hFw : Follow P L X) {l : Loc} {p : Nat}
    {ok acq : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X y ⟨2205, .wait l p ok acq sc⟩) :
    Sched.threadTime (timed P L) X y = qUtccpSlot := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := next_state hp hFw hn (fun _ h => by cases h)
  obtain ⟨d, n, rfl, -, -, hE, hl, -⟩ := tma_state hJ hi hev hpc ⟨by simp, by simp⟩
  have hs := (site_pc hl hE.1).1 rfl
  rw [timed_eq, Sched.threadTime_of hσ]
  simp only [time, fragTime, wg1Time, tmaTime, Tma.time, Tma.place_qWait hs, idleBase, roleBase,
    qUtccpSlot]

/-- **A lane at an event of the TMA code after the election won the election.** -/
theorem tma_won_on (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k : Nat} {e : Event} (he : X.get (y, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) (hon : TmaOn L y e.pc) :
    ∃ k0 < k, ∃ inst, X.get (y, k0) = some ⟨2165, .elect (2 ^ 32 - 1) inst (PTX.laneOf L y)⟩ :=
  tma_won hp hX hFw he hub ⟨hon.2, hon.1.2.2⟩

/-! ### The waits -/

section
variable {g : Nat} (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
  (hFw : Follow P L X)
include hp hX hFw

/-- **The TMA lane at a poll after `bar_q_utccp` at its trace's end**: the election's winner
with an event at a `TmaOn` pc, its words, the reference invariant at its counts, at time
`tmaOrg + place`. -/
private theorem tma_wait_end {e : Event} (hn : Sched.NextEv L kernel Assumptions.all m X g e)
    (hub : ∀ f, e.kind ≠ .ub f) (hr : 2205 < e.pc ∧ e.pc < 2332) :
    ∃ d : Tma.D, Tma.Ev L g d e ∧ (∀ i, d.site ≠ .leave i) ∧ warp L g = 5 ∧
      (∃ k e, X.get (g, k) = some e ∧ (∀ f, e.kind ≠ .ub f) ∧ TmaOn L g e.pc) ∧
      tmaWordsOk P L g d ∧ Tma.RefCore L g d (fun c => (X.tr g).countP (Tma.cls c)) ∧
      Sched.threadTime (timed P L) X g = tmaOrg + Tma.place d := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := next_state hp hFw hn hub
  obtain ⟨d, n, rfl, hR, -, hE, hl, hw⟩ := tma_state hJ hi hev hpc ⟨by omega, hr.2⟩
  have hu : ((X.tr g).take (X.tr g).length).countP (cls .ub) = 0 :=
    (state_count hσ .ub).symm.trans (next_ub hn hσ)
  obtain ⟨-, u1⟩ := ub_zero hu (Nat.le_refl _)
  have hR := hR (next_ub hn hσ) ((state_count hσ (.tma .ub)).trans u1)
  have hpc' : e.pc = d.site.pc := hE.1
  have hne : d.site ≠ .elect := fun h => by rw [h] at hpc'; simp only [Tma.Site.pc] at hpc'; omega
  obtain ⟨j, hjl, inst, hj⟩ := tma_won_at hp hX hFw hσ hR hne
  obtain ⟨d', n', heq, -, hwd, hR'⟩ := tma_win_state hp hX hFw hj hjl hσ hu
  simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq] at heq
  obtain ⟨⟨-, -, -, rfl⟩, -⟩ := heq
  have hj1 : j + 1 < (X.tr g).length := by
    refine Nat.lt_of_le_of_ne hjl fun h => ?_
    rcases tma_lead hp hX hFw hj with hn' | ⟨dj, nj, hn'⟩
    · rw [h, hσ] at hn'
      cases hn'
    · rw [h, hσ] at hn'
      simp only [Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff,
        heq_eq_eq] at hn'
      obtain ⟨⟨-, -, -, rfl⟩, -⟩ := hn'
      rcases Tma.lead_site dj (batch_in hp g) with h' | h' | h' <;>
        rw [h'] at hpc' <;> simp only [Tma.Site.pc] at hpc' <;> omega
  refine ⟨d, hE, hl, hw, tma_on_of hp hX hFw hj hj1 (Nat.le_refl _) hu, hwd, ?_, ?_⟩
  · rw [List.take_length] at hR'
    exact hR'
  · rw [timed_eq, Sched.threadTime_of hσ]
    simp only [time, fragTime, wg1Time, tmaTime, Tma.time, idleBase, roleBase, tmaOrg]

/-- **The TMA lane at its wait on `last_store_done`** (pc 2209): it has a `TmaOn` event, waits
for the object's first use and is no earlier than `lastWait`. -/
theorem tma_lastWait {c p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨2209, .wait (mbarLoc L c .lastStoreDone) p ok acq sc⟩) :
    (∃ k e, X.get (g, k) = some e ∧ (∀ f, e.kind ≠ .ub f) ∧ TmaOn L g e.pc) ∧
    okPolls (mbarLoc L c .lastStoreDone) (X.tr g) < 1 ∧
    lastWait ≤ Sched.threadTime (timed P L) X g := by
  obtain ⟨d, hE, hl, hw, hon, -, hR, ht⟩ :=
    tma_wait_end hp hX hFw hn (fun _ h => by cases h) ⟨by simp, by simp⟩
  obtain ⟨-, h2, -, -⟩ := site_pc hl hE.1
  have hs := h2 rfl
  obtain ⟨-, hK⟩ := hE
  simp only [Tma.EvK, hs, Tma.Poll] at hK
  rcases hK with ⟨ok', hk⟩ | ⟨f, hk⟩
  · simp only [Kind.wait.injEq] at hk
    obtain ⟨hl', -⟩ := hk
    obtain ⟨rfl, -⟩ := Tma.loc_fam (hl'.trans (Tma.lastW_loc hp))
    have hpro : Tma.ProSite d.site := by rw [hs]; exact ⟨rfl, by simp, by simp⟩
    have hP := lane5_okPolls hp hX hFw hw (X.tr g).length (loc L g .lastStoreDone)
    rw [List.take_length, (Tma.core_pro hpro).mp hR _ (by simp), hs] at hP
    refine ⟨hon, ?_, ?_⟩
    · have h0 := Tma.tcnt_pro1 (g := g) hp
      simp only [Tma.Site.pro] at hP
      simp only [loc] at hP h0
      omega
    · rw [ht, Tma.place_pro hpro, hs]
      simp [Tma.Site.ord, lastWait, tmaOrg, tmaLastW]
  · cases hk

/-- **The TMA lane at its wait on `coordReady j`** (pc 2234): it has a `TmaOn` event, waits for
a use below the CTA's uses of the slot, and is no earlier than `crWaitT` of that use's block. -/
theorem tma_crWait {c p : Nat} {j : Fin 4} {ok acq : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨2234, .wait (mbarLoc L c (.coordReady j)) p ok acq sc⟩) :
    (∃ k e, X.get (g, k) = some e ∧ (∀ f, e.kind ≠ .ub f) ∧ TmaOn L g e.pc) ∧
    okPolls (mbarLoc L c (.coordReady j)) (X.tr g) < ringUses 4 j.val (blocksOf P L c) ∧
    crWaitT (4 * okPolls (mbarLoc L c (.coordReady j)) (X.tr g) + j.val) ≤
      Sched.threadTime (timed P L) X g := by
  obtain ⟨d, hE, hl, hw, hon, hwd, hR, ht⟩ :=
    tma_wait_end hp hX hFw hn (fun _ h => by cases h) ⟨by simp, by simp⟩
  obtain ⟨-, -, h3, -⟩ := site_pc hl hE.1
  have hs := h3 rfl
  have hlp : d.site.inLoop = true := by rw [hs]; rfl
  obtain ⟨⟨-, -, -, hrR, -, -, hslot, -, -, -⟩, hcnt⟩ := (Tma.core_loop hlp).mp hR
  have hrd := tma_rounds_of (by rw [hs]; simp) (by rw [hs]; simp) hwd
  obtain ⟨-, hK⟩ := hE
  simp only [Tma.EvK, hs, Tma.Poll] at hK
  rcases hK with ⟨ok', hk⟩ | ⟨f, hk⟩
  · simp only [Kind.wait.injEq] at hk
    obtain ⟨hl', -⟩ := hk
    obtain ⟨rfl, hj⟩ :=
      Tma.loc_fam (hl'.trans ((Tma.ready_of hslot).trans (Tma.ready_loc hp (slot4 d.cnt.toNat))))
    cases MbarFam.coordReady.inj hj
    have hP := lane5_okPolls hp hX hFw hw (X.tr g).length
      (loc L g (.coordReady (slot4 d.cnt.toNat)))
    rw [List.take_length, hcnt _ (by simp), Tma.tcnt_ready hp] at hP
    simp only [loc] at hP
    rw [hP, ht, Tma.place_loop hlp, ← hrd]
    refine ⟨hon, ?_, ?_⟩ <;>
      simp only [hs, Tma.useAt, ringUses, Tma.ind, slot4, Tma.Site.idx, Tma.Site.stage,
        Tma.Site.rdN, Tma.Site.gN, crWaitT, frame, loopBase, stride, tmaOff, tmaCw, tmaBlk0,
        tmaOrg] <;>
      split_ifs <;> omega
  · cases hk

/-- **The TMA lane at its wait on `rawFree j`** (pc 2245): it has a `TmaOn` event, waits for a
use below the CTA's uses of the slot, and is no earlier than `rfWait` of that use's block. -/
theorem tma_rfWait {c p : Nat} {j : Fin 2} {ok acq : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨2245, .wait (mbarLoc L c (.rawFree j)) p ok acq sc⟩) :
    (∃ k e, X.get (g, k) = some e ∧ (∀ f, e.kind ≠ .ub f) ∧ TmaOn L g e.pc) ∧
    okPolls (mbarLoc L c (.rawFree j)) (X.tr g) < ringUses 2 j.val (blocksOf P L c) ∧
    rfWait (2 * okPolls (mbarLoc L c (.rawFree j)) (X.tr g) + j.val) ≤
      Sched.threadTime (timed P L) X g := by
  obtain ⟨d, hE, hl, hw, hon, hwd, hR, ht⟩ :=
    tma_wait_end hp hX hFw hn (fun _ h => by cases h) ⟨by simp, by simp⟩
  obtain ⟨-, -, -, h4⟩ := site_pc hl hE.1
  have hs := h4 rfl
  have hlp : d.site.inLoop = true := by rw [hs]; rfl
  obtain ⟨⟨-, -, -, hrR, -, hbuf, -, -, -, -⟩, hcnt⟩ := (Tma.core_loop hlp).mp hR
  have hrd := tma_rounds_of (by rw [hs]; simp) (by rw [hs]; simp) hwd
  obtain ⟨-, hK⟩ := hE
  simp only [Tma.EvK, hs, Tma.Poll] at hK
  rcases hK with ⟨ok', hk⟩ | ⟨f, hk⟩
  · simp only [Kind.wait.injEq] at hk
    obtain ⟨hl', -⟩ := hk
    obtain ⟨rfl, hj⟩ :=
      Tma.loc_fam (hl'.trans ((Tma.free_of hbuf).trans (Tma.free_loc hp (slot2 d.cnt.toNat))))
    cases MbarFam.rawFree.inj hj
    have hP := lane5_okPolls hp hX hFw hw (X.tr g).length
      (loc L g (.rawFree (slot2 d.cnt.toNat)))
    rw [List.take_length, hcnt _ (by simp), Tma.tcnt_free hp] at hP
    simp only [loc] at hP
    rw [hP, ht, Tma.place_loop hlp, ← hrd]
    refine ⟨hon, ?_, ?_⟩ <;>
      simp only [hs, Tma.useAt, ringUses, Tma.ind, slot2, Tma.Site.idx, Tma.Site.stage,
        Tma.Site.rdN, Tma.Site.gN, rfWait, frame, loopBase, stride, tmaOff, tmaRw, tmaBlk0,
        tmaOrg] <;>
      split_ifs <;> omega
  · cases hk

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
