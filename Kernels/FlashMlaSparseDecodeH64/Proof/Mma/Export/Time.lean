-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaWon
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaExit
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.EvKind
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Elect.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Ring
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaWords
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar0
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.LocCnt

@[expose] public section

/-! # The MMA lane's time facts

**The role's lemma table** (channel: producer early / waiter / producer exit). Common
hypotheses: `hp : Pre P L m`, `hX : Consistent L kernel Assumptions.all m X`, `hFw : Follow P L X`.
A producer lane `y` is given by an event of the MMA code after the election,
`he0 : X.get (y, k) = some e0`, `hu0 : ∀ f, e0.kind ≠ .ub f`, `hon : MmaOn L y e0.pc` (the
CTA's `mmaLane`), and `hc : y / L.block = c`; early facts also take `hnu : ¬ HasUb X`, exit facts
`hx : X.get (y, x) = some ⟨pc, .exit⟩`. A waiter is given by
`hn : Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait (mbarLoc L c F) p ok acq sc⟩`.
`R = blocksOf P L c`; `C` the lane's commits (`PTX.Flow.commitsTo`) to the slot's object, `u` the
waiter's successful polls of it, `t` its `Sched.threadTime (timed P L) X`.

* `qUtccp` (commit 1982): early `mma_qUtEarly` (no commit → `t < qUtccpSlot`, from any MMA event
  after the election, before or after pc 1929), the older `mma_slot_early` (an event from pc 1929
  on); exit `mma_commitExit` (`Mma/Export/Count`); waiters `mma_slot_wait` (1983, `t =
  qUtccpSlot`), TMA 2205 (lane Eb), dequant 2644 (`dequant_slot_wait`).
* `dequantReady j` (wait 2012): waiter `mma_drWait` (MMA lane, `u < ringUses 2 j R`,
  `drWait (2u+j) ≤ t`); producers dequant (`deq_drEarly`, `deq_drExit`).
* `soReady j` (wait 2107): waiter `mma_soWait` (MMA lane, `u < ringUses 2 j R`,
  `soWait (2u+j) ≤ t`); producers warpgroup 0.
* `qkDone j` (commit 2105): early `mma_qkEarly` (`C < ringUses 2 j R → t ≤ qkCommit (2C+j)`),
  exit `mma_qkExit` (`ringUses 2 j R ≤ C`); waiter warpgroup 0 (272).
* `svDone j` (commit 2148): early `mma_svEarly` (`C < ringUses 2 j R → t ≤ svCommit (2C+j)`),
  exit `mma_svExit` (`ringUses 2 j R ≤ C`); waiters dequant 2684 (`deq_svWait`), warpgroup 0.

The commit facts are in `Mma/Export/Ring.lean` (imported here); their exit cases rest on
`Common/MmaExit.lean` (after an MMA event the early return is not reached).

## The slot of `bar_q_utccp`

The slot of the commit is `qUtccpSlot` (the time of the MMA lane's wait at pc 1983). A lane of
warp 4 whose next event is that wait is at the slot (`mma_slot_wait`); a lane of warp 4 with an
event of the MMA code from the arrival on (pc 1929) that has not committed to `bar_q_utccp` is
earlier (`mma_slot_early`), in an execution without undefined behaviour.

The ring facts of the MMA lane, with the slots of `Lib/Slots.lean` and the CTA's block count
`blocksOf P L c`: at its wait on `dequantReady j` (pc 2012) it is its CTA's MMA lane (an event at
an MMA pc after barrier 0), waits for a use below the CTA's uses of the slot and is no earlier
than `drWait` of that use's block (`mma_drWait`); the same at `soReady j` (`mma_soWait`). From
one view of the lane at a loop state at its trace's end (`mma_loop_end`: block `r` below
`blocksOf`, the counts `cntAt`, the time). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

private theorem slot_eq : qUtccpSlot = idleBase + 32 := by simp [qUtccpSlot, idleBase, roleBase]

/-- **The MMA lane at its wait on `bar_q_utccp` is at the slot.** -/
theorem mma_slot_wait (hp : Pre P L m) (hFw : Follow P L X) {l : Loc} {p : Nat}
    {ok acq : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X y ⟨1983, .wait l p ok acq sc⟩) :
    Sched.threadTime (timed P L) X y = qUtccpSlot := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := next_state hp hFw hn (fun _ h => by cases h)
  obtain ⟨d, n, rfl, -, hE, hl, -⟩ := mma_state hJ hi hev hpc ⟨by simp, by simp⟩
  have hs : d.site = .qCopyWait := by
    have h1 := hE.1
    rcases Mma.ev_wait hl hE with ⟨hs, -⟩ | ⟨hs, -⟩ | ⟨hs, -⟩ | ⟨hs, -⟩ <;>
      rw [hs] at h1 <;> simp [Mma.Site.pc] at h1
    exact hs
  rw [timed_eq, Sched.threadTime_of hσ]
  simp [time, fragTime, wg1Time, mmaTime, Mma.time, Mma.place, hs, Mma.Site.ord, Mma.Site.inLoop,
    slot_eq, idleBase, roleBase]

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hnu : ¬ HasUb X) (hw : warp L y = 4)
include hp hX hFw hnu hw

omit hp hX hFw hw in
private theorem noUb (k : Nat) : ((X.tr y).take k).countP (Mma.cls .ub) = 0 := by
  refine List.countP_eq_zero.mpr fun f hf hcl => hnu ?_
  obtain ⟨j, -, hj⟩ := get_lt_of_mem_take hf
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | ub fl => exact ⟨(y, j), pc, fl, hj⟩
  | wait l q ok a sc => cases ok <;> simp [Mma.cls, Mma.kindOf] at hcl
  | tc t => cases t <;> simp [Mma.cls, Mma.kindOf] at hcl
  | _ => simp [Mma.cls, Mma.kindOf] at hcl

/-- The place of a later state before the commit. -/
private theorem place_le {j i : Nat} {e0 : Event} (he0 : X.get (y, j) = some e0)
    (hu0 : ∀ f, e0.kind ≠ .ub f) (hr0 : 1929 ≤ e0.pc ∧ e0.pc < 2162) (hji : j ≤ i)
    (h0 : (X.tr y).countP (PTX.Flow.commitsTo (loc L y .qUtccp)) = 0) {d : Mma.D}
    (hR : Mma.Ref L y d (fun c => ((X.tr y).take i).countP (Mma.cls c)))
    (hP : Mma.Post d.site) : Mma.place d ≤ 31 := by
  obtain ⟨d0, hR0, hE0, hP0⟩ := post_at hp hX hFw he0 hu0 ⟨by omega, hr0.2⟩ (Nat.le_refl j) he0 hu0
  have h8 := Mma.tma_eight (hR0 (take_noUb hX he0)) hP0.2 (by rw [← hE0.1]; omega)
    (by rw [← hE0.1]; omega)
  have hmono : ((X.tr y).take j).countP (Mma.cls .tma) ≤
      ((X.tr y).take i).countP (Mma.cls .tma) :=
    (List.take_sublist_take_left hji).countP_le
  have hc0 : ((X.tr y).take i).countP (Mma.cls (.commit (Mma.objs L y).qUt)) = 0 := by
    rw [Mma.qUt_eq, Mma.qUt_loc hp, ← lane4_commits hp hX hFw hw i]
    have h3 : ((X.tr y).take i).countP (MbarRow.commitsTo (loc L y .qUtccp)) ≤
        (X.tr y).countP (MbarRow.commitsTo (loc L y .qUtccp)) :=
      (List.take_sublist i (X.tr y)).countP_le
    rw [flow_commitsTo] at h0
    omega
  exact Mma.place_pre_commit (hR (noUb hnu i)) hP.2 (by omega) hc0

/-- **The MMA lane before its commit to `bar_q_utccp` is earlier than the slot.** -/
theorem mma_slot_early {j : Nat} {e0 : Event} (he0 : X.get (y, j) = some e0)
    (hu0 : ∀ f, e0.kind ≠ .ub f) (hr0 : 1929 ≤ e0.pc ∧ e0.pc < 2162)
    (h0 : (X.tr y).countP (PTX.Flow.commitsTo (loc L y .qUtccp)) = 0) :
    Sched.threadTime (timed P L) X y < qUtccpSlot := by
  have hjl : j < (X.tr y).length := (List.getElem?_eq_some_iff.mp he0).1
  have hr1 : 1853 < e0.pc ∧ e0.pc < 2162 := ⟨by omega, hr0.2⟩
  rw [timed_eq]
  cases hs : Frame.stateAt (thread P L) X y (X.tr y).length with
  | some o =>
    cases o with
    | none => exact absurd hs (follow_iff.mp hFw y (Frame.lt_of_get hX he0) _).1
    | some σ =>
      obtain ⟨d, n, rfl, hR, hP⟩ := post_state hp hX hFw hnu he0 hu0 hr1 hjl.le hs
      have := place_le hp hX hFw hnu hw he0 hu0 hr0 hjl.le h0 hR hP
      rw [Sched.threadTime_of hs]
      simp only [time, fragTime, wg1Time, mmaTime, Mma.time, slot_eq]
      omega
  | none =>
    unfold Sched.threadTime
    rw [hs]
    simp only
    cases hs' : Frame.stateAt (thread P L) X y ((X.tr y).length - 1) with
    | none => simp [slot_eq]
    | some o =>
      cases o with
      | none => simp [slot_eq]
      | some σ =>
        obtain ⟨d, n, rfl, hR, hP⟩ := post_state hp hX hFw hnu he0 hu0 hr1 (by omega) hs'
        have h31 := place_le hp hX hFw hnu hw he0 hu0 hr0 (by omega) h0 hR hP
        have hne : Mma.place d ≠ 31 := by
          intro h
          have hq := Mma.place_31 h
          obtain ⟨f, hf⟩ : ∃ f, (X.tr y)[(X.tr y).length - 1]? = some f :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          have hn := Frame.stateAt_succ (C := thread P L) hf
          rw [Nat.sub_add_cancel (by omega), hs, hs'] at hn
          simp [Code.toMachine, Mma.succ, hq] at hn
        simp only [time, fragTime, wg1Time, mmaTime, Mma.time, slot_eq]
        omega

end

/-! ### The lane at a loop state -/

section
variable {g : Nat}

/-- An MMA-pc event of the lane after barrier 0: its commit to `bar_q_utccp`. -/
private theorem mma_on (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g = 4)
    (h1 : 1 ≤ (X.tr g).countP (Mma.cls (.commit (loc L g .qUtccp)))) :
    ∃ k e, X.get (g, k) = some e ∧ (∀ f, e.kind ≠ .ub f) ∧ MmaOn L g e.pc ∧
      0 < ((X.tr g).take k).countP isBar0 := by
  obtain ⟨f, hf, hc⟩ := List.countP_pos_iff.mp
    (show 0 < (X.tr g).countP (Mma.cls (.commit (loc L g .qUtccp))) by omega)
  obtain ⟨k, hk, hfk⟩ := List.getElem_of_mem hf
  have he : X.get (g, k) = some f := by
    show (X.tr g)[k]? = some f
    rw [List.getElem?_eq_getElem hk, hfk]
  obtain ⟨pc, kd⟩ := f
  simp only [Mma.cls, Mma.inRole, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hr, hkd⟩ := hc
  cases kd with
  | tc t =>
    cases t with
    | commit sp =>
      obtain ⟨d, -, hev, hl, -⟩ :=
        mma_at hp hX hFw he (fun _ h => by cases h) ⟨by simp only; omega, by simp only; omega⟩
      have hpc := hev.1
      have h1853 : 1853 < pc := by
        rcases Mma.ev_commit hl hev with ⟨hs, -⟩ | ⟨hs, -⟩ | ⟨hs, -⟩ <;>
          rw [hs] at hpc <;> simp only [Mma.Site.pc] at hpc <;> omega
      exact ⟨k, _, he, (fun _ h => by cases h),
        ⟨⟨hw, by simp only; omega, by simp only; omega⟩, h1853⟩,
        bar0_before hp hX hFw he (fun _ h => by cases h) (by simp only; omega)⟩
    | _ => simp [Mma.kindOf] at hkd
  | wait l q ok a sc => cases ok <;> simp [Mma.kindOf] at hkd
  | _ => simp [Mma.kindOf] at hkd

/-- **The MMA lane at a loop state at its trace's end**: it is its CTA's MMA lane, the state is
block `r` below the CTA's block count with the counts `cntAt`, at time
`frame r + mmaOff + off`. -/
private theorem mma_loop_end (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {e : Event} (hn : Sched.NextEv L kernel Assumptions.all m X g e)
    (hub : ∀ f, e.kind ≠ .ub f) (hr : 1850 ≤ e.pc ∧ e.pc < 2162) :
    ∃ d : Mma.D, Mma.Ev L g d e ∧ (∀ i, d.site ≠ .leave i) ∧ warp L g = 4 ∧
      (d.site.inLoop = true →
        (∃ k e, X.get (g, k) = some e ∧ (∀ f, e.kind ≠ .ub f) ∧ MmaOn L g e.pc ∧
          0 < ((X.tr g).take k).countP isBar0) ∧
        Mma.LoopOk d ∧ d.cnt.toNat < blocksOf P L (g / L.block) ∧
        (∀ c, c ≠ .ub → (X.tr g).countP (Mma.cls c) =
          Mma.cntAt (Mma.objs L g) 31 d.cnt.toNat d.site.idx false c) ∧
        Sched.threadTime (timed P L) X g = frame d.cnt.toNat + mmaOff + d.site.off) := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := next_state hp hFw hn hub
  obtain ⟨d, n, rfl, hR, hE, hl, hw⟩ := mma_state hJ hi hev hpc hr
  obtain ⟨-, -, -, -, hu⟩ := next_mma hp hFw hn hub hr
  have hc : (fun c => n (.mma c)) = fun c => (X.tr g).countP (Mma.cls c) :=
    funext fun c => (state_count hσ (.mma c)).trans (by rw [List.take_length]; rfl)
  have hR := hR (next_ub hn hσ)
  rw [hc] at hR
  refine ⟨d, hE, hl, hw, fun hlp => ?_⟩
  obtain ⟨hok, hcnt⟩ := (Mma.core_loop hlp).mp (hR hu)
  have h1 : 1 ≤ (X.tr g).countP (Mma.cls (.commit (loc L g .qUtccp))) := by
    rw [hcnt _ (by simp)]
    simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.obj_qUt hp, Mma.obj_qk hp, Mma.obj_sv hp,
      Mma.mloc_eq_iff, Mma.ind]
  have hon := mma_on hp hX hFw hw h1
  obtain ⟨k, e0, he0, hu0, ⟨⟨-, -, h2162⟩, hr0⟩, -⟩ := id hon
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he0).1
  have hrd := mma_rounds hp hX hFw he0 hu0 ⟨hr0, h2162⟩ hk.le hσ
    (fun h => by rw [h] at hlp; cases hlp) (fun h => by rw [h] at hlp; cases hlp)
  obtain ⟨-, -, -, hrR, -⟩ := id hok
  refine ⟨hon, hok, by rw [← hrd]; exact hrR, hcnt, ?_⟩
  rw [timed_eq, Sched.threadTime_of hσ]
  simp only [time, fragTime, wg1Time, mmaTime, Mma.time, Mma.place_loop hlp, frame, idleBase,
    roleBase, mmaBlk0, loopBase, mmaOff, mmaOrg]
  omega

/-- **The MMA lane at its wait on `dequantReady j`** (pc 2012): it is its CTA's MMA lane, waits
for a use below the CTA's uses of the slot, and is no earlier than `drWait` of that use's
block. -/
theorem mma_drWait (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {c p : Nat} {j : Fin 2} {ok acq : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨2012, .wait (mbarLoc L c (.dequantReady j)) p ok acq sc⟩) :
    (∃ k e, X.get (g, k) = some e ∧ (∀ f, e.kind ≠ .ub f) ∧ MmaOn L g e.pc ∧
      0 < ((X.tr g).take k).countP isBar0) ∧
    okPolls (mbarLoc L c (.dequantReady j)) (X.tr g) < ringUses 2 j.val (blocksOf P L c) ∧
    drWait (2 * okPolls (mbarLoc L c (.dequantReady j)) (X.tr g) + j.val) ≤
      Sched.threadTime (timed P L) X g := by
  obtain ⟨d, hE, hl, hw, hL⟩ := mma_loop_end hp hX hFw hn (fun _ h => by cases h)
    ⟨show 1850 ≤ 2012 by omega, show 2012 < 2162 by omega⟩
  have h1 := hE.1
  rcases Mma.ev_wait hl hE with ⟨hs, -⟩ | ⟨hs, -⟩ | ⟨hs, hm⟩ | ⟨hs, -⟩ <;>
    rw [hs] at h1 <;> simp only [Mma.Site.pc] at h1 <;> try omega
  obtain ⟨hon, ⟨-, -, -, -, -, hpha, -⟩, hrR, hcnt, ht⟩ := hL (by rw [hs]; rfl)
  rw [hpha] at hm
  obtain ⟨rfl, hj⟩ := Mma.mloc_fam (hm.trans (Mma.ready_loc hp (slot2 d.cnt.toNat)))
  cases MbarFam.dequantReady.inj hj
  have hP := lane4_okPolls hp hX hFw hw (X.tr g).length
    (loc L g (.dequantReady (slot2 d.cnt.toNat)))
  rw [List.take_length, hcnt _ (by simp), Mma.cnt_ready hp] at hP
  simp only [loc] at hP
  rw [hP, ht]
  refine ⟨hon, ?_, ?_⟩ <;>
    simp only [hs, Mma.useAt, ringUses, Mma.ind, slot2, Mma.Site.off, Mma.Site.idx, drWait, mmaKv,
      frame, loopBase, stride, mmaOff] <;>
    split_ifs <;> omega

/-- **The MMA lane at its wait on `soReady j`** (pc 2107): it is its CTA's MMA lane, waits for a
use below the CTA's uses of the slot, and is no earlier than `soWait` of that use's block. -/
theorem mma_soWait (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {c p : Nat} {j : Fin 2} {ok acq : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨2107, .wait (mbarLoc L c (.soReady j)) p ok acq sc⟩) :
    (∃ k e, X.get (g, k) = some e ∧ (∀ f, e.kind ≠ .ub f) ∧ MmaOn L g e.pc ∧
      0 < ((X.tr g).take k).countP isBar0) ∧
    okPolls (mbarLoc L c (.soReady j)) (X.tr g) < ringUses 2 j.val (blocksOf P L c) ∧
    soWait (2 * okPolls (mbarLoc L c (.soReady j)) (X.tr g) + j.val) ≤
      Sched.threadTime (timed P L) X g := by
  obtain ⟨d, hE, hl, hw, hL⟩ := mma_loop_end hp hX hFw hn (fun _ h => by cases h)
    ⟨show 1850 ≤ 2107 by omega, show 2107 < 2162 by omega⟩
  have h1 := hE.1
  rcases Mma.ev_wait hl hE with ⟨hs, -⟩ | ⟨hs, -⟩ | ⟨hs, -⟩ | ⟨hs, hm⟩ <;>
    rw [hs] at h1 <;> simp only [Mma.Site.pc] at h1 <;> try omega
  obtain ⟨hon, ⟨-, -, -, -, -, hpha, -⟩, hrR, hcnt, ht⟩ := hL (by rw [hs]; rfl)
  rw [hpha] at hm
  obtain ⟨rfl, hj⟩ := Mma.mloc_fam (hm.trans (Mma.so_loc hp (slot2 d.cnt.toNat)))
  cases MbarFam.soReady.inj hj
  have hP := lane4_okPolls hp hX hFw hw (X.tr g).length
    (loc L g (.soReady (slot2 d.cnt.toNat)))
  rw [List.take_length, hcnt _ (by simp), Mma.cnt_so hp] at hP
  simp only [loc] at hP
  rw [hP, ht]
  refine ⟨hon, ?_, ?_⟩ <;>
    simp only [hs, Mma.useAt, ringUses, Mma.ind, slot2, Mma.Site.off, Mma.Site.idx, soWait, mmaSo,
      frame, loopBase, stride, mmaOff] <;>
    split_ifs <;> omega

end

/-! ### The winner before its first event of the MMA code -/

/-- The elected lane's first site (every CTA is in the batch): a length load, the trap or the
first query load, at a pc of the MMA code after the election and a place at most `4`. -/
private theorem lead_site (hp : Pre P L m) (d : Mma.D) :
    1853 < (Mma.leadNext P L y d).site.pc ∧ (Mma.leadNext P L y d).site.pc < 2162 ∧
      Mma.place (Mma.leadNext P L y d) ≤ 4 := by
  unfold Mma.leadNext Mma.afterTopk Mma.lensD
  simp only [batch_in hp y, Bool.false_eq_true, ite_false]
  split_ifs <;> simp [Mma.Site.pc, Mma.place, Mma.Site.ord, Mma.Site.inLoop]

/-- **The election's winner** (its event at pc 1853 with its own lane as leader) has an event
of the MMA code after the election (the hypothesis of the lane's producer facts), or its
election is its last event: then it has no `exit` event and its time is at most `electSlot`. -/
theorem mma_wonOn (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {k inst : Nat}
    (hj : X.get (y, k) = some ⟨1853, .elect (2 ^ 32 - 1) inst (PTX.laneOf L y)⟩) :
    (∃ k e, X.get (y, k) = some e ∧ (∀ f, e.kind ≠ .ub f) ∧ MmaOn L y e.pc) ∨
      ((∀ x pc, X.get (y, x) ≠ some ⟨pc, .exit⟩) ∧
        Sched.threadTime (timed P L) X y ≤ electSlot) := by
  have hg := Frame.lt_of_get hX hj
  have hk : k < (X.tr y).length := (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨σj, hσj, hJj, hij, hevj, hpcj⟩ := ev_at hp hX hFw hj (fun _ h => by cases h)
  obtain ⟨dj, nj, rfl, -, hEj, hlj, hw⟩ := mma_state hJj hij hevj hpcj
    ⟨show 1850 ≤ 1853 by decide, show 1853 < 2162 by decide⟩
  obtain ⟨hsj, -, -⟩ := Mma.ev_elect hlj hEj
  obtain ⟨h1, h2, h3⟩ := lead_site (y := y) hp dj
  have hn : Frame.stateAt (thread P L) X y (k + 1) = (thread P L y).toMachine.next (some
      (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, dj⟩⟩, nj)) ⟨1853, .elect (2 ^ 32 - 1) inst
        (PTX.laneOf L y)⟩ := by
    rw [Frame.stateAt_succ hj, hσj]
    rfl
  -- the election is the last event: no exit
  have hlast : k + 1 = (X.tr y).length → ∀ x pc, X.get (y, x) ≠ some ⟨pc, .exit⟩ :=
    fun hl x pc hx => by
      have := Execution.exit_last hX hg hx
      obtain rfl : x = k := by omega
      rw [hj] at hx
      cases hx
  have hmore : k + 1 < (X.tr y).length → ∃ σ, Frame.stateAt (thread P L) X y (k + 1) =
      some (some σ) ∧ ∃ e, X.get (y, k + 1) = some e ∧ (∀ f, e.kind ≠ .ub f) ∧
        e.pc = (thread P L y).pc σ := fun hl => by
    obtain ⟨e, he⟩ : ∃ e, X.get (y, k + 1) = some e := ⟨_, List.getElem?_eq_getElem hl⟩
    have hub : ∀ f, e.kind ≠ .ub f := fun f h => hnu ⟨(y, k + 1), e.pc, f, by rw [he, ← h]⟩
    obtain ⟨σ, hσ, -, -, -, hpc⟩ := ev_at hp hX hFw he hub
    exact ⟨σ, hσ, e, he, hub, hpc⟩
  cases hn' : (thread P L y).toMachine.next (some (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, dj⟩⟩, nj))
      ⟨1853, .elect (2 ^ 32 - 1) inst (PTX.laneOf L y)⟩ with
  | none =>
    rw [hn'] at hn
    rcases Nat.lt_or_ge (k + 1) (X.tr y).length with hl | hl
    · obtain ⟨σ, hσ, -⟩ := hmore hl
      rw [hn] at hσ
      cases hσ
    have hl : k + 1 = (X.tr y).length := by omega
    refine .inr ⟨hlast hl, ?_⟩
    rw [timed_eq]
    unfold Sched.threadTime
    rw [← hl, hn]
    simp only [Nat.add_sub_cancel, hσj]
    simp [time, fragTime, wg1Time, mmaTime, Mma.time, Mma.place, hsj, Mma.Site.ord,
      Mma.Site.inLoop, electSlot, tmaOrg, idleBase, roleBase]
  | some o =>
    cases o with
    | none => simp [Code.toMachine, Mma.succ, hsj] at hn'
    | some σ1 =>
      rw [hn'] at hn
      obtain ⟨a, ha, rfl⟩ := sub_step hn' fun a ha => by
        simp only [Code.withStubsAt] at ha
        simp [Mma.succ, hsj] at ha
        subst ha
        simp [subBack, (Mma.lead_post (P := P) (L := L) (g := y) dj).2 _]
      simp only [Code.withStubsAt] at ha
      simp only [Mma.succ, hsj, ↓reduceIte, Option.some.injEq] at ha
      subst ha
      rcases Nat.lt_or_ge (k + 1) (X.tr y).length with hl | hl
      · obtain ⟨σ, hσ, e, he, hub, hpc⟩ := hmore hl
        obtain rfl := Option.some.inj (Option.some.inj (hn.symm.trans hσ))
        have hpc' : e.pc = (Mma.leadNext P L y dj).site.pc := hpc
        exact .inl ⟨k + 1, e, he, hub, ⟨⟨hw, by omega, by omega⟩, by omega⟩⟩
      have hl : k + 1 = (X.tr y).length := by omega
      refine .inr ⟨hlast hl, ?_⟩
      rw [timed_eq, Sched.threadTime_of (hl ▸ hn)]
      simp only [time, fragTime, wg1Time, mmaTime, Mma.time, electSlot, tmaOrg, idleBase,
        roleBase]
      omega

/-- **The MMA lane that exited has committed to `bar_q_utccp`**, from any event of the MMA code
after the election. -/
theorem mma_qUtExit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k x pc : Nat} {e0 : Event} (he0 : X.get (y, k) = some e0)
    (hu0 : ∀ f, e0.kind ≠ .ub f) (hon : MmaOn L y e0.pc)
    (hx : X.get (y, x) = some ⟨pc, .exit⟩) :
    1 ≤ (X.tr y).countP (PTX.Flow.commitsTo (loc L y .qUtccp)) := by
  obtain ⟨⟨hw, -, h2⟩, h1⟩ := hon
  have h3 := mma_exit_full hp hX hFw he0 hu0 ⟨h1, h2⟩ hx (.commit (loc L y .qUtccp)) (by simp)
  have hq : Mma.cntAt (Mma.objs L y) 31 (blocksOf P L (y / L.block)) 0 true
      (.commit (loc L y .qUtccp)) = 1 := by
    simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.obj_qUt hp, Mma.obj_qk hp, Mma.obj_sv hp,
      Mma.mloc_eq_iff, Mma.ind]
  have hc := lane4_commits hp hX hFw hw x (loc L y .qUtccp)
  have hle : ((X.tr y).take x).countP (MbarRow.commitsTo (loc L y .qUtccp)) ≤
      (X.tr y).countP (MbarRow.commitsTo (loc L y .qUtccp)) := (List.take_sublist _ _).countP_le
  rw [flow_commitsTo]
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
