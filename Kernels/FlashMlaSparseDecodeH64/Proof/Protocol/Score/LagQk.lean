-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Score.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Elect
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Lemmas.Protocol.NotifyBlocker
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar0
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.ObjNe
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Commit
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Wait

@[expose] public section

/-! # The score's progress row (`qk_done`, wait at 272)

Warpgroup 0's lanes wait at pc 272 on `qkDone j` of their CTA with the parity of their successful
polls. Block `r` of slot `j = r % 2` is completed by the MMA lane's commit at `qkCommit r` and
awaited by warpgroup 0 at `qkWait r` (`qk_lt`). The schedule (`qkDone_lag`, `Sched.LagN`):
`τ u = qkCommit (2 u + j) + 1`, `δ = 0`, producers the CTA's MMA producer short of the CTA's uses
of the slot (`MmaProd`: before the election `electSlot` is below every frame, `elect_lt`; after
it `mma_qkEarly`, `mma_qkExit`), consumers the lanes whose next event is the wait
(`wg0_qkWait`), `U` the CTA's uses of the slot.

At a blocked poll (`qkDone_blk`) the notify blocker (`Notify.Obj.blocker`, reuse paths `qkReach`
from the score ring, `KRingOff.reachF`) gives an undelivered commit notification (an open
`.commit` obligation) or no more commits of the CTA's MMA lane than the waiter's polls. A lane
that committed to a score barrier is the CTA's MMA lane (`score_lane`), so the MMA producer is
short of the waited use and `LagN.blk` makes it a blocker. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section
set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The producer of `qkDone j` of CTA `c` while it lags: the CTA's MMA producer short of the uses
of the slot. -/
def QkProd (P : Params) (L : Launch) (X : Execution) (c : Nat) (j : Fin 2) (y : Nat) : Prop :=
  MmaProd P L X c y ∧
    (X.tr y).countP (commitsTo (mbarLoc L c (.qkDone j))) < ringUses 2 j.val (blocksOf P L c)

/-- Lane `g`'s next event is the wait at 272 on `qkDone j` of CTA `c`. -/
def QkCons (L : Launch) (m : Mem0) (X : Execution) (c : Nat) (j : Fin 2) (g : Nat) : Prop :=
  ∃ p ok acq sc, Sched.NextEv L kernel Assumptions.all m X g
    ⟨272, .wait (mbarLoc L c (.qkDone j)) p ok acq sc⟩

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **The `qkDone` schedule** of slot `j` of CTA `c`. -/
theorem qkDone_lag (hub : ¬ HasUb X) (c : Nat) (j : Fin 2) :
    Sched.LagN (timed P L) X (mbarLoc L c (.qkDone j)) 0 (QkProd P L X c j) (QkCons L m X c j)
      (fun u => qkCommit (2 * u + j.val) + 1) (ringUses 2 j.val (blocksOf P L c))
      (commitsTo (mbarLoc L c (.qkDone j))) := by
  refine ⟨fun a b h => ?_, fun g hg => ?_, fun y hy _ => ?_, fun y k pc hy hx => ?_,
    fun g hg => ?_⟩
  · simp only [qkCommit, frame, stride, loopBase, mmaOff, mmaQkc]
    omega
  · obtain ⟨p, ok, acq, sc, hn⟩ := hg
    obtain ⟨-, -, hw, -⟩ := wg0_qkWait hp hX hFw hn
    have := qk_lt (2 * okPolls (mbarLoc L c (.qkDone j)) (X.tr g) + j.val)
    omega
  · obtain ⟨⟨hyc, -, ⟨-, ht⟩ | ⟨k, e0, he0, hu0, hon⟩⟩, hlt⟩ := hy
    · have := elect_lt (2 * ((X.tr y).countP (commitsTo (mbarLoc L c (.qkDone j))) + 0) + j.val)
        (mmaOff + mmaQkc)
      simp only [qkCommit]
      omega
    · have := mma_qkEarly hp hX hFw hub he0 hu0 hon hyc hlt
      simp only [Nat.add_zero]
      omega
  · obtain ⟨⟨hyc, -, ⟨hnx, -⟩ | ⟨k0, e0, he0, hu0, hon⟩⟩, -⟩ := hy
    · exact (hnx k pc hx).elim
    · exact mma_qkExit hp hX hFw he0 hu0 hon hyc hx
  · obtain ⟨p, ok, acq, sc, hn⟩ := hg
    exact (wg0_qkWait hp hX hFw hn).2.1

/-- **A lane that committed to a score or PV barrier of CTA `c` is the CTA's MMA lane.** -/
theorem score_lane (hR : MbarRows P L X) {z c : Nat} {f : MbarFam}
    (hf : ∃ s, f = .qkDone s ∨ f = .svDone s)
    (hpos : 0 < (X.tr z).countP (commitsTo (mbarLoc L c f))) :
    z = mmaLane L X c ∧ z / L.block = c := by
  obtain ⟨e, hmem, hpe⟩ := List.countP_pos_iff.mp hpos
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
  have he : X.get (z, k) = some e := hk
  obtain ⟨sp, hks, hsm⟩ := Notify.commit_of_commitsTo hpe
  obtain ⟨pce, kd⟩ := e
  simp only at hks
  subst hks
  obtain ⟨rank, ht⟩ := mma_commitHit hp hX he hsm
  have hm : Frame.MbarOf ⟨pce, .tc (.commit sp)⟩ (mbarLoc L c f) := ⟨rank, ht⟩
  obtain ⟨s, hs⟩ := hf
  have hf' : ∃ s, f = .qkDone s ∨ f = .soReady s ∨ f = .svDone s := by
    rcases hs with rfl | rfl
    · exact ⟨s, .inl rfl⟩
    · exact ⟨s, .inr (.inr rfl)⟩
  rcases score_use hR hf' (Frame.lt_of_get hX he) he hm with ⟨n, hk'⟩ | ⟨hzc, ⟨hat, -⟩ |
    ⟨-, ⟨-, ok', hk'⟩ | ⟨-, hk'⟩ | ⟨-, q, ok', hk'⟩⟩ | ⟨-, -, ok', hk'⟩⟩
  · cases hk'
  · refine ⟨?_, hzc⟩
    rw [← hzc]
    exact laneOn_eq (mmaOne hp hX hFw) he (fun _ h => by cases h) hat
  all_goals cases hk'

/-- **The reuse paths of `qkDone s`** as warpgroup-0 lane `b` polls it (`KRingOff.reachF`). -/
theorem qkReach (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (c : Nat)
    (s : Fin 2) (b : Fin 128) :
    Notify.Reach L kernel Assumptions.all X (mbarLoc L c (.qkDone s)) (mmaLane L X c)
      (mbarLoc L c (.qkDone s)) 0 (wg0Lane L c b) :=
  fun _ hx _ hj => (scoreSlot hp hX hFw hR hI hB c s).reachF hX hx b hj

/-- **Warpgroup 0's wait on `qkDone s` is blocked**, when the object's records do not fault: by
an undelivered commit notification, or by the CTA's MMA producer short of the waited use. -/
theorem qkDone_blk (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hub : ¬ HasUb X) {g q : Nat} {s : Fin 2} {sc : MbarScope} (hw : MbarRow.Wg0At L g 272)
    (hff : ∀ r ∈ X.objects (MbarRow.loc L g (.qkDone s)), r.fault = none)
    (hq : q = okPolls (MbarRow.loc L g (.qkDone s)) (X.tr g) % 2)
    (hrel : Step.Released L X g)
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨272, .wait (MbarRow.loc L g (.qkDone s)) q false true sc⟩) :
    Sched.WaitBlk (timed P L) X g (MbarRow.loc L g (.qkDone s)) q := by
  simp only [MbarRow.loc] at hff hq hn ⊢
  have hg := hn.lt
  obtain ⟨-, -, -, hb0⟩ := wg0_qkWait hp hX hFw hn
  obtain ⟨b, hb⟩ := wg0_lane hp hw
  have hb0' : 0 < ((X.tr g).take (X.tr g).length).countP isBar0 := by
    rw [List.take_length]
    exact hb0
  have N := qkDone_obj hp hX hFw hR hI hB (mmaOne hp hX hFw) (g / L.block) s
  obtain ⟨st, hst⟩ := Unit.final_of_init hX N.init N.noInval
    (objects_ne hp hX hFw hI hg (.inr ⟨rfl, hrel⟩) hb0' (.qkDone s))
  refine ⟨st, hst, fun hpar => ?_⟩
  rw [hq, Nat.mod_mod] at hpar
  have hRch := qkReach hp hX hFw hR hI hB (g / L.block) s b
  rw [← hb] at hRch
  obtain ⟨hle, hb'⟩ := N.blocker hX hRch hff (fun he' hm' => mma_commitHit hp hX he' hm') hst
    (by rw [Nat.add_zero]; exact hpar) (Nat.zero_le _)
  rcases hb' with hb' | hb'
  · have hne : X.tr g ≠ [] := by
      intro h
      simp [h] at hb0
    obtain ⟨y, hyt, hyP, -⟩ := mma_producer hp hX hFw hub (c := g / L.block) (by
      have := hp.block
      have := Nat.div_mul_le_self g L.block
      omega)
    have hCy : (X.tr y).countP (commitsTo (mbarLoc L (g / L.block) (.qkDone s))) ≤
        okPolls (mbarLoc L (g / L.block) (.qkDone s)) (X.tr g) := by
      by_cases h0 : (X.tr y).countP (commitsTo (mbarLoc L (g / L.block) (.qkDone s))) = 0
      · omega
      · obtain ⟨hym, -⟩ := score_lane hp hX hFw hR (z := y) (c := g / L.block) ⟨s, .inl rfl⟩
          (by omega)
        rw [hym]
        omega
    have hlt := (wg0_qkWait hp hX hFw hn).2.1
    exact (qkDone_lag hp hX hFw hub (g / L.block) s).blk hX hub hg ⟨_, _, _, _, hn⟩ hne
      ⟨hyP, by omega⟩ hyt (by rw [hyP.1]) (by omega)
  · exact .inl ⟨.commit, by simp, hb'⟩

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
