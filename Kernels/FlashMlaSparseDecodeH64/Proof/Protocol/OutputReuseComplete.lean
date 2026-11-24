-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputWaitGeneration
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PvIssueHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityHistory
import Lemmas.Protocol.NotifyBlocker

@[expose] public section

/-! # Resolve the slot-one alias of the first output tile -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputReuseAudit

open PTX PTX.Flow PTX.AsyncCopy PTX.MbarRing

/-- A later MMA block follows all eight tracked PV operations of an earlier odd block. -/
theorem pv_issue_before_later_block {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {issuer cta j block : Nat} {d : Wg1Mma.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hCta : ctaOf L issuer = cta)
    (he : X.get (issuer, j) = some e)
    (hd : Frame.stateAt (Machine.code P L) X issuer j = some (some (.mma d)))
    (hOdd : block % 2 = 1) (hPast : block < d.i) (k : Fin 8) :
    ∃ i, Frame.stateAt (Machine.code P L) X issuer i = some (some (.mma ⟨.pvMma k, block⟩)) ∧
      X.MmaIssue (issuer, i) (Wg1Mma.pvDest k) (MmaDataTrace.pvOperands L issuer block k)
        (MmaDataTrace.pvAccum block k) [0, 0, 0, 0] := by
  let m := GemmRing.empty L cta 1
  let hMachine (h : Nat) (hh : h < L.threads) := (hs h hh).machine
  have hg := Frame.lt_of_get hX he
  have hCount := Wg1MmaGemmTrace.slot_one_pv_commits_before_block hpre hg
    ((hMachine issuer hg).produces (hX.thr issuer hg)) hd
  change ((X.tr issuer).take j).countP (commitsTo (GemmRing.empty L (ctaOf L issuer) 1)) =
    d.i / 2 at hCount
  rw [hCta] at hCount
  change ((X.tr issuer).take j).countP (commitsTo m) = d.i / 2 at hCount
  obtain ⟨c, ev, _, hc, hTick, hOrdinal⟩ :=
    exists_nthEv (X := X) (p := commitsTo m) (g := issuer) (k := j)
      (n := block / 2) (by omega)
  obtain ⟨sp, hKind, hMbar⟩ := Notify.commit_of_commitsTo hTick
  obtain ⟨state, o, hState, hFired⟩ :=
    RingSourceSites.fired_from_trace hX (hMachine issuer hg) ht hc (by
      intro _ h; rw [hKind] at h; cases h)
  have hSite := RingCommitEvents.commit_site hFired hKind
  have hTarget : TcCommit.target sp 0 = some m := by
    cases state <;> try exact hSite.elim
    case mma q =>
      obtain ⟨sp', he', _, hTargets⟩ := RingCommitEvents.commit_issue hpre hg hSite hFired
      obtain rfl := TcKind.commit.inj (Kind.tc.inj (hKind.symm.trans he'))
      rw [hTargets, ite_eq_left rfl, hMbar]
  obtain ⟨_, _, pv, hPvSlot, hpv, hpvState⟩ :=
    GemmRing.notification (obj := .svDone) (slot := 1) hpre hX (hMachine issuer hg) ht
      hc hKind hTarget
  have hPvSite : pv.site = .pvCommit := by
    rcases hpv with ⟨h, _⟩ | ⟨_, h⟩
    · cases h
    · exact h
  have hPvCount := Wg1MmaGemmTrace.composed_count_here hpre hg .pv
    ((hMachine issuer hg).produces (hX.thr issuer hg)) hpvState hPvSlot
  simp only [Wg1MmaGemmTrace.completed, Bool.false_eq_true, ↓reduceIte,
    Nat.add_zero] at hPvCount
  change ((X.tr issuer).take c).countP (commitsTo (GemmRing.empty L (ctaOf L issuer) 1)) =
    pv.i / 2 at hPvCount
  rw [hCta] at hPvCount
  have hQuot : pv.i / 2 = block / 2 := hPvCount.symm.trans hOrdinal
  have hBlock : pv.i = block := by
    change pv.i % 2 = 1 at hPvSlot
    omega
  obtain ⟨i, _, hi, hIssue⟩ :=
    PvIssueHistory.pv_issue_of_commit hpre hX hs hc hpvState hPvSite k
  rw [hBlock] at hi hIssue
  exact ⟨i, hi, hIssue⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputReuseAudit
