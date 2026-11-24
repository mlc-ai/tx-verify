-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetimeCompletion
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaDataTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryCopyCompletion
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryCopyHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryTmaHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryTmaSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingCommitEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2ReuseHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaLeader
import Lemmas.Protocol.NamedBarSources

public section

/-! # Query-copy notification and query TMA completion at CTA exit -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetime

open PTX PTX.Flow PTX.AsyncCopy Protocol

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem wg2_query_poll (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {c : Nat} (hc : c < L.grid) (hx : CtaExited L X c) :
    ∃ g j tag, ctaOf L g = c ∧ X.get (g, j) = some
      ⟨tag, .wait (QueryCopy.object L c) 0 true true .cta⟩ := by
  let g := c * L.block + 256
  have hBase : c + 1 ≤ L.grid := by omega
  have hSpan := Nat.mul_le_mul_right L.block hBase
  have hG : g < L.threads := by
    change c * L.block + 256 < L.grid * L.block
    rw [Nat.add_mul, Nat.one_mul] at hSpan
    have hSize := hpre.block
    omega
  have hCta : ctaOf L g = c := by
    simp [g, ctaOf, hpre.block, Nat.mul_comm c 384, Nat.mul_add_div]
  have hWg : wgOf L g = 2 := by
    simp [wgOf, tidOf_eq hpre, g, hpre.block, Nat.mul_comm c 384]
  obtain ⟨tag, hLast⟩ := hx g hG hCta
  rw [List.getLast?_eq_getElem?] at hLast
  have hLast' : X.get (g, (X.tr g).length - 1) = some ⟨tag, .exit⟩ := hLast
  obtain ⟨j, e, _, he, hFirst⟩ :=
    Wg2ReuseHistory.first_store_before_exit hpre hX hs ht hWg hLast'
  obtain ⟨d, _, hd, hSite, _⟩ :=
    Wg2ReuseHistory.first_store_state hX (hs g hG).machine ht he hFirst
  obtain ⟨w, _, wt, hw⟩ :=
    Wg2ReuseHistory.query_before_first_store hpre hX (hs g hG).machine hG hd hSite
  exact ⟨g, w, wt, hCta, by simpa only [QueryCopy.object, Wg2.qUtccpOff, hCta] using hw⟩

private theorem commit_notify_present (hX : Consistent L kernel Assumptions.all mem0 X)
    {i w : EvId} {tag : Nat} {sp : TcCommit.Spec} {m : Loc} {rank : Fin 16}
    {acq : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨tag, .tc (.commit sp)⟩)
    (hw : WaitObserves X (.async i (.tcNotify rank)) w m acq scope) :
    TcCommit.target sp rank = some m ∧ X.RefPresent (.async i (.tcNotify rank)) := by
  obtain ⟨j, _, r, _, _, hr, hid, _, _⟩ := hw.2
  have ha := (hX.tma.2.2.1 m).2.1 r (List.mem_of_getElem? hr)
  rw [hid] at ha
  simp [objectAction, he] at ha
  exact ha.1.1

private theorem target_rank_zero (hpre : Pre P L mem0)
    {g : Nat} {d : Wg1Mma.D} {e : Event} {o : Option TState}
    {sp : TcCommit.Spec} {m : Loc} {rank : Fin 16} (hg : g < L.threads)
    (hf : (Machine.machine P L g).Fired (some (.mma d)) e o)
    (hk : e.kind = .tc (.commit sp)) (htgt : TcCommit.target sp rank = some m) :
    rank = 0 := by
  obtain ⟨sp', hk', _, hTargets⟩ := RingCommitEvents.commit_issue hpre hg
    (RingCommitEvents.commit_site hf hk) hf
  obtain rfl := TcKind.commit.inj (Kind.tc.inj (hk.symm.trans hk'))
  rw [hTargets] at htgt
  split at htgt
  · assumption
  · cases htgt

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) {g i : Nat}
include hpre hX hs ht

/-- The query-copy commit has been observed by a dequantizer of any exited CTA. -/
theorem query_commit_exit_order {d : Wg1Mma.D} {sp : TcCommit.Spec} {m : Loc} {rank : Fin 16}
    (hi : X.Commit (g, i) sp) (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hSite : d.site = .qCopyCommit) (hTarget : TcCommit.target sp rank = some m)
    (hx : CtaExited L X (ctaOf L g)) :
    RecordExitOrder L X (.async (g, i) (.tcNotify rank)) (ctaOf L g) := by
  let c := ctaOf L g
  have hg := Frame.lt_of_get hX hi.choose_spec
  have hc : c < L.grid := NamedBar.cta_lt hg
  obtain ⟨w, j, tag, hwCta, hPoll⟩ := wg2_query_poll hpre hX hs ht hc hx
  obtain ⟨issuer, cm, cmTag, spec, cmRank, q, hCommit, hIssuer, hQ, hState, hObs⟩ :=
    QueryCopy.observe_query_copy_commit hpre hX (fun t ht' => (hs t ht').machine) ht hPoll
  obtain ⟨_, hLeader⟩ := Wg1MmaLeader.cta_issuer (cta := c) hpre hX
    (fun t ht' => (hs t ht').machine)
  have hgEq := (hLeader issuer cm q hIssuer hState (by simp [hQ])).trans
    (hLeader g i d rfl hd (by simp [hSite])).symm
  subst issuer
  have hSame := QueryTmaSites.commit_site_unique hi.choose_spec hCommit hd hState hSite hQ
  subst cm
  have hSpec := TcKind.commit.inj (Kind.tc.inj (congrArg Event.kind
    (Option.some.inj (hi.choose_spec.symm.trans hCommit))))
  subst spec
  obtain ⟨hObsTarget, hp⟩ := commit_notify_present hX hCommit hObs
  obtain ⟨o, hf⟩ := ((hs g hg).machine.produces (hX.thr g hg)).fired_at hCommit hd
  have hRank := (target_rank_zero hpre hg hf rfl hTarget).trans
    (target_rank_zero hpre hg hf rfl hObsTarget).symm
  subst cmRank
  have hExit : CtaExited L X (ctaOf L w) := hwCta ▸ hx
  have hFinished := record_exit_order hX hp hObs hExit
  simpa only [hwCta, c] using hFinished

/-- The observed commit satisfies the shared lifetime check. -/
theorem query_commit_finished {d : Wg1Mma.D} {sp : TcCommit.Spec} {m : Loc} {rank : Fin 16}
    (hi : X.Commit (g, i) sp) (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hSite : d.site = .qCopyCommit) (hTarget : TcCommit.target sp rank = some m)
    (hx : CtaExited L X (ctaOf L g)) :
    SharedFinished L kernel Assumptions.all X (.async (g, i) (.tcNotify rank)) (ctaOf L g) :=
  (query_commit_exit_order hpre hX hs ht hi hd hSite hTarget hx).finished

/-- The elected query TMA producer acquires the phase covering each query tile before it exits. -/
theorem query_load_finished {tile : Fin 8}
    (hi : X.TensorIssue (g, i) (P.param1Base + Wg1Mma.qMapOff)
      (MmaDataTrace.queryTmaSpec P L g tile)) (hx : CtaExited L X (ctaOf L g)) :
    SharedFinished L kernel Assumptions.all X (.async (g, i) (.notify .load)) (ctaOf L g) := by
  let c := ctaOf L g
  let hSound := fun t ht' => (hs t ht').machine
  have hc : c < L.grid := NamedBar.cta_lt (Frame.lt_of_get hX hi.choose_spec)
  obtain ⟨w, j, _, _, hPoll⟩ := wg2_query_poll hpre hX hs ht hc hx
  obtain ⟨issuer, cm, _, _, _, q, hCommit, hIssuer, hQ, hState, _⟩ :=
    QueryCopy.observe_query_copy_commit hpre hX hSound ht hPoll
  have hMbar : (MmaDataTrace.queryTmaSpec P L g tile).mbar = QueryTmaRecords.object L c := by
    simp [MmaDataTrace.queryTmaSpec, Wg1Mma.qTmaAddr_eq, c]
  obtain ⟨_, d, tile', hd, hSite, _⟩ :=
    QueryTmaRecords.issue_source hpre hX hSound ht hi.choose_spec rfl hMbar
  obtain ⟨_, hLeader⟩ := Wg1MmaLeader.cta_issuer (cta := c) hpre hX hSound
  have hgEq := (hLeader issuer cm q hIssuer hState (by simp [hQ])).trans
    (hLeader g i d rfl hd (by simp [hSite])).symm
  subst issuer
  have hS := hSound g (Frame.lt_of_get hX hCommit)
  obtain ⟨k, e, r, _, _, he, hr, hR, _, _⟩ :=
    QueryCopyHistory.query_copy_site_before_commit (0 : Fin 16) hpre hX hS
      hCommit hState hQ
  obtain ⟨p, _, _, _, _, _, hWait⟩ := QueryTmaHistory.wait_before_copy hpre hX hS he hr hR
  have hObs := QueryTmaWait.tile_observed hpre hX hSound ht hi hWait
  exact load_notify_finished hX hObs hx

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetime
