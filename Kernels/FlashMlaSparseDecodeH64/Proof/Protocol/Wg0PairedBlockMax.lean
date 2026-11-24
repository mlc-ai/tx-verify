-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PairedReferenceHistory
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0VoteSuccessor
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityUnique
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0MaxTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteBranch
import Lemmas.Order.OrderWaits
import Lemmas.Order.OrderBaseCausality

@[expose] public section

/-! # Paired softmax lanes read the same two local maxima in opposite order -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PairedReference

open PTX PTX.Flow PTX.Assumption Wg0 MachineTracking

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An actual local maximum store of this sparse block. -/
structure RowMaxVisit (P : Params) (L : Launch) (X : Execution)
    (g j block : Nat) (d : D) : Prop where
  state : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d))
  site : d.site = .rowMax
  blockEq : d.block = block
  write : ∃ a, X.Writes (g, j) a (rowLocalMax L d).toBytes

private theorem row_max_unique {g i j block : Nat} {d q : D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hi : RowMaxVisit P L X g i block d) (hj : RowMaxVisit P L X g j block q) :
    d = q := by
  obtain ⟨_, tag, hGet⟩ := hi.write
  obtain ⟨_, tag', hGet'⟩ := hj.write
  have hg := Frame.lt_of_get hX hGet
  have hsub {k : Nat} {w : D} {e : Event}
      (h : RowMaxVisit P L X g k block w) (he : X.get (g, k) = some e) : w.sub = 0 := by
    obtain ⟨_, _, _, _, hI, _, _⟩ := Frame.fired_site hs hX he h.state
    have hI' : Inv P L g w := hI
    have hBound := hI'.subLt
    rw [h.site] at hBound
    change w.sub < 1 at hBound
    omega
  have hSame : Bound.rank P L g (.wg0 d) = Bound.rank P L g (.wg0 q) := by
    simp only [Bound.rank, Bound.wg0Rank, Bound.wg0Block, hi.site, hj.site,
      hi.blockEq, hj.blockEq, hsub hi hGet, hsub hj hGet']
  have hEq : i = j := by
    by_contra hn
    rcases Nat.lt_or_gt_of_ne hn with hlt | hlt
    · have h := Wg0ProbabilityUnique.rank_strict_of_counted hpre hX (hs g hg).machine ht
        hGet rfl (PTX.len_of_get hGet').le hi.state hj.state hlt
      omega
    · have h := Wg0ProbabilityUnique.rank_strict_of_counted hpre hX (hs g hg).machine ht
        hGet' rfl (PTX.len_of_get hGet).le hj.state hi.state hlt
      omega
  have h := hi.state
  rw [hEq, hj.state] at h
  exact (Machine.ThreadD.wg0.inj (Option.some.inj (Option.some.inj h))).symm

private theorem max_read_step {g : Nat} {q d : D} {e : Event}
    (hsite : q.site = .maxRead)
    (hn : Machine.next P L g (.wg0 q) e = some (some (.wg0 d))) :
    ∃ a bytes peer, e.kind = .rd a bytes ∧ rebuild 3 bytes = .ok peer ∧ q.block = d.block ∧
      peerMaxE (rowLocalMax L q) peer = .ok d.blockMax := by
  simp only [Machine.next] at hn
  split at hn
  · rename_i v hNext
    cases hn
    simp only [Wg0.next, nextSite, hsite] at hNext
    split at hNext
    · rename_i a bytes hKind
      split at hNext
      · obtain ⟨peer, hBytes, hMap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hNext)
        obtain ⟨_, hValue, rfl⟩ := Option.map_eq_some_iff.mp hMap
        simp only [withPeerMax, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hValue
        obtain ⟨m, hm, _, _, _, _, _, _, _, _, rfl⟩ := hValue
        refine ⟨a, bytes, peer, hKind, ?_, rfl, ?_⟩
        · cases h : rebuild 3 bytes <;> simp_all [Except.toOption]
        · change peerMaxE (rowLocalMax L q) peer = .ok m
          cases h : peerMaxE (rowLocalMax L q) peer <;> simp_all [Except.toOption]
      · cases hNext
    · cases hNext
  · split_ifs at hn <;> cases hn
  · cases hn

/-- The actual vote combines the local maximum stores of its lane and its paired lane. -/
theorem visit_of_vote {g i : Nat} {d : D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hg : g < L.threads)
    (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleVote) :
    ∃ j k own peer, RowMaxVisit P L X g j d.block own ∧
      RowMaxVisit P L X (Wg0PeerSources.partner L g) k d.block peer ∧
      d.scoreSums = own.scoreSums ∧
      peerMaxE (rowLocalMax L own) (rowLocalMax L peer) = .ok d.blockMax := by
  obtain ⟨r, e, q, hr, he, hq, hMax, hSums⟩ :=
    Wg0MaxTrace.maxRead_before_vote hX hs hg hi hd hsite
  have hLen : r ≤ (X.tr g).length := (PTX.len_of_get he).le
  have hn : Machine.next P L g (.wg0 q) e = some (some (.wg0 d)) := by
    rw [← hr, Frame.stateAt_succ he, hq] at hd
    exact hd
  obtain ⟨a, bytes, w, hKind, hBytes, hBlock, hValue⟩ := max_read_step hMax hn
  have hRead : X.Reads (g, r) a bytes := by
    obtain ⟨tag, kind⟩ := e
    cases hKind
    exact ⟨tag, he⟩
  obtain ⟨k, peer, fp, hPeer, hPeerSite, hPeerBlock, hPeerWrite, hRebuild⟩ :=
    Wg0MaxReadback.readback_value hpre hX hs ht hRead hq hMax
  have hPeerWord : w = rowLocalMax L peer := Except.ok.inj (hBytes.symm.trans hRebuild)
  obtain ⟨b, bar, _, hrb, hBar, hBarBlock, hBarState, _⟩ :=
    Wg0MaxTrace.barrier_before_maxRead hpre hX hs hg hLen hq hMax
  obtain ⟨j, own, op, hOwnExit, hOwnSite, hOwnBlock, hOwn, hOwnWrite, _, _⟩ :=
    Wg0MaxTrace.rowMax_before_barrier hpre hX hs hg (by omega) hBarState hBar
  obtain ⟨j', own', hAt, hOwn', _, _, hOwnSums⟩ :=
    Wg0MaxTrace.rowMax_state_before_maxRead hX hs hg hLen hq hMax
  have hJ : j' = j := by omega
  rw [hJ, hOwn] at hOwn'
  obtain rfl := Machine.ThreadD.wg0.inj (Option.some.inj (Option.some.inj hOwn'))
  refine ⟨j, k, own, peer, ?_, ⟨hPeer, hPeerSite, hPeerBlock.trans hBlock, fp, hPeerWrite⟩,
    hSums.trans hOwnSums, ?_⟩
  · exact ⟨hOwn, hOwnSite, hOwnBlock.trans (hBarBlock.trans hBlock), op, hOwnWrite⟩
  · have hf : rowLocalMax L q = rowLocalMax L own := by simp only [rowLocalMax, hOwnSums]
    rwa [hf, hPeerWord] at hValue

/-- The row maxima used by a followed vote come from its causal prefix. -/
theorem causal_visit_of_vote {g i cut : Nat} {d : D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hg : g < L.threads) (hCut : i ≤ cut) (hLen : cut < (X.tr g).length)
    (hPrior : ∀ t, baseCausality L X t (g, cut) → ¬ Dismisses P L X t)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleVote) :
    ∃ j k own peer, RowMaxVisit P L X g j d.block own ∧
      RowMaxVisit P L X (Wg0PeerSources.partner L g) k d.block peer ∧
      j ≤ cut ∧ baseCausality L X (Wg0PeerSources.partner L g, k) (g, cut) ∧
      d.scoreSums = own.scoreSums ∧
      peerMaxE (rowLocalMax L own) (rowLocalMax L peer) = .ok d.blockMax := by
  obtain ⟨r, e, q, hr, he, hq, hMax, hSums⟩ :=
    Wg0MaxTrace.maxRead_before_vote hX hs hg (hCut.trans hLen.le) hd hsite
  have hReadLen : r ≤ (X.tr g).length := (PTX.len_of_get he).le
  have hn : Machine.next P L g (.wg0 q) e = some (some (.wg0 d)) := by
    rw [← hr, Frame.stateAt_succ he, hq] at hd
    exact hd
  obtain ⟨a, bytes, w, hKind, hBytes, hBlock, hValue⟩ := max_read_step hMax hn
  have hRead : X.Reads (g, r) a bytes := by
    obtain ⟨tag, kind⟩ := e
    cases hKind
    exact ⟨tag, he⟩
  have hVoteLen : i < (X.tr g).length := hCut.trans_lt hLen
  have hVote : X.get (g, i) = some ((X.tr g)[i]'hVoteLen) := List.getElem?_eq_getElem hVoteLen
  have hAcc := vote_event_nonaccess hX hs hVote hd hsite
  have hNone : (X.get (g, i)).bind Event.acc = none := by rw [hVote]; exact hAcc
  have hStep : baseCausality L X (g, r) (g, i) :=
    .single (.inl (po_of_not_access rfl (by omega) hVoteLen hNone))
  have hBeforeCut : baseCausality L X (g, r) (g, cut) := by
    rcases Nat.eq_or_lt_of_le hCut with rfl | hlt
    · exact hStep
    · exact hStep.trans (.single (.inl (po_of_source_not_access rfl hlt hLen hNone)))
  obtain ⟨k, peer, fp, hPeer, hPeerSite, hPeerBlock, hPeerWrite, hBefore, hRebuild⟩ :=
    Wg0MaxReadback.actual_readback_value hpre hX hs hRead hq hMax
      (show r ≤ cut by omega) hLen hPrior
  have hPeerWord : w = rowLocalMax L peer := Except.ok.inj (hBytes.symm.trans hRebuild)
  obtain ⟨b, bar, _, hrb, hBar, hBarBlock, hBarState, _⟩ :=
    Wg0MaxTrace.barrier_before_maxRead hpre hX hs hg hReadLen hq hMax
  obtain ⟨j, own, op, hOwnExit, hOwnSite, hOwnBlock, hOwn, hOwnWrite, _, _⟩ :=
    Wg0MaxTrace.rowMax_before_barrier hpre hX hs hg (by omega) hBarState hBar
  obtain ⟨j', own', hAt, hOwn', _, _, hOwnSums⟩ :=
    Wg0MaxTrace.rowMax_state_before_maxRead hX hs hg hReadLen hq hMax
  have hJ : j' = j := by omega
  rw [hJ, hOwn] at hOwn'
  obtain rfl := Machine.ThreadD.wg0.inj (Option.some.inj (Option.some.inj hOwn'))
  refine ⟨j, k, own, peer, ?_, ⟨hPeer, hPeerSite, hPeerBlock.trans hBlock, fp, hPeerWrite⟩,
    by omega, hBefore.trans hBeforeCut, hSums.trans hOwnSums, ?_⟩
  · exact ⟨hOwn, hOwnSite, hOwnBlock.trans (hBarBlock.trans hBlock), op, hOwnWrite⟩
  · have hf : rowLocalMax L q = rowLocalMax L own := by simp only [rowLocalMax, hOwnSums]
    rwa [hf, hPeerWord] at hValue

private theorem actual_prefix {g i : Nat} {d : D}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) :
    ∃ k ≤ (X.tr g).length, g < L.threads ∧
      Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d)) := by
  let len := (X.tr g).length
  have hTrace : 0 < len := by
    by_contra! hn
    have hz : X.tr g = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hEq : Frame.stateAt (Machine.code P L) X g i =
        Frame.stateAt (Machine.code P L) X g 0 := by
      simp only [Frame.stateAt, hz, List.take_nil]
      rfl
    rw [hEq, Frame.stateAt_zero] at hd
    cases hd
  have hGet : ∃ e, X.get (g, 0) = some e := ⟨_, List.getElem?_eq_getElem hTrace⟩
  have hg := Frame.lt_of_get hX hGet.choose_spec
  by_cases h : i ≤ len
  · exact ⟨i, h, hg, hd⟩
  · refine ⟨len, le_rfl, hg, ?_⟩
    have hTake := List.take_of_length_le (show (X.tr g).length ≤ i by omega)
    change (Machine.machine P L g).after (Machine.machine P L g).init ((X.tr g).take i) = _ at hd
    change (Machine.machine P L g).after (Machine.machine P L g).init
      ((X.tr g).take (X.tr g).length) = _
    rw [List.take_length]
    rwa [hTake] at hd

private theorem partner_involutive {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) (hw : warpOf L g < 4) :
    Wg0PeerSources.partner L (Wg0PeerSources.partner L g) = g := by
  let a := Wg0PeerSources.partner L g
  let b := Wg0PeerSources.partner L a
  obtain ⟨hA, hWg, hTa⟩ := Wg0MaxReadback.partner_geometry hpre hg hw
  have hWarpA := Wg0.warpLt hpre hWg
  obtain ⟨hB, hWg', hTb⟩ := Wg0MaxReadback.partner_geometry hpre hA.1 hWarpA
  have hlim {t : Nat} (h : warpOf L t < 4) : tidOf L t < 128 := by
    change tidOf L t / 32 < 4 at h
    omega
  rw [Nat.mod_eq_of_lt (hlim hWarpA), Nat.mod_eq_of_lt (hlim hw)] at hTa
  rw [Nat.mod_eq_of_lt (hlim (Wg0.warpLt hpre hWg')), Nat.mod_eq_of_lt (hlim hWarpA)] at hTb
  have hx : ∀ t : Fin 128, (t.val ^^^ 64) ^^^ 64 = t.val := by decide
  have hTid : tidOf L b = tidOf L g := by
    rw [hTb, hTa]
    exact hx ⟨tidOf L g, hlim hw⟩
  have hCta : b / L.block = g / L.block := hB.2.2.trans hA.2.2
  rw [tidOf_eq hpre, tidOf_eq hpre] at hTid
  rw [hpre.block] at hCta
  change b = g
  omega

/-- Actual matched votes have the same canonical maximum because each reads the other
lane's unique local maximum of this block. -/
theorem actual_paired_block_max
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hv : Wg0PeerQkValues.QkValues P L X) :
    PairedBlockMax P L X := by
  intro g i j d q hd hq hD hQ hBlock
  obtain ⟨i', hi, hg, hd⟩ := actual_prefix hX hd
  obtain ⟨j', hj, hh, hq⟩ := actual_prefix hX hq
  have hw := Wg0.warpLt hpre (RingRoleGeometry.of_trace hX hg (hs g hg).machine hd)
  have hMate := partner_involutive hpre hg hw
  obtain ⟨a, b, own, peer, hOwn, hPeer, hOwnWords, hL⟩ :=
    visit_of_vote hpre hX hs ht hg hi hd hD
  obtain ⟨c, e, other, partner, hOther, hPartner, hOtherWords, hR⟩ :=
    visit_of_vote hpre hX hs ht hh hj hq hQ
  rw [hBlock] at hOther hPartner
  rw [hMate] at hPartner
  have hOwnEq := row_max_unique hpre hX hs ht hPartner hOwn
  have hPeerEq := row_max_unique hpre hX hs ht hPeer hOther
  rw [hOwnEq, ← hPeerEq] at hR
  obtain ⟨_, hSums⟩ := Wg0VoteSuccessor.inputs_of_vote hpre hX hs ht hv hg hi hd hD
  obtain ⟨_, hSums'⟩ := Wg0VoteSuccessor.inputs_of_vote hpre hX hs ht hv hh hj hq hQ
  rw [hOwnWords] at hSums
  rw [hOtherWords, ← hPeerEq] at hSums'
  obtain ⟨m, hm⟩ := Wg0.rowLocalMax_of_masked hpre hSums
  obtain ⟨n, hn⟩ := Wg0.rowLocalMax_of_masked hpre hSums'
  rw [hm, hn, Wg0.peerMaxE_peak] at hL hR
  exact ⟨max m n, (Except.ok.inj hL).symm,
    (Except.ok.inj hR).symm.trans (congrArg peakVal (max_comm n m))⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PairedReference
