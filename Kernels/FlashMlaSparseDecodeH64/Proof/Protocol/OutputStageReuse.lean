-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputReuseComplete
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PvIssueHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityHistory

@[expose] public section

/-! # Shared byte order from dequantization to output staging -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputStageReuse

open PTX PTX.Flow AsyncCopy

/-- A byte of a vector store to a dequantization ring slot. -/
def dequantStoreByte (L : Launch) (cta : Nat) (lane : Fin 128) (buf : Nat)
    (r : Fin 4) (s : Fin 8) (b : Fin 16) : Loc :=
  ⟨.shared, cta, L.sharedBase + Wg2.tileBase buf +
    Wg2.tileOff L (GemmRing.producer L cta lane) r.val s.val + b.val⟩

private theorem producer_cta {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) (cta : Nat) (lane : Fin 128) :
    ctaOf L (GemmRing.producer L cta lane) = cta := by
  have hl := lane.isLt
  simp only [RawRing.consumer, ctaOf, hpre.block]
  omega

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Invert an actual dequantization write footprint at any byte covered by it. -/
theorem dequantStoreByte_of_cover {cta j : Nat} {lane : Fin 128} {dq : Wg2.D} {r : Fin 4}
    {s : Fin 8} {e : Event} {u : TState} {a : Acc} {bytes : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hstore : dq.site = .store r s)
    (hf : (Wg2.machine P L (GemmRing.producer L cta lane)).Fired (some (.inr dq)) e (some u))
    (he : X.get (GemmRing.producer L cta lane, j) = some e)
    (hwrite : X.Writes (GemmRing.producer L cta lane, j) a bytes) (hcover : a.Covers l) :
    ∃ b : Fin 16, l = dequantStoreByte L cta lane dq.buf r s b := by
  obtain ⟨fp, hkind, hloc, hsize⟩ := Wg2.fired_store_event hpre hstore hf
  obtain ⟨tag, hget⟩ := hwrite
  have hk := congrArg Event.kind (Option.some.inj (he.symm.trans hget))
  rw [hkind] at hk
  obtain ⟨rfl, _⟩ := Kind.wr.inj hk
  obtain ⟨hspace, hcta, hlow, hhigh⟩ := hcover
  have hbound : l.addr - fp.loc.addr < 16 := by omega
  have heq : l = fp.loc.at (l.addr - fp.loc.addr) := by
    cases l
    have haddr : fp.loc.addr + _ = _ := Nat.add_sub_of_le hlow
    simpa [Loc.at, haddr] using And.intro hspace hcta
  have hbyte (b : Fin 16) : fp.loc.at b.val = dequantStoreByte L cta lane dq.buf r s b := by
    rw [hloc, producer_cta hpre cta lane]
    rfl
  let b : Fin 16 := ⟨l.addr - fp.loc.addr, hbound⟩
  exact ⟨b, heq.trans (hbyte b)⟩

/-- A dequantization store is ordered at an overlapping byte before an access reached
after an acquire that observed the PV issue reading that byte. -/
theorem dequant_store_before_observer {cta issuer i j dest : Nat} {lane : Fin 128} {r : Fin 4}
    {s : Fin 8} {dq : Wg2.D} {pv : Wg1Mma.D} {e : Event} {u : TState} {accum : Bool}
    {mask : List Nat} {wait : EvId} {dst : Ref} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (_ht : Frame.Tracked (Machine.code P L) X)
    (hmma : GemmRing.MmaIssuer P L X cta issuer) (hcta : ctaOf L issuer = cta)
    (he : X.get (GemmRing.producer L cta lane, j) = some e)
    (hdq : Frame.stateAt (Machine.code P L) X (GemmRing.producer L cta lane) j =
      some (some (.wg2 dq))) (hstore : dq.site = .store r s) (hblock : dq.block = pv.i)
    (hf : (Wg2.machine P L (GemmRing.producer L cta lane)).Fired (some (.inr dq)) e (some u))
    (hop : X.MmaIssue (issuer, i) dest
      (MmaDataTrace.pvOperands L issuer pv.i (MmaDataTrace.pvDequantIssue r s)) accum mask)
    (hpv : Frame.stateAt (Machine.code P L) X issuer i = some (some (.mma pv)))
    (hsite : pv.site = .pvMma (MmaDataTrace.pvDequantIssue r s))
    (hobs : ∃ scope, AsyncObserved X (issuer, i) .mmaDone wait true scope ∧
      ScopesMeet L .cluster issuer scope wait.1) (hnext : po X wait dst.issuer) (b : Fin 16)
    (htouch : ∃ a, X.MemTouches dst a ∧ a.Covers (dequantStoreByte L cta lane dq.buf r s b)) :
    ByteCausality L X (dequantStoreByte L cta lane dq.buf r s b)
      (.thread (GemmRing.producer L cta lane, j)) dst := by
  let writer := GemmRing.producer L cta lane
  let loc := dequantStoreByte L cta lane dq.buf r s b
  let slot : Fin 2 := ⟨pv.i % 2, Nat.mod_lt _ (by decide)⟩
  have hwriterCta : ctaOf L writer = cta := producer_cta hpre cta lane
  have htid : tidOf L writer = 256 + lane.val := by
    have hl := lane.isLt
    simp only [writer, RawRing.consumer, tidOf_eq hpre, hpre.block]
    omega
  have hInv : Wg2.Inv P L writer dq := hf.choose_spec.1.2
  have hbuf : dq.buf = pv.i % 2 := hInv.bufBlock.trans (congrArg (· % 2) hblock)
  obtain ⟨fp, hkind, hloc, hsize⟩ := Wg2.fired_store_event hpre hstore hf
  let bytes := (Wg2.Numeric.dequantChunk dq.raw
    (Wg2.Numeric.byteAt dq.sc (Wg2.scaleIdx L writer s.val))).toBytes
  have hwrite : X.Writes (writer, j) fp bytes := by
    obtain ⟨tag, kind⟩ := e
    change kind = _ at hkind
    exact ⟨tag, by simpa only [hkind] using he⟩
  have hbyte : fp.loc.at b.val = loc := by
    rw [hloc, hwriterCta]
    rfl
  have hcover : fp.Covers loc := by
    rw [← hbyte]
    exact Acc.covers_at (by simpa only [hsize] using b.isLt)
  have hproxy : ProxyBefore L X (writer, j) (issuer, i) loc :=
    GemmRing.dequant_proxy_before_consumer (slot := slot) hpre hX
      (fun g hg => (hs g hg).machine) hmma hcta hop.choose_spec hpv
      (by rw [hsite]; rfl) rfl he hdq ⟨r, s, hstore⟩ hblock ⟨_, _, hkind⟩ rfl rfl
  have hdone : X.AsyncPresent (issuer, i) .mmaDone := by
    obtain ⟨_, ⟨_, _, hn, _⟩, _⟩ := hobs
    obtain ⟨commit, _, rank, _, tracks, _, _, notified⟩ := hn
    exact (hX.tcCommit commit rank notified).2 _ tracks
  have hoperand := PvIssueHistory.dequant_operand_byte_observed hpre hX.tma.2.1
    (hcta.trans hwriterCta.symm) htid r s b hdone hop
  rw [hwriterCta, ← hbuf] at hoperand
  obtain ⟨value, hread⟩ := hoperand
  let part : Part := .mmaRead true (MmaDataTrace.pvDequantIndex lane s b)
  have hpart : AsyncCovers X (issuer, i) part loc :=
    ⟨{loc := loc, size := 1}, false, ⟨rfl, rfl, hread.1⟩,
      Acc.covers_at (k := 0) (show 0 < 1 by decide)⟩
  obtain ⟨scope, hObserved, hsMeet⟩ := hobs
  exact .commitOperand rfl ⟨fp, .inr (.inl ⟨_, hwrite, rfl⟩), hcover⟩
    (.inl ⟨_, _, _, _, hop⟩) ⟨value, hread⟩ (.direct ⟨hpart, .inl hproxy⟩)
    ⟨scope, hObserved, hsMeet⟩ hnext htouch

/-- A dequant store of an overlapping staging byte is ordered before a staging or output
access of the lane that observed its MMA use. -/
theorem dequant_store_before_epilogue {cta i j : Nat} {lane softmaxLane : Fin 128} {r : Fin 4}
    {s : Fin 8} {dq : Wg2.D} {out : Wg0.D} {e outEvent : Event} {u : TState} {dst : Ref}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (GemmRing.producer L cta lane, j) = some e)
    (hdq : Frame.stateAt (Machine.code P L) X (GemmRing.producer L cta lane) j =
      some (some (.wg2 dq))) (hstore : dq.site = .store r s) (hbuf : dq.buf = 1)
    (hf : (Wg2.machine P L (GemmRing.producer L cta lane)).Fired (some (.inr dq)) e (some u))
    (hout : Frame.stateAt (Machine.code P L) X (GemmRing.softmax L cta softmaxLane) i =
      some (some (.wg0 out)))
    (hsite : (∃ tile chunk, out.site = .oStage tile chunk) ∨ (∃ tile, out.site = .tmaStore tile))
    (hget : X.get (GemmRing.softmax L cta softmaxLane, i) = some outEvent)
    (hDst : dst.issuer = (GemmRing.softmax L cta softmaxLane, i)) (b : Fin 16)
    (htouch : ∃ a, X.MemTouches dst a ∧ a.Covers (dequantStoreByte L cta lane dq.buf r s b)) :
    ByteCausality L X (dequantStoreByte L cta lane dq.buf r s b)
      (.thread (GemmRing.producer L cta lane, j)) dst := by
  let g := GemmRing.softmax L cta softmaxLane
  let writer := GemmRing.producer L cta lane
  let k := MmaDataTrace.pvDequantIssue r s
  let seq (t : Nat) (ht : t < L.threads) := (hs t ht).machine
  have hg := Frame.lt_of_get hX hget
  have hCta : ctaOf L g = cta := by
    have hl := softmaxLane.isLt
    simp only [g, GemmRing.softmax, ctaOf, hpre.block]
    omega
  have hWriterCta : ctaOf L writer = cta := producer_cta hpre cta lane
  obtain ⟨_, _, _, _, hOut, _, _⟩ := Frame.fired_site hs hX hget hout
  have hLast := (show Wg0.Inv P L g out from hOut).epilogueLast (by
    rcases hsite with ⟨_, _, h⟩ | ⟨_, h⟩ <;> rw [h] <;> rfl)
  have hDq : Wg2.Inv P L writer dq := hf.choose_spec.1.2
  have hBatch : Wg2.eOf L writer = Wg0.eOf L g := by
    simp only [Wg2.eOf, Wg0.eOf, ctaidY, hWriterCta, hCta]
  have hBound := hDq.block
  rw [hDq.len0, hDq.len1, hBatch] at hBound
  change dq.block < Wg0.blocksOf P L g at hBound
  have hOdd : dq.block % 2 = 1 := hDq.bufBlock.symm.trans hbuf
  obtain ⟨issuer, hmma⟩ := GemmRing.exists_issuer (cta := cta) hpre hX seq
  rcases Nat.lt_or_eq_of_le (show dq.block ≤ out.block by omega) with hEarlier | hFinal
  · have hProb := match hsite with
      | .inl ⟨_, _, h⟩ => Wg0ProbabilityHistory.before_stage hX hg (seq g hg) hout h
      | .inr ⟨_, h⟩ => Wg0ProbabilityHistory.before_output hX hg (seq g hg) hout h
    obtain ⟨prob, hprobLt, d, p, ev, hprob, hblock, hprobSite, hgetProb, _⟩ := hProb
    obtain ⟨_, _, _, _, _, c, _, _, _, mma, _, hc, _, hd, hI, _, hSame, _, _⟩ :=
      GemmRing.qk_commit_before_probability hpre hX seq ht hmma hprob hprobSite hgetProb
    have hpast : dq.block < mma.i := (hSame.trans hblock).symm ▸ hEarlier
    obtain ⟨op, hpv, hop⟩ :=
      OutputReuseAudit.pv_issue_before_later_block hpre hX hs ht hI hc hd hOdd hpast k
    have hAsync : X.TcAsync (issuer, op) := .inl ⟨_, _, _, _, hop⟩
    have hprior : dq.block < d.block := hblock.symm ▸ hEarlier
    obtain ⟨_, w, hwLt, hFinished⟩ :=
      GemmRing.prior_pv_completion (byte := 0) hpre hX seq ht hmma hI hAsync
        hpv rfl hprior hprob hprobSite hgetProb
    obtain ⟨scope, hObs, hScopes⟩ :
        ∃ scope, AsyncObserved X (issuer, op) .mmaDone (g, w) true scope ∧
          ScopesMeet L .cluster issuer scope g := by
      rcases hFinished with ⟨kind, hVisible, _, _⟩ | ⟨scope, hObs, hScopes⟩
      · cases kind with
        | cpAsync => cases hVisible
        | bulk mode => cases mode <;> cases hVisible
      · exact ⟨scope, hObs, hScopes⟩
    obtain ⟨tag, parity, hWait⟩ := hObs.choose_spec.choose_spec.2.1
    have hnext : po X (g, w) dst.issuer := hDst ▸ po_of_source_not_access rfl
      (hwLt.trans hprobLt) (PTX.len_of_get hget) (by rw [hWait]; rfl)
    exact dequant_store_before_observer hpre hX hs ht hmma hI
      he hdq hstore rfl
      hf hop hpv rfl ⟨scope, hObs, hScopes⟩ hnext b htouch
  · have hWait := match hsite with
      | .inl ⟨_, _, h⟩ =>
        Wg0OutputVisits.pvWaitBeforeStage_state hpre hX hg (seq g hg) hOut hout h
      | .inr ⟨_, h⟩ =>
        Wg0OutputVisits.pvWaitBeforeIssue_state hpre hX hg (seq g hg) hOut hout h
    obtain ⟨w, hwlt, tag, scope, hw, d, hWaitState, hSite, hWaitBlock⟩ := hWait
    have hMatch : d.block = dq.block := hWaitBlock.trans hFinal.symm
    have hSlot : d.block % 2 = (1 : Fin 2).val := hMatch ▸ hOdd
    have hWait : X.get (g, w) =
        some ⟨tag, .wait (GemmRing.empty L cta 1) (d.block / 2 % 2) true true scope⟩ := by
      rw [hCta, ← hWaitBlock, hSlot] at hw
      exact hw
    obtain ⟨commit, ctag, spec, rank, pv, hc, hTarget, hI, hPv, hPvSite, hPvBlock, hObs⟩ :=
      OutputReuseAudit.final_pv_observed hpre hX hs ht hmma hWaitState hSite hSlot hWait
    obtain ⟨op, hopLt, hpv, hop⟩ := PvIssueHistory.pv_issue_of_commit hpre hX hs hc hPv hPvSite k
    have hk := k.isLt
    have htrack : TracksMma X (issuer, op) (issuer, commit) :=
      ⟨rfl, by omega, .inl ⟨_, _, _, _, hop⟩, spec, ctag, hc⟩
    obtain ⟨hDelivered, hObserved⟩ := hObs.waitObserves_tcNotify hWait
    have hIssuer := Frame.lt_of_get hX hc
    have hSameCta := hI.trans hCta.symm
    have hScopes : ScopesMeet L .cluster issuer scope g := by
      refine ⟨⟨hIssuer, hg, congrArg L.clusterOfCta hSameCta⟩, ?_⟩
      cases scope
      · exact ⟨hg, hIssuer, hSameCta.symm⟩
      · exact ⟨hg, hIssuer, congrArg L.clusterOfCta hSameCta.symm⟩
      · exact ⟨hg, hIssuer⟩
      · exact ⟨hg, hIssuer⟩
    have hnext : po X (g, w) dst.issuer := hDst ▸
      po_of_source_not_access rfl hwlt (PTX.len_of_get hget) (by rw [hWait]; rfl)
    exact dequant_store_before_observer (pv := ⟨.pvMma k, pv.i⟩)
      hpre hX hs ht hmma hI he hdq hstore
      (hPvBlock.trans hMatch).symm hf hop hpv rfl
      ⟨scope, ⟨_, _, ⟨_, spec, rank, rfl, htrack, ⟨ctag, hc⟩, hTarget, hDelivered⟩, hObserved⟩,
        hScopes⟩ hnext b htouch

/-- Every slot-one dequantization byte precedes a staging write that covers it. -/
theorem dequant_store_before_stage {cta i j : Nat} {lane softmaxLane : Fin 128} {r tile : Fin 4}
    {s chunk : Fin 8} {dq : Wg2.D} {out : Wg0.D} {e : Event} {u : TState} {fp : Acc}
    {bytes : List Byte} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (GemmRing.producer L cta lane, j) = some e)
    (hdq : Frame.stateAt (Machine.code P L) X (GemmRing.producer L cta lane) j =
      some (some (.wg2 dq))) (hstore : dq.site = .store r s) (hbuf : dq.buf = 1)
    (hf : (Wg2.machine P L (GemmRing.producer L cta lane)).Fired (some (.inr dq)) e (some u))
    (hout : Frame.stateAt (Machine.code P L) X (GemmRing.softmax L cta softmaxLane) i =
      some (some (.wg0 out))) (hstage : out.site = .oStage tile chunk)
    (hwrite : X.Writes (GemmRing.softmax L cta softmaxLane, i) fp bytes) (b : Fin 16)
    (hcover : fp.Covers (dequantStoreByte L cta lane dq.buf r s b)) :
    ByteCausality L X (dequantStoreByte L cta lane dq.buf r s b)
      (.thread (GemmRing.producer L cta lane, j))
      (.thread (GemmRing.softmax L cta softmaxLane, i)) := by
  exact dequant_store_before_epilogue hpre hX hs ht he hdq hstore hbuf hf hout
    (.inl ⟨tile, chunk, hstage⟩) hwrite.choose_spec rfl b
    ⟨fp, .inl ⟨true, .inr (.inl ⟨bytes, hwrite, rfl⟩)⟩, hcover⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputStageReuse
