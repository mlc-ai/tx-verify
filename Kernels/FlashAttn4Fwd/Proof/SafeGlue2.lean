-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Safety.TcAccess
public import Kernels.FlashAttn4Fwd.Proof.Safety.WarpSync
public import Kernels.FlashAttn4Fwd.Proof.Protocol.TmemReach
public import Kernels.FlashAttn4Fwd.Proof.Protocol.TmemReachGates
public import Kernels.FlashAttn4Fwd.Proof.Protocol.ORoute
public import Kernels.FlashAttn4Fwd.Proof.Protocol.PReadyObj
public import Kernels.FlashAttn4Fwd.Proof.Protocol.P2Obj
public import Kernels.FlashAttn4Fwd.Proof.Protocol.P2Warp
public import Kernels.FlashAttn4Fwd.Proof.Protocol.P2Init
public import Kernels.FlashAttn4Fwd.Proof.Protocol.ScoreSFull
public import Kernels.FlashAttn4Fwd.Proof.Protocol.ScoreSFullUnits
public import Kernels.FlashAttn4Fwd.Proof.Protocol.OFullHandoff
public import Kernels.FlashAttn4Fwd.Proof.Protocol.OAccReady
public import Kernels.FlashAttn4Fwd.Proof.Protocol.InitFirst
public import Kernels.FlashAttn4Fwd.Proof.Protocol.HsInitProof
public import Kernels.FlashAttn4Fwd.Proof.Protocol.TmemLife
public import Kernels.FlashAttn4Fwd.Proof.Protocol.PairAlloc
public import Kernels.FlashAttn4Fwd.Proof.Protocol.FloatsSources
public import Kernels.FlashAttn4Fwd.Proof.Protocol.OutputRegion
public import Kernels.FlashAttn4Fwd.Proof.Protocol.TcMmaSourcesDone
public import Kernels.FlashAttn4Fwd.Proof.Protocol.TcMmaSourcesA
public import Kernels.FlashAttn4Fwd.Proof.Protocol.TcMmaSourcesAcc
public import Kernels.FlashAttn4Fwd.Proof.Protocol.TcMmaSourcesValues
public import Kernels.FlashAttn4Fwd.Proof.Protocol.LifetimePeer
public import Kernels.FlashAttn4Fwd.Proof.Protocol.LifetimeCopy
public import Kernels.FlashAttn4Fwd.Proof.Protocol.LifetimeMma
public import Kernels.FlashAttn4Fwd.Proof.Protocol.LifetimeCommit
public import Kernels.FlashAttn4Fwd.Proof.SafeGlue
public import Kernels.FlashAttn4Fwd.Proof.FloatsGlue
public import Kernels.FlashAttn4Fwd.Proof.TcFacts
public import Kernels.FlashAttn4Fwd.Proof.Thread.ElectFull

@[expose] public section

/-! # The score, Tensor Memory, value and lifetime branches' protocol inputs

This file sits at the top of the proof tree, outside the layer order (as `SafeFacts.lean` does):
it builds, from the thread layer's interface structures, the protocols' exports that the safety
branches take.

* **The routes** (`routeCtx`): the context of the reuse paths through the S-full, O-full, P-ready
  and statistics objects (`Score.RouteCtx`), from the thread facts, the barriers' first
  initializations (`InitFirst.*`), the commit premises (`Score.sFullCommit`, `OAcc.oFullCommit`)
  and the full election mask (`elect_full`).
* **The handoffs** (`handoffs`): the S-full, P-ready, second P-ready, O-full handoffs, the second
  P-ready gate and the accumulator's readiness, each from the reuse paths.
* **The Tensor Memory lifetime** (`tmemLifetime`, `tmemLive`, `mmaLive`): an access is allocated
  (`TmemLife.allocOwn`, and the paired allocation for the other CTA's cells,
  `PairAlloc.coversPeer`), and it completes before every release of a covering allocation
  (`mmaDoneDealloc`, `waitDealloc`), as `Safety.no_access_unsafe` reads them.
* **The values** (`valueCtx`): the context of the MMA values (`TcMmaSources.ValueCtx`).
* **The exits** (`lifetimeSafe'`): the four finished premises of the shared lifetimes
  (`Lifetime.peerThreadFinished`, `copyFinished`, `mmaFinished`, `commitFinished`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma Tmem.Pair

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The context of the routes**, from the thread facts. -/
theorem routeCtx (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hr : RouteFacts L X) (hp : PReadyFacts L X) (h2 : P2Facts L X) (hs : SFullFacts L X)
    (ho : OFullFacts L X) (hst : StatsFacts L X) (htm : TmemFacts L X) (hi : InitFacts L X)
    (hc : ClusterFacts L X) (hsoft : Stats.SoftArrives L X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, kernel.CanonicalSpin pc exit) : Score.RouteCtx P L mem0 kernel asms X where
  pre := hpre
  cons := hX
  rt := hr
  pf := hp
  p2 := h2
  sf := hs
  ofa := ho
  stf := hst
  tm := htm
  ini := hi
  pinit := InitFirst.pReadyInit hpre hX hc htm hi hp
  p2init := InitFirst.p2Init hpre hX hc htm hi h2
  sinit := InitFirst.sFullInit hpre hX hc htm hi hs
  oinit := InitFirst.oFullInit hpre hX hc htm hi ho
  scom := Score.sFullCommit hX hs
  ocom := OAcc.oFullCommit hX ho
  soft := hsoft
  spin := hspin
  efull := fun he => elect_full hX he

/-- **The handoffs of the Tensor Memory objects.** -/
structure Handoffs (L : Launch) (X : Execution) : Prop where
  sFull : Score.SFullHandoff L X
  pReady : Score.PReadyHandoff L X
  p2Handoff : Score.P2Handoff L X
  p2Gate : Score.P2Gate L X
  oFull : OAcc.OFullHandoff L X
  oReady : OAcc.OReady L X

/-- **Every handoff**, from the context of the routes. -/
theorem handoffs (H : Score.RouteCtx P L mem0 kernel asms X) (ht : ScoreFacts L X) :
    Handoffs L X := by
  have hS : Score.SFullHandoff L X := Score.sFullHandoff H.pre H.cons H.sf
    (Score.sFullUnits_of_facts H.cons H.sf H.tm H.ini H.sinit (Score.sFullReach H))
  have hO : OAcc.OFullHandoff L X :=
    OAcc.oFullHandoff_of_facts H.pre H.cons H.ofa H.tm H.ini H.oinit
    (Score.oFullReach H)
  have h2 : Score.P2Handoff L X := Score.p2Handoff H.pre H.cons H.p2 H.tm H.p2init (Score.p2Reach H)
  exact ⟨hS, Score.pReadyHandoff H.pre H.cons H.pf H.tm H.pinit (Score.pReadyReach H), h2,
    Score.p2Gate_of H.cons H.pre ht H.p2 h2, hO, OAcc.oready ht hS hO (OAcc.oRoute H)⟩

/-- **The other barriers' records are fault-free**, from the context of the routes. -/
theorem otherFaultFree (H : Score.RouteCtx P L mem0 kernel asms X) (hc : ClusterFacts L X)
    (ha : AsyncFacts P L X) (ho : OutputFacts L X) (hspare : Faults.SpareUnused L X) :
    Safety.OtherFaultFree L X :=
  Faults.otherFaultFree_of_route H hc ha ho hspare

/-- **The four lifetime premises of the Tensor Memory accesses.** -/
theorem tmemLifetime (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hst : StatsFacts L X) (ht : ScoreFacts L X) (ho : OAccFacts L X) (htc : TcFacts L X)
    (htm : TmemFacts L X) (hi : InitFacts L X) (hc : ClusterFacts L X) (hl : TmemLifeFacts L X)
    (hO : OAcc.OFullHandoff L X) :
    Safety.AllocBefore L X ∧ Safety.PeerCovers L X ∧ Safety.MmaDoneDealloc L X ∧
      Safety.WaitDealloc L X :=
  have hs := fun cta => HsInitProof.hsInit hpre hX hc htm hi cta
  ⟨fun hacc hcta => TmemLife.allocOwn hpre hX hst ht hl hacc hcta,
    fun hacc hne => by
      obtain ⟨-, hpair, hcol, -⟩ := Safety.access_info ht ho htc hacc
      obtain ⟨j, pc, grp, dst, n, hal, hlen, hhb⟩ := TmemLife.allocAt hpre hX hst ht hl hacc
      exact PairAlloc.coversPeer hpre hX htm hal hlen hhb hpair hne hcol,
    fun hi' hd hpair => TmemLife.mmaDoneDealloc hpre hX hst ht hO hl hi' hd hpair,
    fun hh h12 hk hd hpair => TmemLife.waitDealloc hpre hX hst htm hl hs hh h12 hk hd hpair⟩

/-- **Every MMA's access is live**: no release of a covering allocation precedes the MMA's
completion. -/
theorem mmaLive (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) (ht : ScoreFacts L X)
    (ho : OAccFacts L X) (htc : TcFacts L X) (htm : TmemFacts L X)
    (hmd : Safety.MmaDoneDealloc L X) : TcMmaSources.MmaLive L X := by
  intro i cell hi hacc cta r hr hcov rel hrel
  obtain ⟨-, hcta, -, -⟩ := Safety.access_info ht ho htc (Or.inl hacc)
  obtain ⟨-, -, -, hown, -⟩ := hcov
  obtain ⟨hlc, -⟩ := record_info hX (Safety.tmemWarpOps hpre htm) hr
  obtain ⟨pc, grp, a, n, hd, hdc⟩ := Safety.release_cta hpre hX htm hr hrel
  exact hmd hi hd (by rw [hdc, ← hlc, ← hown, hcta])

/-- **Every Tensor Memory access completes before every release of a covering allocation.** -/
theorem tmemLive (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) (ht : ScoreFacts L X)
    (ho : OAccFacts L X) (htc : TcFacts L X) (htm : TmemFacts L X)
    (hmd : Safety.MmaDoneDealloc L X) (hwd : Safety.WaitDealloc L X) : Floats.TmemLive L X := by
  intro e cell hacc cta r hr hcov d hrel
  obtain ⟨he, hcta, -, hk⟩ := Safety.access_info ht ho htc hacc
  have hown := Safety.covers_owner hcov
  obtain ⟨hlc, -⟩ := record_info hX (Safety.tmemWarpOps hpre htm) hr
  obtain ⟨pc, grp, a, n, hd, hdc⟩ := Safety.release_cta hpre hX htm hr hrel
  exact Safety.access_done ht ho hmd hwd he hk hd (by rw [hdc, ← hlc, ← hown, hcta])

/-- **The context of the MMA values.** -/
theorem valueCtx (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) (ht : ScoreFacts L X)
    (ho : OAccFacts L X) (htc : TcFacts L X) (htt : TcMmaThreadFacts L X) (hF : P2Facts L X)
    (hh : Handoffs L X) (hlive : TcMmaSources.MmaLive L X) (hsm : TcMmaSources.SmemElements X)
    (hfl : FloatFacts L X) (hcc : Floats.CorrCover L X) (htl : Floats.TmemLive L X)
    (hsg : SyncGuarded L kernel X) (hsc : Floats.SoftCover L X)
    (hst : ∀ {h j pc : Nat} {a : Acc} {bs : List (Option Byte)}, h < L.threads →
      8 ≤ warpOf L h → warpOf L h < 12 → X.get (h, j) = some ⟨pc, .rd a bs⟩ →
      (∀ {g i : Nat}, g < L.threads → warpOf L g < 8 → ctaOf L g = ctaOf L h →
        i < (X.tr g).length → baseCausality L X (g, i) (h, j) → ∀ k < i,
          ∀ pc a' (vals' : List Value), X.get (g, k) = some ⟨pc, .tc (.ld a' vals' .s32x32b)⟩ →
            F32s vals') → ∃ x, F32Read bs x) :
    TcMmaSources.ValueCtx P L mem0 X where
  pre := hpre
  cons := hX
  score := ht
  oacc := ho
  tc := htc
  thread := htt
  p2 := hF
  sFull := hh.sFull
  pReady := hh.pReady
  p2Handoff := hh.p2Handoff
  p2Gate := hh.p2Gate
  oReady := hh.oReady
  live := hlive
  smem := hsm
  floats := hfl
  corrCover := hcc
  tmemLive := htl
  guard := hsg
  softCover := hsc
  stats := hst

/-- **The shared bytes' lifetimes**, from the exit facts. -/
theorem lifetimeSafe' (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hr : RingFacts L X) (hcp : RingCopies P L X) (htm : TmemFacts L X) (hs : ScoreFacts L X)
    (hst : StatsFacts L X) (ho : OutputFacts L X) (hc : ClusterFacts L X) (ha : AsyncFacts P L X)
    (hi : InitFacts L X) (hx : ExitFacts P L X) (hof : OFullFacts L X) (hsf : SFullFacts L X)
    (hh : Handoffs L X) (hsel : Lifetime.SelectedPerformed asms X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, kernel.CanonicalSpin pc exit) : ¬ SharedLifetimeUnsafe L kernel asms X :=
  have hhs := fun cta => HsInitProof.hsInit hpre hX hc htm hi cta
  have hring := InitFirst.ringInit hpre hX hc htm hi hr
  lifetimeSafe hpre hX hr hcp htm hs ho hc ha
    (Lifetime.peerThreadFinished hpre hX htm hst hc ha hx hhs)
    (Lifetime.copyFinished hpre hX hr hcp htm ha hx hhs hring)
    (Lifetime.mmaFinished hpre hX hs ha hx hh.oFull hspin)
    (Lifetime.commitFinished hpre hX hr htm hof hsf hx hring hh.oFull hh.sFull hsel hspin)

end
end PTX.Kernels.FlashAttn4Fwd.Proof
