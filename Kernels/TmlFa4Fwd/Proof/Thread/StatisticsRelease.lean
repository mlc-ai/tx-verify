-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.NamedBarriers
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.CtaBarAppendWarp

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g : Nat}
    (hg : g < l.threads) (hWarp : Prologue.warpIndex l g < 8) (round : Round) (ordinal : Nat)
    (hPeers : ∀ peer, SameWarp l g peer → ∃ i, Publishes X (peer,i) round ∧
      (before X (peer,i)).notices = ordinal) (hPub : Publishes X (g,(X.tr g).length-1) round)
    (hRank : (before X (g,(X.tr g).length-1)).notices = ordinal)
include hp hMax hFrame hg hWarp round ordinal hPeers hPub hRank

/-- After all lanes publish the same statistics occurrence, that warp's
arrive-only barrier returns independently of the correction warp. -/
theorem statisticsRecordedHistoryOfWarpWithObjects :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.objects = X.objects ∧
      (g,(X.tr g).length-1) ∈ (Y.barriers (g/l.block)).flatMap CtaBarrier.Record.refs := by
  classical
  let w : Fin 8 := ⟨Prologue.warpIndex l g,hWarp⟩
  let i := (g,(X.tr g).length-1)
  let id := 3+w.val
  have hCuQ : Epilogue.DrainCuQProtected p X :=
    hp.cuQ_protected (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
  have hFault := Protocol.noActualNamedBarrierFault hp hMax.1 hCuQ
  obtain ⟨_,⟨event,hEvent,hKind,_,_⟩,_,_⟩ := publishes hp hMax.1 hPub
  have he : X.get i = some ⟨event.pc,.bar id (some 64) .arrive⟩ := by
    obtain ⟨pc,k⟩ := event
    change k = _ at hKind
    subst k
    exact hEvent
  have hOrdinal : ((X.tr g).take i.2).countP (Execution.isBarId id) = ordinal := by
    rw [← barrierOrdinal]
    change (before X (g,(X.tr g).length-1)).barrier (3+Prologue.warpIndex l g) = ordinal
    exact (notificationOrdinal hp hMax.1 hWarp).symm.trans hRank
  by_cases hRecorded : i ∈ (X.barriers (g/l.block)).flatMap CtaBarrier.Record.refs
  · exact ⟨X,hMax,rfl,rfl,hRecorded⟩
  have hId : id < 16 := by have := w.isLt; dsimp [id]; omega
  have hAll (lane : Nat) (hLane : lane < l.block) (hSame : lane/32 = g%l.block/32) :
      ∃ j pc mode, X.get (g/l.block*l.block+lane,j) = some ⟨pc,.bar id (some 64) mode⟩ ∧
        ((X.tr (g/l.block*l.block+lane)).take j).countP (Execution.isBarId id) =
          ((X.tr g).take i.2).countP (Execution.isBarId id) := by
    let peer := g/l.block*l.block+lane
    have hPeer : peer < l.threads := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hLane
    have hBlock : 0 < l.block := by rw [hp.block]; decide
    obtain ⟨hOwner,hLocal⟩ := NamedBar.lane_cta (c := g/l.block) hBlock hLane
    change peer/l.block = g/l.block at hOwner
    change peer%l.block = lane at hLocal
    have hw : Prologue.warpIndex l peer = Prologue.warpIndex l g := by
      simpa only [Prologue.warpIndex,hLocal] using hSame
    obtain ⟨j,hPeerStats,hPeerRank⟩ := hPeers peer ⟨⟨hg,hPeer,hOwner.symm⟩,hw.symm⟩
    obtain ⟨_,⟨event,hEvent,hKind,_,_⟩,_,_⟩ := publishes hp hMax.1 hPeerStats
    refine ⟨j,event.pc,.arrive,?_,?_⟩
    · obtain ⟨pc,k⟩ := event
      change k = _ at hKind
      rw [hw] at hKind
      subst k
      exact hEvent
    · rw [hOrdinal]
      have hPeerWarp : Prologue.warpIndex l peer < 8 := hw.symm ▸ hWarp
      rw [← barrierOrdinal X (peer,j) id]
      change (before X (peer,j)).barrier (3+Prologue.warpIndex l g) = ordinal
      rw [← hw]
      exact (notificationOrdinal hp hMax.1 hPeerWarp).symm.trans hPeerRank
  obtain ⟨Y,hY,hTrace,hObjects,hMem⟩ :=
    NamedBar.arrive_release_preserving_objects hMax Assumptions.wfStep
    hFault hg hId (by rw [hp.block]; rfl) he hRecorded hAll
  exact ⟨Y,hY,hTrace,hObjects,hMem⟩

/-- After all lanes publish the same statistics occurrence, that warp's
arrive-only barrier returns independently of the correction warp. -/
theorem statisticsRecordedHistoryOfWarp :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      (g,(X.tr g).length-1) ∈ (Y.barriers (g/l.block)).flatMap CtaBarrier.Record.refs := by
  obtain ⟨Y,hY,hTrace,_,hRecord⟩ :=
    statisticsRecordedHistoryOfWarpWithObjects hp hMax hFrame hg hWarp round ordinal
      hPeers hPub hRank
  exact ⟨Y,hY,hTrace,hRecord⟩

theorem statisticsReleasedHistoryOfWarp :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g := by
  obtain ⟨Y,hY,hTrace,hRecord⟩ :=
    statisticsRecordedHistoryOfWarp hp hMax hFrame hg hWarp round ordinal hPeers hPub hRank
  have hPubY : Publishes Y (g,(X.tr g).length-1) round := by
    obtain ⟨e,he,hn⟩ := hPub
    exact ⟨e,by simpa only [Execution.get,hTrace] using he,hn⟩
  obtain ⟨_,⟨event,hEvent,hKind,_,_⟩,_,_⟩ := publishes hp hY.1 hPubY
  have he : Y.get (g,(X.tr g).length-1) =
      some ⟨event.pc,.bar (3+Prologue.warpIndex l g) (some 64) .arrive⟩ := by
    obtain ⟨pc,k⟩ := event
    change k = _ at hKind
    subst k
    exact hEvent
  obtain ⟨_,hKey⟩ := NamedBar.recorded_arrivalK hY.1 he hg hRecord
  refine ⟨Y,hY,hTrace,⟨?_⟩⟩
  intro pc kind _ _
  rw [hTrace]
  exact NamedBar.ready_of_arrivalK hY.1.ctaBar he hKey
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {lead : Nat}
    (hWarp : Prologue.warpIndex l lead < 8) (round : Round) (ordinal : Nat) (position : Nat → Nat)
    (hPeers : ∀ g, SameWarp l lead g → Publishes X (g,position g) round ∧
      (before X (g,position g)).notices = ordinal)
include hp hMax hFrame hWarp round ordinal position hPeers

/-- One maximal history with the same traces releases all pending members of
the selected same-ordinal statistics warp. -/
theorem statisticsWarpReleasedHistoryWithObjects :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.objects = X.objects ∧
      ∀ g, SameWarp l lead g → position g+1 = (X.tr g).length → Step.Released l Y g := by
  classical
  by_cases pending : ∃ g, SameWarp l lead g ∧ position g+1 = (X.tr g).length
  · obtain ⟨g,hg,hLast⟩ := pending
    have hgWarp : Prologue.warpIndex l g < 8 := by
      rw [Prologue.warpIndex,← hg.2]
      exact hWarp
    have hLastG : (X.tr g).length-1 = position g := by omega
    obtain ⟨Y,hY,hTrace,hObjects,hRecord⟩ :=
      statisticsRecordedHistoryOfWarpWithObjects hp hMax hFrame hg.1.2.1 hgWarp round ordinal
        (fun peer h => ⟨position peer,hPeers peer (Step.sameWarp_trans hg h)⟩)
        (by rw [hLastG]; exact (hPeers g hg).1)
        (by rw [hLastG]; exact (hPeers g hg).2)
    rw [hLastG] at hRecord
    let cta := g/l.block
    let id := 3+Prologue.warpIndex l g
    have hCount (peer : Nat) (hPeer : SameWarp l lead peer) :
        ((Y.tr peer).take (position peer)).countP (Execution.isBarId id) = ordinal := by
      have hSame := Step.sameWarp_trans (sameWarp_symm hg) hPeer
      have hIdx : Prologue.warpIndex l g = Prologue.warpIndex l peer := hSame.2
      have hPeerWarp : Prologue.warpIndex l peer < 8 := hIdx ▸ hgWarp
      rw [hTrace,← barrierOrdinal X (peer,position peer) id]
      change (before X (peer,position peer)).barrier (3+Prologue.warpIndex l g) = ordinal
      rw [hIdx]
      exact (notificationOrdinal hp hMax.1 hPeerWarp).symm.trans (hPeers peer hPeer).2
    have hEvent (peer : Nat) (hPeer : SameWarp l lead peer) :
        ∃ pc, Y.get (peer,position peer) = some ⟨pc,.bar id (some 64) .arrive⟩ := by
      have hPub : Publishes Y (peer,position peer) round := by
        obtain ⟨e,he,hn⟩ := (hPeers peer hPeer).1
        exact ⟨e,by simpa only [Execution.get,hTrace] using he,hn⟩
      obtain ⟨_,⟨⟨pc,kind⟩,he,hKind,_,_⟩,_,_⟩ := publishes hp hY.1 hPub
      have hSame := Step.sameWarp_trans (sameWarp_symm hg) hPeer
      have hIdx : Prologue.warpIndex l g = Prologue.warpIndex l peer := hSame.2
      change kind = .bar (3+Prologue.warpIndex l peer) (some 64) .arrive at hKind
      rw [← hIdx] at hKind
      exact ⟨pc,hKind ▸ he⟩
    obtain ⟨pc,he⟩ := hEvent g hg
    have hDecompG : cta*l.block+g%l.block = g := by
      unfold cta
      rw [Nat.mul_comm]
      exact Nat.div_add_mod g l.block
    have hBlock : 0 < l.block := by rw [hp.block]; decide
    refine ⟨Y,hY,hTrace,hObjects,?_⟩
    intro peer hPeer hPeerLast
    have hSame := Step.sameWarp_trans (sameWarp_symm hg) hPeer
    have hOwner : cta = peer/l.block := hSame.1.2.2
    obtain ⟨pc',he'⟩ := hEvent peer hPeer
    have hDecompPeer : cta*l.block+peer%l.block = peer := by
      rw [hOwner,Nat.mul_comm]
      exact Nat.div_add_mod peer l.block
    have hNoExit (k pc : Nat) : Y.get (peer,k) ≠ some ⟨pc,.exit⟩ := by
      intro hExit
      have hLen := Execution.exit_last hY.1 hPeer.1.2.1 hExit
      rw [hTrace,← hPeerLast] at hLen
      have h : k = position peer := by omega
      rw [h,he'] at hExit
      cases hExit
    have hRecorded :
        (peer,position peer) ∈ (Y.barriers (peer/l.block)).flatMap CtaBarrier.Record.refs := by
      rw [← hOwner,← hDecompPeer]
      apply NamedBar.recorded_of_lane hY.1 (NamedBar.cta_lt hg.1.2.1)
        (Nat.mod_lt g hBlock) (Nat.mod_lt peer hBlock) hSame.2
        (by rw [hDecompG]; exact he) (by rw [hDecompPeer]; exact he')
        (by rw [hDecompG,hDecompPeer,hCount g hg,hCount peer hPeer])
        (by rw [hDecompG]; exact hRecord)
      change ∀ k pc, Y.get (cta*l.block+peer%l.block,k) ≠ some ⟨pc,.exit⟩
      simpa only [hDecompPeer] using hNoExit
    obtain ⟨_,hKey⟩ := NamedBar.recorded_arrivalK hY.1 he' hPeer.1.2.1 hRecorded
    constructor
    intro site kind _ _
    have hIndex : (Y.tr peer).length-1 = position peer := by rw [hTrace]; omega
    rw [hIndex]
    exact NamedBar.ready_of_arrivalK hY.1.ctaBar he' hKey
  · exact ⟨X,hMax,rfl,rfl,fun g hg h => (pending ⟨g,hg,h⟩).elim⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
