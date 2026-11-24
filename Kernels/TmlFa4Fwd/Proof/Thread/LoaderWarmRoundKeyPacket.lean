-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundPages
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeyEvenProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringSwizzle
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringLengthSeed
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringSwizzle
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerPrefix
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerReload
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringDestinations
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmSecondReload
import Kernels.TmlFa4Fwd.Flow.Code.Part015

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The physical ring stage of the K packet of warm round `round`. -/
def warmKeyStage (round : Nat) : Nat := (kvUseStage (cacheUseOfRound round)).val

theorem warmKeyStage_lt (round : Nat) : warmKeyStage round < 3 := (kvUseStage _).isLt

/-- The copy-size registers set by the first `k` K pairs. Every row of a warm tile is live,
so each pair copies its full 16 bytes. The V packet reuses these registers. -/
def keySizes (k : Nat) : List (Nat × Value) := (List.range k).map (fun i => (1123+i,b32 16))

theorem keySizes_succ (k : Nat) : keySizes (k+1) = keySizes k ++ [(1123+k,b32 16)] := by
  simp [keySizes,List.range_succ]

theorem keySizeReg (group : Fin 16) :
    packetSizeReg (recurringPacketSite 0) group = 1123+group.val := rfl

theorem holds_snoc {R : Nat → Option Value} {A : List (Nat × Value)} {r : Nat} {v : Value}
    (hA : Holds R A) (hr : R r = some v) : Holds R (A ++ [(r,v)]) :=
  (holds_append ..).mpr ⟨hA,hr,trivial⟩

/-- A packet checkpoint also records the size operand of its pair after the copy facts. -/
theorem retainPacketSize {l : Launch} {X : Execution} {g pc shuffles votes : Nat}
    {site : Fin 6} {stage : Nat} {src : Nat → Nat} {group : Fin 16}
    {K : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g pc (fun lane =>
      packetCopyFacts l site stage (warpLane l g lane%l.block) (src lane) 16 group ++ K lane)
      shuffles votes ends) :
    ∃ next : SchedulerWarpReached l X g pc (fun lane =>
      packetCopyFacts l site stage (warpLane l g lane%l.block) (src lane) 16 group ++
        (K lane ++ [(packetSizeReg site group,b32 16)])) shuffles votes ends,
      next.pos = cur.pos := by
  apply cur.advanceLocalWithPosition
  intro lane hl
  have hs := cur.checkpoint lane hl
  refine ⟨cur.state lane,.refl,hs.mono ?_⟩
  have h := (holds_append ..).mp hs.2.2.2.2
  exact (holds_append ..).mpr ⟨h.1,holds_snoc h.2 h.1.2.2.1⟩

def warmRoundKeyLanePointer (p : Params) (l : Launch) (g batch round lane : Nat) : Nat :=
  primingKRowPointer p batch ((assignedCoordinates p batch (g/l.block)).2/6)
    (warmRoundSlotRow p l g batch round lane 0)

def warmRoundKeySource (p : Params) (l : Launch) (g batch round lane : Nat) : Nat :=
  recurringSourceAddress (warmRoundKeyLanePointer p l g batch round (pointerBroadcastLane lane))
    (warpLane l g lane%l.block)


def warmRoundKeyResidual (p : Params) (l : Launch) (g batch round lane : Nat) : Nat :=
  p.kLength batch - (128*warmRoundTile p l g batch round+(warpLane l g lane%l.block)/8%8)

def warmRoundKeyPacked (p : Params) (l : Launch) (g batch round lane : Nat) :
    List (Nat × Value) :=
  [(169,.pred true),(1997,b32 (warmRoundKeyResidual p l g batch round lane))] ++
    recurringSwizzleFacts l (warpLane l g lane%l.block) 0 ++ warmRoundKeyCarry p l g batch round
        lane

/-- The packed K carry together with the copy sizes of the first `k` pairs. -/
def warmRoundKeySized (p : Params) (l : Launch) (g batch round k lane : Nat) :
    List (Nat × Value) :=
  warmRoundKeyPacked p l g batch round lane ++ keySizes k

set_option maxRecDepth 4096 in
/-- The first warm K pass computes both destination bases and its live row selector. -/
theorem warmRoundKeyPackFrameOfSaved {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch round shuffles votes : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 978
      (fun lane => warmRoundKeyPointerCarry p l g batch round lane false) shuffles votes ends) :
    ∃ ready : SchedulerWarpReached l X g 1003 (warmRoundKeyPacked p l g batch round)
        shuffles votes ends, ready.pos = cur.pos := by
  apply cur.advanceLocalWithPosition
  intro lane hl
  let g' := warpLane l g lane
  let tid := g'%l.block
  let F := warmRoundKeyCarry p l g batch round lane
  let n := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  let tile := warmRoundTile p l g batch round
  let len := p.kLength batch
  let row := tid/8%8
  let res := warmRoundKeyResidual p l g batch round lane
  let G := (1979,b32 row)::F
  let H := recurringSwizzleFacts l tid 0 ++ F
  have hTid : tid < 512 := by dsimp [tid]; rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hCount : n ≤ (len+127)/128 :=
    (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).2.1
  have hLen : len < 2^31 := by have := (hp.lengths batch hb).2.2; omega
  have hTile : n-2 < 2^31 := by omega
  have hRow : row < 8 := Nat.mod_lt _ (by decide)
  have hRes : 0 < res := recurringKeyResidualLive (round := round) 0 (by omega) hCount hRow
  have hLive : 128*tile+row < len := by
    change 0 < len-(128*tile+row) at hRes
    omega
  have hResSmall : res < 2^31 := by change len-(128*tile+row) < _; omega
  have hAt := cur.checkpoint lane hl
  obtain ⟨a,ha,hA⟩ := warmPointerRoute (l := l) (g := g') false
    (by set_option maxRecDepth 100000 in kernel_rfl) hAt
  let ar := hA.2.2.2.2.2.2
  have hA' : At a 981 ([(1061,b32 tid)]++F) :=
    hA.mono ⟨holds_lookup ar rfl,ar⟩
  obtain ⟨b,hbRun,hB⟩ := roundStraightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (keyCopyLaneOffsetCore (l := l) (g := g') hTid false) hA'
  change At b 983 G at hB
  have hB' : At b 983 (recurringSwizzleInputs l tid 0 ++ G) := by
    refine hB.mono ((holds_append ..).mpr ⟨?_,hB.2.2.2.2⟩)
    exact ⟨holds_lookup hB.2.2.2.2 rfl,holds_lookup hB.2.2.2.2 rfl,
      holds_lookup hB.2.2.2.2 rfl,trivial⟩
  obtain ⟨c,hc,hC⟩ := roundStraightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (recurringSwizzleCore (l := l) (g := g') hTid hp.shared.2.1 0) hB'
  change At c 996 (recurringSwizzleFacts l tid 0 ++ G) at hC
  have hC' : At c 996 ([(1116,b32 (n-2)),(7174,b32 round),(1979,b32 row),(1086,b32 len)]++H) := by
    have hs := hC.2.2.2.2
    have hSplit := (holds_append ..).mp hs
    have hH : Holds c.regs H := (holds_append c.regs (recurringSwizzleFacts l tid 0) F).mpr
      ⟨hSplit.1,hSplit.2.2⟩
    exact hC.mono ⟨holds_lookup hs rfl,holds_lookup hs rfl,holds_lookup hs rfl,holds_lookup hs rfl,
      hH⟩
  obtain ⟨d,hd,hD⟩ := roundStraightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (warmKeyCopyResidualCore (l := l) (g := g') (round := round) (by omega)
      hTile hRow hLive hLen) hC'
  change At d 1002 ((1997,b32 res)::H) at hD
  have hCmp : Seg kernel [] l g' 1 1002 [(1997,b32 res)] 1003 [(169,.pred true)] :=
    liveKeyCompareCore Flow.code_1002 hRes hResSmall
  obtain ⟨e,he,hE⟩ := roundStraightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hCmp
    (show At d 1002 ([(1997,b32 res)] ++ ((1997,b32 res)::H)) from
      hD.mono ⟨hD.2.2.2.2.1,hD.2.2.2.2⟩)
  exact ⟨e,run_rtg (run_comp ha (run_comp hbRun (run_comp hc (run_comp hd he)))),hE⟩


variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g batch round : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hReleased : cacheUseOfRound round/3 ≤
      Protocol.Loader.cacheEmptyUnits l X g (kvUseStage (cacheUseOfRound round)))
include hp hMax hFrame hg hw hb hLo hHi hTrips hReleased

set_option maxRecDepth 4096 in
/-- The first warm pointer reload leaves its sibling lane-local cell current. -/
theorem WarmRoundPages.reloadKeyPointerPreservingOfMaximal (c : WarmRoundPages p l X g batch round)
    :
    let head := (assignedCoordinates p batch (g/l.block)).2/6
    let ptr := fun lane => primingKRowPointer p batch head (warmRoundSlotRow p l g batch round lane
        0)
    ∃ done : SchedulerWarpReached l X g 1004
        (fun lane => warmKeyWords 0 (ptr lane) ++ warmRoundKeyPacked p l g batch round lane)
        c.shuffles c.votes c.ends,
      ∀ lane < 32, PrimingCellValue X (warpLane l g lane) (done.pos lane) 977
        (pointerSaveAccess l (warpLane l g lane) 0 1)
        (b64 (primingKRowPointer p batch head
          (warmRoundSlotRow p l g batch round lane 1))).toBytes ∧
        ∀ slot isRow, warmRoundMetadata p l X g batch round lane (done.pos lane) slot isRow := by
  dsimp only
  let head := (assignedCoordinates p batch (g/l.block)).2/6
  let ptr := fun lane => primingKRowPointer p batch head (warmRoundSlotRow p l g batch round lane 0)
  let addr := l.localBase+32
  have hh : head < p.kvHeads := by
    have hv := (assignedCoordinates_valid hp hLo hHi).2
    unfold Params.heads at hv
    omega
  have hAddr : addr+warmKFirstReload.offset < 2^64 := by
    have h := hp.localMemory.2.1
    change l.localBase+32+0 < 2^64
    omega
  have hAlign : (addr+warmKFirstReload.offset)%8 = 0 := by
    have h := hp.localMemory.1
    change (l.localBase+32+0)%8 = 0
    omega
  have hPtr (lane : Nat) : ptr lane < 2^64 := by
    let row := warmRoundSlotRow p l g batch round lane 0
    have h := sourceScratchPayload_live hp 0 (primingScratchPageBound hp (row := row) hb)
      (Nat.mod_lt row (by decide)) hh
    have hEq : sourceScratchPayload (primingScratchPage p batch row) (row%16)
        p.kLayout.pageStride p.kLayout.rowStride
        (p.kLayout.base+2*(head*p.kLayout.headStride)) = ptr lane := h.1
    exact hEq ▸ h.2.1
  obtain ⟨saved,hSaved⟩ :=
    c.saveKeyPointersKeepingOfMaximal hp hMax hFrame hg hw hb hLo hHi hReleased
  obtain ⟨ready,hReady⟩ := warmRoundKeyPackFrameOfSaved hp hb hLo hHi hTrips saved
  have hFresh : ∀ lane < 32, ∀ pair ∈ warmRoundKeyPacked p l g batch round lane,
      pair.1 ≠ warmKFirstReload.lowReg ∧ pair.1 ≠ warmKFirstReload.highReg := by
    intro lane _ pair hm
    have h : ((warmRoundKeyPacked p l g batch round lane).map Prod.fst).all
        (fun r => decide (r ≠ warmKFirstReload.lowReg ∧ r ≠ warmKFirstReload.highReg)) = true := rfl
    exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))
  have hCell (lane : Nat) (hl : lane < 32) :
      PrimingCellValue X (warpLane l g lane) (ready.pos lane) 977
        (warmKFirstReload.cell (warpLane l g lane) addr) (b64 (ptr lane)).toBytes := by
    rw [hReady]
    exact (hSaved lane hl).1 0
  obtain ⟨done,_,hKeep⟩ := warmKFirstReload.warpReadPreservingOfMaximal hp hMax hg (by decide)
    Flow.code_1003 hAddr hAlign (by decide) ptr (fun lane _ => hPtr lane) ready
    (fun _ _ => by simp [addr,warmKFirstReload,warmRoundKeyPacked,warmRoundKeyCarry,
      warmRoundPagesFrame,
      warmRoundFrame,openingWarmFrame,warmStartFrame,
      warmPageRoots,warmLaneRoots]) hFresh hCell
  refine ⟨done,fun lane hl => ⟨(hKeep lane hl).2 ?_,fun slot isRow => (hKeep lane hl).2 ?_⟩⟩
  · rw [hReady]
    exact (hSaved lane hl).1 1
  · rw [hReady]
    exact (hSaved lane hl).2 slot isRow



omit hp hMax hFrame hg hw hb hLo hHi hTrips hReleased in
def warmRoundKeyFirstWords (p : Params) (l : Launch) (g batch round lane : Nat) :
    List (Nat × Value) :=
  warmKeyWords 0 (warmRoundKeyLanePointer p l g batch round lane) ++ warmRoundKeyPacked p l g batch
      round lane

omit hp hMax hFrame hg hw hb hLo hHi hTrips hReleased in
private theorem warmRoundKeySourceAndColumn {l : Launch} {g base tid : Nat}
    (hBase : base < 2^64) :
    Seg kernel [] l g 3 1006 (warmKPairInputs 0 base tid)
      1009 [(7667,b64 (recurringSourceAddress base tid)),(7666,b64 (16*(tid%8)))] := by
  have hFit : 8 * (tid%8) < 2^32 := by omega
  intro s hs
  change At s 1006 [(2000,b32 (base%2^32)),(2001,b32 (base/2^32)),(1119,b32 (8*(tid%8)))] at hs
  have hWord := warmKPairSourceCore (l := l) (g := g) (tid := tid) hBase 0
  obtain ⟨u,hu,hU⟩ := hWord s hs
  have hColumn : Seg kernel [] l g 3 1006
      [(2000,b32 (base%2^32)),(2001,b32 (base/2^32)),(1119,b32 (8*(tid%8)))]
      1009 [(7666,b64 (16*(tid%8)))] := by
    intro a ha
    seg_fp ha using
      norm_bits [Nat.mod_eq_of_lt hFit,show 8*(tid%8)*2 = 16*(tid%8) by omega]
  obtain ⟨v,hv,hV⟩ := hColumn s hs
  have he : v = u := Option.some.inj (hv.symm.trans hu)
  exact ⟨u,hu,hU.mono ⟨hU.2.2.2.2.1,he ▸ hV.2.2.2.2⟩⟩

omit hp hMax hFrame hg hw hb hLo hHi hTrips hReleased in
set_option maxRecDepth 4096 in
private theorem warmRoundKeyEvenPrepared {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch round shuffles votes : Nat}
    (hPtr : ∀ lane < 32, warmRoundKeyLanePointer p l g batch round lane < 2^64)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1006 (fun lane =>
      warmKeyExchangeWords 0 (warmRoundKeyLanePointer p l g batch round (pointerBroadcastLane
          lane)) ++
        warmRoundKeyFirstWords p l g batch round lane) shuffles votes ends) :
    ∃ ready : SchedulerWarpReached l X g 1012 (fun lane =>
      let tid := warpLane l g lane%l.block
      packetCopyFacts l (recurringPacketSite 0) (warmKeyStage round) tid
        (warmRoundKeySource p l g batch round lane) 16 0 ++
        warmKeyEvenCarry l (warmKeyStage round) tid (warmRoundKeyFirstWords p l g batch round lane))
      shuffles votes ends, ready.pos = cur.pos := by
  apply cur.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let tid := t%l.block
  let sender := pointerBroadcastLane lane
  let ptr := warmRoundKeyLanePointer p l g batch round sender
  let src := warmRoundKeySource p l g batch round lane
  let F := warmRoundKeyFirstWords p l g batch round lane
  let S := [(7667,b64 src),(7666,b64 (16*(tid%8)))]
  have hSender : sender < 32 := by unfold sender pointerBroadcastLane; omega
  have hs := cur.checkpoint lane hl
  have hStart : At (cur.state lane) 1006 (warmKPairInputs 0 ptr tid ++ F) := by
    have hSplit := (holds_append ..).mp hs.2.2.2.2
    refine hs.mono ((holds_append ..).mpr ⟨?_,hSplit.2⟩)
    exact ⟨hSplit.1.1,hSplit.1.2.1,holds_lookup hSplit.2 rfl,trivial⟩
  have hSource : Seg kernel [] l t 3 1006 (warmKPairInputs 0 ptr tid) 1009 S :=
    warmRoundKeySourceAndColumn (hPtr sender hSender)
  obtain ⟨u,hu,hU⟩ := roundStraightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hSource hStart
  have hAt : At u 1009
      ([(7179,b32 (warmKeyStage round)),(1992,b32 (kvCopyAddress l.sharedBase 0 tid 0
          false))]++(S++F)) :=
    hU.mono ⟨holds_lookup hU.2.2.2.2 rfl,holds_lookup hU.2.2.2.2 rfl,hU.2.2.2.2⟩
  have hEven : Seg kernel [] l t 2 1009
      [(7179,b32 (warmKeyStage round)),(1992,b32 (kvCopyAddress l.sharedBase 0 tid 0 false))] 1011
      (recurringEvenFacts l 0 (warmKeyStage round) tid) :=
    recurringEvenCore hp (g := t) 0 (warmKeyStage_lt round)
  obtain ⟨v,hv,hV⟩ := roundStraightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hEven hAt
  let I := recurringEvenFacts l 0 (warmKeyStage round) tid ++ S ++ F
  have hSelect : Seg kernel [] l t 1 1011 [(169,.pred true)] 1012 [(1123,b32 16)] :=
    liveKeySelectCore Flow.code_1011
  obtain ⟨w,hw,hW⟩ := roundStraightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hSelect
    (show At v 1011 ([(169,.pred true)]++I) from hV.mono
      ⟨holds_lookup hV.2.2.2.2 rfl,hV.2.2.2.2⟩)
  refine ⟨w,run_rtg (run_comp hu (run_comp hv hw)),hW.mono ?_⟩
  exact ⟨hW.2.2.2.2.2.1,hW.2.2.2.2.2.2.2.1,hW.2.2.2.2.1,
    hW.2.2.2.2.2.2.2.2.1,hW.2.2.2.2.2.2.1,hW.2.2.2.2.2.1,
    hW.2.2.2.2.2.2.2.2.2⟩

omit hp hMax hFrame hg hw hb hLo hHi hTrips hReleased in
def warmRoundKeySavedUpper (p : Params) (l : Launch) (X : Execution)
    (g batch round lane index : Nat) : Prop :=
  let head := (assignedCoordinates p batch (g/l.block)).2/6
  let t := warpLane l g lane
  PrimingCellValue X t index 977 (pointerSaveAccess l t 0 1)
    (b64 (primingKRowPointer p batch head (warmRoundSlotRow p l g batch round lane 1))).toBytes

omit hp hMax hFrame hg hw hb hLo hHi hTrips hReleased in
theorem warmRoundKeyLanePointerBounds {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch round lane : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (slot : Fin 2) :
    let head := (assignedCoordinates p batch (g/l.block)).2/6
    let ptr := primingKRowPointer p batch head (warmRoundSlotRow p l g batch round lane slot)
    ptr < 2^64 ∧ ptr%16 = 0 := by
  dsimp only
  let head := (assignedCoordinates p batch (g/l.block)).2/6
  let row := warmRoundSlotRow p l g batch round lane slot
  have hh : head < p.kvHeads := by
    have hv := (assignedCoordinates_valid hp hLo hHi).2
    unfold Params.heads at hv
    omega
  have h := sourceScratchPayload_live hp 0 (primingScratchPageBound hp (row := row) hb)
    (Nat.mod_lt row (by decide)) hh
  have hEq : sourceScratchPayload (primingScratchPage p batch row) (row%16)
      p.kLayout.pageStride p.kLayout.rowStride
      (p.kLayout.base+2*(head*p.kLayout.headStride)) = primingKRowPointer p batch head row :=
    h.1
  exact hEq ▸ h.2

set_option maxRecDepth 4096 in
/-- The first actual pair leaves the even stage base and the second private pointer live. -/
theorem WarmRoundPages.firstKeyPairCursorOfMaximal (c : WarmRoundPages p l X g batch round) :
    ∃ done : SchedulerWarpReached l X g 1014
        (fun lane => warmKeyEvenCarry l (warmKeyStage round) (warpLane l g lane%l.block)
          (warmKeyWords 0 (warmRoundKeyLanePointer p l g batch round lane) ++
            warmRoundKeySized p l g batch round 1 lane)) (c.shuffles+2) c.votes c.ends,
      ∀ lane < 32, warmRoundKeySavedUpper p l X g batch round lane (done.pos lane) ∧
        ∀ slot isRow, warmRoundMetadata p l X g batch round lane (done.pos lane) slot isRow := by
  let ptr := warmRoundKeyLanePointer p l g batch round
  let src := warmRoundKeySource p l g batch round
  let F := warmRoundKeyPacked p l g batch round
  have hPtr (lane : Nat) : ptr lane < 2^64 ∧ ptr lane%16 = 0 :=
    warmRoundKeyLanePointerBounds hp (lane := lane) hb hLo hHi 0
  obtain ⟨words,hUpper⟩ := c.reloadKeyPointerPreservingOfMaximal hp hMax hFrame hg hw hb hLo hHi
      hTrips
    hReleased
  have hFresh (lane : Nat) (_ : lane < 32) (pair : Nat × Value)
      (hm : pair ∈ warmKeyWords 0 (ptr lane) ++ F lane) :
      pair.1 ≠ warmKShuffleOutput 0 ∧ pair.1 ≠ warmKShuffleOutput 0+1 := by
    have h : (((warmKeyWords 0 (ptr lane)) ++ F lane).map Prod.fst).all
        (fun r => decide (r ≠ 2000 ∧ r ≠ 2001)) = true := rfl
    exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))
  obtain ⟨exchanged,hEx⟩ := warmKeyExchangeOfMaximal hp hMax hg 0 ptr hFresh words
  obtain ⟨ready,hReady⟩ := warmRoundKeyEvenPrepared hp (fun lane _ => (hPtr lane).1) exchanged
  have hAlign (lane : Nat) : src lane%16 = 0 := by
    unfold src warmRoundKeySource recurringSourceAddress
    rw [Nat.mod_mod_of_dvd _ (show 16 ∣ (2 : Nat)^64 by decide)]
    have hLocal : warmRoundKeyLanePointer p l g batch round (pointerBroadcastLane lane)%16 = 0 :=
      (hPtr (pointerBroadcastLane lane)).2
    simp [Nat.add_mod,hLocal]
  obtain ⟨ready',hReady'⟩ := retainPacketSize ready
  obtain ⟨done,_,hDone⟩ := packetPairWarpOfMaximal hp hMax hg (recurringPacketSite 0) 0
    (by have := warmKeyStage_lt round; change warmKeyStage round+0 < 3; omega)
    src (fun _ => 16) (fun _ _ => Nat.mod_lt _ (by decide))
    (fun lane _ => hAlign lane) (fun _ _ => le_rfl) ready'
  obtain ⟨done',hDone'⟩ := done.advanceLocalWithPosition (pc' := 1014)
    (G := fun lane => warmKeyEvenCarry l (warmKeyStage round) (warpLane l g lane%l.block)
      (warmKeyWords 0 (ptr lane) ++ warmRoundKeySized p l g batch round 1 lane)) (by
      intro lane hl
      have hs := done.checkpoint lane hl
      refine ⟨done.state lane,.refl,hs.mono ?_⟩
      have h := hs.2.2.2.2
      simpa [warmKeyEvenCarry,warmRoundKeyFirstWords,warmRoundKeySized,keySizes,keySizeReg]
        using h)
  refine ⟨done',fun lane hl => ⟨?_,fun slot isRow => ?_⟩⟩
  · rw [hDone']
    apply (hDone lane hl).2
    rw [hReady',hReady]
    exact (hEx lane hl).2 (hUpper lane hl).1
  · rw [hDone']
    apply (hDone lane hl).2
    rw [hReady',hReady]
    exact (hEx lane hl).2 ((hUpper lane hl).2 slot isRow)


omit hp hMax hFrame hg hw hb hLo hHi hTrips hReleased in
theorem warmRoundKeyLive {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch round lane : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (group : Fin 16) :
    8*group.val < warmRoundKeyResidual p l g batch round lane ∧
      warmRoundKeyResidual p l g batch round lane < 2^31 := by
  have hBound := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).2.1
  have hLen := (hp.lengths batch hb).2.2
  refine ⟨?_,?_⟩
  · exact recurringKeyResidualLive (round := round) group (by omega) hBound (Nat.mod_lt _ (by
      decide))
  · unfold warmRoundKeyResidual
    omega

omit hp hMax hFrame hg hw hb hLo hHi hTrips hReleased in
set_option maxRecDepth 4096 in
private theorem warmRoundKeyOddPrepared {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch round shuffles votes : Nat}
    (hPtr : ∀ lane < 32, warmRoundKeyLanePointer p l g batch round lane < 2^64)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1017 (fun lane =>
      let tid := warpLane l g lane%l.block
      let ptr := warmRoundKeyLanePointer p l g batch round
      warmKeyExchangeWords 1 (ptr (warmKShuffleSender lane 1)) ++
        warmKeyWords 1 (ptr lane) ++ (170,.pred true) ::
          warmKeyEvenCarry l (warmKeyStage round) tid (warmRoundKeySized p l g batch round 1 lane))
      shuffles votes ends) :
    ∃ ready : SchedulerWarpReached l X g 1021 (fun lane =>
      let tid := warpLane l g lane%l.block
      let ptr := warmRoundKeyLanePointer p l g batch round
      packetCopyFacts l (recurringPacketSite 0) (warmKeyStage round) tid
          (recurringSourceAddress (ptr (warmKShuffleSender lane 1)) tid) 16 1 ++
        warmKeyPairOperands l (warmKeyStage round) tid 1 (ptr lane)
          (warmRoundKeySized p l g batch round 1 lane))
      shuffles votes ends, ready.pos = cur.pos := by
  apply cur.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let tid := t%l.block
  let ptr := warmRoundKeyLanePointer p l g batch round
  let sender := warmKShuffleSender lane 1
  let src := recurringSourceAddress (ptr sender) tid
  let F := warmKeyWords 1 (ptr lane) ++
    warmKeyEvenCarry l (warmKeyStage round) tid (warmRoundKeySized p l g batch round 1 lane)
  let G := (170,.pred true)::F
  have hSender : sender < 32 := by unfold sender warmKShuffleSender pointerBroadcastLane; omega
  have hs := cur.checkpoint lane hl
  have hStart : At (cur.state lane) 1017 (warmKPairInputs 1 (ptr sender) tid ++ G) := by
    refine hs.mono ((holds_append ..).mpr ⟨?_,?_⟩)
    · exact ⟨holds_lookup hs.2.2.2.2 rfl,holds_lookup hs.2.2.2.2 rfl,
        holds_lookup hs.2.2.2.2 rfl,trivial⟩
    · exact ⟨holds_lookup hs.2.2.2.2 rfl,hs.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.1,
        hs.2.2.2.2.2.2.2.2.2⟩
  have hSource : Seg kernel [] l t 2 1017 (warmKPairInputs 1 (ptr sender) tid)
      1019 [(7669,b64 src)] := warmKPairSourceCore (g := t) (hPtr sender hSender) 1
  obtain ⟨u,hu,hU⟩ := roundStraightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hSource hStart
  let H := (7669,b64 src)::G
  have hAt : At u 1019
      ([(1988,b32 (kvCopyAddress l.sharedBase 0 tid 1 false)),(2002,b32 (32768*warmKeyStage
          round))]++H) :=
    hU.mono ⟨holds_lookup hU.2.2.2.2 rfl,holds_lookup hU.2.2.2.2 rfl,hU.2.2.2.2⟩
  have hOdd : Seg kernel Assumptions.all l t 1 1019
      [(1988,b32 (kvCopyAddress l.sharedBase 0 tid 1 false)),(2002,b32 (32768*warmKeyStage round))]
          1020
      [(2006,b32 (kvCopyAddress l.sharedBase (warmKeyStage round) tid 1 false))] :=
    recurringOddSeedRun hp (g := t) 0 (warmKeyStage_lt round)
  obtain ⟨v,hv,hV⟩ := hOdd u (hAt.mono ⟨hAt.2.2.2.2.1,hAt.2.2.2.2.2.1,trivial⟩)
  have hRun : run kernel [] l t 1 u = some v := by
    have hDecode := loaderOutCore (l := l) (g := t) (t := u)
      (by rw [hAt.1]; decide) (by rw [hAt.1]; decide)
    simpa only [run,tauStep,hDecode] using hv
  have hKeep := (loaderLinear (regs := H.map Prod.fst) (by decide) (by decide) hAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hRun).2
  have hHF := holdsSchedulerFrame hAt.2.2.2.2.2.2 hKeep (fun _ hm => List.mem_map_of_mem hm)
  let J := (2006,b32 (kvCopyAddress l.sharedBase (warmKeyStage round) tid 1 false))::(7669,b64
      src)::F
  have hJA : At v 1020 ([(170,.pred true)]++J) :=
    hV.mono ⟨hHF.2.1,hV.2.2.2.2.1,hHF.1,hHF.2.2⟩
  have hSelect : Seg kernel [] l t 1 1020 [(170,.pred true)] 1021 [(1124,b32 16)] :=
    liveKeySelectCore Flow.code_1020
  obtain ⟨w,hw,hW⟩ := roundStraightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hSelect hJA
  refine ⟨w,run_rtg (run_comp hu (run_comp hv hw)),hW.mono ?_⟩
  have hHW := hW.2.2.2.2
  exact ⟨holds_lookup hHW rfl,holds_lookup hHW rfl,holds_lookup hHW rfl,
    holds_lookup hHW rfl,holds_lookup hHW rfl,holds_lookup hHW rfl,holds_lookup hHW rfl,
    holds_lookup hHW rfl,holds_lookup hHW rfl,hHW.2.2.2.2.2.2.2.2⟩

set_option maxRecDepth 4096 in
/-- The first odd pair installs the second destination base while preserving the upper pointer. -/
theorem WarmRoundPages.firstTwoKeyPairsOfMaximal (c : WarmRoundPages p l X g batch round) :
    ∃ done : SchedulerWarpReached l X g 1023
        (fun lane => warmKeyPairOperands l (warmKeyStage round) (warpLane l g lane%l.block) 1
          (warmRoundKeyLanePointer p l g batch round lane)
          (warmRoundKeySized p l g batch round 2 lane))
        (c.shuffles+4) c.votes c.ends,
      ∀ lane < 32, warmRoundKeySavedUpper p l X g batch round lane (done.pos lane) ∧
        ∀ slot isRow, warmRoundMetadata p l X g batch round lane (done.pos lane) slot isRow := by
  let ptr := warmRoundKeyLanePointer p l g batch round
  let res := warmRoundKeyResidual p l g batch round
  let P := warmRoundKeySized p l g batch round 1
  let F := fun lane => warmKeyEvenCarry l (warmKeyStage round) (warpLane l g lane%l.block)
    (warmKeyWords 0 (ptr lane) ++ P lane)
  let G := fun lane => (170,.pred true)::warmKeyEvenCarry l (warmKeyStage round) (warpLane l g
      lane%l.block) (P lane)
  have hPtr (lane : Nat) : ptr lane < 2^64 ∧ ptr lane%16 = 0 :=
    warmRoundKeyLanePointerBounds hp (lane := lane) hb hLo hHi 0
  obtain ⟨afterEven,hUpper⟩ := c.firstKeyPairCursorOfMaximal hp hMax hFrame hg hw hb hLo hHi hTrips
    hReleased
  obtain ⟨maskStart,hMaskStart⟩ := afterEven.advanceLocalWithPosition (pc' := warmKeyMaskPc 1)
    (G := fun lane => (1997,b32 (res lane))::F lane) (by
      intro lane hl
      let hs := afterEven.checkpoint lane hl
      exact ⟨afterEven.state lane,.refl,hs.mono ⟨holds_lookup hs.2.2.2.2 rfl,hs.2.2.2.2⟩⟩)
  have hFresh (lane : Nat) (_ : lane < 32) (pair : Nat × Value) (hm : pair ∈ F lane) :
      pair.1 ≠ 169+(1 : Fin 16).val := by
    have h : ((F lane).map Prod.fst).all (fun r => decide (r ≠ 170)) = true := rfl
    exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))
  obtain ⟨masked,hMasked⟩ := warmKeyMaskOfReached 1 res
    (fun lane _ => (warmRoundKeyLive hp (lane := lane) hb hLo hHi hTrips 1).1)
    (fun lane _ => (warmRoundKeyLive hp (lane := lane) hb hLo hHi hTrips 1).2)
    hFresh maskStart
  obtain ⟨shuffle,hShuffle⟩ := masked.advanceLocalWithPosition (pc' := warmKShufflePc 1)
    (G := fun lane => warmKeyWords 1 (ptr lane) ++ G lane) (by
      intro lane hl
      let hs := masked.checkpoint lane hl
      refine ⟨masked.state lane,.refl,hs.mono ?_⟩
      exact ⟨holds_lookup hs.2.2.2.2 rfl,holds_lookup hs.2.2.2.2 rfl,hs.2.2.2.2.1,
        hs.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.2.1,
        hs.2.2.2.2.2.2.2.2.2.2.2⟩)
  have hFresh' (lane : Nat) (_ : lane < 32) (pair : Nat × Value)
      (hm : pair ∈ warmKeyWords 1 (ptr lane) ++ G lane) :
      pair.1 ≠ warmKShuffleOutput 1 ∧ pair.1 ≠ warmKShuffleOutput 1+1 := by
    have h : ((warmKeyWords 1 (ptr lane) ++ G lane).map Prod.fst).all
        (fun r => decide (r ≠ 2004 ∧ r ≠ 2005)) = true := rfl
    exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))
  obtain ⟨exchanged,hEx⟩ := warmKeyExchangeOfMaximal hp hMax hg 1 ptr hFresh' shuffle
  obtain ⟨ready,hReady⟩ := warmRoundKeyOddPrepared hp (fun lane _ => (hPtr lane).1) exchanged
  let src := fun lane => recurringSourceAddress (ptr (warmKShuffleSender lane 1))
    (warpLane l g lane%l.block)
  have hAlign (lane : Nat) : src lane%16 = 0 := by
    unfold src recurringSourceAddress
    rw [Nat.mod_mod_of_dvd _ (show 16 ∣ (2 : Nat)^64 by decide)]
    simp [Nat.add_mod,(hPtr (warmKShuffleSender lane 1)).2]
  obtain ⟨ready',hReady'⟩ := retainPacketSize ready
  obtain ⟨done,_,hDone⟩ := packetPairWarpOfMaximal hp hMax hg (recurringPacketSite 0) 1
    (by have := warmKeyStage_lt round; change warmKeyStage round+0 < 3; omega)
    src (fun _ => 16) (fun _ _ => Nat.mod_lt _ (by decide))
    (fun lane _ => hAlign lane) (fun _ _ => le_rfl) ready'
  obtain ⟨done',hDone'⟩ := done.advanceLocalWithPosition (pc' := 1023)
    (G := fun lane => warmKeyPairOperands l (warmKeyStage round) (warpLane l g lane%l.block) 1
      (ptr lane) (warmRoundKeySized p l g batch round 2 lane)) (by
      intro lane hl
      have hs := done.checkpoint lane hl
      refine ⟨done.state lane,.refl,hs.mono ?_⟩
      have h := hs.2.2.2.2
      simpa [warmKeyPairOperands,warmKeyPairCarry,warmRoundKeySized,keySizes,keySizeReg,
        List.range_succ] using h)
  refine ⟨done',fun lane hl => ⟨?_,fun slot isRow => ?_⟩⟩
  · rw [hDone']
    apply (hDone lane hl).2
    rw [hReady',hReady]
    apply (hEx lane hl).2
    rw [hShuffle,hMasked,hMaskStart]
    exact (hUpper lane hl).1
  · rw [hDone']
    apply (hDone lane hl).2
    rw [hReady',hReady]
    apply (hEx lane hl).2
    rw [hShuffle,hMasked,hMaskStart]
    exact (hUpper lane hl).2 slot isRow

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
