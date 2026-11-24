-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmFirstPages
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringSwizzle
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringSwizzle
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringLengthSeed
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerPrefix
import Kernels.TmlFa4Fwd.Flow.Code.Part015

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

def warmFirstKeyResidual (p : Params) (l : Launch) (g batch lane : Nat) : Nat :=
  p.kLength batch - (128*warmFirstTile p l g batch+(warpLane l g lane%l.block)/8%8)

def warmFirstKeyPacked (p : Params) (l : Launch) (g batch lane : Nat) :
    List (Nat × Value) :=
  [(169,.pred true),(1997,b32 (warmFirstKeyResidual p l g batch lane))] ++
    recurringSwizzleFacts l (warpLane l g lane%l.block) 0 ++ warmFirstKeyCarry p l g batch lane

private theorem straightFrame {l : Launch} {g n begin finish : Nat}
    {A F G : List (Nat × Value)}
    (hLo : 174 ≤ begin) (hHi : begin+n ≤ 1906)
    (hKeep : ((kernel.code.drop begin).take n).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true)
    (hSeq : ((kernel.code.drop begin).take (n-1)).all
      (fun i => schedulerFallsThrough i.op) = true)
    (hCore : Seg kernel [] l g n begin A finish G)
    {s : TState} (hs : At s begin (A++F)) :
    ∃ u, run kernel Assumptions.all l g n s = some u ∧ At u finish (G++F) := by
  have hFields := (holds_append ..).mp hs.2.2.2.2
  obtain ⟨u,hu,hU⟩ := hCore s (hs.mono hFields.1)
  obtain ⟨huA,huF⟩ := loaderLinear (regs := F.map Prod.fst) hLo hHi hs.1 hKeep hSeq hu
  exact ⟨u,huA,hU.mono ((holds_append ..).mpr ⟨hU.2.2.2.2,
    holdsSchedulerFrame hFields.2 huF (fun _ hm => List.mem_map_of_mem hm)⟩)⟩

set_option maxRecDepth 4096 in
/-- The first warm K pass computes both destination bases and its live row selector. -/
theorem warmFirstKeyPackFrameOfSaved {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch shuffles votes : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 978
      (fun lane => warmFirstKeyPointerCarry p l g batch lane false) shuffles votes ends) :
    ∃ ready : SchedulerWarpReached l X g 1003 (warmFirstKeyPacked p l g batch)
        shuffles votes ends, ready.pos = cur.pos := by
  apply cur.advanceLocalWithPosition
  intro lane hl
  let g' := warpLane l g lane
  let tid := g'%l.block
  let F := warmFirstKeyCarry p l g batch lane
  let n := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  let tile := warmFirstTile p l g batch
  let len := p.kLength batch
  let row := tid/8%8
  let res := warmFirstKeyResidual p l g batch lane
  let G := (1979,b32 row)::F
  let H := recurringSwizzleFacts l tid 0 ++ F
  have hTid : tid < 512 := by dsimp [tid]; rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hCount : n ≤ (len+127)/128 :=
    (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).2.1
  have hLen : len < 2^31 := by have := (hp.lengths batch hb).2.2; omega
  have hTile : tile < 2^31 := by dsimp [tile,warmFirstTile]; omega
  have hRow : row < 8 := Nat.mod_lt _ (by decide)
  have hRes : 0 < res := recurringKeyResidualLive (round := 0) 0 hTrips hCount hRow
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
  obtain ⟨b,hbRun,hB⟩ := straightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (keyCopyLaneOffsetCore (l := l) (g := g') hTid false) hA'
  change At b 983 G at hB
  have hB' : At b 983 (recurringSwizzleInputs l tid 0 ++ G) := by
    refine hB.mono ((holds_append ..).mpr ⟨?_,hB.2.2.2.2⟩)
    exact ⟨holds_lookup hB.2.2.2.2 rfl,holds_lookup hB.2.2.2.2 rfl,
      holds_lookup hB.2.2.2.2 rfl,trivial⟩
  obtain ⟨c,hc,hC⟩ := straightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (recurringSwizzleCore (l := l) (g := g') hTid hp.shared.2.1 0) hB'
  change At c 996 (recurringSwizzleFacts l tid 0 ++ G) at hC
  have hC' : At c 996 ([(1116,b32 tile),(7174,b32 0),(1979,b32 row),(1086,b32 len)]++H) := by
    have hs := hC.2.2.2.2
    have hSplit := (holds_append ..).mp hs
    have hH : Holds c.regs H := (holds_append c.regs (recurringSwizzleFacts l tid 0) F).mpr
      ⟨hSplit.1,hSplit.2.2⟩
    exact hC.mono ⟨holds_lookup hs rfl,holds_lookup hs rfl,holds_lookup hs rfl,holds_lookup hs rfl,
      hH⟩
  obtain ⟨d,hd,hD⟩ := straightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (warmKeyCopyResidualCore (l := l) (g := g') (round := 0) (by omega)
      hTile hRow (by simpa only [Nat.sub_zero] using hLive) hLen) hC'
  change At d 1002 ((1997,b32 res)::H) at hD
  have hCmp : Seg kernel [] l g' 1 1002 [(1997,b32 res)] 1003 [(169,.pred true)] :=
    liveKeyCompareCore Flow.code_1002 hRes hResSmall
  obtain ⟨e,he,hE⟩ := straightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hCmp
    (show At d 1002 ([(1997,b32 res)] ++ ((1997,b32 res)::H)) from
      hD.mono ⟨hD.2.2.2.2.1,hD.2.2.2.2⟩)
  exact ⟨e,run_rtg (run_comp ha (run_comp hbRun (run_comp hc (run_comp hd he)))),hE⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
