-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalFirstRoute
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionIdleArrival
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerBallotCursor
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalDrainStart
import Kernels.TmlFa4Fwd.Proof.Thread.RowDrainRecordedKeep
import Kernels.TmlFa4Fwd.Flow.Code.Part143

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

def terminalBallotCarry (l : Launch) (part tiles : Nat) : List (Nat × Value) :=
  [(7283,b32 part),(7282,b32 tiles)] ++ terminalFreeFrame l 0

private theorem terminalLocalKeep {l : Launch} {g start n : Nat} {s t : TState}
    {F : List (Nat × Value)} (hs : At s start F)
    (hLo : 9083 ≤ start) (hHi : start+n ≤ 9201)
    (hKeep : ((kernel.code.drop start).take n).all
      (fun i => (F.map Prod.fst).all fun r => !(writesRegs i.op).contains r) = true)
    (hStraight : ((kernel.code.drop start).take (n-1)).all
      (fun i => schedulerFallsThrough i.op) = true)
    (hr : run kernel [] l g n s = some t) :
    Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t ∧ Holds t.regs F :=
  ⟨RowDrainRole.correction.drainLocals hLo hHi hs.1 hStraight hr,
    holdsSchedulerFrame hs.2.2.2.2
      (fun r hm => schedulerLocalFrame hKeep hStraight hr hs.1.ge (by rw [hs.1]) hm)
      (fun _ hm => List.mem_map_of_mem hm)⟩

private theorem terminalBallotArithmetic (l : Launch) (g : Nat)
    {base count part heads cta : Nat} (hPrefix : part ≤ count) (hCount : count < 2^31)
    (hHead : heads < 2^31) (hCta : cta < 2^31) (hEnd : base+count*heads < 2^31) :
    Seg kernel [] l g 4 9190
      [(7284,b32 count),(7143,b32 heads),(7286,b32 (base+count*heads)),
        (7283,b32 part),(1618,b32 cta)] 9194
      [(769,.pred (decide (base+part*heads ≤ cta)))] := by
  have hMul := Nat.mul_le_mul_right heads hPrefix
  have hBase : base < 2^31 := by omega
  have hProd : count*heads < 2^31 := by omega
  have hPre : part < 2^31 := by omega
  have hPrefixWork : base+part*heads < 2^31 := by omega
  intro s hs
  seg_fp hs using
    first
    | norm_cmp
    | (simp only [compare,Option.getD_some,← BitVec.ofNat_mul,
        truncBits_ofNat (show count < 2^32 by omega) (by decide),
        truncBits_ofNat (show heads < 2^32 by omega) (by decide),
        truncBits_ofNat (show part < 2^32 by omega) (by decide),
        truncBits_ofNat (show cta < 2^32 by omega) (by decide)]
       norm_cmp)

private theorem terminalBallotLocal {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g first : Nat} (hg : g < l.threads) (hFirst : first < p.batch)
    {t : TState} (ht : At t 9187
      ((7131,b32 (l.sharedBase+232))::terminalSelectedFrame p l g first)) :
    let part := prefixWindow (groupLaneTiles p first) 32 (laneOf l g)
    let base := tilePrefix p first*p.heads
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 9194 ((769,.pred (decide (base+part*p.heads ≤ g/l.block)))::
        terminalBallotCarry l part (groupLaneTiles p first (laneOf l g))) := by
  let xs := groupLaneTiles p first
  let lane := laneOf l g
  let base := tilePrefix p first*p.heads
  let cta := g/l.block
  let part := prefixWindow xs 32 lane
  let total := terminalGroupTotal p first
  let bound := terminalCutoff p first
  let F := (7131,b32 (l.sharedBase+232)) :: terminalSelectedFrame p l g first
  let G := terminalBallotCarry l part (xs lane)
  have hBatch : p.batch < 2^31 := hp.shape.2.1
  have hFirst32 : first < 2^32 := by omega
  have hBatch32 : p.batch < 2^32 := by omega
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hTotal : total < 2^31 := hp.groupWindow_signed hFirst.le (by decide : 31 < 32) 32
  have hPartTotal : part ≤ total := by
    rw [show total = ∑ i ∈ Finset.range 32, xs i from prefixWindow_warp _ (by decide)]
    exact prefixWindow_le_warp xs 32 hLane
  have hSum : base+total*p.heads = bound := by
    have h := congrArg (· * p.heads) (groupTiles_eq p hFirst.le (by decide : 32 ≤ 32))
    rw [show total = ∑ i ∈ Finset.range 32, xs i from prefixWindow_warp _ (by decide)]
    simpa only [show min 31 32 = 31 by decide,Nat.add_mul,base,bound,terminalCutoff,xs] using h
  have hFit : bound < 2^31 := hp.prefixWork_signed (Nat.min_le_left p.batch (first+31))
  have hCta : cta < 2^31 := (NamedBar.cta_lt hg).trans hp.grid.2.2
  have hGuard : Seg kernel [] l g 2 9187 [(7285,b32 first),(7153,b32 p.batch)]
      9189 [(768,.pred false),(7287,b32 0)] := by
    intro s hs
    seg_fp hs using
      first
      | rfl
      | simp only [compare,Option.getD_some,truncBits_ofNat hBatch32 (by decide),
          truncBits_ofNat hFirst32 (by decide),RowDrainRole.signedWord hBatch,
          RowDrainRole.signedWord (hFirst.trans hBatch),ge_iff_le,Int.ofNat_le,
          decide_eq_false (Nat.not_le_of_lt hFirst)]
  obtain ⟨v,hv,hAt⟩ := hGuard.apply
    (ht.mono ⟨holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,trivial⟩)
  have ht' : At t 9187 F := ht
  obtain ⟨hPath,hKeep⟩ := terminalLocalKeep ht' (by decide) (by decide)
    (by
      change ((kernel.code.drop 9187).take 2).all
        (fun i => [7131,7286,7285,7284,7283,7282,7143,7153,1616,7506,1618].all
          (fun r => !(writesRegs i.op).contains r)) = true
      decide +kernel) (by decide +kernel) hv
  have hV : At v 9189 ((768,.pred false)::(7287,b32 0)::F) :=
    hAt.mono ⟨hAt.2.2.2.2.1,hAt.2.2.2.2.2.1,hKeep⟩
  obtain ⟨s,hs,hS⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_9189 false hV hV.2.2.2.2.1 (by simp)
  have hInputs : At s 9190
      [(7284,b32 total),(7143,b32 p.heads),(7286,b32 bound),(7283,b32 part),(1618,b32 cta)] :=
    hS.mono ⟨holds_lookup hS.2.2.2.2 rfl,holds_lookup hS.2.2.2.2 rfl,
      holds_lookup hS.2.2.2.2 rfl,holds_lookup hS.2.2.2.2 rfl,
      holds_lookup hS.2.2.2.2 rfl,trivial⟩
  have hSegment := terminalBallotArithmetic l g hPartTotal hTotal hp.heads_signed hCta
    (hSum.symm ▸ hFit)
  rw [hSum] at hSegment
  obtain ⟨u,hu,hU⟩ := hSegment.apply hInputs
  have hSave : At s 9190 G := hS.mono ⟨holds_lookup hS.2.2.2.2 rfl,
    holds_lookup hS.2.2.2.2 rfl,holds_lookup hS.2.2.2.2 rfl,holds_lookup hS.2.2.2.2 rfl,trivial⟩
  obtain ⟨hLast,hRegs⟩ := terminalLocalKeep hSave (by decide) (by decide)
    (by
      change ((kernel.code.drop 9190).take 4).all
        (fun i => [7283,7282,7131,7287].all (fun r => !(writesRegs i.op).contains r)) = true
      decide +kernel) (by decide +kernel) hu
  exact ⟨u,(hPath.trans (RowDrainRole.correction.drainLocals (n := 1)
    (by decide) (by decide) hV.1 (by simp) hs)).trans hLast,hU.mono ⟨hU.2.2.2.2.1,hRegs⟩⟩

private theorem terminalFreeAddressPreserved {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) {g batch first : Nat}
    (c : LseTailReached p l X g batch)
    (d : OpeningTripCursor l X g 9187 (terminalSelectedFrame p l g first)) :
    Holds d.ready.regs [(7131,b32 (l.sharedBase+232))] := by
  let span : RowDrainSpan := ⟨9083,9188,9188⟩
  have hReg : c.cursor.ready.regs 7131 = some (b32 (l.sharedBase+232)) :=
    holds_lookup c.cursor.checkpoint.2.2.2.2 rfl
  refine span.recordedKeep hp (by decide) (by decide) (by decide) rfl
    (fun _ hm => (beforeCorrectionDrain hm).trans (by decide))
    (fun _ hm => (beforeCorrectionDrain hm).trans (by decide))
    ?_ ?_ ?_ ?_ (withFrame c.cursor
      (show Holds c.cursor.ready.regs [(7131,b32 (l.sharedBase+232))] from ⟨hReg,trivial⟩)) d
  · set_option maxRecDepth 100000 in kernel_rfl
  · apply span.segmentKeeps_of_audit
    set_option maxRecDepth 100000 in kernel_rfl
  · set_option maxRecDepth 100000 in kernel_rfl
  · set_option maxRecDepth 100000 in kernel_rfl

/-- The terminal correction ballot searches the exact prefix of the selected
request group and carries its actual released-slot address and phase. -/
theorem terminalSelectedGroupBallot {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g first batch shuffles votes : Nat} (hg : g < l.threads)
    (hFirst : first < p.batch) (hLo : tilePrefix p first*p.heads ≤ g/l.block)
    (hHi : g/l.block < terminalCutoff p first) {ends : Nat → Option TState}
    (tails : ∀ lane < 32, Nonempty (LseTailReached p l X (warpLane l g lane) batch))
    (cur : SchedulerWarpReached l X g 9187
      (fun lane => terminalSelectedFrame p l (warpLane l g lane) first) shuffles votes ends) :
    ∃ n < 31, Nonempty (SchedulerWarpReached l X g 9194
      (fun lane => (769,.pred (decide (lane < n)))::
        terminalBallotCarry l (prefixWindow (groupLaneTiles p first) 32 lane)
          (groupLaneTiles p first lane)) shuffles votes ends) := by
  obtain ⟨found,⟨hStart,hGroup,hBatch,hBelow,hAbove⟩,_⟩ := groupContains_request p hLo hHi
  let n := found-first
  have hn : n < 31 := by dsimp [n]; omega
  refine ⟨n,hn,?_⟩
  apply cur.advanceLocal
  intro lane hl
  have hBlock : l.block%32=0 := by rw [hp.block]
  have hWarp := Step.sameWarp_lane hBlock hg hl
  let hCur := laneCursor cur hl
  obtain ⟨tail⟩ := tails lane hl
  have hFrame : Holds hCur.ready.regs
      ((7131,b32 (l.sharedBase+232))::terminalSelectedFrame p l (warpLane l g lane) first) :=
    ⟨(terminalFreeAddressPreserved hp tail hCur).1,hCur.checkpoint.2.2.2.2⟩
  obtain ⟨u,hPath,hAt⟩ := terminalBallotLocal (g := warpLane l g lane) hp hWarp.1.1.2.1 hFirst
    (hCur.checkpoint.mono hFrame)
  have hLane : laneOf l (warpLane l g lane) = lane := hWarp.2
  have hCta : warpLane l g lane/l.block = g/l.block := hWarp.1.1.2.2.symm
  rw [hLane,hCta] at hAt
  have hPart : (tilePrefix p first*p.heads+
      prefixWindow (groupLaneTiles p first) 32 lane*p.heads ≤ g/l.block) ↔ lane < n := by
    rw [← Nat.add_mul,prefixWindow_warp _ hl]
    exact (groupBallot_iff p hStart hGroup hBatch hl hBelow hAbove).trans (by dsimp [n]; omega)
  have hBool : decide _ = decide (lane < n) := Bool.eq_iff_iff.mpr (by
    simpa only [decide_eq_true_eq] using hPart)
  rw [hBool] at hAt
  exact ⟨u,by simpa only [hCur,laneCursor] using hPath,hAt⟩

end PTX.Kernels.TmlFa4Fwd.Correction
