-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundTail
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmValueStart
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmValueSaves
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmValueReload
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringSwizzle
import Kernels.TmlFa4Fwd.Flow.Code.Part018
import Kernels.TmlFa4Fwd.Flow.Code.Part019
import Lemmas.Flow.Run

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader
open LocalAccessCode (DoesNotClobber)

/-- The carry of the V packet of warm round `round`. The two Bias phase registers hold
`bias`; warp 15 keeps the round's phases and warp 14 has toggled them before V. -/
def warmRoundVCarry (p : Params) (l : Launch) (g batch round : Nat) (bias : Value)
    (lane : Nat) : List (Nat × Value) :=
  let co := assignedCoordinates p batch (g/l.block)
  let n := Mma.trips p batch co.1
  let residual := vPrimingResidual p batch co.1
  let use := cacheUseOfRound round
  recurringVTransitionFacts 0 (kvUseStage use) (kvEmptyPhase use) ++
    ((recurringBarrierFacts l 0 (kvUseStage use) (cacheEmptyParity use) ++
      ((1119,b32 (8*(warpLane l g lane%l.block%8))) ::
        ([(7174,b32 round),(7178,bias),(7179,b32 (kvUseStage use).val),
          (7180,loaderPhaseWord (kvEmptyPhase use)),
          (1117,b32 (residual/2^31)),(1116,b32 (n-2)),
          (7,.pred (decide (10 < n) && warmResidueFlag residual))] ++
          [(164,.pred (warmResidueFlag residual)),(7177,bias)] ++
          openingWarmFrame p l g batch lane ++ drainSchedulerFrame p l (warpLane l g lane)))) ++
      keySizes 16)

/-- The frame at the start of the V pointer saves of warm round `round`. -/
def warmRoundVAcquired (p : Params) (l : Launch) (g batch round : Nat) (bias : Value)
    (lane : Nat) : List (Nat × Value) :=
  recurringBarrierFacts l 1 (kvUseStage (cacheUseOfRound round+1))
    (cacheEmptyParity (cacheUseOfRound round+1)) ++ warmRoundVCarry p l g batch round bias lane

def warmRoundVHeadBase (p : Params) (l : Launch) (g batch : Nat) : Nat :=
  p.vLayout.base+2*((assignedCoordinates p batch (g/l.block)).2/6*p.vLayout.headStride)

def warmRoundValuePointer (p : Params) (l : Launch) (g batch round lane : Nat) (slot : Fin 2) :
    Nat :=
  primingVRowPointer p batch ((assignedCoordinates p batch (g/l.block)).2/6)
    (warmRoundSlotRow p l g batch round lane slot)

private theorem warmRoundVSaveFrame (p : Params) (l : Launch) (g batch round : Nat)
    (bias : Value) (lane : Nat) (more : Bool) :
    RecurringSaveFrame 1 ((10,.pred more) :: warmRoundVAcquired p l g batch round bias lane) := by
  let F := (10,.pred more) :: warmRoundVAcquired p l g batch round bias lane
  have hFresh : (F.map Prod.fst).all (fun r => decide (r ≠ 7710 ∧ r ≠ 7712)) = true := rfl
  have hf (pair : Nat × Value) (hm : pair ∈ F) : pair.1 ≠ 7710 ∧ pair.1 ≠ 7712 :=
    of_decide_eq_true (List.all_eq_true.mp hFresh _ (List.mem_map_of_mem hm))
  exact ⟨by set_option maxRecDepth 100000 in kernel_rfl,fun pair hm => (hf pair hm).1,
    by set_option maxRecDepth 100000 in kernel_rfl,fun pair hm => (hf pair hm).2,
    by set_option maxRecDepth 100000 in kernel_rfl⟩

set_option maxRecDepth 4096 in
private theorem warmRoundVPointerSlotOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch round shuffles votes : Nat} {bias : Value} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (slot : Fin 2) (more : Bool)
    {ends : Nat → Option TState}
    (start : SchedulerWarpReached l X g 1212 (fun lane =>
      recurringScratchSaveInput l 1 slot p.vLayout.pageStride p.vLayout.rowStride
        (warmRoundVHeadBase p l g batch) ++
        ((10,.pred more) :: warmRoundVAcquired p l g batch round bias lane))
      shuffles votes ends)
    (hCells : ∀ lane < 32, ∀ isRow,
      warmRoundMetadata p l X g batch round lane (start.pos lane) slot isRow) :
    ∃ done : SchedulerWarpReached l X g 1224
        (fun lane => (10,.pred more) :: warmRoundVAcquired p l g batch round bias lane)
        shuffles votes ends,
      ∀ lane < 32,
        let t := warpLane l g lane
        let dst := pointerSaveAccess l t 1 slot
        let bs := (b64 (warmRoundValuePointer p l g batch round lane slot)).toBytes
        PrimingCellValue X t (done.pos lane) 1223 dst bs ∧
        ∀ {saved : Nat} {cell : Acc} {data : List Byte},
          PrimingCellValue X t (start.pos lane) saved cell data →
          DoesNotClobber cell ⟨1223,.wr dst bs⟩ →
          PrimingCellValue X t (done.pos lane) saved cell data := by
  dsimp only
  let head := (assignedCoordinates p batch (g/l.block)).2/6
  let base := warmRoundVHeadBase p l g batch
  let ps := p.vLayout.pageStride
  let rs := p.vLayout.rowStride
  let row := fun lane => warmRoundSlotRow p l g batch round lane slot
  let page := fun lane => primingScratchPage p batch (row lane)
  have hh : head < p.kvHeads := by
    have hv := (assignedCoordinates_valid hp hLo hHi).2
    unfold Params.heads at hv
    omega
  have hPS : ps < 2 ^ 64 := (hp.objectBytes 2 40 8 ps (by simp [ps,Params.objectWords])).1
  have hRS : rs < 2 ^ 64 := (hp.objectBytes 2 24 8 rs (by simp [rs,Params.objectWords])).1
  have hPageSigned (lane : Nat) : page lane < 2 ^ 31 := by
    dsimp [page,primingScratchPage]
    split
    · rename_i h
      exact ((hp.pageTable batch hb).2 (row lane/16) (by omega)).2
    · decide
  have hPayload (lane : Nat) :
      sourceScratchPayload (page lane) (row lane%16) ps rs base =
        primingVRowPointer p batch head (row lane) ∧
      sourceScratchPayload (page lane) (row lane%16) ps rs base < 2^64 := by
    have h := sourceScratchPayload_live hp 1 (primingScratchPageBound hp (row := row lane) hb)
      (Nat.mod_lt (row lane) (by decide)) hh
    exact ⟨h.1,h.2.1⟩
  obtain ⟨done,_,hSaved⟩ := recurringPointerSaveWarpPreservingOfMaximal hp hMax hg hw 1 slot page
    (fun lane => row lane%16) (fun lane _ => hPageSigned lane)
    (fun _ _ => (Nat.mod_lt _ (by decide : 0 < 16)).trans (by decide))
    hPS hRS (fun lane _ => (hPayload lane).2)
    (fun lane _ => warmRoundVSaveFrame p l g batch round bias lane more) start
    (fun lane hl isRow => by
      cases isRow
      · exact hCells lane hl false
      · exact hCells lane hl true)
  refine ⟨done,fun lane hl => ?_⟩
  have h := hSaved lane hl
  dsimp only at h ⊢
  rw [(hPayload lane).1] at h
  exact h

set_option maxRecDepth 4096 in
private theorem warmRoundVSaveInput {l : Launch} {g : Nat} {p : Params} {batch round : Nat}
    {bias : Value} {lane : Nat} {s : TState} (slot : Fin 2) (more : Bool)
    (hs : At s 1212 ((9538,b64 slot.val) :: (10,.pred more) ::
      warmRoundVAcquired p l g batch round bias lane)) :
    At s 1212 (recurringScratchSaveInput l 1 slot p.vLayout.pageStride p.vLayout.rowStride
      (warmRoundVHeadBase p l g batch) ++
      ((10,.pred more) :: warmRoundVAcquired p l g batch round bias lane)) := by
  refine hs.mono ((holds_append ..).mpr ⟨?_,hs.2.2.2.2.2⟩)
  have hF := hs.2.2.2.2
  simp only [recurringScratchSaveInput,recurringScratchCarry,recurringSaveInputs,
    pointerReloadBase,pointerReloadAddress,List.cons_append,List.nil_append,Holds,
    warmRoundVHeadBase]
  refine ⟨holds_mem hF ?_,holds_mem hF ?_,holds_mem hF ?_,holds_mem hF ?_,holds_mem hF ?_,
    hF.1,holds_mem hF ?_,trivial⟩ <;>
    simp [warmRoundVAcquired,warmRoundVCarry,openingWarmFrame,warmStartFrame,
      primingVScratchAbi]

/-- The V pointers of warm round `round` are computed and saved, the lane column and both
swizzled destination bases are prepared, and the first pointer is reloaded. -/
structure WarmRoundVReloaded (p : Params) (l : Launch) (X : Execution) (g batch round : Nat)
    (bias : Value) (shuffles votes : Nat) (ends : Nat → Option TState) where
  reached : SchedulerWarpReached l X g 1239 (fun lane =>
    let t := warpLane l g lane
    let tid := t%l.block
    let ptr := warmRoundValuePointer p l g batch round lane 0
    [(2077,b32 (ptr%2^32)),(2078,b32 (ptr/2^32)),(2066,b32 (16*tid))] ++
      recurringSwizzleFacts l tid 1 ++ (9538,b64 1) :: (777,.pred false) ::
        warmRoundVAcquired p l g batch round bias lane) shuffles votes ends
  upper : ∀ lane < 32, PrimingCellValue X (warpLane l g lane) (reached.pos lane) 1223
    (pointerSaveAccess l (warpLane l g lane) 1 1)
    (b64 (warmRoundValuePointer p l g batch round lane 1)).toBytes

set_option maxRecDepth 4096 in
private theorem warmRoundVSwizzleLocal {l : Launch} {g tid : Nat} {s : TState}
    {F : List (Nat × Value)} (hTid : tid < 512) (hBase : l.sharedBase+232448 ≤ 2^18)
    (hKeep : ((kernel.code.drop 1227).take 11).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 1227 ([(1061,b32 tid),(2535,b32 l.sharedBase)] ++ F)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 1238 ([(2066,b32 (16*tid))] ++ recurringSwizzleFacts l tid 1 ++ F) := by
  obtain ⟨u,hu,hU⟩ := roundStraightFrame (A := recurringSwizzleInputs l tid 1)
    (by decide) (by decide) hKeep (by set_option maxRecDepth 100000 in kernel_rfl)
    (recurringSwizzleCore (l := l) (g := g) hTid hBase 1) hs
  obtain ⟨v,hv,hV⟩ := warmValueColumnCore (l := l) (g := g) hTid s
    (hs.mono ⟨hs.2.2.2.2.1,trivial⟩)
  have hvA := (loaderLinear (regs := []) (by decide) (by decide) hs.1 (by simp) rfl hv).1
  have hRest : run kernel Assumptions.all l g 10 v = some u := by
    have h := run_add (K := kernel) (A := Assumptions.all) (L := l) (g := g) 1 10 s
    rw [hvA,Option.bind_some] at h
    rw [← h]
    exact hu
  have hRest' := loaderRunWithoutAssumptions (lo := 1228) (len := 10) (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl) hRest (le_of_eq hV.1.symm)
    (by rw [hV.1])
  obtain ⟨_,hCol⟩ := loaderLinear (regs := [2066]) (by decide) (by decide) hV.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hRest'
  refine ⟨u,run_rtg hu,hU.mono ⟨(hCol 2066 (by simp)).trans hV.2.2.2.2.1,hU.2.2.2.2⟩⟩

set_option maxRecDepth 4096 in
/-- From its V acquire, a loader warp of warm round `round` saves both V pointers, prepares
the lane column and destination bases, and reloads the first pointer. The page and row words
written by the round's K refresh supply the pointers. -/
theorem warmRoundVPointersOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch round shuffles votes : Nat} {bias : Value} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1209 (warmRoundVAcquired p l g batch round bias)
      shuffles votes ends)
    (hCells : ∀ lane < 32, ∀ slot isRow,
      warmRoundMetadata p l X g batch round lane (cur.pos lane) slot isRow) :
    Nonempty (WarmRoundVReloaded p l X g batch round bias shuffles votes ends) := by
  let VA := warmRoundVAcquired p l g batch round bias
  let head := (assignedCoordinates p batch (g/l.block)).2/6
  have hh : head < p.kvHeads := by
    have hv := (assignedCoordinates_valid hp hLo hHi).2
    unfold Params.heads at hv
    omega
  -- seed the slot loop
  obtain ⟨seed,hSeed⟩ := cur.advanceLocalWithPosition (pc' := 1212)
    (G := fun lane => (9538,b64 (0 : Fin 2).val) :: (10,.pred true) :: VA lane) (by
      intro lane hl
      have hs := cur.checkpoint lane hl
      obtain ⟨u,hu,hU⟩ := roundStraightFrame (A := []) (by decide) (by decide)
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (warmValueSaveSeed (l := l) (g := warpLane l g lane)) (hs.mono hs.2.2.2.2)
      exact ⟨u,run_rtg hu,hU⟩)
  obtain ⟨start0,hStart0⟩ := seed.advanceLocalWithPosition (pc' := 1212)
    (G := fun lane => recurringScratchSaveInput l 1 0 p.vLayout.pageStride p.vLayout.rowStride
      (warmRoundVHeadBase p l g batch) ++ ((10,.pred true) :: VA lane)) (by
      intro lane hl
      exact ⟨seed.state lane,.refl,warmRoundVSaveInput 0 true (seed.checkpoint lane hl)⟩)
  obtain ⟨saved0,hSaved0⟩ := warmRoundVPointerSlotOfMaximal hp hMax hg hw hb hLo hHi 0 true
    start0 (fun lane hl isRow => by rw [hStart0,hSeed]; exact hCells lane hl 0 isRow)
  -- second slot
  obtain ⟨start1,hStart1⟩ := saved0.advanceLocalWithPosition (pc' := 1212)
    (G := fun lane => recurringScratchSaveInput l 1 1 p.vLayout.pageStride p.vLayout.rowStride
      (warmRoundVHeadBase p l g batch) ++ ((10,.pred false) :: VA lane)) (by
      intro lane hl
      have hs := saved0.checkpoint lane hl
      obtain ⟨u,hu,hU⟩ := warmValueSaveRoute (l := l) (g := warpLane l g lane) (F := VA lane) true
        (by set_option maxRecDepth 100000 in kernel_rfl) hs
      obtain ⟨v,hv,hV⟩ := warmValueNextEntry (l := l) (g := warpLane l g lane) (F := VA lane)
        (by set_option maxRecDepth 100000 in kernel_rfl) hU
      exact ⟨v,run_rtg (run_comp hu hv),warmRoundVSaveInput 1 false hV⟩)
  obtain ⟨saved1,hSaved1⟩ := warmRoundVPointerSlotOfMaximal hp hMax hg hw hb hLo hHi 1 false
    start1 (fun lane hl isRow => by
      rw [hStart1]
      exact (hSaved0 lane hl).2 (by rw [hStart0,hSeed]; exact hCells lane hl 1 isRow)
        (metadataApartFromPointerSave l _ 1 1 0 isRow _ _))
  -- column, swizzle and reload
  obtain ⟨prep,hPrep⟩ := saved1.advanceLocalWithPosition (pc' := 1238)
    (G := fun lane =>
      let tid := warpLane l g lane%l.block
      [(2066,b32 (16*tid))] ++ recurringSwizzleFacts l tid 1 ++
        (9538,b64 1) :: (777,.pred false) :: VA lane) (by
      intro lane hl
      let t := warpLane l g lane
      let tid := t%l.block
      have hTid : tid < 512 := by dsimp [tid]; rw [hp.block]; exact Nat.mod_lt _ (by decide)
      have hs := saved1.checkpoint lane hl
      obtain ⟨u,hu,hU⟩ := warmValueSaveRoute (l := l) (g := t) (F := VA lane) false
        (by set_option maxRecDepth 100000 in kernel_rfl) hs
      have hF := hU.2.2.2.2
      have hIn : At u 1227 ([(1061,b32 tid),(2535,b32 l.sharedBase)] ++
          ((9538,b64 1) :: (777,.pred false) :: VA lane)) := by
        refine hU.mono ⟨holds_mem hF.2.2 ?_,holds_mem hF.2.2 ?_,hF⟩ <;>
          simp [VA,warmRoundVAcquired,warmRoundVCarry,openingWarmFrame,warmStartFrame,
            warmPageRoots,warmLaneRoots,tid,t]
      obtain ⟨v,hv,hV⟩ := warmRoundVSwizzleLocal (g := t) hTid hp.shared.2.1
        (by set_option maxRecDepth 100000 in kernel_rfl) hIn
      exact ⟨v,(run_rtg hu).trans hv,hV⟩)
  let addr := l.localBase
  have hAddr : addr+warmVFirstReload.offset < 2^64 := by
    have h := hp.localMemory.2.1
    change l.localBase+0 < 2^64
    omega
  have hAlign : (addr+warmVFirstReload.offset)%8 = 0 := by
    have h := hp.localMemory.1
    change (l.localBase+0)%8 = 0
    omega
  have hPtr (lane : Nat) (slot : Fin 2) :
      warmRoundValuePointer p l g batch round lane slot < 2^64 := by
    let row := warmRoundSlotRow p l g batch round lane slot
    obtain ⟨hEq,hLt,_⟩ := sourceScratchPayload_live hp 1
      (primingScratchPageBound hp (row := row) hb) (Nat.mod_lt row (by decide)) hh
    rw [hEq] at hLt
    simpa [warmRoundValuePointer,primingVRowPointer] using hLt
  obtain ⟨done,hDone,hRead⟩ := warmVFirstReload.warpReadPreservingOfMaximal hp hMax hg
    (by decide) Flow.code_1238 hAddr hAlign (by decide)
    (fun lane => warmRoundValuePointer p l g batch round lane 0) (fun lane _ => hPtr lane 0) prep
    (fun lane _ => by
      simp [warmVFirstReload,addr,VA,warmRoundVAcquired,warmRoundVCarry,openingWarmFrame,
        warmStartFrame,primingVScratchAbi])
    (fun lane _ pair hm => by
      have h : ((let tid := warpLane l g lane%l.block
        [(2066,b32 (16*tid))] ++ recurringSwizzleFacts l tid 1 ++
          (9538,b64 1) :: (777,.pred false) :: VA lane).map Prod.fst).all
          (fun r => decide (r ≠ 2077 ∧ r ≠ 2078)) = true := rfl
      exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm)))
    (fun lane hl => by
      rw [hPrep]
      exact (hSaved1 lane hl).2 (by rw [hStart1]; exact (hSaved0 lane hl).1) (by
        intro dst _ hKind
        cases hKind
        rintro ⟨loc,hLoc,hWrite⟩
        simp [warmVFirstReload,SavedPointerReload.cell,addr,pointerSaveAccess,
          pointerSaveAddress,pointerReloadAddress,Acc.Covers,Loc.InRange] at hLoc hWrite
        omega))
  refine ⟨⟨done,fun lane hl => ?_⟩⟩
  apply (hRead lane hl).2
  rw [hPrep]
  exact (hSaved1 lane hl).1

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
