-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingScratchLoop
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKFromScratch
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderStoreProgress
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.ProtectedReadProgress
import Lemmas.Step.DrainInOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

private theorem dropRecorded {X : Execution} {g j : Nat} {e : Event}
    (he : X.get (g,j) = some e) : (X.tr g).drop j = e :: (X.tr g).drop (j+1) := by
  have h := List.getElem?_eq_some_iff.mp he
  rw [List.drop_eq_getElem_cons h.1,h.2]

/-- A scratch iteration records its optional page read, its page save, and its row save
at the actual replay boundary of a maximal loader trace. -/
theorem primingScratchIterationOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g i batch base : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hb : batch < p.batch) (entry : Fin 2) (hRow : base+64*entry.val < 2^31)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    {s t : TState} {extra : List (Nat × Value)} (hExtra : PrimingScratchExtra extra)
    (ht : At t 488 (primingScratchFacts p l batch base entry ++ extra))
    {ending : Option TState}
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take i) (some s))
    (hTail : Run kernel Assumptions.all l g s ((X.tr g).drop i) ending)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (hPos : 0 < i) (hBound : i ≤ (X.tr g).length)
    (hRelease : i = (X.tr g).length → Step.Released l X g) :
    let events := primingScratchEvents p l g batch base entry
    let stop := i+events.length
    ∃ v u, (X.tr g).drop i = events ++ (X.tr g).drop stop ∧
      At u (if entry.val == 0 then 488 else 515) (primingScratchFacts p l batch base 1 ++ extra) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take stop) (some v) ∧
      Run kernel Assumptions.all l g v ((X.tr g).drop stop) ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) v u ∧
      stop ≤ (X.tr g).length ∧ (stop = (X.tr g).length → Step.Released l X g) := by
  dsimp only
  let row := base+64*entry.val
  let page := primingScratchPage p batch row
  let addr : Acc := {loc := globalLoc (pageWordAddress p batch (row/16)),size := 4}
  let read := Event.mk 503 (.rd addr ((b32 page).toBytes.map some))
  let reads := if row < p.kLength batch then [read] else []
  let j := i+reads.length
  let F := primingPageCarry p l batch row entry ++ extra
  obtain ⟨v,hv,hV⟩ := primingScratchPrepare (g := g) hp hb entry hRow hExtra ht
  obtain ⟨w,hwStep,hW⟩ := primingScratchPageGuard (g := g) hV
  have hGate := (hLocal.trans hv).trans (run_rtg hwStep)
  have hRead : ∃ before ready,
      (X.tr g).drop i = reads ++ (X.tr g).drop j ∧
      At ready 504 ((7173,b32 page) :: F) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take j) (some before) ∧
      Run kernel Assumptions.all l g before ((X.tr g).drop j) ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) before ready ∧
      j ≤ (X.tr g).length ∧ (j = (X.tr g).length → Step.Released l X g) := by
    by_cases hLive : row < p.kLength batch
    · have hW' : At w 501 F := by
        rw [ite_eq_left hLive] at hW
        exact hW.mono hW.2.2.2.2.2
      have hPage : page = p.page batch (row/16) := by simp [page,primingScratchPage,hLive]
      obtain ⟨z,hNext,hZ,hState,hReady⟩ := primingPageReadNext (g := g) hp hb hLive
        entry hExtra.page hW'
      have hn : Next kernel Assumptions.all l g s z (.read addr (afterLoad z [7173])) :=
        ⟨hGate.trans hNext.steps,hNext.stop⟩
      have hIndex : row/16 < (p.kLength batch+15)/16 := by omega
      obtain ⟨he,hPast,hRest⟩ := Step.protected_read_of_maximal hMax hg (a := addr)
        (value := b32 page) rfl (hPage ▸ hp.pageBytes batch hb (row/16) hIndex)
        (primingPageProtected hp hb hLive writes) hn hPrefix hTail hPos hBound hRelease
        (Assumptions.wf_snoc_initial hMax.1)
      rw [hZ.1] at he
      rw [← hPage] at hState hReady
      rw [hState] at hPast hRest
      have hJ : j = i+1 := by simp [j,reads,hLive]
      refine ⟨_,_,?_,hReady,?_,?_,.refl,?_,?_⟩
      · simpa only [reads,ite_eq_left hLive,hJ,List.singleton_append] using dropRecorded he
      · rwa [hJ]
      · rwa [hJ]
      · rw [hJ]; exact len_of_get he
      · rw [hJ]; exact releasedIfLast he (by intro h; cases h)
    · have hJ : j = i := by simp [j,reads,hLive]
      rw [ite_eq_right hLive] at hW
      have hW' : At w 504 ((7173,b32 page) :: F) := by
        simpa only [page,primingScratchPage,ite_eq_right hLive] using hW
      refine ⟨s,w,?_,hW',?_,?_,hGate,?_,?_⟩
      · simp [reads,hLive,hJ]
      · rwa [hJ]
      · rwa [hJ]
      · rwa [hJ]
      · rwa [hJ]
  obtain ⟨before,ready,hRd,hReady,hPast,hRest,hTo,hLimit,hRel⟩ := hRead
  have hJPos : 0 < j := hPos.trans_le (Nat.le_add_right _ _)
  obtain ⟨save,hSave,hNext⟩ := primingPageStoreNext (g := g) hp entry hExtra.page hReady
  have hn : Next kernel Assumptions.all l g before save
      (.write (scratchWordAccess l g 0 entry) (b32 page).toBytes (next save)) :=
    ⟨hTo.trans hNext.steps,hNext.stop⟩
  obtain ⟨he,hPast',hRest'⟩ :=
    plainLoaderStoreOfMaximal hp hMax hg hw rfl hn hPast hRest hJPos hLimit hRel
  rw [hSave.1] at he
  obtain ⟨rowStore,hRowStore,hRowNext⟩ := primingScratchRowNext (g := g) hp hRow
    entry hExtra hSave.next
  obtain ⟨he',hPast'',hRest''⟩ :=
    plainLoaderStoreOfMaximal hp hMax hg hw rfl hRowNext hPast' hRest' (Nat.succ_pos _)
      (len_of_get he) (releasedIfLast he (by intro h; cases h))
  rw [hRowStore.1] at he'
  obtain ⟨finish,hFinish,hAt⟩ := primingScratchFinish (g := g) entry hExtra hRowStore.next
  have hEvents : primingScratchEvents p l g batch base entry =
      reads ++ [⟨506,.wr (scratchWordAccess l g 0 entry) (b32 page).toBytes⟩,
        ⟨511,.wr (rowScratchAccess l g entry) (b32 (row%16)).toBytes⟩] := rfl
  have hEnd : i+(primingScratchEvents p l g batch base entry).length = j+1+1 := by
    rw [hEvents,List.length_append]
    change i+(_+2) = j+1+1
    dsimp only [j]
    omega
  rw [hEnd]
  refine ⟨_,finish,?_,hAt,hPast'',hRest'',hFinish,len_of_get he',
    releasedIfLast he' (by intro h; cases h)⟩
  rw [hRd,dropRecorded he,dropRecorded he',hEvents,List.append_assoc]
  rfl

/-- The initial scratch selector and pack frame at either iteration. -/
def loaderScratchIterationFrame (p : Params) (l : Launch) (batch head tile warp : Nat)
    (entry : Fin 2) (lane : Nat) : List (Nat × Value) :=
  primingScratchFacts p l batch (primingLaneRow tile (32*warp+lane)) entry ++
    primingKPackFrame p l batch head tile warp lane

private theorem primingScratchEventsOrdinals (p : Params) (l : Launch) (g batch base : Nat)
    (entry : Fin 2) :
    (primingScratchEvents p l g batch base entry).countP Execution.isShfl = 0 ∧
    (primingScratchEvents p l g batch base entry).countP isFullWarpVote = 0 := by
  simp only [primingScratchEvents]
  split <;> exact ⟨rfl,rfl⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
include hp hMax writes

/-- A maximal active loader warp records all scratch events for the given decoded iteration. -/
theorem primingScratchWarpWithTrace {g batch head tile shuffles votes : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch) (hTile : 128*tile+127 < 2^31) (entry : Fin 2)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 488
      (loaderScratchIterationFrame p l batch head tile (warpIndex l g) entry)
      shuffles votes ends) :
    ∃ done : SchedulerWarpReached l X g (if entry.val == 0 then 488 else 515)
      (loaderScratchIterationFrame p l batch head tile (warpIndex l g) 1) shuffles votes ends,
      ∀ lane < 32,
        let thread := warpLane l g lane
        let base := primingLaneRow tile (32*warpIndex l g+lane)
        let events := primingScratchEvents p l thread batch base entry
        done.pos lane = cur.pos lane+events.length ∧
          (X.tr thread).drop (cur.pos lane) = events ++ (X.tr thread).drop (done.pos lane) := by
  classical
  let warp := warpIndex l g
  let thread := warpLane l g
  let base := fun lane => primingLaneRow tile (32*warp+lane)
  let events := fun lane => primingScratchEvents p l (thread lane) batch (base lane) entry
  let stop := fun lane => cur.pos lane+(events lane).length
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hReplay (lane : Nat) (hl : lane < 32) : ∃ v u,
      (X.tr (thread lane)).drop (cur.pos lane) =
        events lane ++ (X.tr (thread lane)).drop (stop lane) ∧
      At u (if entry.val == 0 then 488 else 515)
        (loaderScratchIterationFrame p l batch head tile warp 1 lane) ∧
      Run kernel Assumptions.all l (thread lane) {}
        ((X.tr (thread lane)).take (stop lane)) (some v) ∧
      Run kernel Assumptions.all l (thread lane) v
        ((X.tr (thread lane)).drop (stop lane)) (ends lane) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) v u ∧
      stop lane ≤ (X.tr (thread lane)).length ∧
      (stop lane = (X.tr (thread lane)).length → Step.Released l X (thread lane)) := by
    have hSame := (Step.sameWarp_lane hBlock hg hl).1
    have hThread : thread lane < l.threads := hSame.1.2.1
    have hActor : warpIndex l (thread lane) = warp := hSame.2.symm
    have hRows : base lane+64*entry.val < 2^31 := by
      have hHalf := Nat.mod_lt ((32*warp+lane)/8) (by decide : 0 < 8)
      have hColumn := Nat.mod_lt (32*warp+lane) (by decide : 0 < 8)
      have hEntry := entry.isLt
      simp only [base,primingLaneRow,kvCopyColumn,Bool.false_eq_true,ite_false,Nat.add_zero]
      omega
    exact primingScratchIterationOfMaximal hp hMax hThread (hActor.symm ▸ hw) hb entry hRows
      writes (primingKFrameScratch p l batch head tile warp lane) (cur.checkpoint lane hl)
      (cur.recorded lane hl) (cur.continuation lane hl) (cur.localSteps lane hl)
      (cur.positive lane hl) (cur.bounded lane hl) (cur.released lane hl)
  let _ : Inhabited TState := ⟨{}⟩
  choose! v u hTrace hAt hPrefix hTail hLocal hBound hRelease using hReplay
  have hOrd := cur.ordinals.advance events (fun lane hl => ⟨_,hTrace lane hl⟩)
    (fun lane _ => (primingScratchEventsOrdinals p l (thread lane) batch (base lane) entry).1)
    (fun lane _ => (primingScratchEventsOrdinals p l (thread lane) batch (base lane) entry).2)
  exact ⟨⟨⟨stop,v,u,hOrd,hTail,hLocal,hAt⟩,
    fun lane hl => (cur.positive lane hl).trans_le (Nat.le_add_right _ _),
    hBound,hRelease,hPrefix⟩,fun lane hl => ⟨rfl,hTrace lane hl⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
