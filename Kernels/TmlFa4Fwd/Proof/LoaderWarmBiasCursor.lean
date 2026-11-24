-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasEntry
public import Kernels.TmlFa4Fwd.Proof.LoaderRepeatedBiasCoordinates
import Kernels.TmlFa4Fwd.Proof.LoaderWarmIterationCursor
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage half : Fin 2) {g j address : Nat}
    {spec : TensorCopy.Spec} (hw : warpIndex l g = 14)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
include hp hX stage half hw writes

set_option maxRecDepth 10000 in
/-- The same warm iteration as the actual Bias issue retains its counter,
packed Q row, query head and the branch's residual bit. -/
theorem warmBiasEntryOfIssueWithRank (hCTA : g/l.block < tilePrefix p p.batch*p.heads)
    (he : X.get (g,j) = some ⟨warmBiasIssueSite stage half,.tensorIssue address spec⟩) :
    ∃ batch < p.batch,
      tilePrefix p batch*p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1)*p.heads ∧
      let co := assignedCoordinates p batch (g/l.block)
      let trips := Mma.trips p batch co.1
      ∃ iteration < min (trips-1) 9, ∃ pos ≤ j, ∃ s ending,
        At s 917 ([(7174,b32 iteration),(1090,b32 0),
          (1117,b32 (warmBiasResidualBit p batch co.1)),
          (1087,b32 (p.qOffset batch + 256*co.1)),(7169,b32 co.2)]) ∧
        Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending ∧
        (((X.tr g).drop pos).take (j-pos)).countP Execution.isShfl < 64 ∧
        ((X.tr g).take j).countP Execution.isShfl = primingSearchShuffleCount batch+64+
          64*iteration+32 := by
  let event : Event := ⟨warmBiasIssueSite stage half,.tensorIssue address spec⟩
  let lane := laneOf l g
  have hLaneLt : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hGet : X.get (warpLane l g lane,j) = some event := hLane.symm ▸ he
  have hSite : 917 ≤ event.pc ∧ event.pc < 1348 := by
    change 917 ≤ warmBiasIssueSite stage half ∧ warmBiasIssueSite stage half < 1348
    fin_cases stage <;> fin_cases half <;> decide
  have hRankTail : 0 < loaderShuffleTail 1348 event.pc ∧
      loaderShuffleTail 1348 event.pc < 64 := by
    change 0 < loaderShuffleTail 1348 (warmBiasIssueSite stage half) ∧
      loaderShuffleTail 1348 (warmBiasIssueSite stage half) < 64
    fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in decide +kernel)
  have hSafe : ∀ f, event.kind ≠ .ub f := by rintro _ ⟨⟩
  obtain ⟨batch,hb,hLo,hHi,hTwo,start,hStart,s,ending,hs,hr,hStartRank⟩ :=
    warmFirstWithBiasOfEvent hp hX (src := lane) (event_thread_lt hX he) hw.ge hLaneLt
      writes hCTA hGet hSite.1 (.inl (by omega)) hSafe
  rw [hLane] at hs hr hStartRank
  let co := assignedCoordinates p batch (g/l.block)
  let trips := Mma.trips p batch co.1
  let F := (1117,b32 (warmBiasResidualBit p batch co.1)) ::
    warmStartFrame p l batch (co.2/6) trips (warpIndex l g) (g % l.block) ++
    warmBiasRoots p batch co.1 co.2
  have hShared : (2535,b32 l.sharedBase) ∈ F := by simp [F,warmStartFrame]
  have hRole : (1062,b32 (14+(0:Fin 2).val)) ∈ F := by simp [F,warmStartFrame,hw]
  have hTrip : trips-1 < 2^31 := by
    have h := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).2.1
    have hLen := (hp.lengths batch hb).2.2
    change trips ≤ (p.kLength batch+127)/128 at h
    omega
  change 2 ≤ trips at hTwo
  have hInit : 0 < min (trips-1) 9 := by omega
  have hRemain : (1091,b32 (trips-1)) ∈ F := by simp [F,warmStartFrame]
  have hAt : At s 917 ([(7174,b32 0),(1091,b32 (trips-1))] ++ F) :=
    hs.mono ⟨hs.2.2.2.2.1,holds_mem hs.2.2.2.2.2 hRemain,hs.2.2.2.2.2⟩
  have hBody (n : Nat) : ((kernel.code.drop 917).take (1348 - 917)).all
      (fun ins => loaderPipelineCutOp 917 1348 n
        ([7174,1091] ++ F.map Prod.fst) ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hTail : ((kernel.code.drop 1348).take 4).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨iteration,_,hIter,hRank⟩ :=
    warmRoundOfObservedEvent 0 hTrip hInit hShared hRole hBody hTail hAt hr he hStart hSite.2 hSafe
  rw [Nat.sub_zero] at hRank
  change ((X.tr g).take j).countP Execution.isShfl + loaderShuffleTail 1348 event.pc =
    ((X.tr g).take start).countP Execution.isShfl + 64*iteration + 64 at hRank
  have hBefore : ((X.tr g).take start).countP Execution.isShfl + 64*iteration <
      ((X.tr g).take j).countP Execution.isShfl := by omega
  obtain ⟨pos,hPos,u,stop,hBound,hU,hRun,hPrefix⟩ :=
    warmObservedIterations (hops := iteration) 0 hTrip hInit hShared hRole hBody hTail hAt hr
      he hStart (.inl (by simpa using hIter)) hSafe (.inr hBefore)
  simp only [Nat.zero_add] at hU
  have hHeld := hU.2.2.2.2
  refine ⟨batch,hb,hLo,hHi,iteration,hIter,pos,hPos,u,stop,hU.mono ?_,hRun,?_,?_⟩
  · exact ⟨hHeld.1,holds_mem hHeld.2.2 (by simp [F,warmBiasRoots,co]),
      hHeld.2.2.1,holds_mem hHeld.2.2 (by simp [F,warmBiasRoots,co]),
      holds_mem hHeld.2.2 (by simp [F,warmBiasRoots,co]),trivial⟩
  · have hRankAt := hRank
    rw [← Nat.add_sub_of_le hPos,List.take_add,List.countP_append] at hRankAt
    change ((X.tr g).take pos).countP Execution.isShfl + _ + _ = _ at hRankAt
    rw [hPrefix] at hRankAt
    omega

  · have hCount : loaderShuffleTail 1348 event.pc = 32 := by
      change loaderShuffleTail 1348 (warmBiasIssueSite stage half) = 32
      fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
    rw [hStartRank,hCount] at hRank
    omega

set_option maxRecDepth 10000 in
/-- The same warm iteration as the actual Bias issue retains its counter,
packed Q row, query head and the branch's residual bit. -/
theorem warmBiasEntryOfIssue (hCTA : g/l.block < tilePrefix p p.batch*p.heads)
    (he : X.get (g,j) = some ⟨warmBiasIssueSite stage half,.tensorIssue address spec⟩) :
    ∃ batch < p.batch,
      tilePrefix p batch*p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1)*p.heads ∧
      let co := assignedCoordinates p batch (g/l.block)
      let trips := Mma.trips p batch co.1
      ∃ iteration < min (trips-1) 9, ∃ pos ≤ j, ∃ s ending,
        At s 917 ([(7174,b32 iteration),(1090,b32 0),
          (1117,b32 (warmBiasResidualBit p batch co.1)),
          (1087,b32 (p.qOffset batch + 256*co.1)),(7169,b32 co.2)]) ∧
        Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending ∧
        (((X.tr g).drop pos).take (j-pos)).countP Execution.isShfl < 64 := by
  obtain ⟨batch,hb,hLo,hHi,iteration,hIter,pos,hPos,s,ending,hs,hRun,hSame,_⟩ :=
    warmBiasEntryOfIssueWithRank hp hX stage half hw writes hCTA he
  exact ⟨batch,hb,hLo,hHi,iteration,hIter,pos,hPos,s,ending,hs,hRun,hSame⟩

end PTX.Kernels.TmlFa4Fwd.Loader
