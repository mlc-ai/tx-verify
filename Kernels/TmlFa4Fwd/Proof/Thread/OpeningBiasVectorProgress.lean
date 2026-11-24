-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningBiasWordRead
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxOpeningScore
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasVector
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasLayout

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

private structure BiasReadBoundary (l : Launch) (X : Execution) (g pos : Nat)
    (ready : TState) (ending : Option TState) where
  before : TState
  positive : 0 < pos
  bounded : pos ≤ (X.tr g).length
  released : pos = (X.tr g).length → Step.Released l X g
  recorded : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some before)
  continuation : Run kernel Assumptions.all l g before ((X.tr g).drop pos) ending
  localSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before ready

private def biasVectorLoaded (repeated : Bool) (i : Fin 16) (t : TState)
    (words : Nat → Value) : TState :=
  setRegs { t with pc := t.pc+1, sub := 0, acc := [] }
    (biasReadRegs repeated i) ((List.range 4).map words)

private def biasVectorState (repeated : Bool) (i : Fin 16) (t : TState)
    (words : Nat → Value) (k : Nat) : TState :=
  if k < 4 then biasReadSubstate t words k else biasVectorLoaded repeated i t words

/-- A maximal lane reads and unpacks all four words of one Bias vector, retaining
the observed bytes and the live register facts for its next vector. -/
theorem biasVectorCursorOfMaximal {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X) (hGuard : SyncGuarded l kernel X)
    {g base : Nat} (hg : g < l.threads) (repeated : Bool) (i : Fin 16)
    {F : List (Nat × Value)} {ending : Option TState}
    (c : OpeningLaneCursor l X g (biasReadPc repeated i) F ending)
    (hBase : ((biasReadSite repeated i).base,b32 base) ∈ F)
    (hAddr : base + (biasReadSite repeated i).offset < 2^32)
    (hAlign : (base + (biasReadSite repeated i).offset) % 16 = 0)
    (words : Nat → Value) (hShape : ∀ k < 4, BiasWordShape (words k))
    (hValue : ∀ k < 4, ∀ bytes, X.get (g,c.pos+k) = some
      ⟨biasReadPc repeated i,.rd (biasReadAcc l g base repeated i k) bytes⟩ →
      rebuild 3 bytes = .ok (words k))
    (hKeep : ∀ pair ∈ F, biasVectorKeeps repeated i pair.1) :
    ∃ after : OpeningLaneCursor l X g (biasReadPc repeated i+5) F ending,
      after.pos = c.pos+4 ∧ BiasWordReads l X repeated i g c.pos base words ∧
        BiasUnpacked repeated i after.ready words ∧
        (∀ r, biasVectorKeeps repeated i r → after.ready.regs r = c.ready.regs r) := by
  let body := biasVectorState repeated i c.ready words
  let loaded := biasVectorLoaded repeated i c.ready words
  have hState0 : body 0 = c.ready := by
    simp only [body,biasVectorState,show 0 < 4 by decide,ite_true]
    have hAt := c.checkpoint
    cases hT : c.ready
    simp [biasReadSubstate,hT] at hAt ⊢
    exact ⟨hAt.2.1.symm,hAt.2.2.1⟩
  let R (k : Nat) := BiasReadBoundary l X g (c.pos+k) (body k) ending
  let observed (k : Nat) := ∃ bytes, X.get (g,c.pos+k) = some
      ⟨biasReadPc repeated i,.rd (biasReadAcc l g base repeated i k) bytes⟩ ∧
      rebuild 3 bytes = .ok (words k)
  have allReads (k : Nat) (hk : k ≤ 4) : Nonempty (R k) ∧ ∀ j < k, observed j := by
    induction k with
    | zero =>
      have hc : BiasReadBoundary l X g c.pos c.ready ending :=
        ⟨c.before,c.positive,c.bounded,c.released,c.recorded,c.continuation,c.localSteps⟩
      exact ⟨⟨by simpa only [R,Nat.add_zero,hState0] using hc⟩,
        fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ k ih =>
      have hk4 : k < 4 := by omega
      obtain ⟨⟨current⟩,hReads⟩ := ih (by omega)
      have hBody : body k = biasReadSubstate c.ready words k := ite_eq_left hk4
      have hPc : (body k).pc = biasReadPc repeated i := by
        rw [hBody]
        exact c.checkpoint.1
      have hFault : (body k).fault = none := by
        rw [hBody]
        exact c.checkpoint.2.2.2.1
      have hAddress : (body k).regs (biasReadSite repeated i).base = some (b32 base) := by
        rw [hBody]
        exact holds_mem c.checkpoint.2.2.2.2 hBase
      obtain ⟨bytes,hGet,hPast,hTail,hBound,hRelease⟩ :=
        biasWordReadOfMaximal hMax hGuard hg repeated i hPc hFault hAddress hAddr hAlign
          current.recorded current.continuation current.localSteps current.positive
          current.bounded current.released
      have hSub : (body k).sub = k := by rw [hBody]; rfl
      rw [hSub] at hGet
      have hWord := hValue k hk4 bytes hGet
      have hLen : (biasReadRegs repeated i).length = 4 := rfl
      have hStep : afterLoad (body k) (biasReadRegs repeated i) bytes = body (k+1) := by
        by_cases hInner : k+1 < 4
        · have hMore : (body k).sub+1 < (biasReadRegs repeated i).length := by rwa [hSub,hLen]
          rw [afterLoad_mid hWord hMore,hBody]
          simp only [body,biasVectorState,ite_eq_left hInner,biasReadSubstate,List.range_succ,
            List.map_append,List.map_cons,List.map_nil]
        · have hLast : ¬ (body k).sub+1 < (biasReadRegs repeated i).length := by rwa [hSub,hLen]
          have hThree : k = 3 := by omega
          rw [afterLoad_last hWord hLast,hBody,hThree]
          rfl
      rw [hStep] at hPast hTail
      refine ⟨⟨⟨body (k+1),by omega,?_,?_,?_,?_,.refl⟩⟩,?_⟩
      · simpa only [Nat.add_assoc] using hBound
      · simpa only [Nat.add_assoc] using hRelease
      · simpa only [Nat.add_assoc] using hPast
      · simpa only [Nat.add_assoc] using hTail
      · intro j hj
        rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with rfl | hBefore
        · exact ⟨bytes,hGet,hWord⟩
        · exact hReads j hBefore
  obtain ⟨⟨last⟩,hReads⟩ := allReads 4 (by decide)
  have hSkeleton := setRegs_skel
    {c.ready with pc := c.ready.pc+1, sub := 0, acc := []}
    (biasReadRegs repeated i) ((List.range 4).map words)
  have hLoaded : At loaded (biasReadPc repeated i+1) [] :=
    ⟨hSkeleton.1.trans (congrArg (·+1) c.checkpoint.1),hSkeleton.2.1,hSkeleton.2.2.1,
      hSkeleton.2.2.2.trans c.checkpoint.2.2.2.1,trivial⟩
  have hWords : ∀ k < 4, loaded.regs ((biasReadSite repeated i).firstReg+k) = some (words k) := by
    intro k hk
    have hNodup : (biasReadRegs repeated i).Nodup := by cases repeated <;> fin_cases i <;> decide
    apply setRegs_get _ _ _ k _ _ hNodup
    · interval_cases k <;> rfl
    · simp only [List.getElem?_map,List.getElem?_range hk,Option.map_some]
  obtain ⟨u,hRun,hAt,hUnpacked,hUnpackFrame⟩ :=
    biasUnpackRun (l := l) (g := g) repeated i (Nat.le_refl 4) words hShape hLoaded hWords
  have hFrame (r : Nat) (hKeepReg : biasVectorKeeps repeated i r) :
      u.regs r = c.ready.regs r := by
    obtain ⟨hRead,hUnpack⟩ := hKeepReg
    have hEnough : 7 ≤ biasUnpackTop repeated i := by
      cases repeated <;> simp [biasUnpackTop] <;> omega
    have hBounds : r < biasUnpackTop repeated i + 1 - 2*4 ∨
        biasUnpackTop repeated i < r := by
      unfold biasUnpackRegs at hUnpack
      dsimp only at hUnpack
      omega
    exact (hUnpackFrame _ hBounds).trans (setRegs_other _ _ _ _ hRead)
  have hFacts := Epilogue.holdsSchedulerFrame c.checkpoint.2.2.2.2
    (regs := F.map Prod.fst) (S := u.regs)
    (fun r hs => by
      obtain ⟨pair,hMem,rfl⟩ := List.mem_map.mp hs
      exact hFrame pair.1 (hKeep pair hMem))
    (fun _ hMem => List.mem_map_of_mem (f := Prod.fst) hMem)
  let after : OpeningLaneCursor l X g (biasReadPc repeated i+5) F ending :=
    ⟨c.pos+4,last.before,u,by omega,last.bounded,last.released,last.recorded,last.continuation,
      last.localSteps.trans (run_rtg hRun),hAt.mono hFacts⟩
  exact ⟨after,rfl,hReads,hUnpacked,hFrame⟩

private def OpeningLaneCursor.relabel {l : Launch} {X : Execution} {g pc pc' : Nat}
    {F : List (Nat × Value)} {ending : Option TState}
    (c : OpeningLaneCursor l X g pc F ending) (h : pc = pc') :
    OpeningLaneCursor l X g pc' F ending :=
  ⟨c.pos,c.before,c.ready,c.positive,c.bounded,c.released,c.recorded,c.continuation,
    c.localSteps,h ▸ c.checkpoint⟩

/-- The sixteen decoded Bias vectors in a maximal lane all read and unpack,
and their collective result is present at the actual post-load proxy-fence cursor. -/
theorem biasVectorCursorsOfMaximal {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X) (hGuard : SyncGuarded l kernel X)
    {g : Nat} (hg : g < l.threads) (repeated : Bool)
    {F : List (Nat × Value)} {ending : Option TState}
    (c : OpeningLaneCursor l X g (biasReadPc repeated 0) F ending)
    (base : Fin 16 → Nat) (words : Fin 16 → Nat → Value)
    (hBases : ∀ i, ((biasReadSite repeated i).base,b32 (base i)) ∈ F)
    (hAddr : ∀ i, base i + (biasReadSite repeated i).offset < 2^32)
    (hAlign : ∀ i, (base i + (biasReadSite repeated i).offset) % 16 = 0)
    (hShape : ∀ i k, k < 4 → BiasWordShape (words i k))
    (hValue : ∀ i k, k < 4 → ∀ bytes, X.get (g,c.pos+4*i.val+k) = some
      ⟨biasReadPc repeated i,.rd (biasReadAcc l g (base i) repeated i k) bytes⟩ →
      rebuild 3 bytes = .ok (words i k))
    (hKeep : ∀ pair ∈ F, ∀ i, biasVectorKeeps repeated i pair.1) :
    ∃ after : OpeningLaneCursor l X g (biasReadPc repeated 0+80) F ending,
      after.pos = c.pos+64 ∧
      (∀ i, BiasWordReads l X repeated i g (c.pos+4*i.val) (base i) (words i) ∧
        BiasUnpacked repeated i after.ready (words i)) ∧
      (∀ r, (∀ i, biasVectorKeeps repeated i r) → after.ready.regs r = c.ready.regs r) := by
  let pc := biasReadPc repeated 0
  have replay (n : Nat) (hn : n ≤ 16)
      (s : OpeningLaneCursor l X g (pc+5*(16-n)) F ending)
      (hPos : s.pos = c.pos+4*(16-n)) :
      ∃ after : OpeningLaneCursor l X g (pc+80) F ending,
        after.pos = c.pos+64 ∧
        (∀ i : Fin 16, 16-n ≤ i.val →
          BiasWordReads l X repeated i g (c.pos+4*i.val) (base i) (words i) ∧
          BiasUnpacked repeated i after.ready (words i)) ∧
        ∀ r, (∀ i : Fin 16, 16-n ≤ i.val → biasVectorKeeps repeated i r) →
          after.ready.regs r = s.ready.regs r := by
    induction n with
    | zero =>
      exact ⟨s,hPos,fun i h => (Nat.not_le_of_lt i.isLt h).elim,fun _ _ => rfl⟩
    | succ n ih =>
      let i : Fin 16 := ⟨16-(n+1),by omega⟩
      have hHere : biasReadPc repeated i = pc+5*(16-(n+1)) := rfl
      let start := s.relabel hHere.symm
      have hStart : start.pos = c.pos+4*i.val := hPos
      have hFacts : ∀ k < 4, ∀ bytes, X.get (g,start.pos+k) = some
          ⟨biasReadPc repeated i,.rd (biasReadAcc l g (base i) repeated i k) bytes⟩ →
          rebuild 3 bytes = .ok (words i k) := by
        rw [hStart]
        exact hValue i
      obtain ⟨next,hNext,hRead,hUnpacked,hFrame⟩ :=
        biasVectorCursorOfMaximal hMax hGuard hg repeated i start (hBases i) (hAddr i)
          (hAlign i) (words i) (hShape i) hFacts (fun p hp => hKeep p hp i)
      have hStep : biasReadPc repeated i+5 = pc+5*(16-n) := by rw [hHere]; omega
      have hIndex : next.pos = c.pos+4*(16-n) := by
        rw [hNext,hStart]
        change c.pos+4*(16-(n+1))+4 = c.pos+4*(16-n)
        omega
      let continuation := next.relabel hStep
      obtain ⟨after,hAfter,hOther,hOtherFrame⟩ := ih (by omega) continuation hIndex
      refine ⟨after,hAfter,?_,?_⟩
      · intro q hq
        by_cases hLater : 16-n ≤ q.val
        · exact hOther q hLater
        · have hSame : q = i := Fin.ext (by change q.val = 16-(n+1); omega)
          subst q
          refine ⟨hStart ▸ hRead,?_⟩
          intro k hk
          have hKeepResult (r : Nat) (h :
              r = (biasUnpackRegs repeated i k).1 ∨ r = (biasUnpackRegs repeated i k).2) :
              after.ready.regs r = next.ready.regs r := by
            exact hOtherFrame r (fun other ho =>
              biasVectorKeepPrevious repeated i other (by change 16-(n+1) < other.val; omega) hk h)
          refine ⟨(hKeepResult _ (.inl rfl)).trans (hUnpacked k hk).1,
            (hKeepResult _ (.inr rfl)).trans (hUnpacked k hk).2⟩
      · intro r hR
        exact (hOtherFrame r (fun q hq => hR q (by omega))).trans (hFrame r (hR i (by rfl)))
  have hZero : pc + 5*(16-16) = biasReadPc repeated 0 := rfl
  let entry := c.relabel hZero.symm
  obtain ⟨after,hAfter,hReads,hFrame⟩ := replay 16 (Nat.le_refl _) entry (by
    simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero] using (show entry.pos = c.pos by rfl))
  exact ⟨after,hAfter,fun i => hReads i (Nat.zero_le _),
    fun r hR => hFrame r (fun i _ => hR i)⟩

/-- After the real first Bias acquire, the preserved swizzled address registers
drive every opening Bias load in this lane. -/
theorem openingBiasVectorsOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : SyncGuarded l kernel X) {g batch tile wait : Nat} (hg : g < l.threads)
    (warp : Fin 8) {ending : Option TState}
    (c : OpeningLaneCursor l X g 3501 (openingScoreReturnedFacts p l g batch tile warp) ending)
    (hPos : c.pos = wait+1) (words : Fin 16 → Nat → Value)
    (hShape : ∀ i k, k < 4 → BiasWordShape (words i k))
    (hValue : ∀ i k, k < 4 → ∀ bs, X.get (g,wait+1+4*i.val+k) = some
      ⟨biasReadPc false i,.rd (biasReadAcc l g
        (biasVectorBase l g (stageOf warp) false i) false i k) bs⟩ →
      rebuild 3 bs = .ok (words i k)) :
    ∃ after : OpeningLaneCursor l X g 3581 (openingScoreReturnedFacts p l g batch tile warp) ending,
      after.pos = wait+65 ∧
      (∀ i, BiasWordReads l X false i g (wait+1+4*i.val)
          (biasVectorBase l g (stageOf warp) false i) (words i) ∧
        BiasUnpacked false i after.ready (words i)) ∧
      (∀ r, (∀ i, biasVectorKeeps false i r) → after.ready.regs r = c.ready.regs r) := by
  let F := openingScoreReturnedFacts p l g batch tile warp
  let base := biasVectorBase l g (stageOf warp) false
  have hBase (i : Fin 16) : ((biasReadSite false i).base,b32 (base i)) ∈ F := by
    have hCarry :
        ((biasReadSite false i).base,b32 (base i)) ∈ singleVisitGeometryCarry l g warp := by
      let address (q : Fin 16) := ((biasReadSite false q).base,b32 (base q))
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_map_of_mem (f := address) (show i ∈ List.finRange 16 by simp)))
    exact List.mem_append_right _ hCarry
  have hAddress (i : Fin 16) : base i + (biasReadSite false i).offset < 2^32 ∧
      (base i + (biasReadSite false i).offset) % 16 = 0 := by
    simpa only [base,biasVectorBase_add] using biasVectorAddressBounds hp g (stageOf warp) i
  have hKeep (pair : Nat × Value) (hMem : pair ∈ F) (i : Fin 16) :
      biasVectorKeeps false i pair.1 := by
    let safe (r : Nat) (q : Fin 16) := decide (r ∉ biasReadRegs false q ∧
      (r < (biasUnpackRegs false q 3).2 ∨ (biasUnpackRegs false q 0).1 < r))
    have audit : (F.map Prod.fst).all (fun r => (List.finRange 16).all (safe r)) = true := rfl
    have hs : safe pair.1 i = true := List.all_eq_true.mp
      (List.all_eq_true.mp audit pair.1 (List.mem_map_of_mem hMem)) i (by simp)
    change pair.1 ∉ biasReadRegs false i ∧
      (pair.1 < (biasUnpackRegs false i 3).2 ∨ (biasUnpackRegs false i 0).1 < pair.1)
    exact of_decide_eq_true hs
  obtain ⟨after,hAfter,hReads,hFrame⟩ :=
    biasVectorCursorsOfMaximal hMax hGuard hg false c base words hBase
    (fun i => (hAddress i).1) (fun i => (hAddress i).2) hShape
    (fun i k hk bs he => hValue i k hk bs (hPos ▸ he)) hKeep
  rw [hPos] at hAfter hReads
  exact ⟨after,by omega,hReads,hFrame⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
