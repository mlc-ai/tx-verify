-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaPollOrdinalProgress
import all Kernels.TmlFa4Fwd.Proof.MmaPoll
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue
open Correction (OpeningTripCursor)

private theorem replaySuccessfulPoll {l : Launch} {g : Nat} (site : Fin 14)
    {addr phase : Nat} (hAddr : addr < 2^32) (hAlign : addr%8 = 0) (hPhase : phase < 2)
    {F : List (Nat × Value)} (hFresh : ∀ pair ∈ F, pair.1 ≠ (waitSite site).result)
    (hBase : ((waitSite site).base,b32 addr) ∈ F)
    (hPar : ((waitSite site).phase,b32 phase) ∈ F) (n : Nat)
    {before ready : TState} {past tail : List Event} {ending : Option TState}
    (hAt : At ready (waitSite site).pc F)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before ready)
    (hPrefix : Run kernel Assumptions.all l g {} past (some before))
    (hTail : let ev (ok : Bool) : Event :=
      ⟨(waitSite site).pc,.wait ⟨.shared,g/l.block,addr⟩ phase ok true .cta⟩
      Run kernel Assumptions.all l g before
        (List.replicate n (ev false) ++ ev true :: tail) ending) :
    let ev (ok : Bool) : Event :=
      ⟨(waitSite site).pc,.wait ⟨.shared,g/l.block,addr⟩ phase ok true .cta⟩
    ∃ after state,
      Run kernel Assumptions.all l g {} (past ++ List.replicate n (ev false) ++ [ev true])
        (some after) ∧ Run kernel Assumptions.all l g after tail ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) after state ∧
      At state ((waitSite site).pc+3) F := by
  let loc : Loc := ⟨.shared,g/l.block,addr⟩
  let ev := fun ok => Event.mk (waitSite site).pc (.wait loc phase ok true .cta)
  change Run kernel Assumptions.all l g before
    (List.replicate n (ev false) ++ ev true :: tail) ending at hTail
  induction n generalizing before ready past with
  | zero =>
    have hOut := waitTemplate (l := l) (g := g) site hAddr hAlign hPhase hAt.1 hAt.2.2.2.1
      (holds_mem hAt.2.2.2.2 hBase) (holds_mem hAt.2.2.2.2 hPar)
    let resume := fun ok => next (setReg ready (waitSite site).result (.pred ok))
    have hNext : Next kernel Assumptions.all l g before ready (.wait loc phase resume true .cta) :=
      ⟨hLocal,hOut⟩
    obtain ⟨_,⟨ok,hEv,hDest⟩,hRest⟩ := hNext.continuing_event
      (by rintro ⟨_,_,h⟩; cases h) (by simpa using hTail)
    have hOk : ok = true := by
      have hKind := congrArg Event.kind hEv
      cases ok <;> simp_all [ev]
    subst ok
    obtain rfl := Option.some.inj hDest
    have hStep : EStep kernel Assumptions.all l g ready (ev true) (some (resume true)) :=
      ⟨_,hOut,true,hEv,rfl⟩
    obtain ⟨s,hs,hPost⟩ := afterWait site true (hAt.set hFresh)
    exact ⟨_,s,by simpa using hPrefix.snoc hLocal hStep,hRest,hs,hPost⟩
  | succ n ih =>
    have hOut := waitTemplate (l := l) (g := g) site hAddr hAlign hPhase hAt.1 hAt.2.2.2.1
      (holds_mem hAt.2.2.2.2 hBase) (holds_mem hAt.2.2.2.2 hPar)
    let resume := fun ok => next (setReg ready (waitSite site).result (.pred ok))
    have hNext : Next kernel Assumptions.all l g before ready (.wait loc phase resume true .cta) :=
      ⟨hLocal,hOut⟩
    simp only [List.replicate_succ,List.cons_append] at hTail
    obtain ⟨_,⟨ok,hEv,hDest⟩,hRest⟩ := hNext.continuing_event
      (by rintro ⟨_,_,h⟩; cases h) hTail
    have hOk : ok = false := by
      have hKind := congrArg Event.kind hEv
      cases ok <;> simp_all [ev]
    subst ok
    obtain rfl := Option.some.inj hDest
    have hStep : EStep kernel Assumptions.all l g ready (ev false) (some (resume false)) :=
      ⟨_,hOut,false,hEv,rfl⟩
    obtain ⟨retry,hRetry,hAgain⟩ := afterWait site false (hAt.set hFresh)
    have hResult := ih hAgain hRetry (hPrefix.snoc hLocal hStep) hRest
    simpa only [List.replicate_succ,List.append_assoc,List.singleton_append] using hResult

/-- Record the returned cursor of a concrete successful wait. The proof
replays the actual failures and preserves the remaining actual trace. -/
theorem replayPollFromTrace {l : Launch} {X : Execution} {g : Nat} (site : Fin 14)
    {addr phase : Nat} (hAddr : addr < 2^32) (hAlign : addr%8 = 0) (hPhase : phase < 2)
    {F : List (Nat × Value)} (hFresh : ∀ pair ∈ F, pair.1 ≠ (waitSite site).result)
    (hBase : ((waitSite site).base,b32 addr) ∈ F)
    (hPar : ((waitSite site).phase,b32 phase) ∈ F)
    (c : OpeningTripCursor l X g (waitSite site).pc F)
    {n : Nat} {tail : List Event}
    (hTrace : let ev (ok : Bool) : Event :=
      ⟨(waitSite site).pc,.wait ⟨.shared,g/l.block,addr⟩ phase ok true .cta⟩
      (X.tr g).drop c.pos = List.replicate n (ev false) ++ ev true :: tail) :
    ∃ after : OpeningTripCursor l X g ((waitSite site).pc+3) F,
      after.pos = c.pos+n+1 ∧ after.ending = c.ending := by
  let loc : Loc := ⟨.shared,g/l.block,addr⟩
  let ev := fun ok => Event.mk (waitSite site).pc (.wait loc phase ok true .cta)
  have hTrace : (X.tr g).drop c.pos = List.replicate n (ev false) ++ ev true :: tail := hTrace
  have hRem := c.remaining
  rw [hTrace] at hRem
  obtain ⟨before,state,hPast,hTail,hLocal,hAt⟩ :=
    replaySuccessfulPoll site hAddr hAlign hPhase hFresh hBase hPar n c.checkpoint
      c.localSteps c.recorded hRem
  have he : ((X.tr g).drop c.pos)[n]? = some (ev true) := by
    rw [hTrace,List.getElem?_append_right (by simp)]
    simp
  rw [List.getElem?_drop] at he
  have hGet : X.get (g,c.pos+n) = some (ev true) := he
  let es := List.replicate n (ev false) ++ [ev true]
  have hLen : es.length = n+1 := by simp [es]
  have hCut : (X.tr g).drop c.pos = es ++ tail := by
    simpa only [es,List.append_assoc,List.singleton_append] using hTrace
  have hPrior : (X.tr g).take (c.pos+n+1) = (X.tr g).take c.pos ++ es := by
    rw [Nat.add_assoc,List.take_add,hCut,← hLen,List.take_append_length]
  have hRest : (X.tr g).drop (c.pos+n+1) = tail := by
    rw [Nat.add_assoc,← List.drop_drop,hCut,← hLen,List.drop_left]
  refine ⟨⟨c.pos+n+1,before,state,c.ending,by omega,len_of_get hGet,?_,hAt,?_,?_,hLocal⟩,rfl,rfl⟩
  · exact releasedIfLast hGet (by intro h; cases h)
  · rw [hPrior]
    simpa only [es,List.append_assoc] using hPast
  · rwa [hRest]

variable {l : Launch} {m : Mem0} {X : Execution} (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (site : Fin 14) {addr phase gen : Nat} (hAddr : addr < 2^32)
    (hAlign : addr%8 = 0) (hPhase : phase < 2) {F : List (Nat × Value)}
    (hFresh : ∀ pair ∈ F, pair.1 ≠ (waitSite site).result)
    (hBase : ((waitSite site).base,b32 addr) ∈ F) (hPar : ((waitSite site).phase,b32 phase) ∈ F)
    (cur : OpeningTripCursor l X g (waitSite site).pc F)
    (hOrdinal : okPolls ⟨.shared,g/l.block,addr⟩ ((X.tr g).take cur.pos) = gen)
    (hReady : okPolls ⟨.shared,g/l.block,addr⟩ (X.tr g) = gen →
      let log := X.objects ⟨.shared,g/l.block,addr⟩
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase%2 ≠ phase%2)
include hMax hg site hAddr hAlign hPhase hFresh hBase hPar cur hOrdinal hReady

/-- The observed successful poll advances the real cursor. Only the selected
object's count changes, even when some later generations already appear in the
execution. -/
theorem pollOrdinalReturnedWithTraceOfMaximal :
    let loc : Loc := ⟨.shared,g/l.block,addr⟩
    ∃ after : OpeningTripCursor l X g ((waitSite site).pc+3) F,
      cur.pos < after.pos ∧ after.ending = cur.ending ∧
      X.get (g,after.pos-1) = some ⟨(waitSite site).pc,.wait loc phase true true .cta⟩ ∧
      (∀ other, okPolls other ((X.tr g).take after.pos) =
        okPolls other ((X.tr g).take cur.pos) + if other = loc then 1 else 0) ∧
      ∃ retries suffix, after.pos = cur.pos+retries+1 ∧ (X.tr g).drop cur.pos =
        List.replicate retries ⟨(waitSite site).pc,.wait loc phase false true .cta⟩ ++
        ⟨(waitSite site).pc,.wait loc phase true true .cta⟩ :: suffix := by
  let loc : Loc := ⟨.shared,g/l.block,addr⟩
  let ev := fun ok => Event.mk (waitSite site).pc (.wait loc phase ok true .cta)
  obtain ⟨j,hj,he,_⟩ := pollOrdinalOccursOfMaximal hMax hg site hAddr hAlign hPhase hFresh
    hBase hPar cur hOrdinal hReady
  have hGet : ((X.tr g).drop cur.pos)[j-cur.pos]? = some (ev true) := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hj]
    exact he
  have hMem : ev true ∈ (X.tr g).drop cur.pos := List.mem_of_getElem? hGet
  have hNonempty : (X.tr g).drop cur.pos ≠ [] := by intro eq; simp [eq] at hMem
  obtain ⟨_,hWalk⟩ := walkFromRun
    (cur.remaining.after_local_nonempty cur.localSteps hNonempty)
  rcases waitWalk site hAddr hAlign hPhase hFresh hBase hPar cur.checkpoint hWalk with
    ⟨n,hFail⟩ | ⟨n,tail,hTrace,_⟩
  · change (X.tr g).drop cur.pos = List.replicate n (ev false) at hFail
    rw [hFail] at hMem
    simp [List.mem_replicate,ev] at hMem
  · change (X.tr g).drop cur.pos = List.replicate n (ev false) ++ ev true :: tail at hTrace
    obtain ⟨after,hPos,hEnding⟩ :=
      replayPollFromTrace site hAddr hAlign hPhase hFresh hBase hPar cur hTrace
    have hSuccess : ((X.tr g).drop cur.pos)[n]? = some (ev true) := by
      rw [hTrace,List.getElem?_append_right (by simp)]
      simp
    rw [List.getElem?_drop] at hSuccess
    have hIndex : after.pos-1 = cur.pos+n := by omega
    refine ⟨after,by omega,hEnding,by rw [hIndex]; exact hSuccess,?_,n,tail,hPos,hTrace⟩
    intro other
    let consumed := List.replicate n (ev false) ++ [ev true]
    have hLength : consumed.length = n+1 := by simp [consumed]
    have hWhole : (X.tr g).drop cur.pos = consumed ++ tail := by
      simpa only [consumed,List.append_assoc,List.singleton_append] using hTrace
    rw [hPos,Nat.add_assoc,List.take_add,hWhole,←hLength,List.take_append_length]
    simp [consumed,okPolls,List.countP_append,List.countP_replicate,okPoll,sourceWaitSuccess,ev,
      loc,eq_comm]

end PTX.Kernels.TmlFa4Fwd.Mma
