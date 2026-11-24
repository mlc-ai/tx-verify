-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TailPvProbabilityAcquire
import Kernels.TmlFa4Fwd.Proof.Thread.MmaProbabilityParity
import Kernels.TmlFa4Fwd.Proof.Thread.MbarOperands
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Lemmas.Flow.WaitAcquire
import Lemmas.Protocol.MbarOneShot

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy PTX.MBarrier
open PTX.Kernels.TmlFa4Fwd (probabilityWaitSite probabilityWaitSites)
open PTX.Kernels.TmlFa4Fwd.Mma

private theorem probabilityWaitAcquires {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage packet : Fin 2) {g j cta pc q : Nat} {acq : Bool} {scope : MbarScope}
    (he : X.get (g,j) = some ⟨pc,
      .wait (probabilityObject l cta stage packet) q true acq scope⟩) : acq = true := by
  have hSite := (probabilityWaitSite hp hX stage packet he).2
  have audit : ∀ stage packet : Fin 2, ∀ pc ∈ probabilityWaitSites stage packet,
      ∃ pred base phase, kernel.code[pc]? =
        some ⟨none,.mbarWait pred base 0 (.reg phase) true .cta⟩ := by
    intro stage packet pc hm
    fin_cases stage <;> fin_cases packet <;>
      simp [probabilityWaitSites] at hm <;>
      rcases hm with rfl | rfl
    · exact ⟨_,_,_,Flow.code_2297⟩
    · exact ⟨_,_,_,Flow.code_2548⟩
    · exact ⟨_,_,_,Flow.code_2335⟩
    · exact ⟨_,_,_,Flow.code_2586⟩
    · exact ⟨_,_,_,Flow.code_2419⟩
    · exact ⟨_,_,_,Flow.code_2595⟩
    · exact ⟨_,_,_,Flow.code_2450⟩
    · exact ⟨_,_,_,Flow.code_2626⟩
  obtain ⟨pred,base,phase,hCode⟩ := audit stage packet pc hSite
  rcases get_source hX he with ⟨_,hBad⟩ | ⟨s,ins,next,_,hGet,hFire⟩
  · cases hBad
  change kernel.code[pc]? = some ins at hGet
  rw [hCode] at hGet
  obtain rfl := Option.some.inj hGet.symm
  obtain ⟨_,_,_,_,_,hFlags,_⟩ := fires_wait_flags hFire
    (show (⟨pc,.wait (probabilityObject l cta stage packet) q true acq scope⟩ : Event).kind =
      .wait (probabilityObject l cta stage packet) q true acq scope from rfl)
  exact (Op.mbarWait.inj hFlags).2.2.2.2.1.symm

/-- If a PV issue follows a returning probability acquire, it also follows that
lane's first successful acquire of the same object, whose parity is zero. -/
theorem firstProbabilityAcquireBeforePv {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {stage packet : Fin 2} {later : Nat}
    (hAcquire : TailPvProbabilityAcquire l X i stage packet later) :
    ∃ w e scope, X.get (i.1,w) = some e ∧
      e.kind = .wait (probabilityObject l (i.1/l.block) stage packet) 0 true true scope ∧
      Resumes kernel X (i.1,w) i := by
  obtain ⟨g,j⟩ := i
  let obj := probabilityObject l (g/l.block) stage packet
  obtain ⟨⟨source,kind⟩,q,he,hKind⟩ := hAcquire.event
  dsimp only at hKind
  subst kind
  have hLater := hAcquire.resume.1
  have hBudget := MbarRing.Poll.okPoll_get he
  have hMono := MbarRing.Poll.okPolls_mono obj (X.tr g) (show later + 1 ≤ j from hLater.2.1)
  have hPos : 1 ≤ okPolls obj ((X.tr g).take j) := by
    change okPolls obj ((X.tr g).take (later+1)) =
      okPolls obj ((X.tr g).take later)+1 at hBudget
    omega
  obtain ⟨w,pc,parity,acq,scope,hw,hWait,hZero⟩ :=
    MbarRing.Poll.exists_nth (n := 0) hPos
  have hParity := (probabilityAcquireParity hp hX stage packet hWait).2.2
  rw [hZero] at hParity
  subst parity
  have hFlag := probabilityWaitAcquires hp hX stage packet hWait
  subst acq
  obtain ⟨exit,hSpin⟩ := actualCanonicalPoll hX hWait
  have hTrace : TraceBefore X (g,w) (g,j) := ⟨rfl,hw,hLater.2.2⟩
  refine ⟨w,_,scope,hWait,rfl,hTrace,?_⟩
  simp only [hWait,Option.map_some,Kind.resume]
  exact ⟨pc,exit,obj,0,true,scope,hWait,hSpin,hTrace⟩

/-- The initial returning acquire of a PV issue has a clean, successful history record. -/
theorem firstProbabilityAcquireRecord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {stage packet : Fin 2} {later : Nat}
    (hAcquire : TailPvProbabilityAcquire l X i stage packet later) :
    let loc := probabilityObject l (i.1/l.block) stage packet
    ∃ (w k : Nat) (r : Record Ref), (X.objects loc)[k]? = some r ∧ r.id = .thread (i.1,w) ∧
      r.action = .pollParity 0 true ∧ r.reply.waited = some true ∧
      (∃ e scope, X.get (i.1,w) = some e ∧ e.kind = .wait loc 0 true true scope) ∧
      Resumes kernel X (i.1,w) i := by
  let loc := probabilityObject l (i.1/l.block) stage packet
  obtain ⟨w,⟨pc,kind⟩,scope,he,hKind,hResume⟩ := firstProbabilityAcquireBeforePv hp hX hAcquire
  dsimp only at hKind
  subst kind
  have hAction : objectAction X X.async loc (.thread (i.1,w)) = some (.pollParity 0 true) := by
    simp only [objectAction,he,loc,↓reduceIte]
  obtain ⟨k,r,hr,hId,ha⟩ := MbarOneShot.Hist.record_of_action hX hAction
  have hMem := List.mem_of_getElem? hr
  have hClean := actualInitOrPollClean hp hX hMem (.inr ⟨0,true,ha⟩)
  have hWaited := ((hX.tma.2.2.1 loc).2.1 _ hMem).2 0 true ha hClean
  exact ⟨w,k,r,hr,hId,ha,hWaited,⟨_,scope,he,rfl⟩,hResume⟩

/-- A history observation inherits the acquire scope of its actual returning event. -/
theorem probabilityAcquireObserves {X : Execution} {wait : EvId} {source : Ref} {loc : Loc}
    {e : Event} {scope : MbarScope} (he : X.get wait = some e)
    (hKind : e.kind = .wait loc 0 true true scope)
    (hObserved : MbarObserved X source (.thread wait)) :
    WaitObserves X source wait loc true scope := by
  obtain ⟨_,w,target,acq,s,hId,hW,_⟩ := hObserved
  obtain rfl := Ref.thread.inj hId
  obtain ⟨⟨tag,q,hw⟩,hUpdate⟩ := hW
  have hEq := congrArg Event.kind (Option.some.inj (hw.symm.trans he))
  rw [hKind] at hEq
  obtain ⟨rfl,_,_,rfl,rfl⟩ := Kind.wait.inj hEq
  exact ⟨⟨tag,q,hw⟩,hUpdate⟩

/-- An actual probability publication has a unit counter update in its object's history. -/
theorem probabilityCreditRecord {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {cta : Nat} {stage packet : Fin 2}
    (hCredit : ProbabilityCredit l X i cta stage packet) :
    let loc := probabilityObject l cta stage packet
    ∃ (k : Nat) (r : Record Ref), (X.objects loc)[k]? = some r ∧
      r.id = .thread i ∧ CounterUpdate r.action := by
  let loc := probabilityObject l cta stage packet
  obtain ⟨_,he⟩ := hCredit
  have hAct : objectAction X X.async loc (.thread i) = some (.arrive 1 0) := by
    simp only [objectAction,he,loc,↓reduceIte]
  obtain ⟨k,r,hr,hId,ha⟩ := MbarOneShot.Hist.record_of_action hX hAct
  exact ⟨k,r,hr,hId,by rw [ha]; trivial⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
