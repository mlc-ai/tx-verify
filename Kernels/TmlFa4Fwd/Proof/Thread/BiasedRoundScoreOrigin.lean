-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Flow.Code.Part079
public import Kernels.TmlFa4Fwd.Proof.SoftmaxTmem
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityIssuers
import Lemmas.Flow.Async
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.EventFrame Thread.Scores
open Mma

private def beforeBiasedLoad (pc : Nat) (i : Instr) : Bool :=
  !(Assumptions.swExp2Sites.contains pc) && (i.op.isLocal || pc == 5109) &&
    match i.op with
    | .bra dst _ => decide (5032 ≤ dst ∧ dst ≤ 5112)
    | .brx .. => false
    | _ => true

set_option maxRecDepth 100000 in
private theorem biasedHeadAudit :
    (((kernel.code.drop 5032).take (5112-5032)).zipIdx 5032).all
      (fun (i,pc) => beforeBiasedLoad pc i) = true := by kernel_rfl

private theorem biasedHeadAuditAt {pc : Nat} {i : Instr} (hLo : 5032 ≤ pc)
    (hHi : pc < 5112) (hc : kernel.code[pc]? = some i) :
    beforeBiasedLoad pc i = true := by
  apply List.all_eq_true.mp biasedHeadAudit (i,pc)
  apply List.mem_of_getElem? (i := pc-5032)
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hLo,hc]
  rfl

variable {l : Launch}

private theorem biasedHeadTau {g : Nat} {s u : TState} (hLo : 5032 ≤ s.pc) (hHi : s.pc ≤ 5112)
    (ht : Tau kernel Assumptions.all l g s u) :
    5032 ≤ u.pc ∧ u.pc ≤ 5112 := by
  obtain ⟨i,hc,_,hLocal⟩ := tauScoreSource ht
  have hBefore : s.pc < 5112 := by
    by_contra! hAfter
    have hPc : s.pc = 5112 := by omega
    rw [hPc,Flow.code_5112] at hc
    obtain rfl := Option.some.inj hc
    rcases hLocal with ⟨_,hSkip⟩ | ⟨_,hLocal,_⟩
    · cases hSkip
    · cases hLocal
  have hAudit := biasedHeadAuditAt hLo hBefore hc
  rcases hLocal with ⟨rfl,_⟩ | ⟨_,_,hExec⟩
  · change 5032 ≤ s.pc+1 ∧ s.pc+1 ≤ 5112
    omega
  rcases scoreExecLocal hExec with hFrame | ⟨m,hSite,_,_⟩
  · have hPc := hFrame.pc
    cases hOp : i.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
    case bra dst uniform =>
      rw [hPc]
      simp only [beforeBiasedLoad,hOp,Bool.and_eq_true,decide_eq_true_eq] at hAudit
      exact hAudit.2
    case brx => simp [beforeBiasedLoad,hOp] at hAudit
    all_goals omega
  · simp only [beforeBiasedLoad,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,
      decide_eq_false_iff_not] at hAudit
    exact (hAudit.1.1 hSite).elim

private theorem biasedHeadWait {g : Nat} {s u : TState} {e : Event} (hLo : 5032 ≤ s.pc)
    (hHi : s.pc < 5112) (he : EStep kernel Assumptions.all l g s e (some u)) :
    u.pc = 5110 ∧ e.pc = 5109 ∧ ∀ loc, arrivesOn loc e = false := by
  obtain ⟨i,hc,hNonlocal,hFire⟩ := estep_event_source he
  have hAudit := biasedHeadAuditAt hLo hHi hc
  simp only [beforeBiasedLoad,Bool.and_eq_true,hNonlocal,Bool.false_or,beq_iff_eq] at hAudit
  have hp := hAudit.1.2
  rw [hp,Flow.code_5109] at hc
  obtain rfl := Option.some.inj hc
  obtain ⟨m,phase,ok,scope,rfl,rfl⟩ := fires_wait hFire
  exact ⟨congrArg (·+1) hp,hp,fun _ => rfl⟩

private theorem biasedHeadBeforeLoad {g : Nat} {s : TState} {events : List Event}
    {visits : List Visit} (hRun : Walk kernel Assumptions.all l g s events visits)
    (hLo : 5032 ≤ s.pc) (hHi : s.pc ≤ 5112) (hComplete : (⟨9205,.exit⟩ : Event) ∈ events) :
    ∃ k address words t out, events[k]? = some ⟨5112,.tc (.ld address words .s32x32b)⟩ ∧
      TraceReach kernel Assumptions.all l g s (events.take k) t ∧
      EStep kernel Assumptions.all l g t ⟨5112,.tc (.ld address words .s32x32b)⟩ (some out) ∧
      (∀ loc, (events.take k).countP (arrivesOn loc) = 0) ∧
      ∀ e ∈ events.take k, e.pc = 5109 := by
  induction hRun with
  | stop => cases hComplete
  | tau hTau _ ih =>
    obtain ⟨hLo,hHi⟩ := biasedHeadTau hLo hHi hTau
    obtain ⟨k,address,words,t,out,hGet,hPath,hE,hCount,hRange⟩ := ih hLo hHi hComplete
    exact ⟨k,address,words,t,out,hGet,.tau hTau hPath,hE,hCount,hRange⟩
  | @ev s u e es vs he hWalk ih =>
    by_cases hp : s.pc = 5112
    · have hStep := he
      obtain ⟨ins,hc,_,hFire⟩ := estep_event_source he
      rw [hp,Flow.code_5112] at hc
      obtain rfl := Option.some.inj hc
      obtain ⟨address,values,_,rfl,_⟩ :=
        fires_tcLd (by intro _ h; cases h) hFire (by rw [hp]; decide)
      exact ⟨0,address,values,s,u,by simp only [hp,List.getElem?_cons_zero],.refl _,
        hp ▸ hStep,(fun _ => rfl),fun _ h => by simp at h⟩
    · obtain ⟨hNext,hSite,hNo⟩ := biasedHeadWait hLo (by omega) he
      have hRest : (⟨9205,.exit⟩ : Event) ∈ es := by
        apply (List.mem_cons.mp hComplete).resolve_left
        obtain ⟨_,_,hFire⟩ := he
        exact fun h => hFire.not_exit h.symm
      obtain ⟨k,address,words,t,out,hGet,hPath,hE,hCount,hRange⟩ :=
        ih (by omega) (by omega) hRest
      refine ⟨k+1,address,words,t,out,hGet,.event he hPath,hE,
        (fun loc => by simp [List.take_succ_cons,hNo loc,hCount loc]),?_⟩
      intro ev hv
      exact (List.mem_cons.mp hv).elim (fun h => h ▸ hSite) (fun h => hRange ev h)
  | @last s e he =>
    obtain rfl := List.mem_singleton.mp hComplete
    have hPc := estep_source_pc he
    change 9205 = s.pc at hPc
    omega

/-- A completed biased iteration reaches its first score load and has no early
probability credit between its head and that load. -/
theorem biasedScoreLoadPathOfHead {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g start last pc : Nat} {s : TState}
    (hs : At s 5032 []) (hr : Run kernel Assumptions.all l g s ((X.tr g).drop start) none)
    (hExit : X.get (g,last) = some ⟨pc,.exit⟩) (hLast : start ≤ last) :
    ∃ j address words t out, start ≤ j ∧
      X.get (g,j) = some ⟨scorePc .biased 0,.tc (.ld address words .s32x32b)⟩ ∧
      TraceReach kernel Assumptions.all l g s (((X.tr g).drop start).take (j-start)) t ∧
      EStep kernel Assumptions.all l g t ⟨scorePc .biased 0,.tc (.ld address words .s32x32b)⟩
        (some out) ∧
      (∀ loc, arrivals loc ((X.tr g).take j) = arrivals loc ((X.tr g).take start)) ∧
      ∀ e ∈ ((X.tr g).drop start).take (j-start), e.pc = 5109 := by
  obtain rfl := actualExitPc hX hExit
  obtain ⟨_,walk⟩ := walkFromRun hr
  have hGet : ((X.tr g).drop start)[last-start]? = some ⟨9205,.exit⟩ := by
    rwa [List.getElem?_drop,Nat.add_sub_of_le hLast]
  obtain ⟨k,address,words,t,out,hAt,hPath,hE,hNone,hRange⟩ :=
    biasedHeadBeforeLoad walk hs.1.ge (by rw [hs.1]; decide) (List.mem_of_getElem? hGet)
  rw [List.getElem?_drop] at hAt
  refine ⟨start+k,address,words,t,out,by omega,hAt,?_,hE,(fun loc => ?_),?_⟩
  · rwa [Nat.add_sub_cancel_left]
  · have ht : (X.tr g).take (start+k) =
        (X.tr g).take start ++ ((X.tr g).drop start).take k := List.take_add
    rw [arrivals,ht,List.countP_append,hNone loc,Nat.add_zero]
    rfl
  · rwa [Nat.add_sub_cancel_left]

end PTX.Kernels.TmlFa4Fwd.Softmax
