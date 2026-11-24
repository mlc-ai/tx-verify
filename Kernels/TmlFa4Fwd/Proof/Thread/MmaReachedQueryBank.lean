-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank
public import Kernels.TmlFa4Fwd.Proof.MmaQRegisters
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank
import all Kernels.TmlFa4Fwd.Proof.MmaQkQuerySetupReplay
import Kernels.TmlFa4Fwd.Proof.MmaQkQueryRetarget
import Kernels.TmlFa4Fwd.Proof.MmaRoleFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Mma
open Epilogue

noncomputable section

private inductive BankReach (l : Launch) (g : Nat) : Nat → TState → TState → Prop
  | refl (s : TState) : BankReach l g 0 s s
  | step {s t u : TState} {event : Option Event} {n : Nat} :
    WStep kernel Assumptions.all l g s event t → BankReach l g n t u →
    BankReach l g (n+1) s u

private theorem BankReach.ofTrace {l : Launch} {g : Nat} {s t : TState} {es : List Event}
    (h : TraceReach kernel Assumptions.all l g s es t) :
    ∃ n, BankReach l g n s t := by
  induction h with
  | refl => exact ⟨0,.refl _⟩
  | tau hs _ ih =>
    obtain ⟨n,h⟩ := ih
    exact ⟨n+1,.step (.inl ⟨rfl,hs⟩) h⟩
  | event he _ ih =>
    obtain ⟨n,h⟩ := ih
    exact ⟨n+1,.step (.inr ⟨_,rfl,he⟩) h⟩

private theorem BankReach.staysPastExit {l : Launch} {g n : Nat} {s t : TState}
    (h : BankReach l g n s t) (hs : 2768 ≤ s.pc) : 2768 ≤ t.pc := by
  induction h with
  | refl => exact hs
  | step h _ ih =>
    exact ih (eventTailStepOfAudit bankExitFloor bankExitSegments hs h)

private theorem returningStepClean {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (h : WStep kernel Assumptions.all l g s ev u) : s.fault = none := by
  cases hf : s.fault with
  | none => rfl
  | some fault =>
    have hOut : out kernel Assumptions.all l g s = .ev (.ub fault) := by simp [out,hf]
    rcases h with ⟨rfl,hτ⟩ | ⟨e,rfl,tmpl,hEvt,hFire⟩
    · rw [Tau,hOut] at hτ
      cases hτ
    · obtain rfl := Out.ev.inj (hEvt.symm.trans hOut)
      cases hFire.2

private theorem setupThroughBankPath {l : Launch} {g n fuel : Nat} (block : Fin 4)
    {s z : TState} (hLo : qkSetupStart block ≤ s.pc)
    (hLen : s.pc+n ≤ qkSetupStart block+40)
    (hExit : ¬ (qkSetupStart block ≤ z.pc ∧ z.pc < qkSetupStart block+40))
    (hs : At s s.pc []) (hPath : BankReach l g fuel s z) :
    ∃ u rest, run kernel [] l g n s = some u ∧ At u (s.pc+n) [] ∧
      rest+n = fuel ∧ BankReach l g rest u z := by
  induction n generalizing s fuel with
  | zero => exact ⟨s,fuel,rfl,hs,rfl,hPath⟩
  | succ n ih =>
    have hScope : 1904 ≤ qkSetupStart block ∧ qkSetupStart block+40 ≤ 2768 := by
      fin_cases block <;> decide
    have hCode : 2768 ≤ kernel.code.length := by decide +kernel
    have hHi : s.pc < qkSetupStart block+40 := by omega
    obtain ⟨i,hCode,hGuard,hLocal,_⟩ := setupInstruction block hLo hHi (by omega)
    have hCore := out_eq_core (l := l) (g := g) (t := s) (by omega) (by omega)
    cases hPath with
    | refl => exact (hExit ⟨hLo,hHi⟩).elim
    | @step _ v _ event count hw hn =>
      have hTau : Tau kernel [] l g s v := by
        rcases hw with ⟨rfl,ht⟩ | ⟨e,rfl,tmpl,hEvt,hFire⟩
        · unfold Tau at ht ⊢
          rwa [← hCore]
        · rw [hCore] at hEvt
          have hOut : out kernel [] l g s = match execLocalA [] l g s i.op with
              | .ok u => .tau u
              | .error err => .ev (.ub err) := by
            simp only [out,hs.2.2.2.1,hCode,hGuard,guardHolds,pure,Except.pure,hLocal,↓reduceIte]
            rfl
          rw [hOut] at hEvt
          cases hExec : execLocalA [] l g s i.op <;> rw [hExec] at hEvt
          · obtain rfl := Out.ev.inj hEvt.symm
            cases hFire.2
          · cases hEvt
      have hStep : run kernel [] l g 1 s = some v := by
        simp only [run,tauStep_iff.mpr hTau,Option.bind_some]
      have hEnd : qkSetupStart block+40 = qkPc block := by fin_cases block <;> decide
      have hv := qkSetupLocalFrame block hLo (by omega) hs hStep
      obtain ⟨u,rest,hu,hU,hCount,hRest⟩ :=
        ih (by rw [hv.1]; omega) (by rw [hv.1]; omega) ⟨rfl,hv.2⟩ hn
      exact ⟨u,rest,by
        simpa only [Nat.add_comm 1] using run_comp hStep hu,by
        simpa only [hv.1,Nat.add_assoc,Nat.add_comm 1] using hU,by omega,hRest⟩

private theorem bankThroughReachedPath {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g fuel : Nat} {s z : TState} (hs : BankFrame l s) (hPath : BankReach l g fuel s z)
    (hBound : z.pc < 2768)
    (hFinish : ∀ block : Fin 4,
      ¬ (qkSetupStart block ≤ z.pc ∧ z.pc < qkSetupStart block+40)) :
    BankFrame l z := by
  induction fuel using Nat.strong_induction_on generalizing s with
  | h fuel ih =>
    have hHi : s.pc < 2768 := Nat.lt_of_not_ge
      (fun hb => (Nat.not_le_of_lt hBound) (hPath.staysPastExit hb))
    by_cases hStart : startsSetup s.pc = true
    · obtain ⟨block,_,hBank⟩ := List.any_eq_true.mp hStart
      have hStart' : s.pc = qkSetupStart block := (beq_iff_eq.mp hBank).symm
      have hClean : s.fault = none := by
        cases hPath with
        | refl =>
          exact (hFinish block ⟨hStart'.ge,by rw [hStart']; omega⟩).elim
        | step hw _ => exact returningStepClean hw
      have hSub := hs.shape.2.2 (by rw [hStart']; fin_cases block <;> decide)
      have hAt : At s (qkPc block-40) [] := ⟨hStart',hSub,hs.shape.2.1,hClean,trivial⟩
      obtain ⟨u,rest,hRun,hU,hFuel,hRest⟩ := setupThroughBankPath block hStart'.ge
        (by rw [hStart']) (hFinish block) ⟨rfl,hAt.2⟩ hPath
      have hPc : u.pc = qkPc block := by
        rw [hU.1,hStart']
        fin_cases block <;> decide
      obtain ⟨hAudit,hFlow⟩ := setupPreservesScalar block
      have hKeep {r} (hr : r ∈ [1062,9632]) : u.regs r = s.regs r :=
        schedulerLocalFrame hAudit hFlow hRun hStart'.ge (by rw [hStart']) hr
      have hInput : queryBankStage (qkSetupStart block) = if qkStage block = 0 then 1 else 0 :=
        by fin_cases block <;> rfl
      have hOutput : queryBankStage (qkPc block) = qkStage block := by fin_cases block <;> rfl
      have hOut : 1935 ≤ qkPc block ∧ insideSetup (qkPc block) = false := by
        fin_cases block <;> decide
      have hWords := retargetQkQueryBank hp block hAt (by
        intro step
        rw [← hInput,← hStart']
        exact hs.values step) hRun
      have hNew : BankFrame l u :=
        ⟨hPc.symm ▸ hOut.1,hPc.symm ▸ hOut.2,
          ⟨hU.2.1.symm ▸ by decide,hU.2.2.1,fun _ => hU.2.1⟩,
          (hKeep (by simp)).trans hs.role,(hKeep (by simp)).trans hs.id,
          fun step => by rw [hPc,hOutput]; exact hWords step⟩
      exact ih rest (by omega) hNew hRest
    · have hOrd := Bool.eq_false_iff.mpr hStart
      cases hPath with
      | refl => exact hs
      | @step _ _ _ _ n hw hRest =>
        rcases ordinaryBankStep hs hHi hOrd hw with hExit | hNext
        · exact (Nat.not_le_of_lt hBound (hRest.staysPastExit hExit)).elim
        · exact ih n (by omega) hNext hRest

/-- The actual opening route has retargeted the complete Q bank before returning K.
The returned-state proof uses only its recorded prefix and local continuation. -/
theorem openingQueryBankAtReturnedPrefix {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} {s t : TState} {events : List Event}
    (hs : At s 1935 ((1062,b32 12)::(9632,b32 0x8200490)::qDescriptorFacts l 1))
    (hr : TraceReach kernel Assumptions.all l g s events t) (ht : t.pc = 2275) :
    Holds t.regs ((1062,b32 12)::(9632,b32 0x8200490)::qDescriptorFacts l 1) := by
  have hStart : BankFrame l s := by
    refine ⟨hs.1.symm ▸ le_rfl,hs.1.symm ▸ (by decide),?_,hs.2.2.2.2.1,
      hs.2.2.2.2.2.1,?_⟩
    · exact ⟨hs.2.1.symm ▸ by decide,hs.2.2.1,fun _ => hs.2.1⟩
    · intro i
      have hj : queryBankStage s.pc = 1 := by rw [hs.1]; rfl
      rw [hj]
      exact holds_mem hs.2.2.2.2.2.2 (List.mem_map_of_mem (by simp))
  obtain ⟨fuel,hPath⟩ := BankReach.ofTrace hr
  have hBank := bankThroughReachedPath hp hStart hPath (by rw [ht]; decide)
    (fun block => by rw [ht]; fin_cases block <;> decide)
  have hStage : queryBankStage t.pc = 1 := by rw [ht]; rfl
  refine ⟨hBank.role,hBank.id,?_⟩
  unfold qDescriptorFacts
  generalize List.finRange 8 = steps
  induction steps with
  | nil => trivial
  | cons i rest ih =>
    exact ⟨hStage ▸ hBank.values i,ih⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread
