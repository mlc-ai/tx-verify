-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.PreparationCode
import all Kernels.FlashKdaFwd.Packed.Producer.Pipeline

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.Proof PTX.EventFrame

structure DispatchRegs (t : TState) : Prop where
  threadId : t.regs 307 = some (b32 129)
  selected : t.regs 486 = some (b32 1)
  length : t.regs 314 = some (b32 1)
  leader : t.regs 88 = some (.pred false)

private theorem kept {t u : TState} (vals : DispatchRegs t)
    (fr : ∀ r ∈ preparationRegs, u.regs r = t.regs r) : DispatchRegs u :=
  ⟨(fr _ (by decide)).trans vals.threadId,(fr _ (by decide)).trans vals.selected,
   (fr _ (by decide)).trans vals.length,(fr _ (by decide)).trans vals.leader⟩

private theorem parts {i : Instr} (ok : preservesDispatch i = true) :
    preparationOp i.op = true ∧ ∀ r ∈ preparationRegs, r ∉ writes i.op := by
  simpa [preservesDispatch,Bool.and_eq_true,List.all_eq_true] using ok

private theorem jumps {op : Op} {pc dst : Nat} (ok : preparationOp op = true) (lo : 315 ≤ pc)
    (hi : pc < 1402) (edge : dst = nextPc op pc ∨ BrxTarget op dst) :
    315 ≤ dst ∧ dst ≤ 1402 := by
  have next : 315 ≤ pc+1 ∧ pc+1 ≤ 1402 := by omega
  cases op <;> simp_all [preparationOp,nextPc,BrxTarget]

private theorem prepare_local {base : Nat → Nat → Nat} {L : Launch} {g : Nat} {t u : TState}
    (vals : DispatchRegs t) (lo : 315 ≤ t.pc) (hi : t.pc < 1402)
    (step : Tau kernel (Prologue.assumptions base) L g t u) :
    (315 ≤ u.pc ∧ u.pc ≤ 1402) ∧ DispatchRegs u := by
  have bound : t.pc < kernel.code.length := by rw [code_length]; omega
  let i := kernel.code[t.pc]
  have site : kernel.code[t.pc]? = some i := List.getElem?_eq_getElem bound
  obtain ⟨jump,frame⟩ := parts (preparation_site lo hi site)
  unfold Tau out at step
  cases f : t.fault with
  | some f => simp [f] at step
  | none =>
    simp only [f,site] at step
    cases guard : guardHolds t i.guard with
    | error e => simp [guard] at step
    | ok active =>
      cases active with
      | false =>
        simp only [guard,Out.tau.injEq] at step
        subst u
        exact ⟨by simp only [skip]; omega,kept vals (fun _ _ => rfl)⟩
      | true =>
        by_cases localOp : i.op.isLocal = true
        · simp only [guard,localOp,↓reduceIte] at step
          cases exec : execLocalA (Prologue.assumptions base) L g t i.op with
          | error e => simp [exec] at step
          | ok v =>
            simp only [exec,Out.tau.injEq] at step
            subst u
            have fr := execLocalA_frame (rules_frame base) exec (no_segments base _)
            exact ⟨jumps jump lo hi fr.pc,kept vals (fun r hr =>
              fr.regs r (by simpa [writes,localOp] using frame r hr))⟩
        · simp [guard,localOp] at step

private theorem prepare_event {base : Nat → Nat → Nat} {L : Launch} {g : Nat} {t u : TState}
    {e : Event} (vals : DispatchRegs t) (lo : 315 ≤ t.pc) (hi : t.pc < 1402)
    (step : EStep kernel (Prologue.assumptions base) L g t e (some u)) :
    (315 ≤ u.pc ∧ u.pc ≤ 1402) ∧ DispatchRegs u := by
  obtain ⟨i,site,localOp,fire⟩ := estep_event_source step
  have bound := (parts (preparation_site lo hi site)).2
  have fr := fun {t : TState} {op : Op} {u : TState} =>
    fun (h : execLocalA (Prologue.assumptions base) L g t op = .ok u) =>
      execLocalA_frame (rules_frame base) h (no_segments base _)
  have move := (estep_return_pc step (fun _ _ _ h => fr h)).2
  have same := callbackFrame_fires (Flow.eventTmpl_kept_at (fun _ _ h => fr h)) fire
  exact ⟨by omega,kept vals (fun r hr => same r (by simpa [writes,localOp] using bound r hr))⟩

private theorem with_silent {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
    {t u : TState} {es : List Event} {o : Option TState} (tau : Tau K A L g t u)
    (r : Run K A L g u es o) (nonempty : es ≠ []) : Run K A L g t es o := by
  cases r with
  | nil => exact (nonempty rfl).elim
  | step localSteps he rest => exact .step (.head tau localSteps) he rest
  | last localSteps he => exact .last (.head tau localSteps) he

private theorem record {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
    {t u : TState} {es : List Event} {e : Event} {o : Option TState}
    (path : Flow.TraceReach K A L g t es u) (event : EStep K A L g u e o) :
    Run K A L g t (es ++ [e]) o := by
  induction path with
  | refl =>
    cases o with
    | none => exact .last .refl event
    | some _ => exact .step .refl event (.nil _)
  | tau h _ ih => exact with_silent h (ih event) (by simp)
  | event h _ ih => exact .step .refl h (ih event)

private def noExit (base : Nat → Nat → Nat) (L : Launch) (t : TState) : Prop :=
  ∀ {s es e o}, Flow.TraceReach kernel (Prologue.assumptions base) L 129 t es s →
    EStep kernel (Prologue.assumptions base) L 129 s e o → e.kind ≠ .exit

private theorem dispatch_or_earlier (base : Nat → Nat → Nat) (L : Launch)
    (tid : (L.tidOf 129).x = 129)
    {t : TState} (range : 315 ≤ t.pc ∧ t.pc ≤ 1402) (regs : DispatchRegs t) :
    (315 ≤ t.pc ∧ t.pc < 1402 ∧ DispatchRegs t) ∨ noExit base L t := by
  by_cases pc : t.pc = 1402
  · right
    intro s es e o path event
    have run := record path event
    have last : (es ++ [e])[es.length]? = some e := by simp
    cases f : t.fault with
    | some fault =>
      rw [run.eventOfFault f last]
      simp
    | none =>
      exact no_one_token_exit base L tid pc f regs.threadId regs.selected regs.length regs.leader
        run last
  · exact .inl ⟨range.1,by omega,regs⟩

theorem no_exit_after_producer_selection (base : Nat → Nat → Nat) (L : Launch)
    (tid : (L.tidOf 129).x = 129) {t : TState} (pc : t.pc = 315) (regs : DispatchRegs t)
    {es : List Event} {o : Option TState} (trace : Run kernel (Prologue.assumptions base) L
      129 t es o) {j : Nat} {e : Event} (atIndex : es[j]? = some e) : e.kind ≠ .exit := by
  obtain ⟨s,_,path,step⟩ := trace.before_event atIndex
  have closure {a b : TState} {xs : List Event}
      (path : Flow.TraceReach kernel (Prologue.assumptions base) L 129 a xs b)
      (init : (315 ≤ a.pc ∧ a.pc < 1402 ∧ DispatchRegs a) ∨ noExit base L a) :
      (315 ≤ b.pc ∧ b.pc < 1402 ∧ DispatchRegs b) ∨ noExit base L b := by
    induction path with
    | refl => exact init
    | tau h _ ih =>
      apply ih
      rcases init with ⟨lo,hi,r⟩ | closed
      · obtain ⟨range,vals⟩ := prepare_local r lo hi h
        exact dispatch_or_earlier base L tid range vals
      · exact .inr (fun path event => closed (.tau h path) event)
    | event h _ ih =>
      apply ih
      rcases init with ⟨lo,hi,r⟩ | closed
      · obtain ⟨range,vals⟩ := prepare_event r lo hi h
        exact dispatch_or_earlier base L tid range vals
      · exact .inr (fun path event => closed (.event h path) event)
  rcases closure path (.inl ⟨by omega,by omega,regs⟩) with ⟨lo,hi,_⟩ | noexit
  · intro exit
    obtain ⟨i,site,op⟩ := exit_source step exit
    have supported := (parts (preparation_site lo hi site)).1
    rcases op with eq | eq <;> simp [eq,preparationOp] at supported
  · exact noexit (.refl _) step

end FlashKda.Packed.ProducerControl
