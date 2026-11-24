-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.ProducerControl
public import Kernels.FlashKdaFwd.Packed.RegisterFrame

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.Proof PTX.EventFrame

structure Facts (t : TState) : Prop where
  position : allowed t.pc
  elected : t.regs 88 = some (.pred false)
  threadId : t.pc = 1415 → t.regs 667 = some (b32 129)
  laneId : t.pc = 1416 → t.regs 668 = some (b32 1)
  laneZero : t.pc = 1417 → t.regs 35 = some (.pred false)
  check : tested t.pc → t.regs 2 = some (.pred false)

theorem start {t : TState} (pc : t.pc = 48) (elected : t.regs 88 = some (.pred false)) :
    Facts t := by
  refine ⟨?_,elected,?_,?_,?_,?_⟩ <;> rw [pc] <;> simp [allowed,tested]

private theorem transport {t u : TState} (facts : Facts t) (link : edge t.pc u.pc = true)
    (leader : u.regs 88 = t.regs 88) (flag : u.regs 2 = t.regs 2) : Facts u := by
  obtain ⟨position,gap,passed⟩ := of_decide_eq_true link
  refine ⟨position,leader.trans facts.elected,?_,?_,?_,fun h => flag.trans (facts.check (passed h))⟩
  all_goals intro pc; omega

private theorem targets {pc dst : Nat} {op : Op} (j : branches pc op = true)
    (next : edge pc (pc+1) = true) (h : dst = nextPc op pc ∨ BrxTarget op dst) :
    edge pc dst = true := by
  cases op <;> simp_all [branches,nextPc,BrxTarget]

private theorem components {pc : Nat} {i : Instr} (ok : accepts pc i = true)
    (pos : allowed pc) (normal : ¬ special pc) :
    ((edge pc (pc+1) = true ∧ branches pc i.op = true) ∧ 88 ∉ writes i.op) ∧
      2 ∉ writes i.op := by
  simpa [accepts,pos,normal,Bool.and_eq_true] using ok

theorem tau_ordinary (base : Nat → Nat → Nat) {K : Kernel} {L : Launch} {g : Nat}
    {t u : TState} (facts : Facts t) (normal : ¬ special t.pc)
    (accept : ∀ i, K.code[t.pc]? = some i → accepts t.pc i = true)
    (step : Tau K (Prologue.assumptions base) L g t u) : Facts u := by
  unfold Tau out at step
  cases fault : t.fault with
  | some f => simp [fault] at step
  | none =>
    simp only [fault] at step
    cases site : K.code[t.pc]? with
    | none => simp [site] at step
    | some i =>
      obtain ⟨⟨⟨next,br⟩,keepLeader⟩,keepCheck⟩ := components (accept i site) facts.position normal
      simp only [site] at step
      cases guard : guardHolds t i.guard with
      | error e => simp [guard] at step
      | ok active =>
        cases active with
        | false =>
          simp only [guard,Out.tau.injEq] at step
          subst u
          exact transport facts next rfl rfl
        | true =>
          by_cases localOp : i.op.isLocal = true
          · simp only [guard,localOp,↓reduceIte] at step
            cases exec : execLocalA (Prologue.assumptions base) L g t i.op with
            | error e => simp [exec] at step
            | ok s =>
              simp only [exec,Out.tau.injEq] at step
              subst u
              have fr := execLocalA_frame (rules_frame base) exec (no_segments base _)
              simp only [writes,localOp,↓reduceIte] at keepLeader keepCheck
              exact transport facts (targets br next fr.pc) (fr.regs _ keepLeader)
                (fr.regs _ keepCheck)
          · simp [guard,localOp] at step

theorem event_ordinary (base : Nat → Nat → Nat) {K : Kernel} {L : Launch} {g : Nat}
    {t u : TState} {e : Event} (facts : Facts t) (normal : ¬ special t.pc)
    (accept : ∀ i, K.code[t.pc]? = some i → accepts t.pc i = true)
    (step : EStep K (Prologue.assumptions base) L g t e (some u)) : Facts u := by
  obtain ⟨i,site,notLocal,fire⟩ := estep_event_source step
  obtain ⟨⟨⟨next,_⟩,keepLeader⟩,keepCheck⟩ := components (accept i site) facts.position normal
  have fr := fun {t : TState} {op : Op} {u : TState} =>
    fun (h : execLocalA (Prologue.assumptions base) L g t op = .ok u) =>
      execLocalA_frame (rules_frame base) h (no_segments base _)
  have kept := callbackFrame_fires (Flow.eventTmpl_kept_at (fun _ _ h => fr h)) fire
  have pc := (estep_return_pc step (fun _ _ _ h => fr h)).2
  simp only [writes,notLocal,Bool.false_eq_true,ite_false] at keepLeader keepCheck
  apply transport facts _ (kept _ keepLeader) (kept _ keepCheck)
  rcases pc with same | after
  · rw [same]
    have gap : t.pc ≤ 1414 ∨ 1418 ≤ t.pc := by unfold special at normal; omega
    exact decide_eq_true ⟨facts.position,gap,id⟩
  · rwa [after]

end FlashKda.Packed.ProducerControl
