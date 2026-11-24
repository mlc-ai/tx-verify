-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Flow.NotArrive

@[expose] public section

/-! # Ring-event counts before role dispatch -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RingPrelude

open PTX PTX.Flow

private def pollOp : Op → Bool
  | .mbarWait .. => true
  | _ => false

private def ringlessAt (i : Nat) : Bool :=
  kernel.code[i]?.any (fun ins => !arriveOp ins.op && !pollOp ins.op)

set_option maxRecDepth 100000 in
private theorem prologue_ringless (s : Site) : ringlessAt s.pc = true := by
  cases s
  case init j => fin_cases j <;> decide +kernel
  case handoff wg => fin_cases wg <;> decide +kernel
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem head_ringless {P : Params} {L : Launch} {g : Nat} :
    ringlessAt ((Machine.code P L g).pc .head) = true := by
  change ringlessAt 1843 = true
  decide +kernel

private theorem fired_ringless {P : Params} {L : Launch} {g : Nat}
    {d : Machine.ThreadD} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some d) e o)
    (hn : ringlessAt ((Machine.code P L g).pc d) = true) :
    ∀ a b, arrivesOn a e = false ∧ okPoll b e = false := by
  unfold ringlessAt at hn
  cases hc : kernel.code[(Machine.code P L g).pc d]? with
  | none => simp [hc] at hn
  | some ins =>
    rw [hc] at hn
    have ho : arriveOp ins.op = false ∧ pollOp ins.op = false := by simpa using hn
    obtain ⟨t, _, hf⟩ := hf
    change Fires t.pc (match kernel.code[(Machine.code P L g).pc d]? with
      | some ins => eventTmpl Assumptions.all L g t ins.op
      | none => .ub .pcOutOfRange) e o at hf
    rw [hc] at hf
    have hp : ∀ p b o par a s, ins.op ≠ .mbarWait p b o par a s := by
      intro p b o par a s h
      rw [h] at ho
      exact Bool.noConfusion ho.2
    exact fun a b => ⟨arrivesOn_of_arriveOp ho.1 hf,
      okPoll_notWait (fires_notWait (eventTmpl_notWait hp) hf)⟩

/-- A prologue event contributes zero to arrival and successful-poll counts. -/
theorem prologue_no_counts {P : Params} {L : Launch} {g : Nat}
    {s : Site} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some (.prologue s)) e o) :
    ∀ a b, arrivesOn a e = false ∧ okPoll b e = false :=
  fired_ringless hf (prologue_ringless s)

/-- The dispatch broadcast contributes zero to arrival and successful-poll counts. -/
theorem head_no_counts {P : Params} {L : Launch} {g : Nat} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some .head) e o) :
    ∀ a b, arrivesOn a e = false ∧ okPoll b e = false :=
  fired_ringless hf head_ringless

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RingPrelude
