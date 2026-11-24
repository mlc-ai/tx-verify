-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.StartupBarriers
public import Kernels.FlashKdaFwd.Packed.RegisterFrame
public import Lemmas.Flow.TraceReach
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.Proof PTX.Flow PTX.EventFrame

def passedGate (cut pc : Nat) := if cut < pc then 1 else 0

private theorem passed_succ {cut pc : Nat} (ne : pc ≠ cut) :
    passedGate cut (pc+1) = passedGate cut pc := by
  simp only [passedGate,show (cut < pc+1) ↔ cut < pc by omega]

private theorem transition {pc dst cut : Nat} {op : Op} (member : cut ∈ boundaries)
    (ok : startupBranch pc op = true) (edge : dst = nextPc op pc ∨ BrxTarget op dst)
    (off : pc ≠ cut) : passedGate cut dst = passedGate cut pc := by
  by_cases straight : dst = pc+1
  · simp only [passedGate]
    split_ifs <;> omega
  cases op <;> simp_all [nextPc,BrxTarget,startupBranch]
  have side := of_decide_eq_true (List.all_eq_true.mp ok _ member)
  simp only [passedGate]
  split_ifs <;> omega

variable {base : Nat → Nat → Nat} {L : Launch} {g : Nat}

theorem tau_passed {t u : TState} {cut : Nat} (member : cut ∈ startupBarriers)
    (sites : ∀ pc i, kernel.code[pc]? = some i → startupBranch pc i.op = true)
    (step : Tau kernel (Prologue.assumptions base) L g t u) :
    passedGate cut u.pc = passedGate cut t.pc := by
  have bound : cut ∈ boundaries := by
    simp_all [startupBarriers,boundaries]
    tauto
  unfold Tau out at step
  cases fault : t.fault with
  | some f => simp [fault] at step
  | none =>
    simp only [fault] at step
    cases site : kernel.code[t.pc]? with
    | none => simp [site] at step
    | some i =>
      simp only [site] at step
      have off : t.pc ≠ cut := by
        rintro eq
        rw [eq,barrier_site member] at site
        cases site
        simp [startupSync,guardHolds,Op.isLocal,pure,Except.pure] at step
      cases guard : guardHolds t i.guard with
      | error f => simp [guard] at step
      | ok b =>
        cases b with
        | false =>
          simp only [guard,Out.tau.injEq] at step
          subst u
          exact passed_succ off
        | true =>
          by_cases localOp : i.op.isLocal = true
          · simp only [guard,localOp,↓reduceIte] at step
            cases result : execLocalA (Prologue.assumptions base) L g t i.op with
            | error f => simp [result] at step
            | ok v =>
              simp only [result,Out.tau.injEq] at step
              subst u
              exact transition bound (sites _ _ site)
                (execLocalA_frame (rules_frame base) result (no_segments base _)).pc off
          · simp [guard,localOp] at step

theorem at_barrier {t u : TState} {e : Event} {cut : Nat} (member : cut ∈ startupBarriers)
    (pos : t.pc = cut) (step : EStep kernel (Prologue.assumptions base) L g t e (some u)) :
    e = ⟨cut,.bar 0 none .sync⟩ ∧ u.pc = cut+1 := by
  obtain ⟨i,site,_,fire⟩ := estep_event_source step
  rw [pos,barrier_site member] at site
  cases site
  change Fires t.pc (.bar 0 (next t) none .sync) e (some u) at fire
  obtain ⟨ev,h⟩ := fire
  cases Option.some.inj h
  exact ⟨by simpa [pos] using ev,by simp [next,pos]⟩

def atSync (cut : Nat) (e : Event) :=
  (e.pc == cut) && match e.kind with
    | .bar 0 none .sync => true
    | _ => false

theorem atSync_iff {cut : Nat} {e : Event} : atSync cut e = true ↔ e = ⟨cut,.bar 0 none .sync⟩ := by
  cases e with
  | mk pc kind =>
    simp only [atSync,Bool.and_eq_true,beq_iff_eq,Event.mk.injEq]
    cases kind <;> simp
    rename_i id count mode
    cases id <;> cases count <;> cases mode <;> simp

theorem barriers_passed {t u : TState} {es : List Event} {cut : Nat}
    (member : cut ∈ startupBarriers)
    (sites : ∀ pc i, kernel.code[pc]? = some i → startupBranch pc i.op = true)
    (path : TraceReach kernel (Prologue.assumptions base) L g t es u) :
    es.countP (atSync cut) + passedGate cut t.pc = passedGate cut u.pc := by
  induction path with
  | refl => simp
  | tau step _ ih => rw [← tau_passed member sites step]; exact ih
  | @event s v _ _ e step _ ih =>
    by_cases pos : s.pc = cut
    · obtain ⟨rfl,next⟩ := at_barrier member pos step
      simp [atSync,passedGate,pos,next] at ih ⊢
      omega
    · obtain ⟨event,move⟩ := estep_return_pc step fun t op u h =>
        execLocalA_frame (rules_frame base) h (no_segments base _)
      have same : passedGate cut v.pc = passedGate cut s.pc := by
        rcases move with h | h
        · rw [h]
        · rw [h]; exact passed_succ pos
      simpa [atSync,event,pos,same] using ih

end FlashKda.Packed.ProducerControl
