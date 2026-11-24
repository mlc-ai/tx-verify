-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.BarrierTrace
public import Lemmas.Protocol.NamedBarEarly
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Step.CtaBar

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.Proof PTX.Flow PTX.EventFrame

def roundAt (pc : Nat) := passedGate 85 pc + passedGate 110 pc + passedGate 379 pc

private theorem round_late {pc : Nat} (late : 379 < pc) : roundAt pc = 3 := by
  simp [roundAt,passedGate,late,show 85 < pc by omega,show 110 < pc by omega]

private theorem round_succ {pc : Nat} (off : pc ∉ startupBarriers) :
    roundAt (pc+1) = roundAt pc := by
  simp [startupBarriers] at off
  simp only [roundAt,passedGate,show (85 < pc+1) ↔ 85 < pc by omega,
    show (110 < pc+1) ↔ 110 < pc by omega,show (379 < pc+1) ↔ 379 < pc by omega]

def StartupSites := ∀ pc i, kernel.code[pc]? = some i →
  startupBranch pc i.op = true ∧ barrierSite pc i.op = true

private theorem named_at_gate (sites : StartupSites) {pc : Nat} {i : Instr}
    (site : kernel.code[pc]? = some i) (bar : barOp i.op = true) (early : pc ≤ 379) :
    pc ∈ startupBarriers := by
  have h := (sites pc i site).2
  simp [barrierSite,bar] at h
  simp [startupBarriers]
  omega

variable {base : Nat → Nat → Nat} {L : Launch} {g : Nat}

private theorem round_step (sites : StartupSites) {t u : TState} {e : Event}
    (step : EStep kernel (Prologue.assumptions base) L g t e (some u)) :
    min 3 (roundAt t.pc + (if Execution.isBarId 0 e then 1 else 0)) = roundAt u.pc := by
  by_cases gate : t.pc ∈ startupBarriers
  · obtain ⟨ev,next⟩ := at_barrier gate rfl step
    simp [startupBarriers] at gate
    rcases gate with pos | pos | pos <;>
      simp [ev,next,pos,Execution.isBarId,roundAt,passedGate]
  · obtain ⟨_,move⟩ := estep_return_pc step fun t op u h =>
      execLocalA_frame (rules_frame base) h (no_segments base _)
    have same : roundAt u.pc = roundAt t.pc := move.elim (fun h => by rw [h])
      (fun h => h ▸ round_succ gate)
    rw [same]
    by_cases late : 379 < t.pc
    · rw [round_late late]
      omega
    · have quiet : Execution.isBarId 0 e = false := by
        obtain ⟨i,site,_,fire⟩ := estep_event_source step
        cases k : e.kind <;> simp [Execution.isBarId,k]
        exact (gate (named_at_gate sites site (fires_bar_op fire k) (by omega))).elim
      simp only [quiet,Bool.false_eq_true,↓reduceIte,Nat.add_zero]
      apply Nat.min_eq_right
      simp only [roundAt,passedGate]
      split_ifs <;> omega

theorem rounds_on_path (sites : StartupSites) {t u : TState} {es : List Event}
    (path : TraceReach kernel (Prologue.assumptions base) L g t es u) :
    min 3 (roundAt t.pc + es.countP (Execution.isBarId 0)) = roundAt u.pc := by
  induction path with
  | refl =>
    simp only [List.countP_nil,Nat.add_zero]
    apply Nat.min_eq_right
    simp only [roundAt,passedGate]
    split_ifs <;> omega
  | tau step _ ih =>
    have h := fun cut (m : cut ∈ startupBarriers) =>
      tau_passed m (fun pc i s => (sites pc i s).1) step
    simpa only [roundAt,h 85 (by decide),h 110 (by decide),h 379 (by decide)] using ih
  | @event s v _ es e step _ ih =>
    have move := round_step sites step
    cases test : Execution.isBarId 0 e <;> simp [test] at move ⊢ <;> omega

theorem round_of_event {X : Execution} {mem : Mem0}
    (valid : Consistent L kernel (Prologue.assumptions base) mem X) (sites : StartupSites)
    {id : EvId} {e : Event} (event : X.get id = some e) :
    min 3 (((X.tr id.1).take id.2).countP (Execution.isBarId 0)) = roundAt e.pc := by
  obtain ⟨o,run⟩ := valid.thr id.1 (Step.CtaBar.thread_lt_of_get valid event)
  obtain ⟨t,q,path,fire⟩ := run.before_event event
  have h := rounds_on_path sites path
  rw [estep_source_pc fire]
  simpa only [show roundAt ({} : TState).pc = 0 by decide,Nat.zero_add] using h

theorem first_three_full {X : Execution} {mem : Mem0}
    (valid : Consistent L kernel (Prologue.assumptions base) mem X) (sites : StartupSites)
    (block : L.block = 192) : NamedBar.EarlySources L X none (Finset.range 6) 0 2 := by
  intro e pc cnt bar _ early
  refine ⟨Finset.mem_range.mpr (by rw [block]; omega),?_⟩
  obtain ⟨mode,event⟩ := bar
  have h := round_of_event valid sites event
  have low : pc ≤ 379 := by
    by_contra! high
    rw [round_late high] at h
    omega
  rcases get_source valid event with ⟨_,bad⟩ | ⟨t,i,o,_,site,fire⟩
  · cases bad
  · have member := named_at_gate sites site (fires_bar_op fire rfl) low
    rw [barrier_site member] at site
    cases site
    change Fires pc (.bar 0 (next t) none .sync) ⟨pc,.bar 0 cnt mode⟩ o at fire
    exact (Kind.bar.inj (congrArg Event.kind fire.1)).2.1

end FlashKda.Packed.ProducerControl
