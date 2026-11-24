-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.Dispatch
public import Kernels.FlashKdaFwd.Packed.Producer.PipelineCode
public import Kernels.FlashKdaFwd.Packed.Producer.Trace
public import Lemmas.Flow.NotClc

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.Proof PTX.EventFrame

private theorem instrAt {t : TState} (h : inPipeline t.pc) : ∃ i, kernel.code[t.pc]? = some i := by
  have bound : t.pc < kernel.code.length := by rw [code_length]; unfold inPipeline at h; omega
  exact ⟨_,List.getElem?_eq_getElem bound⟩

private theorem narrow {pc : Nat} (h : allowed pc) (lo : 1411 ≤ pc) (hi : pc ≤ 1882) :
    inPipeline pc := by unfold allowed at h; unfold inPipeline; omega

private theorem destination {op : Op} {pc dst : Nat} (h : stays op = true)
    (region : inPipeline pc) (toDst : dst = nextPc op pc ∨ BrxTarget op dst) :
    1411 ≤ dst ∧ dst ≤ 1882 := by
  have next : 1411 ≤ pc+1 ∧ pc+1 ≤ 1882 := by unfold inPipeline at region; omega
  cases op <;> simp_all [stays,nextPc,BrxTarget]

private theorem local_destination {base : Nat → Nat → Nat} {L : Launch} {g : Nat} {t u : TState}
    (step : Tau kernel (Prologue.assumptions base) L g t u) (live : allowed t.pc)
    (region : inPipeline t.pc) (result : allowed u.pc) : inPipeline u.pc := by
  obtain ⟨i,ins⟩ := instrAt region
  have allowedOp := pipeline_site live region ins
  unfold Tau out at step
  cases f : t.fault with
  | some f => simp [f] at step
  | none =>
    simp only [f,ins] at step
    cases guard : guardHolds t i.guard with
    | error e => simp [guard] at step
    | ok active =>
      cases active with
      | false =>
        simp only [guard,Out.tau.injEq] at step
        subst u
        unfold inPipeline at region
        apply narrow result <;> simp [skip] <;> omega
      | true =>
        by_cases isLocal : i.op.isLocal = true
        · simp only [guard,isLocal,↓reduceIte] at step
          cases exec : execLocalA (Prologue.assumptions base) L g t i.op with
          | error e => simp [exec] at step
          | ok v =>
            simp only [exec,Out.tau.injEq] at step
            subst u
            have fr := execLocalA_frame (rules_frame base) exec (no_segments base _)
            obtain ⟨lo,hi⟩ := destination allowedOp region fr.pc
            exact narrow result lo hi
        · simp [guard,isLocal] at step

private theorem retained {base : Nat → Nat → Nat} {L : Launch} {g : Nat} {t u : TState}
    {es : List Event} (tid : (L.tidOf g).x = 129)
    (path : Flow.TraceReach kernel (Prologue.assumptions base) L g t es u)
    (init : Facts t) (region : inPipeline t.pc) : Facts u ∧ inPipeline u.pc := by
  induction path with
  | refl => exact ⟨init,region⟩
  | tau h _ ih =>
    have next := reachable tid (.tau h (.refl _)) init
    exact ih next (local_destination h init.position region next.position)
  | @event s u _ _ _ h _ ih =>
    have next := reachable tid (.event h (.refl _)) init
    have move := (estep_return_pc h (fun _ _ _ loc =>
      execLocalA_frame (rules_frame base) loc (no_segments base _))).2
    apply ih next
    apply narrow next.position <;> unfold inPipeline at region <;> omega

private theorem exit_source {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
    {t : TState} {e : Event} {o : Option TState} (step : EStep K A L g t e o)
    (exited : e.kind = .exit) : ∃ i, K.code[t.pc]? = some i ∧ (i.op = .ret ∨ i.op = .exit) := by
  obtain ⟨m,ho,hf⟩ := step
  have noFault {f : Fault} (h : Fires t.pc (.ub f) e o) : False := by
    rw [h.1] at exited
    cases exited
  unfold out at ho
  split at ho
  · cases ho; exact (noFault hf).elim
  · split at ho
    · cases ho; exact (noFault hf).elim
    · rename_i i site
      split at ho
      · cases ho; exact (noFault hf).elim
      · cases ho
      · split at ho
        · split at ho
          · cases ho
          · cases ho; exact (noFault hf).elim
        · cases ho; exact ⟨i,site,Flow.fires_exit_op hf exited⟩

theorem no_pipeline_exit (base : Nat → Nat → Nat) (L : Launch) {g : Nat}
    (tid : (L.tidOf g).x = 129) {t : TState} (entry : t.pc = 1411)
    (elected : t.regs 88 = some (.pred false)) {es : List Event} {o : Option TState}
    (trace : Run kernel (Prologue.assumptions base) L g t es o) {j : Nat} {e : Event}
    (atIndex : es[j]? = some e) : e.kind ≠ .exit := by
  have init : Facts t := by
    refine ⟨?_,elected,?_,?_,?_,?_⟩ <;> rw [entry] <;> simp [allowed,tested]
  obtain ⟨s,_,path,step⟩ := trace.before_event atIndex
  obtain ⟨facts,bound⟩ := retained tid path init (by simp [inPipeline,entry])
  intro exit
  obtain ⟨ins,site,op⟩ := exit_source step exit
  have h := pipeline_site facts.position bound site
  rcases op with eq | eq <;> simp [eq,stays] at h

theorem no_one_token_exit (base : Nat → Nat → Nat) (L : Launch) (tid : (L.tidOf 129).x = 129)
    {t : TState} (pc : t.pc = 1402) (clear : t.fault = none)
    (threadId : t.regs 307 = some (b32 129)) (selected : t.regs 486 = some (b32 1))
    (length : t.regs 314 = some (b32 1)) (leader : t.regs 88 = some (.pred false))
    {es : List Event} {o : Option TState} (trace : Run kernel (Prologue.assumptions base) L 129
      t es o) {j : Nat} {e : Event} (atIndex : es[j]? = some e) : e.kind ≠ .exit := by
  obtain ⟨u,steps,entry,_,flag⟩ := one_token_dispatch base L t pc clear threadId selected length
  have rest := trace.after_local_nonempty (run_rtg steps) (fun eq => by simp [eq] at atIndex)
  exact no_pipeline_exit base L tid entry (flag.trans leader) rest atIndex

end FlashKda.Packed.ProducerControl
