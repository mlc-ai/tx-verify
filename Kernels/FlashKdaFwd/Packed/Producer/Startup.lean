-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.InputLeader
public import Kernels.FlashKdaFwd.Packed.Producer.StartupEvents
public import Lemmas.Flow.TraceReach
import all Kernels.FlashKdaFwd.Packed.Producer.Pipeline

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.Proof PTX.EventFrame

private def inside (t : TState) := 48 ≤ t.pc ∧ t.pc < 111

private theorem kept_state {t u : TState} (s : LoaderState t)
    (regs : ∀ r ∈ startupRegs, u.regs r = t.regs r)
    (sub : u.sub = t.sub) (acc : u.acc = t.acc) (fault : u.fault = t.fault) : LoaderState u :=
  ⟨(regs 307 (by decide)).trans s.thread,(regs 2247 (by decide)).trans s.offsets,
    (regs 88 (by decide)).trans s.leader,sub.trans s.scalar,acc.trans s.fresh,fault.trans s.clear⟩

private theorem before_local {base : Nat → Nat → Nat} {L : Launch} {t u : TState}
    (s : LoaderState t) (p : inside t) (h : Tau kernel (Prologue.assumptions base) L 129 t u) :
    (48 ≤ u.pc ∧ u.pc ≤ 111) ∧ LoaderState u := by
  obtain ⟨lo,hi⟩ := p
  have bound : t.pc < kernel.code.length := by rw [code_length]; omega
  let i := kernel.code[t.pc]
  have ins : kernel.code[t.pc]? = some i := List.getElem?_eq_getElem bound
  obtain ⟨dst,_,_,_,regs⟩ := startup_site lo hi ins
  unfold Tau out at h
  simp only [s.clear,ins] at h
  cases guard : guardHolds t i.guard with
  | error e => simp [guard] at h
  | ok active =>
    cases active with
    | false =>
      simp only [guard,Out.tau.injEq] at h
      subst u
      exact ⟨by simp only [skip]; omega,
        kept_state s (fun _ _ => rfl) s.scalar.symm s.fresh.symm rfl⟩
    | true =>
      by_cases localOp : i.op.isLocal = true
      · simp only [guard,localOp,↓reduceIte] at h
        cases op : execLocalA (Prologue.assumptions base) L 129 t i.op with
        | error f => simp [op] at h
        | ok v =>
          simp only [op,Out.tau.injEq] at h
          subst u
          have fr := execLocalA_frame (rules_frame base) op (no_segments base _)
          exact ⟨dst _ fr.pc,kept_state s (fun r hr =>
            fr.regs r (by simpa [writes,localOp] using regs r hr)) fr.sub fr.acc fr.fault⟩
      · simp [guard,localOp] at h

private theorem before_event {base : Nat → Nat → Nat} {L : Launch} {t u : TState} {e : Event}
    (s : LoaderState t) (p : inside t)
    (h : EStep kernel (Prologue.assumptions base) L 129 t e (some u)) :
    (48 ≤ u.pc ∧ u.pc ≤ 111) ∧ LoaderState u := by
  obtain ⟨i,ins,notLocal,fire⟩ := estep_event_source h
  obtain ⟨lo,hi⟩ := p
  obtain ⟨_,_,_,kind,regs⟩ := startup_site lo hi ins
  obtain ⟨pc,sub,acc,good⟩ := startup_event_frame (kind notLocal) fire
  have fr := fun {t : TState} {op : Op} {u : TState} =>
    fun (loc : execLocalA (Prologue.assumptions base) L 129 t op = .ok u) =>
      execLocalA_frame (rules_frame base) loc (no_segments base _)
  have same := callbackFrame_fires (Flow.eventTmpl_kept_at (fun _ _ loc => fr loc)) fire
  exact ⟨by omega,kept_state s (fun r hr =>
    same r (by simpa [writes,notLocal] using regs r hr)) sub acc good⟩

theorem cut_at_offsets {base : Nat → Nat → Nat} {L : Launch} {t s : TState} {es : List Event}
    {e : Event} {o : Option TState} (initial : LoaderState t) (lo : 48 ≤ t.pc) (hi : t.pc ≤ 111)
    (path : Flow.TraceReach kernel (Prologue.assumptions base) L 129 t es s)
    (final : EStep kernel (Prologue.assumptions base) L 129 s e o) (exit : e.kind = .exit) :
    ∃ pre rest u, es = pre ++ rest ∧ u.pc = 111 ∧ LoaderState u ∧
      Flow.TraceReach kernel (Prologue.assumptions base) L 129 u rest s := by
  induction path with
  | refl a =>
    by_cases pos : a.pc = 111
    · exact ⟨[],[],_,rfl,pos,initial,.refl _⟩
    obtain ⟨i,ins,op⟩ := exit_source final exit
    obtain ⟨_,nr,ne,_⟩ := startup_site lo (by omega) ins
    exact (op.elim nr ne).elim
  | @tau a b c xs step rest ih =>
    by_cases pos : a.pc = 111
    · exact ⟨[],xs,_,rfl,pos,initial,.tau step rest⟩
    obtain ⟨⟨low,high⟩,state⟩ := before_local initial ⟨lo,by omega⟩ step
    exact ih state low high final
  | @event a b c xs ev step rest ih =>
    by_cases pos : a.pc = 111
    · exact ⟨[],ev :: xs,_,rfl,pos,initial,.event step rest⟩
    obtain ⟨⟨low,high⟩,state⟩ := before_event initial ⟨lo,by omega⟩ step
    obtain ⟨pre,tail,u,eq,atCut,facts,after⟩ := ih state low high final
    exact ⟨ev :: pre,tail,u,by simp [eq],atCut,facts,after⟩

end FlashKda.Packed.ProducerControl
