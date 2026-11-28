-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Payload
import Kernels.InklingRelDecode.Proof.Prologue.StepAt
import Kernels.InklingRelDecode.Proof.Prologue.Steps.ReadFault
import Kernels.InklingRelDecode.Flow.Code.Part000
import Lemmas.Flow.LandsU
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
private theorem canonical {a b} (ok : (subValue b a).regBits.isSome) :
    ∃ x, subValue b a = .bits 32 x := by
  cases b <;> first | exact ⟨_,rfl⟩ | contradiction

private theorem payload_or_fault {Q L g w d d' t ev u ins}
    (hi : Payload d) (atD : (code Q L g w).AtD d t) (hc : kernel.code[d.site.pc]? = some ins)
    (fire : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ev (some u))
    (step : next Q L g d ev = some (some d')) :
    Payload d' ∨ Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) u := by
  by_cases hr : ∃ j, d.site = .ld j
  case neg => exact .inl (payload_next step hi (fun j h => hr ⟨j,h⟩))
  obtain ⟨j,hs⟩ := hr
  obtain ⟨s,a,b,c,won⟩ := d
  cases hs
  obtain ⟨pc,sub,acc,hf,regs⟩ := atD
  fin_cases j
  · cases ek : ev.kind <;> simp only [next,ek,reduceCtorEq,Option.some.injEq] at step
    subst d'
    left
    change (41≤37 → _) ∧ (130≤37 → _)
    exact ⟨fun h => by omega,fun h => by omega⟩
  · by_cases bit : a.regBits.isSome
    · cases ek : ev.kind <;> simp only [next,ek,reduceCtorEq,Option.some.injEq] at step
      subst d'
      left
      change (41≤41 → _) ∧ (130≤41 → _)
      exact ⟨fun _ => bit,fun h => by omega⟩
    · right
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_37)
      have k : 610 ∈ ctlLive 37 := by decide +kernel
      exact read_fault (pc := 37) (diff := 481) (src := 610) (dst := 611)
        rfl rfl rfl rfl pc sub acc hf
        (holds_mem regs (mem_factsFrom k)) (by decide) bit Flow.code_38 (by decide) fire
  · by_cases bit : (subValue b a).regBits.isSome
    · cases ek : ev.kind <;> simp only [next,ek,reduceCtorEq,Option.some.injEq] at step
      subst d'
      exact .inl (words_payload ⟨hi.1 (by change 41≤41; decide),canonical bit⟩)
    · right
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_41)
      have k : 481 ∈ ctlLive 41 := by decide +kernel
      exact read_fault (pc := 41) (diff := 482) (src := 481) (dst := 612)
        rfl rfl rfl rfl pc sub acc hf
        (holds_mem regs (mem_factsFrom k)) (by decide) bit Flow.code_42 (by decide) fire

/-- The successful input subtractions certify the carried word types used by
the softmax entry. The successor remains the same for every read payload. -/
theorem checked_stepAt {m} (hp : Pre Q L m) (d : D) : (checkedCode Q L g w).StepAtU d where
  site := fun hi => (stepAt (g := g) (w := w) hp d hi.2).site hi.1
  step := by
    intro t ev u ins atD hi hc fire
    obtain ⟨inv,pay⟩ := hi
    rcases (stepAt (g := g) (w := w) hp d pay).step ins atD inv hc fire with (halt|succ)|dead
    · exact .inl (.inl halt)
    · obtain ⟨d',t',hn,steps,good⟩ := succ
      apply Or.inl; apply Or.inr
      rcases payload_or_fault pay atD hc fire hn with ok|fault
      · rcases good with ⟨hat,inv'⟩|ub
        · exact ⟨d',t',hn,steps,.inl ⟨hat,inv',ok⟩⟩
        · exact ⟨d',t',hn,steps,.inr ub⟩
      · obtain ⟨s,run,land⟩ := Code.goodU_of_dead (C := checkedCode Q L g w) d' fault
        exact ⟨d',s,hn,run,land⟩
    · exact .inr dead

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
