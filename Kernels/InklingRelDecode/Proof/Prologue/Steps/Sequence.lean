-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Length
import Kernels.InklingRelDecode.Proof.Prologue.Steps.SequenceMath
import Kernels.InklingRelDecode.Proof.Prologue.Steps.TaggedSequence
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Geometry
import Kernels.InklingRelDecode.Proof.Prologue.Steps.QuerySetup
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Sub
import Kernels.InklingRelDecode.Flow.Code.Part000
import Lemmas.Flow.SegChain

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32
set_option maxRecDepth 100000

private theorem length_bits {a b : Value} (ok : (subValue b a).regBits.isSome) :
    ∃ x, subValue b a = .bits 32 x := by
  cases b <;> first | exact ⟨_,rfl⟩ | contradiction

private theorem carry {Q L g w a b v won bcast r} (key : r ∈ ctlLive 43) (h₁ : r ≠ 482)
    (h₂ : r ≠ 612) : r ∈ ctlLive 41 ∧
      valueOf Q L g w ⟨.ld 2,a,b,b32 0,won,bcast⟩ r =
      valueOf Q L g w ⟨.el 0,a,b,v,won,bcast⟩ r := by
  have keys : ctlLive 43 =
      [3,462,463,464,478,479,480,481,482,526,527,528,532,610,612,1949,2018,2019,2020] := by
    decide +kernel
  rw [keys] at key
  simp only [List.mem_cons,List.not_mem_nil,or_false] at key
  rcases key with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | contradiction | exact ⟨by decide +kernel,by simp only [valueOf,registerValue]⟩

private theorem sequence_span {Q L g w m} (hp : Pre Q L m) (a b v : Value) (won : Bool)
    (bcast : Value) (bit : a.regBits.isSome) :
    let d : D := ⟨.ld 2,a,b,b32 0,won,bcast⟩
    let dn : D := ⟨.el 0,a,b,v,won,bcast⟩
    SegU kernel Assumptions.all L g 42 ((612,v)::facts Q L g w d 41)
      130 (facts Q L g w dn 130) := by
  intro d dn t ht
  obtain ⟨pc,hs,ha,hf,read,regs⟩ := ht
  let op : IntInstr := ⟨.sub,.int .s 32,false,[some 482],[.reg 612,.reg 481]⟩
  have ev := Lib.workerInt (ii := op) (L := L) (g := g) (by rfl) pc (by decide)
  cases run : execInt L g t op with
  | error f => exact .inr (dead_of_error (pc ▸ Flow.code_42) rfl hf (ev.trans run))
  | ok u =>
    have tau := tau_of_ok (K := kernel) (pc ▸ Flow.code_42) rfl hf (ev.trans run)
    have key : 481 ∈ ctlLive 41 := by decide +kernel
    have len : t.regs 481 = some (subValue b a) := holds_mem regs (mem_factsFrom key)
    obtain ⟨rfl,bits⟩ := sub_result read len run
    let prior := subValue v (subValue b a)
    let s := PTX.next (setReg t 482 prior)
    have pc' : s.pc = 43 := congrArg (·+1) pc
    have written : s.regs 482 = some prior := by simp [s,PTX.next,setReg]
    by_cases hptr : ∃ pw gen sp off, prior = .ptr pw gen sp off
    · obtain ⟨_,_,_,_,p⟩ := hptr
      exact .inr (dead_of_rtg (.single tau) (tagged_sequence_dead (t := s) pc' hf (p ▸ written)))
    obtain ⟨lenW,lenEq⟩ := length_bits bits
    have hb : ∃ x, prior = .bits 32 x := by
      cases v <;> first | exact ⟨_,rfl⟩ | exact False.elim (hptr ⟨_,_,_,_,rfl⟩)
    obtain ⟨pw,hpw⟩ := hb
    have atS : At s 43 (facts Q L g w dn 43) := by
      refine ⟨pc',hs,ha,hf,holds_of_pointwise fun r hr => ?_⟩
      by_cases hrw : r=482
      · subst r; exact written
      change Function.update t.regs 482 (some prior) r = _
      rw [Function.update_of_ne hrw]
      by_cases hseq : r=612
      · subst r; exact read
      obtain ⟨old,eq⟩ := carry (Q := Q) (L := L) (g := g) (w := w) (a := a) (b := b)
        (v := v) (won := won) (bcast := bcast) hr hrw hseq
      exact (holds_mem regs (mem_factsFrom old)).trans (congrArg some eq)
    have bound : g%L.block<256 := by rw [hp.block]; omega
    have tail := ((sequence_math (d := dn) hp pw hpw).comp ((row_segment bound).comp
      (query_setup bound lenW lenEq bit))) s atS
    rcases tail with ⟨u,steps,land⟩|dead
    · have first : Tau kernel Assumptions.all L g t s := tau
      exact .inl ⟨u,(Relation.ReflTransGen.single first).trans steps,land⟩
    · exact .inr (dead_of_rtg (.single tau) dead)

theorem step_sequence {m} (hp : Pre Q L m) (d : D) (hs : d.site = .ld 2)
    (bit : d.first.regBits.isSome) :
    (code Q L g w).StepAtU d := by
  obtain ⟨s,a,b,c,won,bcast⟩ := d
  cases hs
  let d : D := ⟨.ld 2,a,b,c,won,bcast⟩
  let dn := fun v => ({d with seq := v,site := .el 0} : D)
  apply record (d := d) dn Flow.code_41 rfl rfl rfl rfl rfl
    (by change 612 ∉ ctlLive 41; decide +kernel) rfl (fun _ => rfl) (fun _ _ => rfl)
  · intro v hi
    obtain rfl := hi
    exact sequence_span hp a b v won bcast bit
  · exact fun _ _ => trivial

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
