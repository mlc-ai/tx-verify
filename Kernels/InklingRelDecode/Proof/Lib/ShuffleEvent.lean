-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Kernel.PlainStep
import Lemmas.Flow.NotBulk
import Lemmas.Flow.NotShfl
import Lemmas.Flow.Next

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

/-- A shuffle instruction records a shuffle, or an undefined-behaviour event. -/
private theorem fires_shfl_or {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {mode : ShflMode} {d : Nat} {p : Option Nat} {a b c mask : Opnd} {pc : Nat} {e : Event}
    {ty : Option DType} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t
      (.warp ⟨.shfl mode, ty, some d :: (p.map some).toList, [a, b, c], some mask⟩)) e o) :
    Execution.isShfl e=true ∨ ∃ f, e.kind=.ub f := by
  simp only [eventTmpl] at hf
  rcases warpTmpl_shfl (L := L) (g := g) (t := t) (mode := mode) (ty := ty) (d := d)
    (ps := (p.map some).toList) (a := a) (b := b) (c := c) (mask := mask) with h | h <;>
    rw [h] at hf
  swap
  · exact .inr ⟨_,by rw [hf.1]⟩
  have hp : (p.map some).toList.head?.join = p := by cases p <;> rfl
  rw [hp] at hf
  simp only [shflTmpl] at hf
  split at hf
  · split_ifs at hf
    · obtain ⟨recv, ok, rfl, _⟩ := hf
      exact .inl rfl
    all_goals exact .inr ⟨_,by rw [hf.1]⟩
  all_goals exact .inr ⟨_,by rw [hf.1]⟩

/-- The positions of the program's warp shuffles. -/
def shflPcs : List Nat :=
  [17,202,244,286,1261,1838,2234,2242,2244,2246,2248,2253,2255,2464,2512,2603]

private def shflShape : Instr → Bool
  | ⟨none,.warp ⟨.shfl _,_,[some _],[_,_,_],some _⟩⟩ => true
  | _ => false

private theorem shapes : shflPcs.all (fun p => (kernel.code[p]?).any shflShape)=true := by
  decide +kernel

private theorem only : kernel.code.zipIdx.all
    (fun x => !Op.isShfl x.1.op || decide (x.2 ∈ shflPcs))=true := by
  decide +kernel

/-- Exactly the instructions at the listed positions record a shuffle. -/
theorem shfl_event {L m X i e} (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get i=some e) (nu : ∀ f, e.kind≠.ub f) :
    Execution.isShfl e=decide (e.pc ∈ shflPcs) := by
  obtain ⟨f,bad⟩|⟨t,ins,o,_,code,fire⟩ := get_source hX get
  · exact (nu f bad).elim
  cases test : decide (e.pc ∈ shflPcs) with
  | false =>
    cases s : Execution.isShfl e with
    | false => rfl
    | true =>
      have op := fires_shfl_op fire s
      have h := List.all_eq_true.mp only (ins,e.pc) (List.mem_zipIdx_iff_getElem?.mpr code)
      simp only [op,Bool.not_true,Bool.false_or] at h
      exact absurd (of_decide_eq_true h) (of_decide_eq_false test)
  | true =>
    have hit := List.all_eq_true.mp shapes e.pc (of_decide_eq_true test)
    rw [code] at hit
    obtain ⟨g,op⟩ := ins
    change shflShape ⟨g,op⟩=true at hit
    unfold shflShape at hit
    split at hit <;> try contradiction
    rename_i mode ty d a b c mask heq
    cases heq
    rcases fires_shfl_or (p := none) fire with yes|⟨f,bad⟩
    · exact yes
    · exact (nu f bad).elim

end PTX.Kernels.InklingRelDecode.Proof.Lib
