-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.IntStep
public import Lemmas.Flow.Arith32
public import Lemmas.Flow.Facts

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof

/-- Project a successful write onto the next live set. -/
theorem writeLive {val : Nat → Value} {rs rs' : List Nat} {dst : Nat}
    (hl : ∀ r ∈ rs', r = dst ∨ r ∈ rs) {R : Nat → Option Value}
    (hR : Holds R (factsFrom rs val)) :
    Holds (Function.update R dst (some (val dst))) (factsFrom rs' val) := by
  apply holds_of_pointwise
  intro r hr
  by_cases h : r = dst
  · subst r
    exact Function.update_self ..
  · rw [Function.update_of_ne h]
    exact holds_mem hR (mem_factsFrom ((hl r hr).resolve_left h))

/-- A left shift of an arbitrary loaded register. A bad payload ends the thread.
The caller need only give the destination's value and its live set. -/
theorem shiftLive {L : Launch} {g pc dst src : Nat} {s : Int} {rs rs' : List Nat}
    (val : Nat → Value)
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.shl, .int .b 32, false, [some dst],
      [.reg src, .imm s]⟩⟩)
    (hs : Assumptions.emuSites.contains pc = false) (hr : src ∈ rs)
    (hv : val dst = .bits 32 (Arith32.shl ((val src).regBits.getD 0) s))
    (hl : ∀ r ∈ rs', r = dst ∨ r ∈ rs) :
    SegU kernel Assumptions.all L g pc (factsFrom rs val) (pc + 1) (factsFrom rs' val) := by
  apply scalarStepU hc rfl rfl hs (r := dst) (v := val dst)
  · intro t u hR he
    have himm : readBits L g t 32 (.imm s) = .ok (Arith32.i32 s) := rfl
    simp only [execInt, DType.width, himm, bind, Except.bind, pure, Except.pure] at he
    cases hx : readBits L g t 32 (.reg src) <;> rw [hx] at he <;> try contradiction
    rw [readBits_eq_pattern (holds_mem hR (mem_factsFrom hr)) hx] at he
    rw [hv]
    exact (Except.ok.inj he).symm
  · exact fun _ hR => writeLive hl hR

/-- The 32 low bits, when an integer operand can be read. -/
noncomputable abbrev word (v : Value) := truncBits 32 (v.regBits.getD 0)

theorem madStep {L : Launch} {g pc : Nat} {dst a b c : Nat} {F G : List (Nat × Value)}
    {va vb vc : Value}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.mad .lo, .int .s 32, false, [some dst],
      [.reg a, .reg b, .reg c]⟩⟩)
    (hs : Assumptions.emuSites.contains pc = false)
    (ha : (a, va) ∈ F) (hb : (b, vb) ∈ F) (hcv : (c, vc) ∈ F)
    (hwrite : ∀ R, Holds R F → Holds (Function.update R dst (some (.bits 32
      (truncBits 32 (word va * word vb + word vc))))) G) :
    SegU kernel Assumptions.all L g pc F (pc + 1) G := by
  apply scalarStepU hc rfl rfl hs
  · intro t u hF he
    simp only [execInt, DType.width, bind, Except.bind, pure, Except.pure] at he
    cases h1 : readBits L g t 32 (.reg a) <;> rw [h1] at he <;> try contradiction
    cases h2 : readBits L g t 32 (.reg b) <;> rw [h2] at he <;> try contradiction
    cases h3 : readBits L g t 32 (.reg c) <;> rw [h3] at he <;> try contradiction
    rw [readBits_eq_pattern (holds_mem hF ha) h1,
      readBits_eq_pattern (holds_mem hF hb) h2,
      readBits_eq_pattern (holds_mem hF hcv) h3] at he
    exact (Except.ok.inj he).symm
  · exact hwrite

end PTX.Kernels.InklingRelDecode.Proof.Lib
