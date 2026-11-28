-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Machine
public import Lemmas.Flow.Havoc
import Kernels.InklingRelDecode.Proof.Lib.IntStep
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.LandsU
import Lemmas.Flow.Step.SiteCases

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof

variable {L : Launch} {g : Nat} {w : Value} {regs : Nat → Value} (i n a b : Value)

noncomputable abbrev entryFacts :=
  (code L g w regs).facts ⟨.beginBar,i,n,a,b⟩

/-- Both loaded count words are accepted. A successful signed comparison determines the
loop guard. A type error in either operand terminates at this instruction. -/
theorem compare_entry :
    let F := entryFacts (L := L) (g := g) (w := w) (regs := regs) i n a b
    SegU kernel Assumptions.all L g 2347 F 2348
      ((19, .pred (decide (toSigned 32 (bits n) ≤ toSigned 32 (bits i)))) :: F) := by
  intro F
  have hi : (1905, i) ∈ F := mem_factsFrom (val := valueOf L g w regs ⟨.beginBar,i,n,a,b⟩)
    (show 1905 ∈ Flow.live 2346 by decide)
  have hn : (467, n) ∈ F := mem_factsFrom (val := valueOf L g w regs ⟨.beginBar,i,n,a,b⟩)
    (show 467 ∈ Flow.live 2346 by decide)
  apply Lib.scalarStepU Flow.code_2347 rfl rfl (by decide)
  · intro t u hF he
    simp only [execInt, DType.width, bind, Except.bind, pure, Except.pure] at he
    cases h1 : readBits L g t 32 (.reg 1905) <;> rw [h1] at he <;> try contradiction
    cases h2 : readBits L g t 32 (.reg 467) <;> rw [h2] at he <;> try contradiction
    rw [Lib.readBits_eq_pattern (holds_mem hF hi) h1,
      Lib.readBits_eq_pattern (holds_mem hF hn) h2] at he
    exact (Except.ok.inj he).symm
  · intro R hR
    exact ⟨Function.update_self .., holds_update hR (by fact_free)⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- When the initial counter already meets the signed upper bound, the named barrier
at entry transfers directly to the closing barrier (or to a terminal scalar fault). -/
theorem beginBar_skip (hskip : toSigned 32 (bits n) ≤ toSigned 32 (bits i)) :
    (code L g w regs).StepAtU ⟨.beginBar,i,n,a,b⟩ where
  site := fun _ => ⟨_, Flow.code_2346, rfl, trivial⟩
  step := by
    intro t e u ins ht _ hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2346)
    obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSync _ _) from trivial) hf
    let finish : D := ⟨.endBar,i,n,a,b⟩
    have cmp := compare_entry (L := L) (g := g) (w := w) (regs := regs) i n a b
    simp only [hskip, decide_true] at cmp
    have span : SegU kernel Assumptions.all L g 2347
        (entryFacts (L := L) (g := g) (w := w) (regs := regs) i n a b) 2419
        ((code L g w regs).facts finish) := by
      apply cmp.comp
      apply SegU.of_seg (n := 1)
      intro u hu
      dsimp only [entryFacts, finish, code] at hu ⊢
      seg_fp hu using rfl
    obtain ⟨v, hτ, hv⟩ := Code.landsU (C := code L g w regs) (d := finish)
      (At.next (Code.at_of_atD ht rfl rfl)) span (fun h => by cases h) rfl rfl
    exact .inl (.inr ⟨finish, v, by simp [next, hskip, finish], hτ, hv⟩)

end PTX.Kernels.InklingRelDecode.Proof.Loader
