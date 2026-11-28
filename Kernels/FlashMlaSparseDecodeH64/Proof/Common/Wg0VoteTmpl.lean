-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.Stage
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Lemmas.Flow.Step.ShapeClasses

@[expose] public section

/-! # Warpgroup 0's vote names the full mask (`w0_vote_tmpl`)

The vote's mask register (`%r1112`) holds `2 ^ 32 - 1` at the vote site: the template is a
fault or the `.any` vote with that mask and the lane's predicate. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow Control

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- **Warpgroup 0's vote site** has a template that is undefined behaviour or the `.any` vote
with the full mask. -/
theorem w0_vote_tmpl (d : D) (hs : d.site = .vote) :
    ∀ t ins, (code P L g w).AtD d t → (code P L g w).inv d → kernel.code[(code P L g w).pc d]? =
      some ins → (∃ f, eventTmpl Assumptions.all L g t ins.op = .ub f) ∨
        ∃ a k, eventTmpl Assumptions.all L g t ins.op = .voteMode .any (2 ^ 32 - 1) a k ∧
          t.pc = 578 := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  intro t ins hat _ hc
  obtain ⟨hpc, -, -, -, hF⟩ := hat
  w0_body
  have hm := readBits_reg (L := L) (g := g) (rg 1112)
  have hmn : (truncBits 32 (Arith32.i32 (-1))).toNat = 2 ^ 32 - 1 := by decide +kernel
  change (∃ f, voteModeTmpl L g t .any 1 109 false (.reg 1112) = .ub f) ∨
    ∃ a k, voteModeTmpl L g t .any 1 109 false (.reg 1112) = .voteMode .any (2 ^ 32 - 1) a k ∧
      t.pc = 578
  simp only [voteModeTmpl, hm]
  cases hp : readPred L g t (.reg 109) with
  | error f => exact .inl ⟨f, rfl⟩
  | ok p =>
    simp only [hmn]
    split_ifs
    · exact .inr ⟨_, _, rfl, hpc⟩
    · exact .inl ⟨_, rfl⟩
    · exact .inl ⟨_, rfl⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
