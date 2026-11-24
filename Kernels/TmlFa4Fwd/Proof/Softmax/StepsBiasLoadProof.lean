-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.BiasUnpack
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # The last element of a bias load

At sub-step 3 a bias load reads its fourth word; the machine accepts it when it is two `bf16`
payloads or masked halves (`biasOk`, the return kind `.packedWith .bf16`), records the halves of
the four words (`recordBias`) and the code unpacks the words (pcs `pc + 1` to `pc + 4`, the last
word first) before the next load or the fence. The unpacks are four pieces (`seg_unpack`, the
three earlier words accepted by the invariant); the remaining facts are checked by `seg_sym`
without a step. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A program counter that no segment assumption takes (the software `exp2` sites are later). -/
macro "bias_seg_free" : tactic => `(tactic| (
  repeat' (first
    | exact PTX.Assumption.SegFreePc.nil
    | refine PTX.Assumption.SegFreePc.cons ?_ ?_)
  all_goals first
    | seg_free_elem
    | (intro L g t ht; simp only [PTX.Kernels.TmlFa4Fwd.Assumptions.swExp2, ht]; simp
       intro h; exact absurd h (by decide))))

/-- The last element of a bias load at state `⟨.bld b c, v, 3, [a0, a1, a2]⟩` (an override). -/
syntax "soft_bld3" : tactic
macro_rules
  | `(tactic| soft_bld3) => `(tactic| (
      refine PTX.Flow.Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
      refine' (PTX.Flow.Code.step_ldv_last_sel (nv := ?nv) ?hc ?hk ?hnc ?he ?hsub ?hnd
        ?hok ?herr ?hnn ?hl)
      case hc => code_lookup
      case hk => rfl
      case hnc => rfl
      case he => rfl
      case hsub => exact of_decide_eq_false rfl
      case hnd => decide
      case hok => intro x bs v hv; simp only [codeD, succ, hv]; rfl
      case herr => intro x bs f hv; left; simp only [codeD, succ, hv]
      case hnn => intro v; beta_reduce; (repeat' split) <;> simp
      case hl =>
        intro x d' hv
        beta_reduce at hv
        split at hv
        · rename_i hx
          have hd := Option.some.inj (Option.some.inj hv)
          subst hd
          refine ⟨fun hi => ?_, by rfl, by rfl,
            fun _ => by (repeat' split) <;> exact Or.inl ⟨rfl, rfl, rfl⟩⟩
          have hacc : _ := hi.resolve_left (by simp)
          simp only [Site.midOk, List.all_cons, List.all_nil, Bool.and_true,
            Bool.and_eq_true] at hacc
          obtain ⟨-, h0, h1, h2⟩ := hacc
          simp only [codeD]
          vec_facts_norm
          refine PTX.Flow.Seg.comp_ex (PTX.Kernels.TmlFa4Fwd.Proof.Softmax.seg_unpack
            (by code_lookup) (by bias_seg_free) (by simp) hx (by fresh_keys)) ?_
          refine PTX.Flow.Seg.comp_ex (PTX.Kernels.TmlFa4Fwd.Proof.Softmax.seg_unpack
            (by code_lookup) (by bias_seg_free) (by simp) h2 (by fresh_keys)) ?_
          refine PTX.Flow.Seg.comp_ex (PTX.Kernels.TmlFa4Fwd.Proof.Softmax.seg_unpack
            (by code_lookup) (by bias_seg_free) (by simp) h1 (by fresh_keys)) ?_
          refine PTX.Flow.Seg.comp_ex (PTX.Kernels.TmlFa4Fwd.Proof.Softmax.seg_unpack
            (by code_lookup) (by bias_seg_free) (by simp) h0 (by fresh_keys)) ?_
          site_norm
          try drop_norm
          seg_sym using (soft_seg)
        · cases hv))

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
