-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.Stats
public import Lemmas.Flow.SignedBits

@[expose] public section

/-! # Softmax segments with signed integer values

`sm_segs` evaluates a softmax segment as `sm_seg` does and closes the facts the signed integer
rules compute (`shr.s32`, `setp.*.s32`, the masks of a ceiling division) by `norm_signed`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

/-- Evaluate a softmax segment with the signed normal form (`norm_signed`) besides `sm_seg`'s
closers. The item register's operations (`w_rfl`) come last because its unfolding `rfl` can
exceed the recursion depth on a goal that another closer proves. -/
syntax "sm_segs" term:max term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| sm_segs $h $hpre $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      have hbase := ($hpre).sharedRange
      unfold sharedBytes at hbase
      seg_fp $h using
        try simp only [valueX, valueOf, ctrlValues, floatValues, PTX.Flow.lookupLit,
          Option.getD_some, Option.getD_none, Prologue.sb, Prologue.valueOf, Prologue.values,
          List.lookup_cons, List.lookup_nil, Nat.reduceBEq]
        all_goals (try launch_norm $hpre)
        all_goals first
          | with_reducible rfl
          | tmem_close
          | norm_signed [stOf, kOf, statsIdx, $extra,*]
          | seg_close [stOf, kOf, statsIdx, $extra,*]
          | w_rfl))

end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
