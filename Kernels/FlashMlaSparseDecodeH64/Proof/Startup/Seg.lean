-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamSteps
public import Lemmas.Flow.Step.SiteCases
public import Kernels.FlashMlaSparseDecodeH64.Gen.StepStartup

@[expose] public section

/-! # The startup's segment tactic

`st_seg hp` closes a segment goal of the startup by evaluation (`seg_fp`, with the generated
`step_<pc>` lemmas), then the table's values: the launch reads by `launch_norm`, the remaining
word equations by `rfl` or `decide`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

/-- A startup segment: evaluate it and close the table's values. -/
syntax "st_seg" term:max : tactic
macro_rules
  | `(tactic| st_seg $hp) => `(tactic| (
      intro t h
      have hbase := sharedBase_lt $hp
      seg_fp h using
        try simp only [valueOf, values, entryVal, entryVals, PTX.Flow.lookupLit,
          Option.getD_some, Option.getD_none, List.cons_append, List.nil_append]
        all_goals (try launch_norm $hp)
        all_goals (try seg_close [sb])
        all_goals (try simp only [b32, sb, Value.bits.injEq, true_and])
        all_goals decide +kernel))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
