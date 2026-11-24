-- SPDX-License-Identifier: Apache-2.0
module

public import Tests.Gen.Step.FlashMlaIndex
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.SegChain

/-! # A piece checked by step lemmas

`seg_fp` on a piece of FlashMLA's index code (pc 2358, a `mul.wide.u32` with its step lemma in
`Tests/Gen/Step/FlashMlaIndex.lean`) builds the run from the lemmas (`stepChain`), not by
evaluating the code. -/

namespace PTX.Tests.StepUse
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64

set_option linter.unusedTactic false

set_option Elab.async false in
theorem piece (L : Launch) (g : Nat) (x : BitVec 64) :
    Seg kernel Assumptions.all L g 1 2358 [(460, .bits 32 x)] 2359
      [(3024, .bits 64 (BitVec.ofNat 64 ((truncBits 32 x).toNat * 4))), (460, .bits 32 x)] := by
  intro t h
  seg_fp h using rfl

-- the piece's proof is the chain of step lemmas
open Lean in
run_meta do
  let some ci := ((← getEnv).setExporting false).find? ``piece | throwError "no theorem `piece`"
  let v ← match ci with
    | .thmInfo t => pure t.value
    | .axiomInfo _ => throwError "`piece` is an axiom here"
    | _ => throwError "`piece` is not a theorem"
  unless (v.find? (·.isConstOf ``PTX.Flow.run_succ_local)).isSome do
    throwError "the piece is not proved by the step lemmas"

end PTX.Tests.StepUse
