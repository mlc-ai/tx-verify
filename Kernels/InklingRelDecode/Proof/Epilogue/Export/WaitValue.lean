-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Control.Machine

@[expose] public section

/-! # The registers the epilogue's wait site tracks

At the site of the epilogue's poll (pc 2565) the tracked registers 173 and 1760 hold the entry's
skip flag and the zero word. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
open PTX PTX.Proof

public theorem wait_live : 173 ∈ Control.ctlLive 2565 ∧ 1760 ∈ Control.ctlLive 2565 := by
  decide +kernel

public theorem value_skip {e : Control.Entry} {L : Launch} {g : Nat} {v : Value} :
    Control.valueOf e L g v 173 = .pred e.skip := rfl

public theorem value_zero {e : Control.Entry} {L : Launch} {g : Nat} {v : Value} :
    Control.valueOf e L g v 1760 = b32 0 := rfl

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
