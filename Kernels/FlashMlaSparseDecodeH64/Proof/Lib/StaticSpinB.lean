-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Lemmas.Flow.WaitLoopPcs

@[expose] public section

/-! # The wait loops of the polls 2209 to 2684

The library's wait-loop check (`Kernel.waitLoopPcs`) reads the whole code at every poll, so it is
evaluated two polls at a time (`Lib/StaticPoll.lean` combines the halves). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

set_option maxRecDepth 100000 in
theorem waitLoops4 : kernel.waitLoopPcs [2209, 2234] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem waitLoops5 : kernel.waitLoopPcs [2245, 2446] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem waitLoops6 : kernel.waitLoopPcs [2534, 2644] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem waitLoops7 : kernel.waitLoopPcs [2677, 2684] = true := by
  decide +kernel

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
