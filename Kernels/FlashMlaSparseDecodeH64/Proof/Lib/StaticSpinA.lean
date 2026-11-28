-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Lemmas.Flow.WaitLoopPcs

@[expose] public section

/-! # The wait loops of the polls 264 to 2205

The library's wait-loop check (`Kernel.waitLoopPcs`) reads the whole code at every poll, so it is
evaluated two polls at a time (`Lib/StaticPoll.lean` combines the halves). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

set_option maxRecDepth 100000 in
theorem waitLoops0 : kernel.waitLoopPcs [264, 272] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem waitLoops1 : kernel.waitLoopPcs [1184, 1931] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem waitLoops2 : kernel.waitLoopPcs [1983, 2012] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem waitLoops3 : kernel.waitLoopPcs [2107, 2205] = true := by
  decide +kernel

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
