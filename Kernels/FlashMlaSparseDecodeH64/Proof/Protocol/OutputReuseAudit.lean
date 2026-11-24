-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmCompletion
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmFirstWriteOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputVisits
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2Events
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaDataTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PvIssueHistory

@[expose] public section

/-! # The first output tile aliases the second dequantization slot -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputReuseAudit

open PTX PTX.Flow Wg0 AsyncCopy

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputReuseAudit
