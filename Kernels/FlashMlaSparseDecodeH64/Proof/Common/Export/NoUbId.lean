-- SPDX-License-Identifier: Apache-2.0
module

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof

/-- The roles of the thread machine (warpgroup 1's head and idle code are one). -/
inductive RoleId where
  | startup | wg1 | mma | tma | index | dequant | wg0

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
