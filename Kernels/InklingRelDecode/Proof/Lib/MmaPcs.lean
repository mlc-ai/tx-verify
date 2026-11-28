-- SPDX-License-Identifier: Apache-2.0
module

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Lib

/-- The program counter of the `j`-th QK issue of the MMA warp. -/
def qkIssue (j : Fin 8) : Nat := [2483,2486,2488,2490,2492,2494,2496,2498].getD j.val 0

/-- The program counter of the `j`-th PV issue of the MMA warp. -/
def pvIssue (j : Fin 8) : Nat := [2530,2533,2535,2537,2539,2541,2543,2545].getD j.val 0

end PTX.Kernels.InklingRelDecode.Proof.Lib
