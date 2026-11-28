-- SPDX-License-Identifier: Apache-2.0
module

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib

/-- Shuffles of the Softmax rounds before round `i`: three in round zero, nine in each later
round. -/
def shflBase (i : Nat) : Nat := if i=0 then 0 else 9*i-6

theorem shflBase_lt {a b : Nat} (h : a < b) : shflBase a < shflBase b := by
  unfold shflBase
  split <;> split <;> omega

end PTX.Kernels.InklingRelDecode.Proof.Lib
