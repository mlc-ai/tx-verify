-- SPDX-License-Identifier: Apache-2.0
module

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib

/-- The two alternatives for a thread's final full-CTA rendezvous. -/
def finalSync (pc : Nat) : Bool := pc == 2850 || pc == 2853

/-- After that rendezvous a thread can only deallocate and return. -/
def afterFinal (pc : Nat) : Nat := if pc=2851 ∨ pc=2854 ∨ pc=2855 then 1 else 0

end PTX.Kernels.InklingRelDecode.Proof.Lib
