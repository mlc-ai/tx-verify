-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Lemmas.Flow.Roles
public import Tactics.KernelRfl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue
open PTX PTX.Flow

inductive Site where
  | wait | shfl | load | waitLd | lse | store (k : Fin 64)
  | join | setMax | roleWord | sync1 | sync0 | dealloc | exit
  deriving DecidableEq

def storePc (k : Nat) := 2751+k+k/2

def Site.pc : Site → Nat
  | .wait => 2565 | .shfl => 2603 | .load => 2607 | .waitLd => 2608 | .lse => 2682
  | .store k => storePc k | .join => 2846 | .setMax => 2847 | .roleWord => 2848
  | .sync1 => 2849 | .sync0 => 2850 | .dealloc => 2851 | .exit => 2855

def allSites : List Site :=
  [.wait,.shfl,.load,.waitLd,.lse] ++ (List.finRange 64).map Site.store ++
    [.join,.setMax,.roleWord,.sync1,.sync0,.dealloc,.exit]

def region : RoleDecl := ⟨[(2565,2853),(2855,2856)],[]⟩

theorem sites_pcs : allSites.map Site.pc = RoleDecl.sites kernel region := by kernel_rfl
theorem sites_nodup : (allSites.map Site.pc).Nodup := by decide +kernel

theorem Site.pc_range (s : Site) : 2565≤s.pc ∧ s.pc≤2855 := by
  cases s <;> first | decide | (rename_i k; revert k; decide +kernel)

end PTX.Kernels.InklingRelDecode.Proof.Epilogue
