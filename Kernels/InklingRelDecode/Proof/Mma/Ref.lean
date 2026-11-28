-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Ledger

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow

/-- Integer interpretation of the shared loop bound, allowing every value with this pattern. -/
def readsCount (v : Value) (n : Nat) : Prop :=
  v.regBits.isSome ∧ low v = n

def Site.hasCount : Site → Bool
  | .setMaxReg | .ldNum => false
  | _ => true

def Ref (n : Nat) (d : D) : Prop := d.site.hasCount → readsCount d.word n

theorem initial_ref (n : Nat) : Ref n {} := by intro h; cases h

theorem ref_count {n : Nat} {d : D} (hr : Ref n d) (hc : d.site.hasCount) :
    d.limit = n := (hr hc).right

end PTX.Kernels.InklingRelDecode.Proof.Mma
