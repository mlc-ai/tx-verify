-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.RefGate
public import Kernels.InklingRelDecode.Proof.Lib.CollectiveAt

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open Prologue.Control

/-- Elections of the prologue before the site: twelve for the mbarrier initializations, then four
for each preloaded block, at `pel`. -/
def electPosition (p : Nat) : Site → Nat
  | .sMax | .ld _ => 0
  | .el i => i.val
  | .init i => i.val+1
  | .fnc0 | .bar2 => 12
  | .pb b j => 12+4*b.val+(if j.val ≤ 1 then 0 else j.val-1)
  | .arr b | .lb b 0 | .psh b => 12+4*b.val
  | .lb b 1 => 12+4*b.val+2
  | .pel b j => 12+4*b.val+j.val
  | .ptc b j => 12+4*b.val+j.val+1
  | _ => 12+4*p

def Site.isElect : Site → Bool
  | .el _ | .pel .. => true
  | _ => false

/-- A step from an election site is made on an election event. -/
theorem elect_kind {Q L g d dn ev} (move : Control.next Q L g d ev=some (some dn))
    (h : d.site.isElect=true) : ∃ mask inst lead, ev.kind=.elect mask inst lead := by
  obtain ⟨s,f,l,q,e,b⟩ := d
  cases s <;> simp only [Site.isElect, Bool.false_eq_true] at h <;>
    simp only [Control.next] at move <;> split at move <;> first | contradiction | exact ⟨_,_,_,‹_›⟩

/-- No other site of the prologue can record an election. -/
theorem canElect_off (s : Site) (h : s.isElect=false) : Lib.canElect s.pc=false := by
  cases s <;> first | (revert h; decide +kernel) |
    (rename_i j; revert j h; decide +kernel) | (rename_i b j; revert b j h; decide +kernel)

end PTX.Kernels.InklingRelDecode.Proof.Prologue
