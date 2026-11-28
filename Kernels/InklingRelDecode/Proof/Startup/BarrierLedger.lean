-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Startup.Shape
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Startup
open PTX PTX.Flow

def barriers : Site → Nat
  | .alloc | .allocWr | .bar0 => 0
  | .ld0 | .bar1 => 1
  | _ => 2

def Quiet (ev : Event) : Prop :=
  ev.pc<27 ∧ (∀ l, arrivesOn l ev=false) ∧ (∀ l, issuesTo l ev=false) ∧
    Execution.isBarId 1 ev=false

theorem startup_ledger {L g d dn ev} (shape : Ev L g d ev)
    (move : succ L g d ev=some (some dn)) :
    Quiet ev ∧ barriers dn.site=barriers d.site+(Execution.isBarId 0 ev).toNat := by
  obtain ⟨s,tm,x,w⟩ := d
  cases s
  all_goals simp only [Ev] at shape
  case enter => cases move
  case' allocWr => obtain ⟨_,_,rfl⟩ := shape
  case' ld0 => obtain ⟨_,_,rfl,_,_,_⟩ := shape
  case' shfl => obtain ⟨_,_,rfl⟩ := shape
  all_goals try subst ev
  all_goals simp only [succ] at move
  all_goals repeat' split at move
  all_goals cases move
  all_goals constructor
  all_goals first | rfl | exact ⟨by dsimp; decide,fun _ => rfl,fun _ => rfl,rfl⟩

end PTX.Kernels.InklingRelDecode.Proof.Startup
