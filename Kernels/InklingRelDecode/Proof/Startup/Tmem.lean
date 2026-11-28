-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Startup.Shape
public import Lemmas.Tmem.PairProtocol

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Startup
open PTX PTX.Tmem.Pair

def resourceCount (t : Nat) (s : Site) : Nat :=
  if 32≤t then 0 else match s with
  | .alloc => 0
  | .shfl | .enter _ => 2
  | _ => 1

theorem resource_init (L : Launch) (g : Nat) : resourceCount (g%L.block) (init L g).site=0 := by
  unfold init
  split <;> simp_all [resourceCount]

theorem resource_next {L g d sn ev} (inv : Inv L g d) (shape : Ev L g d ev)
    (step : succ L g d ev=some (some sn)) :
    resourceCount (g%L.block) sn.site = resourceCount (g%L.block) d.site+(isTmemOp ev).toNat := by
  obtain ⟨s,t,x,w⟩ := d
  cases s
  case enter => cases step
  case' allocWr => obtain ⟨_,_,rfl⟩ := shape
  case' ld0 => obtain ⟨_,_,rfl,_⟩ := shape
  case' shfl => obtain ⟨_,_,rfl⟩ := shape
  all_goals try subst ev
  all_goals simp only [succ] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals by_cases low : g%L.block<32
  all_goals simp_all [Inv,resourceCount,isTmemOp]
  rw [ite_eq_right (by omega),ite_eq_right (by omega)]

end PTX.Kernels.InklingRelDecode.Proof.Startup
