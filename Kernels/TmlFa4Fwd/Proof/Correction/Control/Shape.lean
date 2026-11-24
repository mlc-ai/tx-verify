-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Ref
import Kernels.TmlFa4Fwd.Proof.Correction.Control.SchedulerProjection
import Kernels.TmlFa4Fwd.Proof.Correction.Control.ShapeArrive
import Kernels.TmlFa4Fwd.Proof.Correction.Control.ShapeBarrier
import Kernels.TmlFa4Fwd.Proof.Correction.Control.ShapeWait
import Kernels.TmlFa4Fwd.Proof.Correction.Control.ShapeStats
import Kernels.TmlFa4Fwd.Proof.Correction.Control.ShapeTensor
import Kernels.TmlFa4Fwd.Proof.Correction.Shapes
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Lemmas.Flow.BallotU

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow PTX.Proof

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

private theorem ballot_shape (v : V) (k : Fin 4) (st : Fin 2) :
    (code p L g).ShapeAt (fun d e => (∀ f, e.kind ≠ .ub f) → Ev p L g d e) ⟨.rvote st,v,k⟩ := by
  fin_cases st <;> intro t ins e o hat hi hc hf
  all_goals
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    refine shape_cont (P := fun e => (∀ f, e.kind ≠ .ub f) → ∃ pred b, e.kind = .vote (2^32-1)
        pred b) hf ⟨nofun, nofun⟩ (fun u h _ => ?_) (fun f h => (h f rfl).elim)
    obtain ⟨_, _, rfl, _⟩ := fires_ballotU h
    exact ⟨_, _, rfl⟩

theorem shapeAt (hp : Pre p L m) (d : D) :
    (code p L g).ShapeAt (fun d e => (∀ f, e.kind ≠ .ub f) → Ev p L g d e) d := by
  intro t ins e o hat hi hc hf hu
  by_cases hs : schedulerSite d.site = true
  · have he := Correction.shapeAt hp d.scheduler (scheduler_atD hs hat) hi hc hf
    exact Ev.of_data he
  obtain ⟨s,v,k⟩ := d
  cases s with
  | rbar st => exact shape_rbar hp v k st hat hi hc hf
  | fbar st => exact shape_fbar hp v k st hat hi hc hf
  | rvote st => exact ballot_shape v k st hat hi hc hf hu
  | rarr st a => exact shape_rarr hp v k st a hat hi hc hf
  | farr0 => exact shape_farr0 hp v k hat hi hc hf
  | farr st => exact shape_farr hp v k st hat hi hc hf
  | fdone st a => exact shape_fdone hp v k st a hat hi hc hf
  | fw st a => exact shape_fw hp v k st a hat hi hc hf
  | rwait st => exact shape_rwait v k st hat hi hc hf
  | fence st => exact shape_fence v k st hat hi hc hf
  | fsum st => exact shape_fsum v k st hat hi hc hf
  | fmax st => exact shape_fmax v k st hat hi hc hf
  | rscale st => exact shape_rscale v k st hat hi hc hf
  | lse h => exact shape_lse v k h hat hi hc hf
  | fld st j => exact shape_fld v k st j hat hi hc hf
  | rld st c => exact shape_rld v k st c hat hi hc hf
  | rldw st c => exact shape_rldw v k st c hat hi hc hf
  | rst st c => exact shape_rst v k st c hat hi hc hf
  | fwl st j => exact shape_fwl v k hp st j hat hi hc hf
  | fst st j h => exact shape_fst v k st j h hat hi hc hf
  | _ => exact (hs rfl).elim

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
