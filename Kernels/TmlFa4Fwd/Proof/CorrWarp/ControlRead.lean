-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Shape
public import Kernels.TmlFa4Fwd.Proof.CorrWarp.EvR
import Kernels.TmlFa4Fwd.Proof.Correction.Control.SchedulerProjection
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Read

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow PTX.Proof

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem read_shapeAt (hp : Pre p L m) (d : D) :
    (code p L g).ShapeAt (fun d => CorrWarp.EvR p L g d.scheduler) d := by
  intro t ins e o hat hi hc hf
  by_cases hs : schedulerSite d.site = true
  · exact CorrWarp.shapeR hp (d := d.scheduler) (scheduler_atD hs hat) hi hc hf
  obtain ⟨s,v,k⟩ := d
  cases s <;> first | exact True.intro | exact (hs rfl).elim

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
