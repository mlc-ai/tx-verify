-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Ballot
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Barrier
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Lse
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Poll
import Kernels.TmlFa4Fwd.Proof.Correction.Control.RescaleStore
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Round
import Kernels.TmlFa4Fwd.Proof.Correction.Control.SchedulerProjection
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Statistics
import Kernels.TmlFa4Fwd.Proof.Correction.Control.StoreLast
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Tensor
import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorWait
import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorRld0
import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorRld1
import Kernels.TmlFa4Fwd.Proof.Correction.Steps

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control

private theorem invalid {p L g d} (h : ¬ (code p L g).inv d) : (code p L g).StepAtU d :=
  ⟨fun hi => (h hi).elim, fun _ _ hi => (h hi).elim⟩

private theorem implicit_zero {p L g} (st : Fin 2) (c : Fin 8) (v : V) :
    (code p L g).StepAtU ⟨.rldw st c,v,0⟩ := by
  have ht : loadOk (.rld st c) (.rldw st c) true = true := by
    fin_cases st
    · exact rld_table0 c
    · exact rld_table1 c
  obtain ⟨_, _, hc, _, _⟩ := load_of_ok ht
  exact ⟨fun _ => ⟨_, hc, rfl, trivial⟩, fun _ _ _ _ _ => .inl (.inl rfl)⟩

/-- Every state of the correction control machine satisfies its relaxed step obligation. -/
theorem stepAtU {p L m g} (hp : Pre p L m) (hg : g < L.threads) (d : D) :
    (code p L g).StepAtU d := by
  by_cases hsched : schedulerSite d.site = true
  · by_cases hx : d.site = .nb 1
    · obtain ⟨s,v,k⟩ := d
      cases hx
      by_cases h0 : k = 0
      · subst k
        exact stepAt_nb_enterU hp v
      · exact invalid (fun hi => hi.elim h0 id)
    · exact project_scheduler d (Correction.stepAt hp hg d.scheduler) hsched hx
  obtain ⟨s,v,k⟩ := d
  by_cases hv : k = 0 ∨ s.midOk k
  swap
  · exact invalid hv
  cases s with
  | fst st j h => exact stepAt_fstU st j h k v
  | rldw st c =>
    rcases hv with rfl | h1
    · exact implicit_zero st c v
    · change k = 1 at h1
      subst k
      exact stepAt_rldwU st c v
  | rbar st => exact (hv.elim id False.elim) ▸ stepAt_rbarU st v
  | rscale st => exact (hv.elim id False.elim) ▸ stepAt_rscaleU st v
  | rvote st => exact (hv.elim id False.elim) ▸ stepAt_rvoteU st v
  | rld st c => exact (hv.elim id False.elim) ▸ stepAt_rldU st c v
  | rst st c => exact (hv.elim id False.elim) ▸ stepAt_rstU st c v
  | rwait st => exact (hv.elim id False.elim) ▸ stepAt_rwaitU st v
  | rarr st i =>
    obtain rfl := hv.elim id False.elim
    fin_cases i
    · exact stepAt_rarr_firstU st v
    · fin_cases st
      · exact stepAt_rarr_switchU v
      · exact stepAt_round_endU hp v
  | farr0 => exact (hv.elim id False.elim) ▸ stepAt_farr0U v
  | fbar st => exact (hv.elim id False.elim) ▸ stepAt_fbarU st v
  | fsum st => exact (hv.elim id False.elim) ▸ stepAt_fsumU st v
  | fmax st => exact (hv.elim id False.elim) ▸ stepAt_fmaxU st v
  | farr st => exact (hv.elim id False.elim) ▸ stepAt_farrU st v
  | fw st i => exact (hv.elim id False.elim) ▸ stepAt_fwU st i v
  | fld st j => exact (hv.elim id False.elim) ▸ stepAt_fldU st j v
  | fwl st j => exact (hv.elim id False.elim) ▸ stepAt_fwlU st j v
  | fence st => exact (hv.elim id False.elim) ▸ stepAt_fenceU st v
  | fdone st i =>
    obtain rfl := hv.elim id False.elim
    fin_cases i
    · exact stepAt_fdone_firstU st v
    · fin_cases st
      · exact stepAt_fdone_switchU v
      · exact stepAt_fdone_lseU hp v
  | lse i => exact (hv.elim id False.elim) ▸ stepAt_lseU hp i v
  | _ => exact (hsched rfl).elim

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
