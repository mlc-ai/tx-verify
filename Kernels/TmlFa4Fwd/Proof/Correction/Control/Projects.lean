-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.ProjectStep
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Project0
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Project1
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Project2
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Project3
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Project4

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control

theorem projects {p L g} (d : Correction.D) : Projects (p := p) (L := L) (g := g) d := by
  obtain ⟨s,v,k⟩ := d
  cases s with
  | setmax => exact project_setmax v k
  | bar1 => exact project_bar1 v k
  | arr x0 => exact project_arr v k x0
  | word x0 => exact project_word v k x0
  | down x0 => exact project_down v k x0
  | up x0 x1 => exact project_up v k x0 x1
  | total x0 => exact project_total v k x0
  | vote x0 => exact project_vote v k x0
  | pre x0 => exact project_pre v k x0
  | tiles x0 => exact project_tiles v k x0
  | q0 => exact project_q0 v k
  | q1 => exact project_q1 v k
  | uk => exact project_uk v k
  | nb x0 => exact project_nb v k x0
  | free => exact project_free v k
  | rbar x0 => exact project_rbar v k x0
  | rscale x0 => exact project_rscale v k x0
  | rvote x0 => exact project_rvote v k x0
  | rld x0 x1 => exact project_rld v k x0 x1
  | rldw x0 x1 => exact project_rldw v k x0 x1
  | rst x0 x1 => exact project_rst v k x0 x1
  | rwait x0 => exact project_rwait v k x0
  | rarr x0 x1 => exact project_rarr v k x0 x1
  | farr0 => exact project_farr0 v k
  | fbar x0 => exact project_fbar v k x0
  | fsum x0 => exact project_fsum v k x0
  | fmax x0 => exact project_fmax v k x0
  | farr x0 => exact project_farr v k x0
  | fw x0 x1 => exact project_fw v k x0 x1
  | fld x0 x1 => exact project_fld v k x0 x1
  | fwl x0 x1 => exact project_fwl v k x0 x1
  | fst x0 x1 x2 => exact project_fst v k x0 x1 x2
  | fence x0 => exact project_fence v k x0
  | fdone x0 x1 => exact project_fdone v k x0 x1
  | lse x0 => exact project_lse v k x0
  | wend x0 => exact project_wend v k x0
  | barEnd x0 => exact project_barEnd v k x0
  | exit x0 => exact project_exit v k x0

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
