-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.ProjectStep
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Project0
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Project1
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Project2
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Project3
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Project4

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control

theorem projects {p L g} (d : Softmax.D) : Projects (p := p) (L := L) (g := g) d := by
  obtain ⟨s,v,k,acc⟩ := d
  cases s with
  | setmax => exact project_setmax v k acc
  | bar1 => exact project_bar1 v k acc
  | word x0 => exact project_word v k acc x0
  | down x0 => exact project_down v k acc x0
  | up x0 x1 => exact project_up v k acc x0 x1
  | total x0 => exact project_total v k acc x0
  | vote x0 => exact project_vote v k acc x0
  | pre x0 => exact project_pre v k acc x0
  | tiles x0 => exact project_tiles v k acc x0
  | q0 => exact project_q0 v k acc
  | q1 => exact project_q1 v k acc
  | uk => exact project_uk v k acc
  | wq => exact project_wq v k acc
  | ws x0 => exact project_ws v k acc x0
  | sld x0 x1 => exact project_sld v k acc x0 x1
  | sldw x0 => exact project_sldw v k acc x0
  | wb x0 => exact project_wb v k acc x0
  | bld x0 x1 => exact project_bld v k acc x0 x1
  | fence x0 => exact project_fence v k acc x0
  | bsync x0 => exact project_bsync v k acc x0
  | barr x0 => exact project_barr v k acc x0
  | stat x0 => exact project_stat v k acc x0
  | narr x0 => exact project_narr v k acc x0
  | pst x0 x1 => exact project_pst v k acc x0 x1
  | pwst x0 x1 => exact project_pwst v k acc x0 x1
  | parr x0 => exact project_parr v k acc x0
  | pws x0 => exact project_pws v k acc x0
  | pel x0 => exact project_pel v k acc x0
  | parr2 x0 => exact project_parr2 v k acc x0
  | pwend r => exact project_pwend v k acc r
  | fin x0 => exact project_fin v k acc x0
  | finarr => exact project_finarr v k acc
  | wend x0 => exact project_wend v k acc x0
  | barEnd x0 => exact project_barEnd v k acc x0
  | exit x0 => exact project_exit v k acc x0

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
