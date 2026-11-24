-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvDAll
public import Kernels.InklingRelDecode.Proof.Thread.DStartBase
public import Kernels.InklingRelDecode.Proof2.Lib.PtcEvent
public import Kernels.InklingRelDecode.Proof.Thread.EvWAll
public import Kernels.InklingRelDecode.Proof.Thread.ShapeProCopy

@[expose] public section

/-!
# The prologue's K/V copies name the `kv_desc` map (thread layer)

`ProA.shape_ptc` leaves the map address of the prologue's twelve tensor copies as some `a` the
launch publishes a map at. The instruction's map operand is the register `%rd1` (`ptc_mapReg`,
an audit by `decide +kernel`), and the prologue's inherited `%rd1` is the pointer to the kernel
parameter `kv_desc` (`DStart.inh`), which `Pre.paramKv` ties to `Q.kvMap`. So the event is the
tensor issue of `Q.kvMap` with `EvW.kvCopySpec`, the same spec the loader's copies have
(`ptc_event`). The statement names the prologue's inherited registers `DStart.inh`, not a
register; `Interface/ShapeCopy.lean` derives `KvMapOnly` from it.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- **A prologue copy is the tensor issue of `Q.kvMap`.** At the copy site `i`, given that the
inherited `%rd1` is the pointer to `kv_desc`, the event is the tensor issue of the `kv_desc` map
with `EvW.kvCopySpec` at the box origin `(copyX, copyY)` (words), the destination `copyDst`
and the barrier `kv_ready (i / 4)` of the thread's CTA. -/
theorem ptc_event (hpre : Pre Q L mem0) {d : ProA.D} {e : Event} {u : TState} {i tm : Nat}
    (hi : i < 12) (hpro : d.dt.pro = DStart.inh L g Q tm)
    (hF : ProA.Fired L g d e (some u)) (hs : d.site = ProA.ptcSite i) :
    e = ⟨ProA.evPc d.site, .tensorIssue Q.kvMap
      (EvW.kvCopySpec Q (g / L.block) (ProA.copyX L g d.dt i) (ProA.copyY L g d.dt i)
        (ProA.copyDst L g d.dt i) ((EvD.kvReadyOf (i / 4)).loc L (g / L.block)))⟩ :=
  ptc_event_map hpre hi (by rw [hpro]; rfl) hF hs

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
