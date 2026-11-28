-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Time
public import Kernels.InklingRelDecode.Proof.Softmax.Requests
public import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine
import Kernels.InklingRelDecode.Proof.Softmax.Strict.Pieces
import Kernels.InklingRelDecode.Proof.Softmax.Strict.Emu
import Kernels.InklingRelDecode.Proof.Softmax.Strict.Live
import Kernels.InklingRelDecode.Proof.Common.LateThread

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX

public theorem regBand {e t} {d} (inv : Softmax.Control.Inv e t d) :
    (Softmax.requestPhase d.site = 1 → Softmax.time d = 285) ∧
    (Softmax.requestPhase d.site = 2 → 285 < Softmax.time d ∧
      Softmax.time d ≤ Lib.Slots.finish) := by
  have lim : d.i < 2^32 := by
    have h1 := inv.bound
    have h2 := inv.entry.limitEq
    have h3 := inv.entry.blockWord
    split at h2 <;> omega
  have pos := Softmax.position_bound d.site
  obtain ⟨s,i,v⟩ := d
  refine ⟨fun h => ?_,fun h => ?_⟩
  · cases s <;> simp_all [Softmax.requestPhase, Softmax.time, Lib.Slots.enter]
  · cases s <;> simp_all [Softmax.requestPhase, Softmax.time, Lib.Slots.reuse,
      Lib.Slots.softmax, Lib.Slots.frame, Lib.Slots.stride, Lib.Slots.finish] <;> omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
