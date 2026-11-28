-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

public import Kernels.InklingRelDecode.Proof.Top.Assembly
public import Kernels.InklingRelDecode.Proof.Top.Safety
public import Kernels.InklingRelDecode.Proof.Top.Bound
import Kernels.InklingRelDecode.Proof.Top.Result.Entry

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

theorem correct (hp : Pre Q L m) :
    Correct kernel Assumptions.all L m (Post Q m) := by
  apply correct_of (safe hp) (progress hp) (Bound.terminates hp fun _ => followed hp)
  intro X mf hX hc hm
  have hf := followed hp hX
  obtain ⟨hn, hz⟩ := Result.lse hp hX hm (Result.lseRest hp (Result.entry hp)) hc hf
  exact ⟨Result.output hp hX hm (Result.outputRest hp (Result.entry hp)) hc hf, hn, hz,
    Result.frame hp hX hm (Result.output_placed hp hX hf)⟩

end PTX.Kernels.InklingRelDecode.Proof.Top
