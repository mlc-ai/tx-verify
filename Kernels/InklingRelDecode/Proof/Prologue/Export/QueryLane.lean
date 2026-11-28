-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.PrologueEvent

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX

/-- A query store comes from a default-partition lane. -/
public theorem query_lane {Q L m X g k a bs} {i : Fin 8} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k)=some ⟨526+6*i.val,.wr a bs⟩) : g%L.block<128 := by
  have := i.isLt
  obtain ⟨_,_,_,_,_,_,_,_,_,_,lane,_⟩ := prologue_event hp hX hf he (fun _ => nofun)
    (by simp only; omega) (by simp only; omega)
  exact lane

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
