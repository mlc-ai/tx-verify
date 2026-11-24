-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Open
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Post
public import Kernels.TmlFa4Fwd.Proof.Top.Base
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.CompleteSoft
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Final
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.LinksAll

@[expose] public section

/-! # F2: the stored log-sum-exp values

`Res.lse`: the log-sum-exp values of a complete execution (`Values.LseWriteValues`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX

variable {p : Params} {l : Launch} {m : Mem0}

/-- **The log-sum-exp values of a complete execution.** -/
theorem Res.lse (hp : Pre p l m)
    {X : Execution} (hX : Consistent l kernel Assumptions.all m X) (hC : Complete l X) :
    Values.LseWriteValues p X := by
  have hFw := launchFollow hp hX
  obtain ⟨D, hLL, hV⟩ := Values.lseLinks hp hX hFw hC (Values.softLink hp hX hFw hC)
    (Values.rowFinite hp hX hFw hC)
  have hL := hLL.links hp hX hFw (inputsUnwritten hp (noInputWrite hp hX hFw))
  have hO := Values.lseRoute hp hX hFw hV
  intro i a bytes hw hg
  obtain ⟨c, t, st, ρ, hT, hst, hρ, hv, hloc, hsize, hbytes⟩ := hO i a bytes hw hg
  have hok := (hL.tile c t hT).2
  refine ⟨t.batch, hok.batch, t.head, hok.head, t.rowOf st ρ, hv, hloc, hsize, ?_⟩
  rw [hbytes, Values.row_lse hp hX hFw hL hT hst hρ hv]

end PTX.Kernels.TmlFa4Fwd.Proof.Top
