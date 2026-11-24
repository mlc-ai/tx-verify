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

/-! # F1: the stored output tile values

`Res.output`: the output tile values of a complete execution (`Values.OutputValues`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX

variable {p : Params} {l : Launch} {m : Mem0}

/-- **The output tile values of a complete execution.** -/
theorem Res.output (hp : Pre p l m)
    {X : Execution} (hX : Consistent l kernel Assumptions.all m X) (hC : Complete l X) :
    Values.OutputValues p X := by
  have hFw := launchFollow hp hX
  obtain ⟨D, hLL, hV⟩ := Values.outputLinks hp hX hFw hC (Values.softLink hp hX hFw hC)
    (Values.rowFinite hp hX hFw hC)
  have hL := hLL.links hp hX hFw (inputsUnwritten hp (noInputWrite hp hX hFw))
  have hO := Values.outRoute hp hX hFw hV
  intro b hb h hh row hr d hd k hk w a bytes hw hc
  obtain ⟨t, st, g, i, ad, j, x, vals, hT, rfl, rfl, hst, h8, h12, rfl, hld, hj, hcol, hpa, hx,
    hbyte⟩ := hO b hb h hh row hr d hd k hk w a bytes hw hc
  rw [hbyte, Values.final_attention hp hX hFw hL hT hst h8 h12 hd hr hld hj hcol hpa
    hx]

end PTX.Kernels.TmlFa4Fwd.Proof.Top
