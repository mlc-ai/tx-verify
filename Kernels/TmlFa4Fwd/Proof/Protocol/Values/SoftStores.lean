-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StoreVals
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Read
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Ordered
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values

/-- Each P store packs two BF16 numbers per cell once the preceding loads return f32. -/
theorem softStores {p L m X} (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow p L X) : SoftStores L X :=
  Softmax.softStores_of_bias hp hX hf
    (biasReadHandoff hp hX hf (inputsUnwritten hp (Top.noInputWrite hp hX hf))
      (biasWrites hp hX hf))

end PTX.Kernels.TmlFa4Fwd.Proof.Values
