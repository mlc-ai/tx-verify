-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.NoUb
public import Kernels.TmlFa4Fwd.Proof.CorrWarp.ReadPayloads

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp

/-- Correction safety from the returned statistics words and TMEM vectors at their PCs. -/
theorem noUb_of_reads {p L m X g k e} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hr : ReadPayloads X)
    (hw : 8 ≤ Prologue.warpIndex L g ∧ Prologue.warpIndex L g ≤ 11)
    (he : X.get (g,k) = some e) (f : Fault) : e.kind ≠ .ub f :=
  noUb hp hX (dataSrc_of_reads hp hX hr) hw (Frame.lt_of_get hX he) rfl he f

end PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
