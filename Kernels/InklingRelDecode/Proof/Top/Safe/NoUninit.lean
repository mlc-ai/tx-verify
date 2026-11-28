-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.InitFirst
import Lemmas.Kernel.Safety.Init

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

theorem Safe.noUninit {L X} (init : Protocol.Mbar.InitRows L X) : ¬ MbarUninit L X := by
  rintro ⟨i,l,use,ordinary,missing⟩
  obtain ⟨ev,he,operand⟩ := Frame.usesMbar_mbarOf use
  exact missing (init.publication he operand (Frame.usesMbar_not_init he ordinary))

end PTX.Kernels.InklingRelDecode.Proof.Top
