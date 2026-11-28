-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Export.Next
public import Kernels.InklingRelDecode.Proof.Top.Prog.LagReady
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.Preload

import Kernels.InklingRelDecode.Proof.Common.Export.Place
import Kernels.InklingRelDecode.Proof.Startup.Export.Mbar
import Kernels.InklingRelDecode.Proof.Prologue.Export.Mbar
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mbar
import Kernels.InklingRelDecode.Proof.Epilogue.Export.Mbar
import Kernels.InklingRelDecode.Proof.Dispatch.Export.Mbar
import Kernels.InklingRelDecode.Proof.Loader.Export.Row
import Kernels.InklingRelDecode.Proof.Mma.Export.Row

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX Protocol

/-- Assemble the role rows for each consistent execution, including the witness
execution of a next poll. Role placement follows from the same trace. -/
theorem mbarRows_of {Q L m} (hp : Pre Q L m)
    {X} (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) : MbarRows Q L X :=
  ⟨Startup.Export.mbarRow (Q := Q) hX, Prologue.Export.mbarRow hp hX hf,
   Softmax.Export.mbarRow hp hX hf,
   Epilogue.Export.mbarRow hp hX hf, Dispatch.Export.mbarRow hp hX hf,
   Loader.Export.mbarRow hp hX hf,
   Mma.Export.mbarRow hp hX hf, Export.mbar_place hp hX hf⟩

theorem initRows_of {Q L m X} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) : Mbar.InitRows L X := by
  have rows := mbarRows_of hp hX hf
  constructor
  rintro ⟨g,k⟩ e l he hm nu
  by_cases late : 574≤e.pc
  · exact Mbar.post_publication hp hX rows he hm late
  · exact Mbar.preload_published hp hX rows he hm (by omega) nu

end PTX.Kernels.InklingRelDecode.Proof.Top
