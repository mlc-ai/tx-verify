-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Prog.Classes
public import Kernels.InklingRelDecode.Proof.Startup.Export.CollLast
public import Kernels.InklingRelDecode.Proof.Prologue.Export.CollLast
public import Kernels.InklingRelDecode.Proof.Softmax.Export.CollLast
public import Kernels.InklingRelDecode.Proof.Epilogue.Export.CollLast
public import Kernels.InklingRelDecode.Proof.Dispatch.Export.CollLast
public import Kernels.InklingRelDecode.Proof.Loader.Export.CollLast
public import Kernels.InklingRelDecode.Proof.Mma.Export.CollLast

/-! # What follows a blocking event

Every fault-free blocking event of a lane, whichever role makes it, is followed by a state of a
machine that has not stopped, and a state at a warp collective only after one of the events that
directly precede one (`Lib.pairs`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Flow PTX.Frame

public theorem Prog.block_any {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g, k) = some e) (hu : ∀ f, e.kind ≠ .ub f) (nu : NoUbBefore X g k)
    (hb : e.pc ∈ Lib.blockPcs) :
    Lib.BlockFacts (schedule Q L).code (CollAt Q L) X g k e := by
  by_cases h1 : e.pc < 27
  · exact Startup.Export.block hp hX hf he hu nu h1 hb
  by_cases h2 : e.pc < 574
  · exact Prologue.Export.block hp hX hf he hu nu ⟨by omega, h2⟩ hb
  by_cases h3 : e.pc < 2331
  · exact Softmax.Export.block hp hX hf he hu nu ⟨by omega, h3⟩ hb
  by_cases h4 : 2333 ≤ e.pc ∧ e.pc ≤ 2338 ∨ e.pc = 2557 ∨ e.pc = 2558 ∨ 2853 ≤ e.pc ∧ e.pc ≤ 2854
  · exact Dispatch.Export.block hp hX hf he hu nu h4 hb
  by_cases h5 : 2344 ≤ e.pc ∧ e.pc < 2422
  · exact Loader.Export.block hp hX hf he hu nu h5 hb
  by_cases h6 : 2422 ≤ e.pc ∧ e.pc < 2557
  · exact Mma.Export.block hp hX hf he hu nu h6 hb
  by_cases h7 : 2565 ≤ e.pc ∧ e.pc < 2853
  · exact Epilogue.Export.block hp hX hf he hu nu h7 hb
  exfalso
  simp only [Lib.blockPcs, List.mem_cons, List.not_mem_nil, or_false] at hb
  omega

end PTX.Kernels.InklingRelDecode.Proof.Top
