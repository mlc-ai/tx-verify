-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.ExitPC
public import Lemmas.Flow.Regs
public import Kernels.InklingRelDecode.Proof.Common.Export.FinalSync
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand

/-! # Where a deallocation is

The kernel's deallocation event is a data lane's, at pc 2851 after the lane's final
`bar.sync 0`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.Proof PTX.Tmem.Pair

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The deallocation's lane is a data lane, at pc 2851, past a final rendezvous.** -/
public theorem dealloc_site (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {h kd pc grp dst da n}
    (hd : X.get (h,kd) = some ⟨pc,.tc (.resource grp dst (.dealloc da n))⟩) :
    h % L.block < 128 ∧ pc = 2851 ∧ ∃ u' pch, u' < kd ∧
      X.get (h,u') = some ⟨pch,.bar 0 none .sync⟩ ∧ Lib.finalSync pch = true ∧
      2 ≤ ((X.tr h).take u').countP (Execution.isBarId 0) := by
  have tc : isTcColl ⟨pc,.tc (.resource grp dst (.dealloc da n))⟩ = true := rfl
  have pcs := Export.tmem_event_pc hX hd (by simp [isTmemOp])
  obtain ⟨i,w,-,-,eq⟩ := Export.tc_operand hp hX hf base hd tc
  have wh := Export.tc_pc_where hp hX hf hd tc
  have is2851 : pc = 2851 := by
    simp only [Lib.resPcs, List.mem_cons, List.not_mem_nil, or_false] at pcs
    rcases pcs with rfl|rfl|rfl|rfl
    · simp [tcStatic, Lib.opStatic] at eq
    · simp [tcStatic, Lib.opStatic] at eq
    · rfl
    · simp [Lib.loopTcPcs] at wh
  subst is2851
  refine ⟨Export.tc_data_lane hp hX hf hd tc,rfl,?_⟩
  exact Export.final_bar_before hp hX hd (fun f h => nomatch h) (by simp [Lib.afterFinal])

end PTX.Kernels.InklingRelDecode.Proof.Tmem
