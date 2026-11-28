-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Query.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.CpOnce
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QUt
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Issue
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Writers
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Order
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCode
import Lemmas.Protocol.UnitHandoff
public import Lemmas.Tcgen05.CpIncomplete

@[expose] public section

/-! # A pending query copy is no Tensor Memory source

Every MMA of the MMA lane follows the lane's poll of `qUtccp`, which observes the notification of
the commit at pc 1982, which tracks every copy before it (`qUtccp_observes`): a copy is done before
any MMA is issued (`cp_done_of_mma`). So a copy that is not done is the source of no A read (the
copy-to-A pipeline reaches an MMA of the lane), of no Tensor Memory load, and the kernel has no
shift: finishing it keeps the read rule (`cp_readOk`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
include hp hX hFw hR hI hB

/-- **A copy is done before every MMA of the lane**: the MMA's poll of `qUtccp` observes the
completion of the commit tracking the copy. -/
theorem cp_done_of_mma {g i j pc pc' dc : Nat} {c : TcCopy.Spec} {sp : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} (hi : X.get (g, i) = some ⟨pc, .tc (.cp c)⟩)
    (hat : MmaAt L g pc) (hj : X.get (g, j) = some ⟨pc', .tc (.mma dc sp acc mask)⟩)
    (hat' : MmaAt L g pc') : X.async.mmaDone (g, i) = true := by
  have hq := mma_mma_qUt hp hX hFw hj hat'
  obtain ⟨jq, pcq, p, acq, sc, -, hpoll, -⟩ := UnitHandoff.exists_poll
    (m := mbarLoc L (g / L.block) .qUtccp) (h := g) (f := j) (c := 0) hq.ge
  have hlane : g = mmaLane L X (g / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hi (fun _ h => by cases h) ⟨hat, mma_cp_on hp hX hFw hi hat⟩
  have hw4 := hat.1
  generalize hc : g / L.block = c' at *
  subst hlane
  have hC1 : (X.tr (mmaLane L X c')).countP (PTX.Flow.commitsTo (mbarLoc L c' .qUtccp)) ≤ 1 := by
    have := mma_commits_le hp hX hFw hw4
    simpa only [loc, hc] using this
  obtain ⟨-, -, ic, sp', rank, hget, -, -, hrank, -⟩ :=
    qUtccp_observes hp hX hFw hR hI hB (mmaOne hp hX hFw) (c := c') hC1 hpoll
  have hlt := mma_cp_before_commit hp hX hFw hi ⟨hat.2.1, hat.2.2⟩ hget (by decide)
  exact (hX.tcCommit _ rank hrank).2 _
    ⟨rfl, hlt, .inr (.inl ⟨c, pc, hi⟩), sp', 1982, hget⟩

omit hR hI hB in
/-- **A copy is at a pc of the MMA code.** -/
theorem cp_mmaAt {g i pc : Nat} {c : TcCopy.Spec} (hcp : X.get (g, i) = some ⟨pc, .tc (.cp c)⟩) :
    MmaAt L g pc := by
  have hT := tmem_rows hp hX hFw
  have hg := Frame.lt_of_get hX hcp
  rcases TmRace.tc_role hT hg hcp rfl with ⟨-, hW⟩ | ⟨h, -⟩ | ⟨_, _, _, h⟩
  · rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;>
      cases h
  · exact h
  · cases h

/-- **Finishing a pending copy keeps the Tensor Memory read rule.** -/
theorem cp_readOk {g i pc : Nat} {c : TcCopy.Spec} (hi : X.CpIssue (g, i) c)
    (hd : X.async.mmaDone (g, i) = false) (hcp : X.get (g, i) = some ⟨pc, .tc (.cp c)⟩) :
    CpReadKept L Assumptions.all X (g, i) := by
  intro v ra rb
  have hT := tmem_rows hp hX hFw
  have hat : MmaAt L g pc := cp_mmaAt hp hX hFw hcp
  refine TcMma.ReadOk.finishCp hX.tcRead hi (fun e s ⟨pc', he⟩ =>
    no_shift_of_code hX code_noShift he s rfl) (fun e addr vals shape hLoad cell =>
      no_ld_source_of_incomplete_cp hi hX.tcCommit hd hLoad cell) ?_
  intro e dst sp accum mask hMma cell hSrc
  obtain ⟨hw, -, copy, dst', sp', accum', mask', -, -, hMma', -⟩ :=
    incomplete_cp_pipelined hi hX.tcCommit hd hSrc.2.2.1
  obtain ⟨pc', he⟩ := hMma'
  obtain ⟨-, hon, -⟩ := TmRace.mma_on hX hT he
  obtain ⟨e1, e2⟩ := e
  have hsame : g = e1 :=
    TmRace.mma_same (mmaOne hp hX hFw) hcp he ⟨hat, mma_cp_on hp hX hFw hcp hat⟩ hon hw.1.2.2
  subst hsame
  have := cp_done_of_mma hp hX hFw hR hI hB hcp hat he hon.1
  rw [hd] at this
  cases this

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
