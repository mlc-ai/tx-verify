-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Live
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Query.CpSource
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Order
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemACell
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.CpOnce

@[expose] public section

/-! # The A reads of the QK MMAs have a source

QK MMA `k` of the MMA lane reads its A operand from the cells of copy `k` (`qk_aCell_eq`), which
precedes the MMA in the lane (`mma_cp_exists`), is done before it (`cp_done_of_mma`) and is
ordered before the A read by the copy-to-A pipeline. No other write has such a cell: the writers
of the other column classes are apart (`writer_cases`), and a second copy to the same column is
the same event (`mma_cp_once`). The source is live (`source_live_mma`). Its value is the copy's
word (`CpDefined`): the bytes of the copied query tile are defined. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow MbarRow

noncomputable section

/-- **The words of a done copy are defined**: every cell of a copy that is done has the word of
its bytes (they are the query tile's, read once the load that wrote them is observed). -/
def CpDefined (X : Execution) : Prop :=
  ∀ (cp : EvId) (c : TcCopy.Spec) (cell : TcMma.Cell), X.CpIssue cp c →
    X.async.mmaDone cp = true → TcMma.CpCell X cp cell → ∃ v, TcMma.CpValue X cp cell v

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hT : TmemRows P L X) (hO : MmaOne L X) (hM : MbarRows P L X) (hI : InitRows L X)
  (hB : Bar0Rows L X) (ht : Tmem.One.Tmem1Facts L X 0)
  (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (hD : CpDefined X)
include hp hX hFw hT hO hM hI hB ht hmd hD

/-- **Every Tensor Memory A read of an MMA has a source with a value**: copy `k` for QK MMA `k`. -/
theorem a_source {i : EvId} {cell : TcMma.Cell} (ha : X.MmaACell i cell) :
    ∃ source value, TcMma.ReadSource L X .a source i cell ∧
      TcMma.Wrote L Assumptions.all X source cell value := by
  obtain ⟨g, j⟩ := i
  obtain ⟨d, s, acc, mask, index, b, ⟨pc, he⟩, hac⟩ := ha
  have hg := Frame.lt_of_get hX he
  rcases tc_role hT hg he rfl with ⟨-, hW⟩ | ⟨hat, hMm⟩ | ⟨_, _, _, hc'⟩
  · rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;> cases h
  · rcases hMm with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨_, k, hk, hpc, h, hops⟩ |
        ⟨_, _, k, -, -, h, -, hops⟩ <;> cases h
    · obtain ⟨hlo, hhi⟩ := ops_cta hp hg (.inl rfl) hops
      obtain ⟨hidx, hceq⟩ := TmemRow.qk_aCell_eq hk hops hlo hhi hac
      have hon : MmaOn L g pc :=
        ⟨hat, by simp only [TmemRow.qkPc] at hpc; split at hpc <;> omega⟩
      obtain ⟨ic, hic, pcc, c, hgc, hrc, hcaddr⟩ :=
        mma_cp_exists hp hX hFw he ⟨hat.2.1, hat.2.2⟩ hk
      obtain ⟨-, hsh, -, hct⟩ := mma_cp_spec hp hX hFw hgc hrc
      obtain ⟨hatc, h1853⟩ := mma_role hp hX hFw hgc (.inr ⟨c, rfl⟩)
      have hcp : TcMma.CpCell X (g, ic) cell := by
        refine ⟨c, g / L.block, index, index / 32, ⟨pcc, hgc⟩, by rw [hct]; simp, ?_, ?_, ?_⟩
        · rw [hsh]
          simp only [TcCpShape.sourceBytes, TcCpShape.rows, TcCpShape.rowBytes]
          omega
        · rw [hsh]
          simp [TcCpShape.lanes, TcCpShape.rowBytes]
        · rw [hsh, hcaddr]
          exact hceq
      have hdone := cp_done_of_mma hp hX hFw hM hI hB hgc hatc he hat
      have hcta : cell.cta = g / L.block := by rw [hceq]; rfl
      refine ⟨(g, ic), _, ?_, .inr (.inr (.inl (hD _ c cell ⟨pcc, hgc⟩ hdone hcp).choose_spec))⟩
      refine ⟨?_, .inr (.inr (.inl hcp)), .inr (.inr ⟨TcMma.sameWarp_self hg, .inl
        (TcMma.baseCausality_of_tc_po hgc rfl hic (len_of_get he)), c, _, s, _, _,
        ⟨pcc, hgc⟩, by rw [hsh]; decide, ⟨pc, he⟩, by rw [hops.1, hcaddr]⟩), ?_,
        source_live_mma hX ht hmd ⟨pc, he⟩ hcta⟩
      · intro heq
        have := congrArg Prod.snd heq
        simp only at this
        omega
      · have hcol := TmemRow.cp_cell (cta := g / L.block) (lane := index / 32)
          (index := index) hk
        rw [← hceq] at hcol
        intro w hw
        left
        obtain ⟨hcw, cw⟩ := writer_cases hp hX hT hw
        rcases cw with ⟨k', -, h1', h2'⟩ | ⟨b', -, hb2, -, h1', h2'⟩ |
          ⟨k', ⟨pc', c', hk', hgw, hon', ha', hsh'⟩, h1', h2'⟩ | ⟨-, h1', -⟩
        · omega
        · omega
        · have hkk : k' = k := by
            have := TmemRow.cp_cell (cta := g / L.block) (lane := index / 32) (index := index)
              (k := k) hk
            rw [hceq] at h1' h2'
            omega
          subst hkk
          have hc : w.1 / L.block = g / L.block := by rw [← hcw, hcta]
          have ht2 := mma_same hO hgw hgc hon' ⟨hatc, h1853⟩ hc
          obtain ⟨g', i'⟩ := w
          simp only at ht2
          subst ht2
          have := mma_cp_once hp hX hFw hgw hgc hon'.1.2 hrc (by rw [ha', hcaddr])
          rw [this]
        · omega
    · obtain ⟨haT, -⟩ := hops
      simp [TcMma.aCell, haT] at hac
  · cases hc'

end

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
