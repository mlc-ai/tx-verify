-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaWords
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.EvKind
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.LocCnt

@[expose] public section

/-! # The last `svDone` commit follows every MMA and copy of the MMA lane

-- domain: consistent

A copy of the query (sites `qCopy k`, the prologue) comes before every commit to `svDone`; a QK
or PV MMA of block `r` (sites `qk k`, `pv k`) has the commits of the blocks before `r` to
`svDone`, `ringUses 2 s r` on slot `s` (`Mma.cnt_sv`), and `r` is below the CTA's block count
`R` (`LoopOk`, `mma_rounds`). So on the slot of the last block, `(R - 1) % 2`, an MMA or copy has
at most `(R - 1) / 2` earlier commits (`mma_asyncSv`): the commit of the last block, the
`(R - 1) / 2`-th of its slot, comes after it in the lane's program order. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

/-- The slot of the last block holds at most `(R - 1) / 2` uses among the first `r < R` blocks. -/
private theorem ru_last {r R : Nat} (h : r < R) :
    ringUses 2 (slot2 (R - 1)).val r ≤ (R - 1) / 2 := by
  simp only [slot2, ringUses]
  omega

/-- **An MMA or copy of the MMA warp has at most `(R - 1) / 2` earlier commits to `svDone` of the
last block's slot**, `R` the CTA's block count. -/
theorem mma_asyncSv (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {i pc : Nat} {k : TcKind}
    (he : X.get (y, i) = some ⟨pc, .tc k⟩) (hat : MbarRow.MmaAt L y pc) (h1853 : 1853 < pc)
    (hk : (∃ b s acc mask, k = .mma b s acc mask) ∨ ∃ s, k = .cp s) :
    ((X.tr y).take i).countP (PTX.Flow.commitsTo (mbarLoc L (y / L.block)
      (.svDone (slot2 (blocksOf P L (y / L.block) - 1))))) ≤
      (blocksOf P L (y / L.block) - 1) / 2 := by
  obtain ⟨-, hlo, hhi⟩ := hat
  have hub : ∀ f, (⟨pc, .tc k⟩ : Event).kind ≠ .ub f := fun _ h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hR, ⟨-, hE⟩, hl, hw⟩ := mma_state hJ hi hev hpc ⟨hlo, hhi⟩
  have hR := hR (state_ub hX hσ he)
  have hc : (fun c => n (.mma c)) = fun c => ((X.tr y).take i).countP (Mma.cls c) :=
    funext fun c => state_count hσ (.mma c)
  rw [hc] at hR
  have hR := hR (take_noUb hX he)
  set s := slot2 (blocksOf P L (y / L.block) - 1) with hsd
  have hC := lane4_commits hp hX hFw hw i (loc L y (.svDone s))
  simp only [loc] at hC
  rw [flow_commitsTo, hC]
  have hloop : ∀ j, d.site.inLoop = true → d.site.idx = j →
      ((X.tr y).take i).countP (Mma.cls (.commit (loc L y (.svDone s)))) ≤
        (blocksOf P L (y / L.block) - 1) / 2 := fun j hs _ => by
    obtain ⟨⟨-, -, -, hrR, -⟩, hn⟩ := (Mma.core_loop hs).mp hR
    have hrd := mma_rounds hp hX hFw he hub ⟨h1853, hhi⟩ le_rfl hσ
      (fun h => by rw [h] at hs; cases hs) (fun h => by rw [h] at hs; cases hs)
    rw [hn _ (by simp), Mma.cnt_sv hp]
    rw [hrd] at hrR
    exact ru_last hrR
  cases hst : d.site with
  | qk j => exact hloop _ (by rw [hst]; rfl) rfl
  | pv j => exact hloop _ (by rw [hst]; rfl) rfl
  | qCopy j =>
    have hn := (Mma.core_pro (by rw [hst]; exact ⟨rfl, by simp, by simp⟩)).mp hR
    rw [hn _ (by simp)]
    simp [hst, Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.useAt, ringUses, Mma.obj_qUt hp,
      Mma.mloc_eq_iff, Mma.ind]
  | leave j => exact absurd hst (hl j)
  | _ =>
    exfalso
    rcases hk with ⟨b, s', acc, mask, rfl⟩ | ⟨s', rfl⟩ <;>
      simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, hst] at hE

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
