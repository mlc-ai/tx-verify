-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma
public import Lemmas.Flow.Polls
public import Lemmas.Flow.Counted
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.EvKind
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.LocCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count

@[expose] public section

/-! # The MMA lane's block of a PV MMA

-- domain: consistent

An MMA of the MMA warp with D below column 256 is a PV MMA (`pv k`; the QK MMAs write D at
column 400) of some block `d` of the loop. The block's events before it are, per block `r ≤ d`,
the poll of `so_ready[r % 2]` and the commit to `qk_done[r % 2]`; the later blocks' come after
it. So at the MMA the lane's successful polls of `soReady j` and its commits to `qkDone j` are
both the uses of slot `j` among the first `d + 1` blocks (`mma_pvBlock`): read off the
reference invariant's counts at the `pv` site (`Mma.cnt_so`, `Mma.cnt_qk`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A slot's uses at a place past its block's event are those of the blocks up to the block. -/
private theorem use_succ {j r i k : Nat} (hj : j < 2) (hk : k ≤ i) :
    Mma.useAt j r i k = ringUses 2 j (r + 1) := by
  unfold Mma.useAt Mma.ind ringUses
  split_ifs <;> omega

/-- **The block of a PV MMA**: at an MMA of the MMA warp with D below column 256, of block `d`,
the lane's successful polls of `soReady j` and its commits to `qkDone j` are the uses of slot `j`
among blocks `0 … d`. -/
theorem mma_pvBlock (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {y i pc b : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (he : X.get (y, i) = some ⟨pc, .tc (.mma b s acc mask)⟩)
    (hat : MbarRow.MmaAt L y pc) (hb : b < 256) :
    ∃ d, ∀ j : Fin 2,
      okPolls (mbarLoc L (y / L.block) (.soReady j)) ((X.tr y).take i) = ringUses 2 j (d + 1) ∧
      ((X.tr y).take i).countP (PTX.Flow.commitsTo (mbarLoc L (y / L.block) (.qkDone j))) =
        ringUses 2 j (d + 1) := by
  obtain ⟨hw, hlo, hhi⟩ := hat
  have hub : ∀ f, (⟨pc, .tc (.mma b s acc mask)⟩ : Event).kind ≠ .ub f := fun _ h => by cases h
  obtain ⟨d, hR, ⟨-, hE⟩, hl, -⟩ := mma_at hp hX hFw he hub ⟨hlo, hhi⟩
  have hc := hR (take_noUb hX he)
  cases hs : d.site with
  | pv k =>
    obtain ⟨-, hn⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hc
    refine ⟨d.cnt.toNat, fun j => ⟨?_, ?_⟩⟩
    · have hP := lane4_okPolls hp hX hFw hw i (loc L y (.soReady j))
      rw [hn _ (by simp), Mma.cnt_so hp, hs] at hP
      simp only [loc] at hP
      rw [hP, use_succ j.isLt (by simp only [Mma.Site.idx]; omega)]
    · have hC := lane4_commits hp hX hFw hw i (loc L y (.qkDone j))
      rw [hn _ (by simp), Mma.cnt_qk hp, hs] at hC
      simp only [loc] at hC
      rw [flow_commitsTo, hC, use_succ j.isLt (by simp only [Mma.Site.idx]; omega)]
  | qk k =>
    exfalso
    simp only [Mma.EvK, hs] at hE
    rcases hE with ⟨s', h1, -⟩ | ⟨f, hf⟩
    · simp only [Kind.tc.injEq, TcKind.mma.injEq] at h1
      have h4 : Mma.qkCol = 400 := rfl
      omega
    · cases hf
  | leave s' => exact absurd hs (hl s')
  | _ =>
    exfalso
    simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, hs] at hE

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
