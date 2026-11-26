-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
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

/-! # The MMA lane's block of a QK MMA

An MMA of the MMA warp with D at column 400 is a QK MMA (`qk k`, `k < 16`) of some block `d` of
the loop. Before it the lane has made, per block before `d`, the poll of `soReady[r % 2]` and the
commit to `qkDone[r % 2]` (they come after the block's QK MMAs): at the MMA the lane's successful
polls of `soReady j` and its commits to `qkDone j` are both the uses of slot `j` among blocks
`0 … d - 1` (`mma_qkMmaBlock`), read off the reference invariant's counts at the `qk` site. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A slot's uses at a place before its block's event are those of the blocks before it. -/
private theorem use_pre {j r i k : Nat} (hk : i < k) :
    Mma.useAt j r i k = ringUses 2 j r := by
  unfold Mma.useAt Mma.ind ringUses
  split_ifs <;> omega

/-- **The block of a QK MMA**: at an MMA of the MMA warp with D at column 400, of block `d`, the
lane's successful polls of `soReady j` and its commits to `qkDone j` are the uses of slot `j`
among blocks `0 … d - 1`. -/
theorem mma_qkMmaBlock (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {y i pc : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (he : X.get (y, i) = some ⟨pc, .tc (.mma 400 s acc mask)⟩)
    (hat : MbarRow.MmaAt L y pc) :
    ∃ d, ∀ j : Fin 2,
      okPolls (mbarLoc L (y / L.block) (.soReady j)) ((X.tr y).take i) = ringUses 2 j d ∧
      ((X.tr y).take i).countP (PTX.Flow.commitsTo (mbarLoc L (y / L.block) (.qkDone j))) =
        ringUses 2 j d := by
  obtain ⟨hw, hlo, hhi⟩ := hat
  have hub : ∀ f, (⟨pc, .tc (.mma 400 s acc mask)⟩ : Event).kind ≠ .ub f :=
    fun _ h => by cases h
  obtain ⟨d, hR, ⟨-, hE⟩, hl, -⟩ := mma_at hp hX hFw he hub ⟨hlo, hhi⟩
  have hc := hR (take_noUb hX he)
  cases hs : d.site with
  | qk k =>
    obtain ⟨-, hn⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hc
    refine ⟨d.cnt.toNat, fun j => ⟨?_, ?_⟩⟩
    · have hP := lane4_okPolls hp hX hFw hw i (loc L y (.soReady j))
      rw [hn _ (by simp), Mma.cnt_so hp, hs] at hP
      simp only [loc] at hP
      rw [hP, use_pre (by simp only [Mma.Site.idx]; omega)]
    · have hC := lane4_commits hp hX hFw hw i (loc L y (.qkDone j))
      rw [hn _ (by simp), Mma.cnt_qk hp, hs] at hC
      simp only [loc] at hC
      rw [flow_commitsTo, hC, use_pre (by simp only [Mma.Site.idx]; omega)]
  | pv k =>
    exfalso
    simp only [Mma.EvK, hs] at hE
    rcases hE with ⟨s', h1, -⟩ | ⟨f, hf⟩
    · simp only [Kind.tc.injEq, TcKind.mma.injEq] at h1
      have h4 : 400 = Mma.pvCol k := h1.1
      simp only [Mma.pvCol] at h4
      omega
    · cases hf
  | leave s' => exact absurd hs (hl s')
  | _ =>
    exfalso
    simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, hs] at hE

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
