-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MmaSlot
public import Lemmas.Flow.Polls
public import Lemmas.Flow.Counted
public import Lemmas.Flow.NotCommit
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.EvKind
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.LocCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count

@[expose] public section

/-! # The block and slot of a QK MMA together

An MMA of the MMA warp with D at column 400 is QK MMA `k` of a block `d`: it is the `24 d + k`-th
MMA issue of the lane, and at it the lane's successful polls of `soReady j` and commits to
`qkDone j` are the uses of slot `j` among the blocks before `d` (`mma_qkAt`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

omit P L m X in
private theorem cls_mma (e : Event) : Mma.cls .mma e = isMmaIssue e := by
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | wait q p ok a sc => cases ok <;> simp [Mma.cls, Mma.inRole, Mma.kindOf, isMmaIssue]
  | tc t => cases t <;> simp [Mma.cls, Mma.inRole, Mma.kindOf, isMmaIssue]
  | _ => simp [Mma.cls, Mma.inRole, Mma.kindOf, isMmaIssue]

omit P L m X in
private theorem issues_eq (xs : List Event) : xs.countP (Mma.cls .mma) = mmaIssues xs :=
  List.countP_congr fun e _ => by rw [cls_mma]

private theorem use_pre {j r i k : Nat} (hk : i < k) :
    Mma.useAt j r i k = ringUses 2 j r := by
  unfold Mma.useAt Mma.ind ringUses
  split_ifs <;> omega

/-- **A QK MMA is the `24 d + k`-th MMA issue of block `d`**, with the lane's polls and commits
before it the uses before block `d`. -/
theorem mma_qkAt (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {y i pc : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (he : X.get (y, i) = some ⟨pc, .tc (.mma 400 s acc mask)⟩)
    (hat : MbarRow.MmaAt L y pc) :
    ∃ d k, k < 16 ∧ mmaIssues ((X.tr y).take i) = 24 * d + k ∧ ∀ j : Fin 2,
      okPolls (mbarLoc L (y / L.block) (.soReady j)) ((X.tr y).take i) = ringUses 2 j d ∧
      ((X.tr y).take i).countP (PTX.Flow.commitsTo (mbarLoc L (y / L.block) (.qkDone j))) =
        ringUses 2 j d := by
  obtain ⟨hw, hlo, hhi⟩ := hat
  obtain ⟨d, hR, ⟨-, hE⟩, hl, -⟩ := mma_at hp hX hFw he (fun _ h => by cases h) ⟨hlo, hhi⟩
  have hc := hR (take_noUb hX he)
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE
  case leave s' => exact absurd rfl (hl s')
  case pv k =>
    obtain ⟨⟨h4, -⟩, -⟩ := hE
    simp only [Mma.pvCol] at h4
    omega
  case qk k =>
    obtain ⟨-, hn⟩ := (Mma.core_loop (by rfl)).mp hc
    have hk := k.isLt
    refine ⟨cnt.toNat, k.val, hk, ?_, fun j => ⟨?_, ?_⟩⟩
    · rw [← issues_eq, hn _ (by simp)]
      simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.idx, Mma.mmaIn,
        show ¬ 2 + k.val ≤ 1 by omega, show 2 + k.val ≤ 18 by omega]
    · have hP := lane4_okPolls hp hX hFw hw i (loc L y (.soReady j))
      rw [hn _ (by simp), Mma.cnt_so hp] at hP
      simp only [loc] at hP
      rw [hP, use_pre (by simp only [Mma.Site.idx]; omega)]
    · have hC := lane4_commits hp hX hFw hw i (loc L y (.qkDone j))
      rw [hn _ (by simp), Mma.cnt_qk hp] at hC
      simp only [loc] at hC
      rw [flow_commitsTo, hC, use_pre (by simp only [Mma.Site.idx]; omega)]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
