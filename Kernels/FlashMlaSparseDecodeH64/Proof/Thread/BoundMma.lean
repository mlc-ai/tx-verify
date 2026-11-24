-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.BoundEntry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.Run

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The query initialization followed by one block's QK and PV instructions. -/
def mmaOrdinal : Wg1Mma.Site → Nat
  | .head => 0
  | .elect => 1
  | .loadTopk => 2
  | .loadExtra => 3
  | .qLoad k => 4 + k.val
  | .qArrive => 12
  | .qWait => 13
  | .qFence => 14
  | .qCopy k => 15 + k.val
  | .qCopyCommit => 31
  | .qCopyWait => 32
  | .qCopyFence => 33
  | .kvWait => 34
  | .kvFence => 35
  | .qkMma k => 36 + k.val
  | .qkCommit => 52
  | .soWait => 53
  | .soFence => 54
  | .pvMma k => 55 + k.val
  | .pvCommit => 63
  | .outBar => 65
  | .exit => 66

/-- Remaining query and GEMM work, with a budget for every remaining block. -/
def mmaRank (P : Params) (L : Launch) (g : Nat) (d : Wg1Mma.D) : Nat :=
  match d.site with
  | .outBar => 2
  | .exit => 1
  | _ => 80 * (Wg1Mma.blocks P L g - d.i) + (70 - mmaOrdinal d.site)

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
theorem mmaRank_step {P : Params} {L : Launch} {g : Nat} {d d' : Wg1Mma.D} {e : Event}
    (hn : Wg1Mma.next P L g d e = some (some d')) :
    mmaRank P L g d' + (if e.counts then 1 else 0) ≤ mmaRank P L g d := by
  have hc := eventCount_le e
  cases hd : d.site <;> simp only [Wg1Mma.next, hd] at hn
  all_goals repeat' split at hn
  all_goals simp only [Option.some.injEq, reduceCtorEq] at hn
  all_goals rw [← hn]
  all_goals simp only [mmaRank, mmaOrdinal, hd, Wg1Mma.startSite, Wg1Mma.afterTopk, Wg1Mma.nextSite]
  all_goals (try split_ifs) <;> (try simp only [mmaRank, mmaOrdinal])
  all_goals first
    | omega
    | (rcases e with ⟨epc, kind⟩; simp_all [Event.counts])

theorem mmaRank_elect (P : Params) (L : Launch) (g : Nat) :
    mmaRank P L g ⟨.elect, 0⟩ ≤ 80 * Result.blocks P (Wg1Mma.eOf L g) + 70 := by
  have he : Wg1Mma.blocks P L g = Result.blocks P (Wg1Mma.eOf L g) := by
    unfold Wg1Mma.blocks Wg1Mma.total Wg1Mma.pad64 Wg1Mma.len0 Wg1Mma.len1
    rw [Result.blocks_eq_kernel]
    unfold Result.origPadded Result.ceilToMultiple Result.topkBlock
    congr 4
  simp only [mmaRank, mmaOrdinal, Nat.sub_zero, he]
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound
