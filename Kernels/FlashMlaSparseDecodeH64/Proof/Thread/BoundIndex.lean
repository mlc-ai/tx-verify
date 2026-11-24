-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.BoundEntry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Index
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.Run

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The current pair, the prefetched pair, the wait, and each pair's ring publication. -/
def indexOrdinal : Wg1Index.Site → Nat
  | .lenOrig => 0
  | .lenExtra => 1
  | .pair _ true false => 2
  | .pair _ true true => 3
  | .pair _ false false => 4
  | .pair _ false true => 5
  | .waitFree _ => 6
  | .quad1 _ => 7
  | .quad2 _ => 8
  | .coord _ false => 9
  | .coord _ true => 10
  | .valid _ => 11
  | .ready _ => 12
  | .barrier => 15

/-- Remaining work in either cache, including the prefetched index pair for the next block. -/
def indexRank (P : Params) (L : Launch) (g : Nat) (d : Wg1Index.D) : Nat :=
  match d.site with
  | .barrier => 1
  | _ => 16 * (Result.blocks P (Wg1Index.eOf L g) - d.block) + (16 - indexOrdinal d.site)

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
theorem indexRank_step {P : Params} {L : Launch} {g : Nat} {d d' : Wg1Index.D} {e : Event}
    (hi : Wg1Index.Inv P L g d) (hn : Wg1Index.next P L g d e = some (some d')) :
    indexRank P L g d' + (if e.counts then 1 else 0) ≤ indexRank P L g d := by
  have hc := eventCount_le e
  have htotal : totalBlocks d.len0 d.len1 = Result.blocks P (Wg1Index.eOf L g) := by
    rw [hi.len0, hi.len1]
    rfl
  have hmain : numOrigBlocks d.len0 ≤ totalBlocks d.len0 d.len1 := by
    unfold numOrigBlocks totalBlocks
    exact Nat.div_le_div_right (Nat.le_add_right _ _)
  rw [htotal] at hmain
  cases hd : d.site <;> simp only [Wg1Index.next, Wg1Index.nextSite, hd] at hn
  case' pair ext first high => cases first <;> cases high
  case' coord ext high => cases high
  all_goals try simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hn
  all_goals repeat' split at hn
  all_goals simp only [Option.some.injEq, reduceCtorEq] at hn
  all_goals rw [← hn]
  all_goals
    simp only [indexRank, indexOrdinal, hd, Wg1Index.afterPairFirst, Wg1Index.afterReady, htotal,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
  all_goals (try split_ifs) <;> (try simp only [indexRank, indexOrdinal])
  all_goals first
    | omega
    | (rcases e with ⟨epc, kind⟩;
        simp_all only [Event.counts, Event.kind, Bool.not_false, Bool.not_true, Bool.false_eq_true,
          not_true_eq_false, Bool.not_eq_true, Nat.add_zero, ↓reduceIte])

theorem indexRank_init (P : Params) (L : Launch) (g : Nat) :
    indexRank P L g (Wg1Index.init P L g) ≤ 16 * Result.blocks P (Wg1Index.eOf L g) + 16 := by
  unfold indexRank Wg1Index.init Wg1Index.firstSite
  split_ifs <;> simp [indexOrdinal]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound
