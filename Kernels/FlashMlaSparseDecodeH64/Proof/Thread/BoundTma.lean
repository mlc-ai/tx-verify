-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.BoundEntry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Tma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.Run

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The coordinate vectors and gather issues interleave after the first vector. -/
def tmaOrdinal : Wg1Tma.Site → Nat
  | .elect => 0
  | .lenOrig => 1
  | .lenExtra => 2
  | .waitQ => 3
  | .waitLast => 4
  | .waitCoord => 5
  | .waitFree => 6
  | .coord k j => 7 + 5 * k.val + j.val - if k.val = 0 then 0 else 1
  | .issue k => 15 + 5 * k.val
  | .rawReady => 91
  | .coordFree => 92
  | .barrier => 98
  | .exit => 99

def tmaBlock (d : Wg1Tma.D) : Nat :=
  match d.site with
  | .elect | .lenOrig | .lenExtra | .waitQ | .waitLast => 0
  | _ => d.block

/-- Remaining work of the elected TMA producer, with one budget per raw block. -/
def tmaRank (P : Params) (L : Launch) (g : Nat) (d : Wg1Tma.D) : Nat :=
  match d.site with
  | .barrier => 2
  | .exit => 1
  | _ => 128 * (Result.blocks P (Wg1Tma.eOf L g) - tmaBlock d) + (100 - tmaOrdinal d.site)

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
theorem tmaRank_step {P : Params} {L : Launch} {g : Nat} {d d' : Wg1Tma.D} {e : Event}
    (hi : Wg1Tma.Inv P L g d)
    (hbar : d.site = .barrier → ∀ id count mode, e.kind = .bar id count mode → id = 12)
    (hn : Wg1Tma.next P L g d e = some (some d')) :
    tmaRank P L g d' + (if e.counts then 1 else 0) ≤ tmaRank P L g d := by
  have hc := eventCount_le e
  have htotal : totalBlocks d.len0 d.len1 = Result.blocks P (Wg1Tma.eOf L g) := by
    rw [hi.len0, hi.len1]
    rfl
  cases hd : d.site <;> simp only [Wg1Tma.next, hd] at hn
  case barrier =>
    split at hn
    · rename_i id count mode he
      have hid := hbar hd id count mode he
      rw [hid] at hn
      simp only [ite_true, Option.some.injEq] at hn
      subst d'
      simp only [tmaRank, hd]
      omega
    · cases hn
  all_goals repeat' split at hn
  all_goals simp only [Option.some.injEq, reduceCtorEq] at hn
  all_goals rw [← hn]
  all_goals
    simp only [tmaRank, tmaBlock, tmaOrdinal, hd, Wg1Tma.firstLenSite,
      Wg1Tma.beginLoop, Wg1Tma.afterCoord, Wg1Tma.afterIssue, Wg1Tma.afterFree, htotal]
  all_goals (try split_ifs) <;> (try simp only [tmaRank, tmaBlock, tmaOrdinal])
  all_goals (try split_ifs)
  all_goals first
    | omega
    | (rcases e with ⟨epc, kind⟩; simp_all [Event.counts])

theorem tmaRank_init (P : Params) (L : Launch) (g : Nat) :
    tmaRank P L g (Wg1Tma.init P L g) ≤ 128 * Result.blocks P (Wg1Tma.eOf L g) + 100 := by
  rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound
