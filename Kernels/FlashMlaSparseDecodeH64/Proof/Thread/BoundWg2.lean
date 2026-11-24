-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.BoundEntry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.Run

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- Each row starts with four scale elements, followed by the pipelined raw reads and stores. -/
def wg2Ordinal : Wg2.Site → Nat
  | .lenOrig => 0
  | .lenExtra => 1
  | .qUtccp => 2
  | .rawReady => 3
  | .svDone => 4
  | .scale r j => 5 + 22 * r.val + j.val
  | .raw r s => if s.val = 0 then 9 + 22 * r.val else 8 + 22 * r.val + 2 * s.val
  | .store r s => 11 + 22 * r.val + 2 * s.val
  | .fence => 93
  | .ready => 94
  | .free => 95
  | .barrier => 97

def wg2Block (d : Wg2.D) : Nat :=
  match d.site with
  | .lenOrig | .lenExtra => 0
  | _ => d.block

/-- Remaining work of one dequantizer lane. -/
def wg2Rank (P : Params) (L : Launch) (g : Nat) (d : Wg2.D) : Nat :=
  match d.site with
  | .barrier => 1
  | _ => 128 * (Result.blocks P (Wg2.eOf L g) - wg2Block d) + (98 - wg2Ordinal d.site)

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
theorem wg2Rank_step {P : Params} {L : Launch} {g : Nat} {d d' : Wg2.D} {e : Event}
    (hi : Wg2.Inv P L g d) (hn : Wg2.next P L g d e = some (some d')) :
    wg2Rank P L g d' + (if e.counts then 1 else 0) ≤ wg2Rank P L g d := by
  have hc := eventCount_le e
  have htotal : totalBlocks d.len0 d.len1 = Result.blocks P (Wg2.eOf L g) := by
    rw [hi.len0, hi.len1]
    rfl
  cases hd : d.site <;> simp only [Wg2.next, Wg2.nextSite, hd] at hn
  case' scale r j =>
    have hr := r.isLt
    have hj := j.isLt
  case' raw r s =>
    have hr := r.isLt
    have hs := s.isLt
  case' store r s =>
    have hr := r.isLt
    have hs := s.isLt
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    simp only [wg2Rank, wg2Ordinal, wg2Block, hd, Wg2.lenOrigNext, Wg2.lenExtraNext, Wg2.init,
      Wg2.afterScale, Wg2.afterRaw, Wg2.afterStore, Wg2.afterFree, htotal]
  all_goals (try split_ifs) <;> (try simp only [wg2Rank, wg2Ordinal, wg2Block])
  all_goals first
    | omega
    | (rcases e with ⟨epc, kind⟩; simp_all [Event.counts])
  all_goals
    have hr := r.isLt
    try have hj := j.isLt
    omega

theorem wg2Rank_init (P : Params) (L : Launch) (g : Nat) :
    wg2Rank P L g (Wg2.init P L g) ≤ 128 * Result.blocks P (Wg2.eOf L g) + 98 := by
  unfold wg2Rank Wg2.init Wg2.firstSite
  split_ifs <;> simp [wg2Block, wg2Ordinal]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound
