-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
public import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Correction.Shape
import Kernels.TmlFa4Fwd.Proof.Lib.EvPc
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.SiteUse
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Sites
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Two lanes of a correction warp polling at one position poll one barrier -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

/-- The correction warps' poll sites. -/
private def corrPolls : List Correction.Site :=
  [.fw 0 0, .fw 0 1, .fw 1 0, .fw 1 1, .wend false, .wend true]

private theorem corr_pc : ∀ s ∈ corrPolls, ∀ s' ∈ corrPolls, s.pc = s'.pc →
    Correction.pollOff s = Correction.pollOff s' := by decide

private theorem corr_mem (s : Correction.Site) (h : Correction.pollOff s ≠ 0) : s ∈ corrPolls := by
  cases s <;> simp only [Correction.pollOff, ne_eq, not_true_eq_false] at h
  all_goals first
    | (rename_i st k; fin_cases st <;> fin_cases k <;> decide)
    | (rename_i l; cases l <;> decide)

/-- A correction lane's poll: its site's barrier and position. -/
private theorem corr_poll (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L g)
    (hw1 : Prologue.warpIndex L g ≤ 11) {k pc par : Nat} {l : Loc}
    {ok acq : Bool} {sc : MbarScope} (he : X.get (g, k) = some ⟨pc, .wait l par ok acq sc⟩) :
    ∃ s ∈ corrPolls, pc = s.pc ∧ l = Correction.bl L g (Correction.pollOff s) := by
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he (fun f h => by cases h) with
    ⟨s, n, hσ, -, -, hi, hev⟩ | ⟨d, n, hσ, -, -, -, hev, -⟩
  · exfalso
    obtain ⟨c, hc⟩ := start_mbar (l := l) hev hi.2 rfl
    cases hc
  · have hpc := ev_pc hp hX he hσ
    rcases hev.data_or_vote with hev | ⟨_,_,h⟩
    case inr => cases h
    rcases corr_mbar2 hev (l := l) rfl with ⟨hk, -⟩ | ⟨_, _, -, hl, hmem⟩
    · cases hk
    · refine ⟨d.site, corr_mem _ (fun h0 => ?_), hpc, hl⟩
      change Correction.pollOff d.site ∈ _ at hmem
      rw [h0] at hmem; simp at hmem

/-- **Two lanes of a correction warp polling at one position poll one barrier.** -/
theorem corr_poll_same (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L g)
    (hw1 : Prologue.warpIndex L g ≤ 11) (hs : SameWarp L g h)
    {k k' pc par par' : Nat} {l l' : Loc} {ok acq ok' acq' : Bool} {sc sc' : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait l par ok acq sc⟩)
    (he' : X.get (h, k') = some ⟨pc, .wait l' par' ok' acq' sc'⟩) : l = l' := by
  have hwe : Prologue.warpIndex L g = Prologue.warpIndex L h := hs.2
  obtain ⟨s, hs1, hpc, hl⟩ := corr_poll hp hX hFw hw hw1 he
  obtain ⟨s', hs2, hpc', hl'⟩ := corr_poll hp hX hFw (by omega) (by omega) he'
  rw [hl, hl', corr_pc s hs1 s' hs2 (hpc.symm.trans hpc')]
  simp only [Correction.bl, hs.1.2.2]

end
end PTX.Kernels.TmlFa4Fwd.Proof
