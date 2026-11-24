-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.SmWarp.Open
import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
import Kernels.TmlFa4Fwd.Proof.Lib.EvPc
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.SiteUse
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Sites
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Two lanes of a softmax warp polling at one position poll one barrier -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

/-- The softmax warps' poll sites. -/
private def softPolls : List Softmax.Site :=
  .wq :: ([.first, .bias, .plain].map .ws ++ [false, true].map .wb ++
    [.first, .bias, .plain].map .pwend ++ [false, true].map .wend)

private theorem soft_pc : ∀ s ∈ softPolls, ∀ s' ∈ softPolls, s.pc = s'.pc →
    Softmax.pollOff s = Softmax.pollOff s' := by decide

private theorem soft_mem (s : Softmax.Site) (h : Softmax.pollOff s ≠ 0) : s ∈ softPolls := by
  cases s <;> simp only [Softmax.pollOff, ne_eq, not_true_eq_false] at h
  all_goals first
    | (rename_i r; cases r <;> decide)
    | decide

/-- A softmax lane's poll: its site's barrier and position. -/
private theorem soft_poll (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g < 8) {k pc par : Nat} {l : Loc}
    {ok acq : Bool} {sc : MbarScope} (he : X.get (g, k) = some ⟨pc, .wait l par ok acq sc⟩) :
    ∃ s ∈ softPolls, pc = s.pc ∧ l = Softmax.bl L g (Softmax.pollOff s) := by
  rcases SmWarp.open_ev hp hX hFw hw he (fun f h => by cases h) with
    ⟨s, n, hσ, -, -, hi, hev⟩ | ⟨d, n, hσ, -, -, -, hev⟩
  · exfalso
    obtain ⟨c, hc⟩ := start_mbar (l := l) hev hi.2 rfl
    cases hc
  · have hpc := ev_pc hp hX he hσ
    rcases soft_mbar hev.1 (l := l) rfl with ⟨hk, -⟩ | ⟨_, _, -, hl, hmem⟩
    · cases hk
    · refine ⟨d.site, soft_mem _ (fun h0 => ?_), hpc, hl⟩
      change Softmax.pollOff d.site ∈ _ at hmem
      rw [h0] at hmem; simp at hmem

/-- **Two lanes of a softmax warp polling at one position poll one barrier.** -/
theorem soft_poll_same (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g < 8) (hs : SameWarp L g h)
    {k k' pc par par' : Nat} {l l' : Loc} {ok acq ok' acq' : Bool} {sc sc' : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait l par ok acq sc⟩)
    (he' : X.get (h, k') = some ⟨pc, .wait l' par' ok' acq' sc'⟩) : l = l' := by
  have hwe : Prologue.warpIndex L g = Prologue.warpIndex L h := hs.2
  obtain ⟨s, hs1, hpc, hl⟩ := soft_poll hp hX hFw hw he
  obtain ⟨s', hs2, hpc', hl'⟩ := soft_poll hp hX hFw (by omega) he'
  rw [hl, hl', soft_pc s hs1 s' hs2 (hpc.symm.trans hpc')]
  have hst : Softmax.stg L g = Softmax.stg L h := by
    unfold Softmax.stg Softmax.warpW
    rw [show g % L.block / 32 = h % L.block / 32 from hs.2]
  simp only [Softmax.bl, Softmax.stS, hs.1.2.2, hst]

end
end PTX.Kernels.TmlFa4Fwd.Proof
