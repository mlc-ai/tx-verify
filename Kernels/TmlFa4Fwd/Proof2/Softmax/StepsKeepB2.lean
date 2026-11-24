-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsKeepB

@[expose] public section

/-! # The bias round's keep test after a maximum of `-∞` before the round

From the maximum `%r3500` (pc 5666) to the statistics store (pc 5682): the test whether the
maximum is `-∞`, the scaled difference to the maximum before the round, its `ex2`, the keep test,
the row maximum, the maximum the exponents subtract and the rescaling factor. The walk runs once
per kind of the maximum before the round and of the fold (finite, or `-∞` when the maximum
before the round is `-∞` and every bias half is masked), so that every value it reads has one
form. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option seg_sym.decideHeartbeats 40000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The statistics store's values with the keep test's three registers given. -/
abbrev keepW (p : Params) (L : Launch) (g : Nat) (v : V) (a b c : Value) : Nat → Value :=
  Function.update (Function.update (Function.update (valueOfD p L g (statB v)) 7256 a) 4565 b)
    1362 c

/-- **`-∞` before the round, a finite fold `r`.** -/
theorem keep_fr (hp : Pre p L m) (sc ukw nb bt bpar spar ppar pl sv bk br mr rs) (r : ℝ) :
    ∃ n, Seg kernel Assumptions.all L g n 5666
      ((4560, .float .f32 r) ::
        keepStart p L g ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, false, mr, rs⟩)
      5682 (factsFrom (liveD 5682)
        (keepW p L g ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, false, mr, rs⟩
          (.float .f32 r) (.float .f32 r) (.float .f32 0))) := by
  have hparams := params hp
  obtain ⟨hw, hs⟩ := scl_word hp
  have hm := mulEReal_coe_bot_pos hs
  seg_sym using (soft_seg)

/-- **`-∞` before the round, every half masked.** -/
theorem keep_fb (hp : Pre p L m) (sc ukw nb bt bpar spar ppar pl sv bk br mr rs) :
    ∃ n, Seg kernel Assumptions.all L g n 5666
      ((4560, negInf32) ::
        keepStart p L g ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, false, mr, rs⟩)
      5682 (factsFrom (liveD 5682)
        (keepW p L g ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, false, mr, rs⟩
          negInf32 (.bits 32 (BitVec.ofNat 64 0)) (.float .f32 0))) := by
  have hparams := params hp
  obtain ⟨hw, hs⟩ := scl_word hp
  have hm := mulEReal_coe_bot_pos hs
  seg_sym using (soft_seg)

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
