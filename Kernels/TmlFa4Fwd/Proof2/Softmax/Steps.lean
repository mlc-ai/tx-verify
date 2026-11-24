-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsStart
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanFirst
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanLoop
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanSecond
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanLoop2
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsSelect
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsReq
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsFirstCtl
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsBiasCtl
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsPlainCtl
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsFin
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsEnd
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsMid
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScore
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsPlainMax2
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsBiasLoad2
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsPlainEnd
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsP1
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsNarr1b
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsBarr1b
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsBarrB
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsPlainP
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsPlainP2
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsPwE2
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsPlainP0

@[expose] public section

/-! # The softmax machine's steps, except at the numeric states

`stepAt_ctl`: the step obligation of the data machine `codeD` at every state that is not an open
numeric state (`D.numeric`), from the family files. Of the 63 states whose following local code
reads data registers, the score packs after the score loads of the first and the biased rounds,
after the implicit waits of a plain round's loads, the plain round's maximum after its fourth load,
the bias unpacks after the last element of each bias load and the end of a plain round are stepped
(`StepsScore.lean`, `StepsPlainMax.lean`, `StepsBiasLoad.lean`, `StepsBiasLoad2.lean`,
`StepsPlainEnd.lean`), the first round from its named barrier to its closing poll
(`StepsBarr1.lean`, `StepsNarr1.lean`, `StepsP1.lean`, `StepsPwE.lean`) and a bias round from its
named barrier to its statistics store (`StepsBarrB.lean`), and a plain round's exponent stretch and
P part (`StepsPlainE3.lean`, `StepsPlainP0.lean`); the 5 others (the bias round's exponents, P part
and closing poll) are `NumSteps` (`DECISIONS.md`). Lane T1's
`frag_steps` takes this theorem and the open states' steps. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **The numeric states not stepped yet**: those whose step runs local code reading data
registers that the data table does not name yet. -/
def D.numeric (d : D) : Bool :=
  match d.site with
  | .narr .bias | .parr .bias | .pwend .bias => true
  | .pst .bias 0 => d.k.val == 1
  | .pst .bias 1 => true
  | _ => false

/-- **The step obligation at every state that is not numeric.** -/
theorem stepAt_ctl (hp : Pre p L m) (hg : g < L.threads) (hw : g % L.block / 32 < 8) (d : D)
    (hn : d.numeric = false) : (codeD p L g).StepAt d := by
  by_cases hi : (d.k = 0 ∧ d.acc = [] ∧ d.site.first = true) ∨ d.site.midOk d.k d.acc
  swap
  · exact stepAt_junk hi
  obtain ⟨s, v, k, acc⟩ := d
  rcases hi with ⟨hk, ha, hf⟩ | hm
  · simp only at hk ha hf
    subst hk ha
    cases s with
    | setmax | bar1 => exact stepAt_start hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
    | word sk | down sk | total sk =>
      cases sk
      · exact stepAt_scan_first hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
      · exact stepAt_scan_loop hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
      · exact stepAt_scan_second hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
      · exact stepAt_scan_loop2 hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
    | up sk j =>
      cases sk
      · exact stepAt_scan_first hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
      · exact stepAt_scan_loop hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
      · exact stepAt_scan_second hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
      · exact stepAt_scan_loop2 hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
    | vote l | pre l | tiles l =>
      cases l
      · exact stepAt_select hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
      · exact stepAt_end hp hg hw ⟨_, v, 0, []⟩ rfl rfl (by simp)
    | wend l | barEnd l | exit l => exact stepAt_end hp hg hw ⟨_, v, 0, []⟩ rfl rfl (by simp)
    | q0 | q1 | uk => exact stepAt_req hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
    | fin _ | finarr => exact stepAt_fin hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
    | bld b c => exact stepAt_mid0 hp hg ⟨_, v, 0, []⟩ rfl rfl (.inl ⟨b, c, rfl⟩)
    | sld r c =>
      cases r
      · exact stepAt_sld hp hg ⟨_, v, 0, []⟩ rfl rfl ⟨c, .inl rfl⟩
      · exact stepAt_sld hp hg ⟨_, v, 0, []⟩ rfl rfl ⟨c, .inr rfl⟩
      · exact stepAt_mid0 hp hg ⟨_, v, 0, []⟩ rfl rfl (.inr (.inr (.inr ⟨c, rfl⟩)))
    | sldw c => simp [Site.first] at hf
    | wq => exact stepAt_first_ctl hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
    | pwst r j =>
      cases r <;> fin_cases j
      · exact stepAt_pwst1_0 hp hg v
      · exact stepAt_pwst1_1 hp hg v
      · exact stepAt_bias_ctl hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
      · exact stepAt_bias_ctl hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
      · exact stepAt_pwstP_0 hp hg v
      · exact stepAt_pwstP_1 hp hg v
    | ws r =>
      cases r
      · exact stepAt_first_ctl hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
      · exact stepAt_bias_ctl hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
      · exact stepAt_plain_ctl hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
    | pws r | pel r | parr2 r =>
      cases r
      · first
        | exact stepAt_pws1 hp hg v
        | exact stepAt_pel1 hp hg v
        | exact stepAt_parr2_1 hp hg v
      · exact stepAt_bias_ctl hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
      · first
        | exact stepAt_pwsP hp hg v
        | exact stepAt_pelP hp hg v
        | exact stepAt_parr2P hp hg v
    | wb b | fence b =>
      cases b
      · exact stepAt_first_ctl hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
      · exact stepAt_bias_ctl hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
    | stat pl =>
      cases pl
      · exact stepAt_bias_ctl hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
      · exact stepAt_plain_ctl hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
    | pst r q =>
      cases r <;> fin_cases q <;> simp [D.numeric] at hn
      · exact stepAt_mid0 hp hg ⟨_, v, 0, []⟩ rfl rfl (.inr (.inl rfl))
      · exact stepAt_pst1_1 hp v
      · exact stepAt_pst1_2 hp hg v
      · exact stepAt_pst1_3 hp hg v
      · exact stepAt_mid0 hp hg ⟨_, v, 0, []⟩ rfl rfl (.inr (.inr (.inl rfl)))
      · exact stepAt_bias_ctl hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
      · exact stepAt_bias_ctl hp hg ⟨_, v, 0, []⟩ rfl rfl (by simp)
      · exact stepAt_pstP_0 hp v
      · exact stepAt_pstP_1 hp v
      · exact stepAt_pstP_2 hp hg v
      · exact stepAt_pstP_3 hp hg v
    | pwend r =>
      cases r
      · exact stepAt_pwend1 hp v
      · simp [D.numeric] at hn
      · exact stepAt_pwend_plain hp v
    | narr r | parr r =>
      cases r <;> simp [D.numeric] at hn
      all_goals first
        | exact stepAt_narr1 hp v
        | exact stepAt_parr1 hp v
        | exact stepAt_narrP hp v
        | exact stepAt_parrP hp v
    | bsync b =>
      cases b
      · exact stepAt_bsync1 hp v
      · exact stepAt_bsyncB hp v
    | barr b =>
      cases b
      · exact stepAt_barr1 hp v
      · exact stepAt_barrB hp v
  · cases s with
    | bld b c =>
      simp only [Site.midOk] at hm
      match k, acc, hm with
      | 0, [], _ => exact stepAt_mid0 hp hg ⟨_, v, 0, []⟩ rfl rfl (.inl ⟨b, c, rfl⟩)
      | 1, acc, hm => exact stepAt_bld1 hp hg ⟨_, v, 1, acc⟩ rfl hm.1 ⟨b, c, rfl⟩
      | 2, acc, hm => exact stepAt_bld2 hp hg ⟨_, v, 2, acc⟩ rfl hm.1 ⟨b, c, rfl⟩
      | 3, acc, hm => exact stepAt_bld3 hp b c v acc hm.1
    | sldw c =>
      simp only [Site.midOk] at hm
      obtain ⟨rfl, rfl⟩ := hm
      by_cases h3 : c.val < 3
      · exact stepAt_sldw hp c h3 v
      · have : c = 3 := Fin.ext (by omega)
        subst this; exact stepAt_sldw3 hp v
    | pst r q =>
      cases r <;> fin_cases q <;> simp [Site.midOk] at hm <;> obtain ⟨rfl, rfl⟩ := hm <;>
        simp [D.numeric] at hn
      exact stepAt_pst1_0s hp v
    | _ => simp [Site.midOk] at hm

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
