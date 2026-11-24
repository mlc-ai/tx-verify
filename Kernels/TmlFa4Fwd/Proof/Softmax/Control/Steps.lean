-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Arrivals
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.BarrierBias
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.BarrierFirst
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.BiasLast
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.BiasLoad
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Exponent
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.ExponentBias
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Fence
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Poll
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Probability
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.RoundBias
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.RoundFirst
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.RoundPlain
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Scheduler
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.ScoreBias
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.ScoreFirst
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.ScorePlain
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.ScoreWait
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Statistics
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Stores
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.SyncBias
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.SyncFirst

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control

private theorem invalid {p L g d} (h : ¬ (code p L g).inv d) : (code p L g).StepAtU d :=
  ⟨fun hi => (h hi).elim, fun _ _ hi => (h hi).elim⟩

private theorem firstStep {p L m g} (hp : Pre p L m) (hg : g < L.threads) (s : Site) (v : V)
    (hs : schedulerSite s = false) (hfirst : s.first = true) :
    (code p L g).StepAtU ⟨s,v,0,[]⟩ := by
  cases s with
  | wq => exact stepAt_wqU v
  | ws r =>
    cases r
    · exact stepAt_ws_firstU v
    · exact stepAt_ws_biasU v
    · exact stepAt_ws_plainU v
  | sld r c =>
    cases r
    · exact stepAt_sld_firstU c v
    · exact stepAt_sld_biasU c v
    · exact stepAt_sld_plainU c v
  | sldw _ => cases hfirst
  | wb b =>
    cases b
    · exact stepAt_wb_firstU v
    · exact stepAt_wb_biasU v
  | bld b c => exact stepAt_bld_midU b c v 0 [] (by decide)
  | fence b =>
    cases b
    · exact stepAt_fence_firstU hp v
    · exact stepAt_fence_biasU hp v
  | bsync b =>
    cases b
    · exact bsyncFirstOfSpan hp v (barrFirstSpan hp v)
    · exact bsyncBiasOfSpan hp v (barrBiasSpan hp v)
  | barr b =>
    cases b
    · exact stepAt_barrFirstU hp v
    · exact stepAt_barrBiasU hp v
  | stat b =>
    cases b
    · exact stepAt_stat_biasU v
    · exact stepAt_stat_plainU v
  | narr r =>
    cases r
    · exact stepAt_narr_firstU v
    · exact stepAt_narr_biasU hp v
    · exact stepAt_narr_plainU v
  | pst r q =>
    fin_cases q
    · cases r
      · exact stepAt_pst_first_waitU v
      · exact stepAt_pst_bias_waitU v
      · exact stepAt_pst_plain0U v
    · cases r
      · exact stepAt_pst_first1U v
      · exact stepAt_pst_bias1U v
      · exact stepAt_pst_plain1U v
    · exact stepAt_probabilityU hp hg _ r v (.inl rfl)
    · exact stepAt_probabilityU hp hg _ r v (.inr (.inr (.inl rfl)))
  | pwst r k =>
    fin_cases k
    · exact stepAt_probabilityU hp hg _ r v (.inr (.inl rfl))
    · exact stepAt_probabilityU hp hg _ r v (.inr (.inr (.inr (.inl rfl))))
  | pws r => exact stepAt_probabilityU hp hg _ r v (by simp)
  | pel r => exact stepAt_probabilityU hp hg _ r v (by simp)
  | parr2 r => exact stepAt_probabilityU hp hg _ r v (by simp)
  | parr r =>
    cases r
    · exact stepAt_parr_firstU v
    · exact stepAt_parr_biasU v
    · exact stepAt_parr_plainU v
  | pwend r =>
    cases r
    · exact stepAt_pwend_firstU hp v
    · exact stepAt_pwend_biasU hp v
    · exact stepAt_pwend_plainU hp v
  | fin k =>
    fin_cases k
    · exact stepAt_fin_sumU v
    · exact stepAt_fin_maxU v
  | _ => cases hs

theorem stepAtU {p L m g} (hp : Pre p L m) (hg : g < L.threads) (hw : g % L.block / 32 < 8)
    (d : D) : (code p L g).StepAtU d := by
  cases hs : schedulerSite d.site with
  | true => exact stepAt_schedulerU hp hg hw d hs
  | false =>
    obtain ⟨s,v,k,acc⟩ := d
    by_cases hi : Inv ⟨s,v,k,acc⟩
    swap
    · exact invalid hi
    by_cases hb : ∃ b c, s = .bld b c
    · obtain ⟨b,c,rfl⟩ := hb
      by_cases h : k.val < 3
      · exact stepAt_bld_midU b c v k acc h
      · have he : k = 3 := Fin.ext (by omega)
        subst k
        exact stepAt_bld_lastU b c v acc
    have h : (k = 0 ∧ acc = [] ∧ s.first = true) ∨ s.midOk k acc := by
      cases s <;> first | exact hi | exact (hb ⟨_,_,rfl⟩).elim
    rcases h with ⟨rfl,rfl,hf⟩ | hm
    · exact firstStep hp hg _ _ hs hf
    cases s with
    | bld b c => exact (hb ⟨b,c,rfl⟩).elim
    | sldw c =>
      obtain ⟨rfl,rfl⟩ := hm
      fin_cases c
      · exact stepAt_sldw0U v
      · exact stepAt_sldw1U v
      · exact stepAt_sldw2U v
      · exact stepAt_sldw3U v
    | pst r q =>
      cases r <;> fin_cases q <;> simp only [Site.midOk] at hm
      all_goals obtain ⟨rfl,rfl⟩ := hm
      · exact stepAt_pst_first0U v
      · exact stepAt_pst_bias0U v
    | _ => cases hm

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
