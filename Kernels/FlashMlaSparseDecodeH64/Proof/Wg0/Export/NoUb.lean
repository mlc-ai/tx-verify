-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NoUbAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Payloads
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.NoUbView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataState
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictEvent
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NoUbLive
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NoUbState
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Shape
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.LseSeq
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.PollNoUb
import Lemmas.Kernel.FrameU

@[expose] public section

/-! # Warpgroup 0 makes no undefined behaviour

`wg0_noUb`: an event fired from a state of warpgroup 0 of a followed lane is no undefined
behaviour, and the machine stops at it only if it is the exit, from the typing of the words the
lanes of warps 0 to 3 read (`W0Payloads`).

The state before the event is a live state of the data machine whose prefix is valid
(`W0Valid.of_payloads`) and holds the words loaded (`w0_upto`); the step into it is strict
(`w0_strict_at`), so the event fires from the template of its site from a strictly good state, and
the template is no fault (`w0_nonub`) when the registers the site's payload reads hold words (the
context of the window, `payAll_of`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **Warpgroup 0 makes no undefined behaviour.** -/
theorem wg0_noUb (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hP : W0Payloads P L X) (k : Nat) (e : Event)
    (he : X.get (g, k) = some e) (ha : AliveIn P L X g k .wg0) :
    (∀ f, e.kind ≠ .ub f) ∧ (StopsAt P L X g k → e.kind = .exit) := by
  obtain ⟨σ, hσ, hr⟩ := aliveIn_iff.mp ha
  cases hr with
  | wg0 d0 n0 =>
  have hg := Frame.lt_of_get hX he
  have hbef := noUbBefore_of_get hX he
  obtain ⟨hw, hC0, hL0⟩ := Wg0.Data.w0_alive_facts hFw hg hbef hσ
  have hTL : ThreadLive P L X g k := ⟨_, hσ⟩
  obtain ⟨hv, hLd⟩ := w0_upto hp hX hFw hw hP hg he hTL k le_rfl
  obtain ⟨st, hstk, hslot, hpre, hI, hPrev, hB⟩ :=
    followW_st hp hX hFw hw he hTL (w0_scale_rd hp) hv k le_rfl
  obtain ⟨d, n, rfl, hdc⟩ : ∃ d n, st = (.inr ⟨.inl .wg0, d⟩, n) ∧ d.c = d0 := by
    have h1 := control_of_data hstk
    rw [hσ] at h1
    obtain ⟨q, nq⟩ := st
    rcases hslot with ⟨b, hb⟩ | ⟨d, hd⟩
    · obtain rfl : q = .inl b := hb
      simp [eraseThread, Code.eraseSum] at h1
    · obtain rfl : q = .inr ⟨.inl .wg0, d⟩ := hd
      simp [eraseThread, Code.eraseSum, Code.eraseStubs, eraseFrag, wg0Erase] at h1
      exact ⟨d, nq, rfl, h1.1.symm⟩
  subst hdc
  obtain ⟨t, o, ins, hgood, hc, hf⟩ := Wg0.Data.w0_strict_at hp hX hFw hw hP hg he hTL hstk
  have hat : (Wg0.Data.code P L g (warpW L g)).AtD d t := hgood.1
  have hi : (Wg0.Data.code P L g (warpW L g)).inv d := hgood.2
  have hc' : kernel.code[(Wg0.Data.code P L g (warpW L g)).pc d]? = some ins := hc
  have hf' : Fires ((Wg0.Data.code P L g (warpW L g)).pc d)
      (eventTmpl Assumptions.all L g t ins.op) e o := hf
  have hK : Wg0.EvK P L g (warpW L g) d.c e :=
    Wg0.shapeK hp (Wg0.Data.w0_ctl_atD hat) hi hc' hf'
  have hpc : e.pc = d.c.site.pc := EventFrame.fires_source_pc hf'
  have hsink : d.c.site = .sink → eqz64 (pw8 (P.sinkBase.getD 0)) = false := by
    intro hsk
    cases k with
    | zero =>
      have := Wg0.Data.site_zero hstk rfl
      rw [hsk] at this
      cases this
    | succ j =>
      rcases hPrev d rfl j rfl with ⟨hs, -⟩ | ⟨f, c, -, -, hsucc, -⟩
      · rw [hsk] at hs
        cases hs
      · obtain ⟨-, hptr, -⟩ := Wg0.sink_pred hsucc hsk
        exact hptr
  have hs : Wg0.Data.W0State P d.c := Wg0.Data.w0State_of_ref hC0 hL0 hsink
  have htid : tidOf L g < 128 := by
    have h1 := tidOf_eq hp g
    have h2 := tidOf_x_eq hp g
    simp only [warp] at hw
    omega
  have hnu : ∀ f, e.kind ≠ .ub f := by
    intro f hfk
    have hpay : Wg0.Data.PayAll t ins := by
      by_cases hps : Wg0.Data.paySite d.c.site = false
      · exact Wg0.Data.pay_of_free hps hc'
      · have hps' : Wg0.Data.paySite d.c.site = true := by simpa using hps
        obtain ⟨hIW, hOk, hCar, -, hIE, hSk⟩ := hI d rfl
        have hld : W0Loaded ((X.tr g).take k) e.pc := by
          rw [hpc]
          exact Wg0.Data.w0Loaded_of (hLd _ hstk d rfl) hIW hIE
        have hv1 := Wg0.Data.w0_valid_pay hp.scalePos hps' hpc hv hld
        obtain ⟨-, -, -, -, hF0⟩ := hat
        have hF := ((holds_append _ _ _).mp hF0).2
        have hctx : Wg0.Data.WCtx L g P.scale ((X.tr g).take k) d e :=
          ⟨w0_scale_rd hp, hIW, hOk, hCar, hSk, hIE, hpc, hi, hv1, hP g k e hg hw he, hld⟩
        exact Wg0.Data.payAll_of hctx hF hc'
    exact absurd hfk (Wg0.Data.w0_nonub hp ⟨hg, cta_lt hp hg⟩ htid rfl d hs hat hi hc' hf' hpay f)
  refine ⟨hnu, fun hst => ?_⟩
  have h1 := Code.counted_next_eq_none_iff.mp (next_none_of_stops he hσ hst)
  have h2 : Wg0.Control.succ P L g (warpW L g) d.c e = none := by
    simpa only [Code.glue_next_inr, Option.map_eq_none_iff] using h1
  refine Wg0.Data.succ_none_exit h2 hK hnu (fun hs x bs hk => ?_)
  have hpl := hP g k e hg hw he
  rcases hs with hs | hs | hs
  · obtain ⟨_, _, -, -, hr⟩ := hpl.sink x bs hk (by rw [hpc, hs]; rfl)
    exact ⟨_, hr⟩
  · exact hpl.length x bs hk (Or.inl (by rw [hpc, hs]; rfl))
  · exact hpl.length x bs hk (Or.inr (by rw [hpc, hs]; rfl))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
