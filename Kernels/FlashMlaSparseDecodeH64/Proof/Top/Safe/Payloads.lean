-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.W0Hq
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Payloads
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.TcSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.ScoreValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.OpcValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.PmValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.PeValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.PeerValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Result.PvWordAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MaskValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SinkValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.NcPay

@[expose] public section

/-! # The typing of warpgroup 0's words

`w0_payloads`: every event of warps 0 to 3 carries the typed words (`W0Payloads`), from the joint
induction `Safe.w0Joint` (the prefix before the event is valid, the Tensor Memory words below it
are known) and the clause lemmas, one per field. No event is assumed to be no undefined
behaviour: the event's own kind says so for each field. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem tcVals_kind {e : Event} {vals : List Value} (h : w0TcVals e = some vals) :
    ∀ f, e.kind ≠ .ub f := by
  obtain ⟨pc, kd⟩ := e
  intro f hf
  simp only [w0TcVals] at h hf
  rw [hf] at h
  cases h

/-- **The typing of warpgroup 0's words.** -/
theorem w0_payloads (hp : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hFw : Follow P L X) : W0Payloads P L X := by
  intro g k e hg hw he
  have hIn := Inputs.of_pre hp
  have J := Safe.w0Joint hp hIn hX hFw
  have hbc : ∀ w e', X.get w = some e' → Relation.TransGen (TcMma.TcStep L X) w (g, k) →
      TmRace.TmClaim L X w ∧ TmRace.RfClaim L X w := fun w e' h _ =>
    ⟨(J w e' h).2.1, (J w e' h).2.2⟩
  have hv : W0Valid P.scale ((X.tr g).take k) := by
    rcases k with _ | j
    · simpa using w0Valid_nil P.scale
    · have hl : j + 1 < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
      have hev : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem (Nat.lt_of_succ_lt hl)
      exact ((J (g, j) _ hev).1.1).valid hw (fun _ he' =>
        noUb_kind_of_lt hX he' (Nat.lt_succ_self j) hl)
  have hU : W0Under P L X g k := fun y j f hf hwy ht =>
    ((J (y, j) f hf).1.1).valid hwy fun _ he' => tcTrans_nonUb hX ht he'
  have hWB : W0Below P L X (w0Partner L g) g k := fun j e' hj ht =>
    ⟨hU _ j e' hj (w0Partner_facts hp hw hg).2.1 ht, tcTrans_nonUb hX ht hj⟩
  have hal : LaneUbFree X g k := noUbBefore_of_get hX he
  have hat : ∀ pc, 103 ≤ pc → pc < 1842 → Wg0At L g pc := fun _ h1 h2 => ⟨hw, h1, h2⟩
  have hEb := Safe.mmaElemBelow hp hIn hX hFw (b := (g, k)) fun h k2 ev hev htc hwh =>
    Wg0.W0Valid.take_le (hU h k2 ev hev hwh htc) (Nat.le_succ k2)
  have hscore : ∀ vals, w0TcVals e = some vals →
      (e.pc = 278 ∨ e.pc = 280 ∨ e.pc = 283 ∨ e.pc = 285) →
      vals.length = 32 ∧ ∀ c < 32, W0HiWord (vals.getD c (.pred false)) ∧
        W0LoWord (vals.getD c (.pred false)) := fun vals h hpc => by
    obtain ⟨vals', h', hlen, hpay⟩ := w0_pay_score hp hIn hX hFw he (tcVals_kind h) hw hpc hbc
    rw [h] at h'
    obtain rfl := Option.some.inj h'
    exact ⟨hlen, hpay⟩
  refine ⟨fun vals h hpc => ?_, fun vals h hpc => ?_, fun x bs hk hpc => ?_,
    fun x bs hk hpc => ?_, fun x bs hk hpc => ?_, fun x bs hk hpc => ?_, fun x bs hk hpc => ?_,
    fun x bs hk hpc => ?_, fun vals h hpc => ?_⟩
  · obtain ⟨hlen, hpay⟩ := hscore vals h (by omega)
    exact ⟨hlen, fun c hc => (hpay c hc).1⟩
  · obtain ⟨hlen, hpay⟩ := hscore vals h (by omega)
    exact ⟨hlen, fun c hc => (hpay c hc).2⟩
  · exact wg0_len_word_pre hp hX hFw hal he (hat _ (by omega) (by omega)) hpc hk
  · obtain ⟨pc, kd⟩ := e
    simp only at hk hpc
    subst hk hpc
    exact w0_pay_mask hp hX hFw (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw)
      (hIn.bar0 hp X hX hFw) (hIn.coord hp X hX hFw) hal he hw
  · obtain ⟨k0, hk0, hpc'⟩ := hpc
    obtain ⟨pc, kd⟩ := e
    simp only at hk hpc'
    subst hk hpc'
    exact w0_pay_peer hp hIn hX hFw hw hk0 he hWB hbc
  · obtain ⟨pc, kd⟩ := e
    simp only at hk hpc
    subst hk hpc
    obtain ⟨v, hrb, hc, hf⟩ := w0_pay_pm hp hIn hX hFw he hw hWB
    exact ⟨v, hrb, hc, hf⟩
  · exact wg0_sink_word_pre hp hX hFw hal he (hat _ (by omega) (by omega)) hpc hk
  · obtain ⟨pc, kd⟩ := e
    simp only at hk hpc
    subst hk hpc
    exact w0_pe_payload hp hIn hX hFw hw he hv hU
  · obtain ⟨vals', h', hlen, hpay⟩ := w0_pay_opc hp hIn hX hFw he (tcVals_kind h) hw hpc hbc hEb
    rw [h] at h'
    obtain rfl := Option.some.inj h'
    exact ⟨hlen, hpay⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
