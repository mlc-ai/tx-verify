-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidCore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidCut
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidRestart
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SinkValid
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.VoteSeen
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Payloads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Loaded
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.WinCanon
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.LdStep

@[expose] public section

/-! # The step of the valid trace over the lane's events

`w0_valid_snoc`: the event `e` at index `n` of a lane of warps 0 to 3 (no undefined behaviour at
it or before it) keeps the prefix valid, from the typing of its word (`W0EvPayload`), the block's
pc bound (`W0Bound`) and the words the block has loaded (`W0Loaded`) at its pc; the kind of the
event at the pcs of the loads is a hypothesis (it is the data machine's, `EvK`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The peer element's pair is unchanged or valid**: the first element of a pair leaves it, the
second finishes a valid pair (the first element's typing is its own payload). -/
theorem w0_peer_hnew (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) (hP : W0Payloads P L X) (hg : g < L.threads)
    {n k0 : Nat} {e : Event} (he : X.get (g, n) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hk0 : k0 < 8) (hpc : e.pc = 477 + 5 * k0) (hv : W0Valid P.scale ((X.tr g).take n)) :
    w0Peer ((w0Fin ((X.tr g).take n)).2 ++ [e]) k0 = w0Peer (w0Fin ((X.tr g).take n)).2 k0 ∨
      W0PeerOk (w0Peer ((w0Fin ((X.tr g).take n)).2 ++ [e]) k0) := by
  obtain ⟨a1, b1, el, hk, hel, -, hpar⟩ := w0_peer_el hp hX hFw hw hv hk0 he hub hpc
  rw [w0Fin_snd]
  have hr : (w0RdVal e).isSome := by simp [w0RdVal, hk]
  have hpf := (hP g n e hg hw he).peer a1 b1 hk ⟨k0, hk0, hpc⟩
  interval_cases el
  · exact Or.inl (w0Peer_snoc_first hpc hr hpar)
  · right
    obtain ⟨x, hx⟩ : ∃ x, ((w0Scan ((X.tr g).take n)).2.filter fun e =>
        e.pc = 477 + 5 * k0 && (w0RdVal e).isSome).getLast? = some x := by
      cases h : ((w0Scan ((X.tr g).take n)).2.filter fun e =>
        e.pc = 477 + 5 * k0 && (w0RdVal e).isSome).getLast? with
      | none =>
        rw [List.getLast?_eq_none_iff] at h
        rw [h] at hpar
        simp at hpar
      | some x => exact ⟨x, rfl⟩
    have hxm : x ∈ ((w0Scan ((X.tr g).take n)).2.filter fun e =>
        e.pc = 477 + 5 * k0 && (w0RdVal e).isSome) := by
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hx
      rw [hys]
      simp
    rw [List.mem_filter] at hxm
    obtain ⟨hxs, hxc⟩ := hxm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hxc
    obtain ⟨hxpc, hxr⟩ := hxc
    obtain ⟨a0, b0, hxk⟩ : ∃ a0 b0, x.kind = .rd a0 b0 := by
      unfold w0RdVal at hxr
      cases hh : x.kind <;> simp [hh] at hxr
      exact ⟨_, _, rfl⟩
    obtain ⟨i, hi, hget⟩ := w0_block_events X g n x (by rw [w0Fin_snd]; exact hxs)
    have px := (hP g i x hg hw hget).peer a0 b0 hxk ⟨k0, hk0, hxpc⟩
    exact w0Peer_second_ok hpc hk hxk hpar hx px hpf

/-- **An event of a lane keeps the prefix valid** (see the file header). -/
theorem w0_valid_snoc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) (hP : W0Payloads P L X) (hg : g < L.threads)
    {n : Nat} {e : Event} (he : X.get (g, n) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hbef : NoUbBefore X g n) (hv : W0Valid P.scale ((X.tr g).take n))
    (hb : W0Bound ((X.tr g).take n) e.pc) (hld : W0Loaded ((X.tr g).take n) e.pc)
    (kT : (e.pc = 278 ∨ e.pc = 280 ∨ e.pc = 283 ∨ e.pc = 285 ∨ e.pc ∈ w0OPcs) →
      ∃ x vals sh, e.kind = .tc (.ld x vals sh))
    (kR : (e.pc = 289 ∨ e.pc = 572 ∨ e.pc = 1157) → ∃ x bs, e.kind = .rd x bs) :
    W0Valid P.scale ((X.tr g).take (n + 1)) := by
  have hsc := hp.scalePos
  have hpay := hP g n e hg hw he
  have htk := trace_take_succ he
  by_cases h1 : e.pc = 103 ∨ e.pc = 156
  · rw [htk]
    exact w0Core_sink hsc h1 (fun h156 a bs hk => hpay.sink a bs hk h156) hv
  by_cases h2 : e.pc = 200
  · exact w0Valid_snoc_restart_hub hp hX hFw he hub hw h2 hv
  by_cases h3 : e.pc = 1122
  · exact w0Valid_snoc_cut_alive hp hX hFw (fun j f hf hj x => by
      rcases Nat.lt_or_ge j n with h | h
      · exact hbef.ne h hf x
      · obtain rfl : j = n := by omega
        rw [he] at hf
        cases hf
        exact hub x) hw he h3 hv
  rw [htk]
  by_cases h4 : e.pc = 278 ∨ e.pc = 280 ∨ e.pc = 283 ∨ e.pc = 285
  · obtain ⟨x, vals, sh, hk⟩ := kT (by rcases h4 with h | h | h | h <;> simp [h])
    have hvv : w0TcVals e = some vals := by simp [w0TcVals, hk]
    exact w0Core_score hsc (by omega) hvv hb (fun h => hpay.scoreHi vals hvv h)
      (fun h => hpay.scoreLo vals hvv h) hv
  by_cases h5 : e.pc = 289
  · obtain ⟨x, bs, hk⟩ := kR (Or.inl h5)
    exact w0Core_mask hsc h5 hk hb (hpay.mask x bs hk h5) hv
  by_cases h6 : ∃ k0 < 8, e.pc = 477 + 5 * k0
  · obtain ⟨k0, hk0, hpc⟩ := h6
    exact w0Core_peer hsc hk0 hpc hb (w0_peer_hnew hp hX hFw hw hP hg he hub hk0 hpc hv) hv
  by_cases h7 : e.pc = 572
  · obtain ⟨x, bs, hk⟩ := kR (Or.inr (Or.inl h7))
    exact (w0Core_pm hsc h7 hk hb (hpay.peerMax x bs hk h7) hv).1
  by_cases h8 : e.pc = 578
  · exact w0Core_vote h8 (hld.score (by omega) (by omega)).1 (hld.score (by omega) (by omega)).2
      (hld.mask (by omega) (by omega)) (fun k0 hk0 => hld.pair k0 hk0 (by omega) (by omega))
      (hld.peerMax (by omega) (by omega)) hv
  by_cases h9 : e.pc ∈ w0OPcs
  · obtain ⟨x, vals, sh, hk⟩ := kT (Or.inr (Or.inr (Or.inr (Or.inr h9))))
    have hvv : w0TcVals e = some vals := by simp [w0TcVals, hk]
    exact w0Core_opc hsc h9 hvv (hpay.acc vals hvv h9) hv
  by_cases h10 : e.pc = 1157
  · obtain ⟨x, bs, hk⟩ := kR (Or.inr (Or.inr h10))
    exact w0Core_pe hsc h10 hk (hpay.rowSum x bs hk h10) hv
  exact W0Valid.snoc_quiet hsc ⟨⟨⟨by unfold w0ArrSPc; omega, by unfold w0ArrLPc; omega⟩,
    ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega, by omega,
    fun k hk hc => h6 ⟨k, hk, hc⟩⟩, ⟨by omega, h9⟩, ⟨by omega, by omega⟩⟩ hv

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
