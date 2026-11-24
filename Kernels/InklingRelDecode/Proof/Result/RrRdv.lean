-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.RdSLoad
public import Kernels.InklingRelDecode.Proof.Interface.RrArrive

@[expose] public section

/-!
# The rendezvous of the S load (`Rd.SRdv`)

The softmax thread's `tcgen05.wait::ld` after the S load of iteration `i` is base-causally before
an event of thread 0 with at most `i / 2` earlier arrivals on `p_ready (i % 2)`.

Thread 0 of the CTA passes the arrival of block `i` (`Rr.sm_reaches_arrive`), and its earlier
arrivals on `p_ready (i % 2)` number `i / 2` (`Rr.arr_cnt`). The route of the CTA
(`Mbar.Route.soft_bar`) gives, for that arrival, a `bar.sync 0, 128` of thread 0 before it and the
`bar.sync 0, 128` of the softmax thread with the same barrier-0 ordinal, which comes after the
thread's `i / 2 + 1` successful polls of `s_ready (i % 2)`. The poll of iteration `i` is two
events before the load, so that event is after the wait that follows the load (the events between
the poll and the load's wait are a shuffle, the load and the wait: no barrier). Named barrier 0's
rendezvous (`Bar.bar128Causal`) gives the base causality to the event after thread 0's
`bar.sync`, which is at or before its arrival.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Rr
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (pReady sReady)

noncomputable section
set_option maxRecDepth 100000
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem below2_self (i : Nat) : SO.below2 (i % 2) i = i / 2 := by
  unfold SO.below2
  omega

/-- **The events between the poll of iteration `i` and the wait after the S load are no
barrier.** The wait is after any `bar.sync 0, 128` whose prefix has the poll's successful polls
of `s_ready (i % 2)`. -/
theorem bar_after_ldS (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k pc a : Nat} {d : Sm.D}
    {vals : List Value} {sh : TcShape} (hg : g < L.threads)
    (hex : ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .ldS)
    (he : X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩) {aa pc2 : Nat}
    (hbar : X.get (g, aa) = some ⟨pc2, .bar 0 (some 128) .sync⟩)
    (hpolls : d.i / 2 + 1 ≤ okPolls (sReady L (g / L.block) (d.i % 2)) ((X.tr g).take aa)) :
    ∃ wl pcw, k < wl ∧ X.get (g, wl) = some ⟨pcw, .tc .waitLd⟩ ∧ wl < aa := by
  have hk : k ≤ (X.tr g).length := (len_of_get he).le
  obtain ⟨d', hσ', hs', -⟩ := ldS_succ hX hf hg he hσ hs
    (later_of_exit he (fun _ h => by cases h) hex)
  have hk1 := lt_length_of_last hX hf hex hσ'
  obtain ⟨e1, he1⟩ : ∃ e1, X.get (g, k + 1) = some e1 := ⟨_, List.getElem?_eq_getElem hk1⟩
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he1 hσ' (by simp [ExitState])
  have hblk : L.block % 32 = 0 := by rw [hpre.block]
  have hev := Sm.shape_waitLd hblk (fired_sm hF) hs'
  rw [hev] at he1
  refine ⟨k + 1, _, by omega, he1, ?_⟩
  obtain ⟨k2, d2, d1, e2, e1', hk2, hge2, hge1, hσ2, hs2, hi2, -, -, -, pcs, recv, ok, hev1⟩ :=
    ldS_back hX hf hg hk hσ hs
  have hcnt := ((Rd.sm_cnt hpre hX hf hg k2 (by omega) _ hσ2).2 d2 rfl).s (d.i % 2)
    (Nat.mod_lt _ (by omega))
  have hsp : SO.smPolled d2 = d2.i := by simp [SO.smPolled, hs2]
  rw [hsp, hi2, below2_self] at hcnt
  have hge : (X.tr g)[k2 + 1]? = some e1' := hge1
  have hgk : (X.tr g)[k2 + 2]? = some ⟨pc, .tc (.ld a vals sh)⟩ := by
    rw [← show k = k2 + 2 from hk2]
    exact he
  have hga : (X.tr g)[aa]? = some ⟨pc2, .bar 0 (some 128) .sync⟩ := hbar
  by_contra hle
  have hle' : aa ≤ k + 1 := by omega
  rcases Nat.lt_or_ge k2 aa with h2 | h2
  · -- the barrier would be one of the three events after the poll
    have : aa = k2 + 1 ∨ aa = k2 + 2 ∨ aa = k2 + 3 := by omega
    rcases this with rfl | rfl | rfl
    · rw [hge, hev1] at hga
      simp at hga
    · rw [hgk] at hga
      simp at hga
    · have : X.get (g, k2 + 3) = some ⟨Sm.evPc d'.site, .tc .waitLd⟩ := by
        have : k2 + 3 = k + 1 := by omega
        rw [this]; exact he1
      rw [hbar] at this
      simp at this
  · have h3 : okPolls (sReady L (g / L.block) (d.i % 2)) ((X.tr g).take aa) ≤
        okPolls (sReady L (g / L.block) (d.i % 2)) ((X.tr g).take k2) :=
      (List.take_sublist_take_left h2).countP_le
    omega

/-- **`Rd.SRdv`**: the wait after the S load is base-causally before an event of thread 0 with at
most `i / 2` arrivals on `p_ready (i % 2)`. -/
theorem sRdv_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hc : Complete L X) (G : SrPkg L kernel asms mem0 X) :
    Rd.SRdv Q L X G := by
  intro g k pc a d vals sh hg hσ hs he
  have hcl : g / L.block < L.grid := cta_lt hX ⟨_, he⟩
  have H := G.ctx (g / L.block) hcl
  have hI := Sv.sm_inv_at hX hf he hσ
  have hdef : g % L.block < 128 := hI.tid
  have hlt : d.i < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
    rw [← r26_eq hpre hX hf hg he hσ]
    exact (hI.late (by rw [hs]; trivial)).2.2
  obtain ⟨g0, hg0, hg0c, hlead, hcz, hcx⟩ := thread0 hpre hg
  obtain ⟨kA, pcA, dA, hσA, hsA, hiA, heA⟩ := sm_reaches_arrive hpre hX hf hg0
    (last_of_complete hX hc hg0) hlead (i0 := d.i) (by rw [hcz, hcx]; exact hlt)
  have hlenA : kA < (X.tr g0).length := len_of_get heA
  rw [hg0c] at heA
  have hb2 : d.i % 2 < 2 := Nat.mod_lt _ (by omega)
  have hp0 : G.p0 (g / L.block) = g0 :=
    (H.facts.p_arrive (m := pReady L (g / L.block) (d.i % 2)) ⟨d.i % 2, hb2, rfl⟩ heA).1.symm
  have hcnt : arrivals (pReady L (g / L.block) (d.i % 2)) ((X.tr g0).take kA) = d.i / 2 := by
    have := ((arr_cnt hpre hX hf hg0 hlead kA hlenA.le _ hσA).2 dA rfl
      (d.i % 2) hb2)
    rw [hg0c, hiA, below2_self] at this
    exact this
  rw [← hp0] at heA
  obtain ⟨y, aa, pc1, pc2, hyA, hy, hag, hord, hsp, -⟩ :=
    H.route.soft_bar (b := d.i % 2) hb2 heA ⟨hg, rfl, hdef⟩
  rw [hp0, hcnt] at hsp
  obtain ⟨wl, pcw, hkw, hwl, hwa⟩ := bar_after_ldS hpre hX hf hg
    (last_of_complete hX hc hg) hσ hs he hag hsp
  refine ⟨wl, pcw, y + 1, hkw, hwl, ?_, ?_⟩
  · rw [hp0]
    have hB := Bar.bar128Causal hpre hX hf.sound hf.tracked (g := g) (p := g0) (a := aa) (y := y)
      (before := wl) (f := y + 1) hg hg0 hg0c.symm hdef (by omega) hag
      (by rw [hp0] at hy; exact hy) (by rw [hp0] at hord; exact hord) hwa (by omega)
      (by omega)
    exact hB
  · rw [hp0]
    have hm : arrivals (pReady L (g / L.block) (d.i % 2)) ((X.tr g0).take (y + 1)) ≤
        arrivals (pReady L (g / L.block) (d.i % 2)) ((X.tr g0).take kA) :=
      (List.take_sublist_take_left (by omega)).countP_le
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.Rr
