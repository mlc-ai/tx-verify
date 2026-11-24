-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.RrRdv
public import Kernels.InklingRelDecode.Proof.Result.RdOLoad
public import Kernels.InklingRelDecode.Proof.Interface.KkBar

@[expose] public section

/-!
# The rendezvous of the rescale load (`Rd.ORdv`) and the `P` stores after the S load
(`Rd.SPstAfter`)

Both go through named barrier 0 at the site `bar20` of the iteration. The barrier-0 ordinal is
matched by the counts of `Interface.Kk.cnt_same`: when the decisions of every iteration agree in
the CTA (`Lk.DecAgree`, proved for every iteration by `Lk.decAgree_every`), two default threads
of a CTA at `bar20` of one iteration have made the same number of barrier-0 events. With that,
`Mbar.Route.soft_bar` is not needed: the pairs of `bar.sync 0, 128` events are the threads' own
`bar20` states.

* `oRdv_of`: the rescale load of iteration `i` is followed by its `tcgen05.wait::ld`, then by
  `bar24` and `bar20` (one more barrier-0 event than at the load, `Kk.cnt_val`); thread 0's
  `bar20` of iteration `i` has the same ordinal (`Kk.cnt_same`) and is followed by its `tmemSt`
  state, where its arrivals on `p_ready (i % 2)` number `i / 2` (`Rr.arr_cnt`).
  `Bar.bar128Causal` gives the base causality from the wait to that state's event.
* `sPstAfter_of`: the S load of iteration `i` is followed by its wait and later by `bar20` of
  iteration `i` (more shuffles at `bar20` than at the load, `Kk.shfl_val`). A `P` store of a
  block `i' ≥ i` is at the state `tmemSt` of an iteration `j ≥ i'` of its thread (the gate's poll
  of `s_ready (i' % 2)` is counted by `Rd.sm_cnt`), which has more barrier-0 events before it
  than the storing thread's own `bar20` of iteration `i`; so that `bar20` is before the store, and
  `Bar.bar128Causal` orders the load's wait before the store.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Kk
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Interface.Kk
open PTX.Kernels.InklingRelDecode.Proof.Lk5B PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Interface.B0N (cnt0 C0 Dc)
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk (DecAgree)
open PTX.Kernels.InklingRelDecode.Proof.EvW (pReady sReady)

noncomputable section
set_option maxRecDepth 100000
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem cnt0_mono (X : Execution) (g : Nat) {a b : Nat} (h : a ≤ b) : cnt0 X g a ≤ cnt0 X g b :=
  (List.take_sublist_take_left h).countP_le

theorem cnt_mono (c : Event → Bool) (X : Execution) (g : Nat) {a b : Nat} (h : a ≤ b) :
    Lk.cnt c X g a ≤ Lk.cnt c X g b :=
  (List.take_sublist_take_left h).countP_le

/-- An event that is no barrier-0 event leaves the count unchanged. -/
theorem cnt0_succ_of {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hb : Execution.isBarId 0 e = false) : cnt0 X g (k + 1) = cnt0 X g k := by
  unfold cnt0
  rw [countP_take_succ _ he, hb]
  simp

/-- An event that is no shuffle leaves the shuffle count unchanged. -/
theorem shfl_succ_of {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hb : Execution.isShfl e = false) : Lk.cnt Execution.isShfl X g (k + 1) =
      Lk.cnt Execution.isShfl X g k := by
  unfold Lk.cnt
  rw [countP_take_succ _ he, hb]
  simp

/-- `RD` grows along the iterations from `bar20` of iteration `i` to `tmemSt` of `j ≥ i`. -/
theorem rd_le (Dc : Nat → Prop) {d d' : Sm.D} (hs : d.site = .bar20) (hs' : d'.site = .tmemSt)
    (hi : d.i ≤ d'.i) : RD Dc d ≤ RD Dc d' := by
  unfold RD
  rw [hs, hs']
  simp only [postR, true_and]
  rcases Nat.lt_or_eq_of_le hi with hlt | heq
  · have h1 := nResc_mono Dc (show d.i + 1 ≤ d'.i by omega)
    rw [nResc_succ] at h1
    split_ifs at h1 ⊢ <;> omega
  · rw [heq]

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hc : Complete L X) (hD : ∀ c j, DecAgree Q L X c j)
include hpre hX hf hc hD

/-- **`Rd.ORdv`**: the wait after the rescale load of iteration `i` is base-causally before an
event of thread 0 with at most `i / 2` arrivals on `p_ready (i % 2)`. -/
theorem oRdv_of (G : SrPkg L kernel asms mem0 X) : Rd.ORdv Q L X G := by
  intro g k pc a d vals sh pcw hg hσ hs he hw
  have hcl : g / L.block < L.grid := cta_lt hX ⟨_, he⟩
  have H := G.ctx (g / L.block) hcl
  have hI := Sv.sm_inv_at hX hf he hσ
  have hdef : g % L.block < 128 := hI.tid
  have hlt : d.i < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
    rw [← Rr.r26_eq hpre hX hf hg he hσ]
    exact (hI.late (by rw [hs]; trivial)).2.2
  have hk : k ≤ (X.tr g).length := (len_of_get he).le
  obtain ⟨hJ, hv⟩ := cnt_val hpre hX hf hg (hD _) hk hσ
  have hres : ¬ Dc Q L X (g / L.block) d.i := hJ.2 (by rw [hs]; rfl)
  have hi1 : 1 ≤ d.i := hJ.1 (Or.inr (by rw [hs]; rfl))
  -- the thread's own `bar20` of the iteration, after the wait
  obtain ⟨kB, dB, -, pcB, hσB, hsB, hiB, heB, -, -, -, -⟩ :=
    sm_reaches_bar20 hpre hX hf hc hg hdef hlt
  have hkB : kB ≤ (X.tr g).length := (len_of_get heB).le
  obtain ⟨-, hvB⟩ := cnt_val hpre hX hf hg (hD _) hkB hσB
  have hcB : (cnt0 X g kB : Int) = cnt0 X g k + 1 := by
    rw [hvB, hv, hsB, hs, hiB]
    simp only [phi, RD, postR, hsB, hs, hiB, hres, hi1]
    simp
    ring
  have hwB : k + 1 < kB := by
    by_contra hle
    have h1 := cnt0_mono X g (show kB ≤ k + 1 by omega)
    rw [cnt0_succ_of he (by simp [Execution.isBarId])] at h1
    omega
  -- thread 0 of the CTA and its `bar20` of the iteration
  obtain ⟨g0, hg0, hg0c, hlead, hcz, hcx⟩ := Rr.thread0 hpre hg
  obtain ⟨kA, pcA, dA, -, -, -, heA⟩ := Rr.sm_reaches_arrive hpre hX hf hg0
    (Rr.last_of_complete hX hc hg0) hlead (i0 := d.i) (by rw [hcz, hcx]; exact hlt)
  rw [hg0c] at heA
  have hb2 : d.i % 2 < 2 := Nat.mod_lt _ (by omega)
  have hp0 : G.p0 (g / L.block) = g0 :=
    (H.facts.p_arrive (m := pReady L (g / L.block) (d.i % 2)) ⟨d.i % 2, hb2, rfl⟩ heA).1.symm
  have hdef0 : g0 % L.block < 128 := by rw [hlead]; omega
  obtain ⟨kB0, dB0, ds0, pcB0, hσB0, hsB0, hiB0, heB0, hσT0, hsT0, hiT0, hlen0⟩ :=
    sm_reaches_bar20 hpre hX hf hc hg0 hdef0 (i0 := d.i) (by rw [hcz, hcx]; exact hlt)
  have hord : cnt0 X g kB = cnt0 X g0 kB0 :=
    cnt_same hpre hX hf hg hg0 hg0c.symm (hD _) hkB (len_of_get heB0).le hσB hσB0
      (by rw [hsB, hsB0]) (by rw [hiB, hiB0])
  have hB := Bar.bar128Causal hpre hX hf.sound hf.tracked (g := g) (p := g0) (a := kB)
    (y := kB0) (before := k + 1) (f := kB0 + 1) hg hg0 hg0c.symm hdef hdef0 heB heB0 hord hwB
    (by omega) hlen0
  refine ⟨kB0 + 1, by rw [hp0]; exact hB, ?_⟩
  rw [hp0]
  have := (Rr.arr_cnt hpre hX hf hg0 hlead (kB0 + 1) hlen0.le _ hσT0).2 ds0 rfl (d.i % 2) hb2
  rw [hg0c, hiT0, Rr.below2_self] at this
  omega

/-- **`Rd.SPstAfter`**: a `P` store of a block `i' ≥ i` of the CTA comes after the S load of
iteration `i`. -/
theorem sPstAfter_of (G : SrPkg L kernel asms mem0 X) : Rd.SPstAfter Q L X G := by
  intro g k pc a d vals sh t sk i' a' vals' sh' hg hσ hs he hP hT hii _
  have hcl : g / L.block < L.grid := cta_lt hX ⟨_, he⟩
  have hI := Sv.sm_inv_at hX hf he hσ
  have hdef : g % L.block < 128 := hI.tid
  have hlt : d.i < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
    rw [← Rr.r26_eq hpre hX hf hg he hσ]
    exact (hI.late (by rw [hs]; trivial)).2.2
  have hk : k ≤ (X.tr g).length := (len_of_get he).le
  -- the wait after the load
  obtain ⟨d', hσ', hs', -⟩ := ldS_succ hX hf hg he hσ hs
    (later_of_exit he (fun _ h => by cases h) (Rr.last_of_complete hX hc hg))
  have hk1 := lt_length_of_complete hX hf hc hg hσ'
  obtain ⟨e1, he1⟩ : ∃ e1, X.get (g, k + 1) = some e1 := ⟨_, List.getElem?_eq_getElem hk1⟩
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he1 hσ' (by simp [ExitState])
  have hblk : L.block % 32 = 0 := by rw [hpre.block]
  have hev := Sm.shape_waitLd hblk (fired_sm hF) hs'
  rw [hev] at he1
  -- the thread's `bar20` of the iteration, after the wait (more shuffles)
  obtain ⟨kB, dB, -, pcB, hσB, hsB, hiB, heB, -, -, -, -⟩ :=
    sm_reaches_bar20 hpre hX hf hc hg hdef hlt
  have hkB : kB ≤ (X.tr g).length := (len_of_get heB).le
  have hwB : k + 1 < kB := by
    by_contra hle
    have h1 := cnt_mono Execution.isShfl X g (show kB ≤ k + 1 by omega)
    rw [shfl_succ_of he (by simp [Execution.isShfl])] at h1
    rw [shfl_val hpre hX hf hg hkB hσB, shfl_val hpre hX hf hg hk hσ] at h1
    simp only [Sm.smW, Sm.smOff, hs, hsB, hiB] at h1
    split_ifs at h1 <;> omega
  -- the storing thread and the state of its store
  obtain ⟨ht, htc, htd⟩ := hP.gate.soft
  obtain ⟨pcs, hget⟩ := hT
  obtain ⟨hsh, -, -⟩ := hP.shape
  subst hsh
  have hne : ∀ pc' f, (⟨pcs, .tc (.st a' vals' (.s16x32bx2 32))⟩ : Event) ≠ ⟨pc', .ub f⟩ := by
    intro pc' f h
    simp only [Event.mk.injEq] at h
    cases h.2
  obtain ⟨s, hσs⟩ := Frame.event_state hf.sound hX hf.tracked hget hne
  obtain ⟨dt, rfl, hst⟩ := tcst_event_state hf.sound hX hget hσs
  have hsT : dt.site = .tmemSt := by
    rcases hst with h | h
    · exact h
    · exfalso
      obtain ⟨u', hF'⟩ := fired_cont hX hf ht hget hσs (by simp [ExitState])
      obtain ⟨vals2, -, -, -, hev2⟩ := Sm.shape_stO (fired_sm hF') h
      simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at hev2
      obtain ⟨-, -, -, hsh2⟩ := hev2
      simp at hsh2
  have hsk : sk ≤ (X.tr t).length := (len_of_get hget).le
  -- the store's iteration is at least `i'`
  have hjt : i' ≤ dt.i := by
    obtain ⟨jp, pcp, p, sc, hjp, hwp, hqp⟩ := hP.gate.poll
    have hb2 : i' % 2 < 2 := Nat.mod_lt _ (by omega)
    have hcnt := ((Rd.sm_cnt hpre hX hf ht sk hsk _ hσs).2 dt rfl).s (i' % 2) hb2
    have hwp' : (X.tr t)[jp]? =
        some ⟨pcp, .wait (sReady L (g / L.block) (i' % 2)) p true true sc⟩ := hwp
    have hp1 := Rd.okPolls_take_succ (sReady L (g / L.block) (i' % 2)) hwp'
    have hok : okPoll (sReady L (g / L.block) (i' % 2))
        ⟨pcp, .wait (sReady L (g / L.block) (i' % 2)) p true true sc⟩ = true := by
      simp [okPoll, sourceWaitSuccess]
    simp only [hok, ↓reduceIte] at hp1
    have hm := Rd.okPolls_mono (sReady L (g / L.block) (i' % 2)) (X.tr t)
      (show jp + 1 ≤ sk by omega)
    rw [htc] at hcnt
    simp only [SO.smPolled, hsT, SO.below2] at hcnt
    omega
  -- the storing thread's `bar20` of iteration `i`, before the store
  have hct : t / L.block = g / L.block := htc
  have hltt : d.i < Q.numIters (ProA.cta L t .z) (ProA.cta L t .x) := by
    rw [ProA.cta_eq_of_block hct .z, ProA.cta_eq_of_block hct .x]
    exact hlt
  obtain ⟨yb, db, -, pcb, hσb, hsb, hib, heb, -, -, -, -⟩ :=
    sm_reaches_bar20 hpre hX hf hc ht htd hltt
  have hyb : yb ≤ (X.tr t).length := (len_of_get heb).le
  have hyl : yb < sk := by
    obtain ⟨-, hv1⟩ := cnt_val hpre hX hf ht (hD _) hyb hσb
    obtain ⟨-, hv2⟩ := cnt_val hpre hX hf ht (hD _) hsk hσs
    have hr := rd_le (Dc Q L X (t / L.block)) hsb hsT (show db.i ≤ dt.i by omega)
    have hlt2 : (cnt0 X t yb : Int) < cnt0 X t sk := by
      rw [hv1, hv2, hsb, hsT]
      simp only [phi]
      have : (db.i : Int) ≤ dt.i := by exact_mod_cast (show db.i ≤ dt.i by omega)
      have : ((RD (Dc Q L X (t / L.block)) db : Nat) : Int) ≤
          ((RD (Dc Q L X (t / L.block)) dt : Nat) : Int) := by exact_mod_cast hr
      omega
    by_contra hge
    have := cnt0_mono X t (show sk ≤ yb by omega)
    omega
  have hord : cnt0 X g kB = cnt0 X t yb :=
    cnt_same hpre hX hf hg ht hct.symm (hD _) hkB hyb hσB hσb (by rw [hsB, hsb])
      (by rw [hiB, hib])
  have hB := Bar.bar128Causal hpre hX hf.sound hf.tracked (g := g) (p := t) (a := kB) (y := yb)
    (before := k + 1) (f := sk) hg ht hct.symm hdef htd heB heb hord hwB hyl (len_of_get hget)
  exact .inl ⟨(g, k + 1), ⟨_, he1⟩, rfl, by simp, .inl hB⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Kk
