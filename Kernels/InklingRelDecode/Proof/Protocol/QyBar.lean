-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.PxAll
public import Kernels.InklingRelDecode.Proof.Protocol.HsAll
public import Kernels.InklingRelDecode.Proof.Protocol.SrOrder
public import Kernels.InklingRelDecode.Proof.Interface.KkBar

@[expose] public section

/-!
# The softmax threads' states that a poll of `p_ready` and a later store imply, on every prefix

The read-source lemmas of the softmax region (`Kk.pReadSrc_of`, `Kk.sPstAfter_of`) take each
thread's later states from `Complete L X` (`Interface.sm_reaches_tmemSt`,
`Kk.sm_reaches_bar20`). Here the states come from an event that exists:

* `arrivals_of_polls`: an MMA lane with more than `q` successful polls of `p_ready b` has seen
  thread 0's arrival with `q` earlier ones, so thread 0 has more than `q` arrivals (the unit
  handoff of `p_ready b`, `SO.p_handoff`, names the arrival each poll synchronizes with);
* `bar21_of_arrivals`: when thread 0 of a CTA has more than `i / 2` arrivals on
  `p_ready (i % 2)`, every softmax thread of the CTA has a state at `bar21` of iteration `i` with
  an event (thread 0's arrival follows its `bar21` of iteration `i`, a `bar.sync 0, 128`; the
  thread has the barrier-0 event of the same count, `Lk.member_of`, which is its own `bar21` of
  iteration `i`, `Hs.bar21_pos`);
* `tmemSt_of_arrivals`: two events before it, the thread's `P` store of iteration `i`;
* `exit_bound20`, `b128_of20`: `Hs.exit_bound` and `Hs.b128_of` for the count of `bar20`, used
  by `Qy.sPstAfterF` (result layer).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Qy
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Lk5B PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Interface.B0N (cnt0 C0 Dc nIt)
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk (DecAgree)
open PTX.Kernels.InklingRelDecode.Proof.EvW (pReady)
open PTX.Kernels.InklingRelDecode.Proof.Hs (p0Of)

noncomputable section
set_option maxRecDepth 100000
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A lane's polls of `p_ready b` are bounded by thread 0's arrivals on it.** -/
theorem arrivals_of_polls {K : Kernel} {A : List Assumption} {c cm p0 tm : Nat}
    {Soft Mma : Nat → Prop} (H : Mbar.Ctx L K A mem0 X c cm p0 Soft Mma)
    (l : Sr.Lane L X c cm p0 tm Soft) {b : Nat} (hb : b < 2) {f q : Nat}
    (hf : q + 1 ≤ okPolls (pReady L c b) ((X.tr cm).take f)) :
    q + 1 ≤ arrivals (pReady L c b) (X.tr p0) := by
  have hp0 := Sr.soft_info H H.route.p0_soft
  have hU := SO.p_handoff H.cons H.facts hb (cons := fun h => h = cm)
    (fun h hh => by subst hh; exact Mbar.pReach H hb H.route.cm_mma)
    (fun hh hw' => by subst hh; exact l.pAcq hb hw')
    (fun h hh => by subst hh; exact ⟨hp0.1, l.cm_ok.1, by rw [hp0.2.1, l.cm_ok.2]⟩)
  obtain ⟨j, pc, p, acq, sc, -, hw, hq⟩ := MbarRing.UnitHandoff.exists_poll hf
  obtain ⟨i, hi, hs⟩ := hU cm j pc p acq sc q rfl hw (by rw [hq]; rfl) p0 ⟨0, rfl⟩
  obtain ⟨ev, hev, ha⟩ := hs.arrives
  have hs1 : arrivals (pReady L c b) ((X.tr p0).take (i + 1)) = q + 1 := by
    have hg : (X.tr p0)[i]? = some ev := hev
    simp only [arrivals] at hi ⊢
    rw [List.take_add_one, hg, Option.toList_some, List.countP_append, hi]
    simp [ha]
  have hm := (List.take_sublist (i + 1) (X.tr p0)).countP_le (p := arrivesOn (pReady L c b))
  simp only [arrivals] at hs1 ⊢
  omega

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hD : ∀ c j, DecAgree Q L X c j)
include hpre hX hf hD

/-- **A softmax thread's `bar21` of iteration `i`, from thread 0's arrivals.** -/
theorem bar21_of_arrivals {c t i : Nat} (htc : t / L.block = c)
    (htd : t % L.block < 128)
    (hgd : i / 2 + 1 ≤ arrivals (pReady L c (i % 2)) (X.tr (p0Of L c))) :
    ∃ (a : Nat) (d' : Sm.D), St Q L X t a = some (some (.d (.sm d'))) ∧ d'.site = .bar21 ∧
      d'.i = i ∧ a < (X.tr t).length := by
  have hb2 : i % 2 < 2 := Nat.mod_lt _ (by omega)
  obtain ⟨hpc, hp0m⟩ := Hs.p0_div hpre c
  obtain ⟨kA, eA, heA, harrA, hcA⟩ := CtaBarrier.countP_index (xs := X.tr (p0Of L c))
    (p := arrivesOn (pReady L c (i % 2))) (n := i / 2) (by unfold arrivals at hgd; omega)
  have heA' : X.get (p0Of L c, kA) = some eA := heA
  have hg0 : p0Of L c < L.threads := event_thread_lt hX heA'
  have hkA : kA < (X.tr (p0Of L c)).length := len_of_get heA'
  obtain ⟨pcA, k⟩ := eA
  cases k with
  | arrive m tx cn rel sc =>
    simp only [arrivesOn, sourceArrive, decide_eq_true_eq] at harrA
    subst harrA
    rcases arrive_event_state hpre hX hf.sound hf.tracked hf.ldRng hg0 heA'
        ⟨_, _, _, _, _, rfl⟩ with
      ⟨dP, -, j, hj, -, hev⟩ | ⟨dA, hσA, hsA, -, hev⟩ | ⟨dL, P, -, hsL, hsh⟩
    · simp only [Event.mk.injEq, Kind.arrive.injEq] at hev
      obtain ⟨-, h, -⟩ := hev
      hs_loc h
    rotate_left
    · unfold EvW.LdShape at hsh
      rw [hsL] at hsh
      simp only [Event.mk.injEq, Kind.arrive.injEq] at hsh
      obtain ⟨-, h, -⟩ := hsh
      hs_loc h
    simp only [Event.mk.injEq, Kind.arrive.injEq] at hev
    obtain ⟨-, hm, -⟩ := hev
    have hm' := hm
    simp only [EvW.pReady, EvD.pReadyOf, EvD.Bar.loc, EvD.Bar.off, EvW.barLoc, EvW.pReadyOff,
      Loc.mk.injEq, true_and] at hm'
    have hmod : dA.i % 2 = i % 2 := by omega
    have harr := (Rr.arr_cnt hpre hX hf hg0 hp0m kA hkA.le _ hσA).2 dA rfl (i % 2) hb2
    rw [hpc, ← hmod, Hs.below2_mod] at harr
    have hcA' : arrivals (pReady L c (i % 2)) ((X.tr (p0Of L c)).take kA) = i / 2 := hcA
    rw [hmod] at harr
    have hiA : dA.i = i := by omega
    rcases Sv.pred_sm hkA.le hσA with ⟨dt, rfl⟩ | ⟨k1, d1, e1, hk1, he1, hσ1, hn1⟩
    · simp [SmEntry.d0] at hsA
    obtain ⟨hs1, hi1⟩ := next_arrive hn1 hsA
    have he1' : X.get (p0Of L c, k1) = some e1 := he1
    have hev1 := Lk.bar_event hpre hX hf hg0 he1' hσ1 (by rw [hs1]; trivial)
    rw [hs1] at hev1
    have hb1 : X.IsBarrier (p0Of L c, k1) 0 (some 128) Sm.Site.bar21.pc := by
      show X.get (p0Of L c, k1) = _
      rw [he1', hev1]
    have hk1l : k1 ≤ (X.tr (p0Of L c)).length := by omega
    have hI1 := Sv.sm_inv_at hX hf he1' hσ1
    have hin : d1.i < nIt Q L (p0Of L c) := by
      have h26 := B0N.r26_numIters hpre hX hf hg0 he1' hσ1
      have := (hI1.late (by rw [hs1]; trivial)).2.2
      simp only [nIt]
      omega
    have htc' : t / L.block = p0Of L c / L.block := by rw [htc, hpc]
    obtain ⟨a, pca, cna, hba, hcnta⟩ := Lk.member_of hpre hX hf hb1 (by simp only; omega)
      (by simp only; omega) htc' htd
      (fun hj => Hs.exit_bound hpre hX hf hD hg0 hk1l hσ1 hs1 hin htc' htd hj)
    obtain ⟨d', hσ', hs', hi'⟩ :=
      Hs.bar21_pos hpre hX hf hD hg0 hk1l hσ1 hs1 hin htc' htd hba hcnta
    have hba' : X.get (t, a) = some ⟨pca, .bar 0 cna .sync⟩ := hba
    exact ⟨a, d', hσ', hs', by omega, len_of_get hba'⟩
  | _ => simp [arrivesOn, sourceArrive] at harrA

/-- **A softmax thread's `P` store of iteration `i`, from thread 0's arrivals.** -/
theorem tmemSt_of_arrivals {c t i : Nat} (ht : t < L.threads) (htc : t / L.block = c)
    (htd : t % L.block < 128)
    (hgd : i / 2 + 1 ≤ arrivals (pReady L c (i % 2)) (X.tr (p0Of L c))) :
    ∃ (k : Nat) (ds : Sm.D) (pc : Nat) (vals : List Value),
      St Q L X t k = some (some (.d (.sm ds))) ∧ ds.site = .tmemSt ∧ ds.i = i ∧
      X.get (t, k) = some ⟨pc, .tc (.st (Sm.tileAddr L t ds) vals (.s16x32bx2 32))⟩ := by
  obtain ⟨a, d', hσ', hs', hi', ha⟩ := bar21_of_arrivals hpre hX hf hD htc htd hgd
  rcases Sv.pred_sm ha.le hσ' with ⟨dt, rfl⟩ | ⟨k1, d1, e1, rfl, he1, hσ1, hn1⟩
  · simp [SmEntry.d0] at hs'
  obtain ⟨hs1, hi1⟩ := next_bar21 hn1 hs'
  rcases Sv.pred_sm (by omega) hσ1 with ⟨dt, rfl⟩ | ⟨k2, d2, e2, rfl, he2, hσ2, hn2⟩
  · simp [SmEntry.d0] at hs1
  obtain ⟨hs2, hi2⟩ := next_tmemWait hn2 hs1
  have hge2 : X.get (t, k2) = some e2 := he2
  obtain ⟨u, hF⟩ := fired_cont hX hf ht hge2 hσ2 (by simp [ExitState])
  obtain ⟨vals, -, -, -, hev⟩ := Sm.shape_tmemSt (fired_sm hF) hs2
  exact ⟨k2, d2, Sm.evPc d2.site, vals, hσ2, hs2, by omega, by rw [hge2, hev]⟩

/-- **An exit of a default thread of the CTA comes after more barrier-0 events** than a state at
`bar20` of an iteration below `num_iters` (`Hs.exit_bound` for `bar20`). -/
theorem exit_bound20 {g k t j pcx : Nat} {d : Sm.D} (hg : g < L.threads)
    (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hs : d.site = .bar20) (hin : d.i < nIt Q L g) (htc : t / L.block = g / L.block)
    (htd : t % L.block < 128) (hj : X.get (t, j) = some ⟨pcx, .exit⟩) :
    cnt0 X g k < cnt0 X t j := by
  have hv := Hs.cnt_at hpre hX hf hD hg hk hσ
  have hjk := (List.getElem?_eq_some_iff.mp hj).1.le
  have hC : C0 Q L t = C0 Q L g := by simp only [C0, B0N.nbQ_cta (Q := Q) htc]
  have hN : nIt Q L t = nIt Q L g := by
    simp only [nIt, ProA.cta_eq_of_block htc .z, ProA.cta_eq_of_block htc .x]
  have hDc : Dc Q L X (t / L.block) = Dc Q L X (g / L.block) := by rw [htc]
  rcases exit_event_state hX hf.sound hf.tracked hj with ⟨de, hσ', hx⟩ | ⟨x, hσ', -⟩
  · have h := B0N.cnt_epi hpre hX hf (I := nIt Q L t) (event_thread_lt hX hj)
      (fun j _ => hD _ j) hjk hσ'
    rw [hC, hN, hDc, Nat.min_self] at h
    have hl := B0N.lfun_ge hin
    have hr1 := nResc_mono (Dc Q L X (g / L.block)) (show d.i + 1 ≤ nIt Q L g by omega)
    rw [nResc_succ] at hr1
    have hr : RD (Dc Q L X (g / L.block)) d ≤ nResc (Dc Q L X (g / L.block)) (nIt Q L g) := by
      have hR : RD (Dc Q L X (g / L.block)) d = nResc (Dc Q L X (g / L.block)) d.i +
          if 1 ≤ d.i ∧ ¬ Dc Q L X (g / L.block) d.i then 1 else 0 := by
        simp [RD, postR, hs]
      rw [hR]
      split_ifs at hr1 ⊢ <;> omega
    have hr' : ((RD (Dc Q L X (g / L.block)) d : Nat) : Int) ≤
        (nResc (Dc Q L X (g / L.block)) (nIt Q L g) : Int) := by exact_mod_cast hr
    simp only [dN0, hx] at h
    rw [hs] at hv
    simp only [phi] at hv
    have : (cnt0 X g k : Int) < cnt0 X t j := by omega
    exact_mod_cast this
  · obtain ⟨s, hs'⟩ := B0N.dstate_of hjk hσ' htd
    cases hs'

/-- **A barrier-0 event of a default thread at the count of `bar20` of an iteration is a
`bar.sync 0, 128`** (`Hs.b128_of` for `bar20`). -/
theorem b128_of20 {g k t a pc : Nat} {cn : Option Nat} {d : Sm.D} (hg : g < L.threads)
    (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hs : d.site = .bar20) (hin : d.i < nIt Q L g) (htc : t / L.block = g / L.block)
    (htd : t % L.block < 128) (hb : X.IsBarrier (t, a) 0 cn pc)
    (hcnt : cnt0 X t a = cnt0 X g k) : cn = some 128 := by
  have hv := Hs.cnt_at hpre hX hf hD hg hk hσ
  rw [hs] at hv
  simp only [phi] at hv
  have hC1 := B0N.c0_pos (Q := Q) (L := L) g
  have hC : C0 Q L t = C0 Q L g := by simp only [C0, B0N.nbQ_cta (Q := Q) htc]
  have hN : nIt Q L t = nIt Q L g := by
    simp only [nIt, ProA.cta_eq_of_block htc .z, ProA.cta_eq_of_block htc .x]
  have hDc : Dc Q L X (t / L.block) = Dc Q L X (g / L.block) := by rw [htc]
  have hcnt' : (cnt0 X t a : Int) = cnt0 X g k := by exact_mod_cast hcnt
  have hRD : (0 : Int) ≤ (RD (Dc Q L X (g / L.block)) d : Int) := Int.natCast_nonneg _
  obtain ⟨s', hσ', hk', hz, hcn⟩ := B0N.bar_state hpre hX hf htd hb
  rcases hcn with ⟨-, h1⟩ | ⟨h, -⟩
  · exfalso
    rcases B0N.b0_state hz with ⟨d0, rfl, hn0⟩ | ⟨d0, rfl, hp⟩ | ⟨d0, rfl, hsm⟩ | ⟨d0, rfl, h3⟩
    · have := B0N.cnt_dstart hpre hX hf (event_thread_lt hX (show X.get (t, a) = _ from hb)) hk'
        hσ' hn0
      have hct : (cnt0 X t a : Int) ≤ 1 := this
      omega
    · simp only [DComp.pc, pro_b0At, hp] at h1
      omega
    · simp only [DComp.pc, sm_b0At, hsm] at h1
      omega
    · have h := B0N.cnt_epi hpre hX hf (I := nIt Q L t) (event_thread_lt hX hb)
        (fun j _ => hD _ j)
        (show a ≤ (X.tr t).length from hk') hσ'
      rw [hC, hN, hDc, Nat.min_self] at h
      have hl := B0N.lfun_ge hin
      have hr1 := nResc_mono (Dc Q L X (g / L.block)) (show d.i + 1 ≤ nIt Q L g by omega)
      rw [nResc_succ] at hr1
      have hr : RD (Dc Q L X (g / L.block)) d ≤
          nResc (Dc Q L X (g / L.block)) (nIt Q L g) := by
        have hR : RD (Dc Q L X (g / L.block)) d = nResc (Dc Q L X (g / L.block)) d.i +
            if 1 ≤ d.i ∧ ¬ Dc Q L X (g / L.block) d.i then 1 else 0 := by
          simp [RD, postR, hs]
        rw [hR]
        split_ifs at hr1 ⊢ <;> omega
      have hr' : ((RD (Dc Q L X (g / L.block)) d : Nat) : Int) ≤
          (nResc (Dc Q L X (g / L.block)) (nIt Q L g) : Int) := by exact_mod_cast hr
      simp only [dN0, h3] at h
      omega
  · exact h

end
end PTX.Kernels.InklingRelDecode.Proof.Qy
