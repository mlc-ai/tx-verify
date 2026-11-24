-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.HsStore
public import Kernels.InklingRelDecode.Proof.Interface.KkBar
public import Kernels.InklingRelDecode.Proof.Interface.RrArrive
public import Kernels.InklingRelDecode.Proof.Interface.ExitFacts
public import Kernels.InklingRelDecode.Proof.Protocol.Lk5MBar
public import Kernels.InklingRelDecode.Proof.Protocol.Lk5Final

@[expose] public section

/-!
# The rendezvous of the softmax stores (`StRdv`), on every prefix

A store of iteration `i` by a softmax thread `t` of CTA `c` (at `tmemSt` or `stO`), and thread 0
`p0` of the CTA with more than `i / 2` arrivals on `p_ready (i % 2)`:

* `p0`'s arrival with `i / 2` earlier ones is at the site `arrive` of iteration `i`
  (`Rr.arr_cnt`), whose predecessor is `bar21` of iteration `i`, a `bar.sync 0, 128`
  (`Interface.next_arrive`, `Lk.bar_event`);
* `t` has a barrier-0 event of the same count (`Lk.member_of`): a thread that exits has made
  more (`exit_bound`, the count of the epilogue `B0N.cnt_epi`), and it is a `bar.sync 0, 128`
  (`b128_of`);
* the counts of `Kk.cnt_val` (with the decisions of every iteration agreeing, `DecAgree`) put
  `t`'s store and its `tcgen05.wait::st` (`tmemWait`, `waitStO`) before that event;
* `Bar.bar128Causal` orders the wait before `p0`'s arrival, which has `i / 2` earlier arrivals.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Hs
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Lk5B PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Interface.B0N (cnt0 C0 Dc nIt)
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk (DecAgree)
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal)

noncomputable section
set_option maxRecDepth 100000
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- `Mbar.Route.soft_bar` for CTA `c` with thread 0 `p0Of L c` and the softmax threads
`Sr.SoftOf L c`. -/
def SoftBar (L : Launch) (X : Execution) (c : Nat) : Prop :=
  ∀ {i pc b h : Nat} {sc : MbarScope}, b < 2 →
    X.get (p0Of L c, i) = some ⟨pc, .arrive (pReady L c b) 0 1 true sc⟩ → Sr.SoftOf L c h →
      ∃ y a pc1 pc2, y < i ∧ X.get (p0Of L c, y) = some ⟨pc1, .bar 0 (some 128) .sync⟩ ∧
        X.get (h, a) = some ⟨pc2, .bar 0 (some 128) .sync⟩ ∧
        ((X.tr h).take a).countP (Execution.isBarId 0) =
          ((X.tr (p0Of L c)).take y).countP (Execution.isBarId 0) ∧
        arrivals (pReady L c b) ((X.tr (p0Of L c)).take i) + 1 ≤
          okPolls (sReady L c b) ((X.tr h).take a) ∧
        (1 ≤ 2 * arrivals (pReady L c b) ((X.tr (p0Of L c)).take i) + b →
          2 * arrivals (pReady L c b) ((X.tr (p0Of L c)).take i) + b ≤
            okPolls (oDone L c) ((X.tr h).take a))

theorem below2_mod (i : Nat) : SO.below2 (i % 2) i = i / 2 := by
  unfold SO.below2
  omega

theorem rd_le_succ (Dc : Nat → Prop) (d : Sm.D) : RD Dc d ≤ nResc Dc (d.i + 1) := by
  unfold RD
  rw [nResc_succ]
  split_ifs <;> simp_all

theorem rd_ge (Dc : Nat → Prop) (d : Sm.D) : nResc Dc d.i ≤ RD Dc d := by
  unfold RD
  omega

theorem cnt0_le (g : Nat) {a b : Nat} (h : a ≤ b) : cnt0 X g a ≤ cnt0 X g b :=
  (List.take_sublist_take_left h).countP_le

theorem cnt0_succ {g k : Nat} {e : Event} (he : X.get (g, k) = some e) :
    cnt0 X g (k + 1) = cnt0 X g k + if Execution.isBarId 0 e = true then 1 else 0 := by
  have he' : (X.tr g)[k]? = some e := he
  unfold cnt0
  rw [List.take_add_one, he']
  simp [List.countP_append]

/-- **The `tcgen05.wait::st` after a softmax store**: the event after a store at `tmemSt` or
`stO` is the wait at `tmemWait` or `waitStO`. -/
theorem wait_after (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    {g k : Nat} {d : Sm.D} (hg : g < L.threads) (hk : k + 1 < (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .tmemSt ∨ d.site = .stO) :
    ∃ pcw, X.get (g, k + 1) = some ⟨pcw, .tc .waitSt⟩ := by
  obtain ⟨e0, he0⟩ : ∃ e0, X.get (g, k) = some e0 :=
    ⟨_, List.getElem?_eq_getElem (show k < (X.tr g).length by omega)⟩
  obtain ⟨ew, hew⟩ : ∃ ew, X.get (g, k + 1) = some ew := ⟨_, List.getElem?_eq_getElem hk⟩
  obtain ⟨u0, hF0⟩ := fired_cont hX hf hg he0 hσ (by simp [ExitState])
  rcases hs with hs | hs
  · obtain ⟨vals', -, -, -, hev⟩ := Sm.shape_tmemSt (fired_sm hF0) hs
    have hn : Sm.next L g d e0 = some (some { d with site := .tmemWait }) := by
      rw [hev]
      simp [Sm.next, hs]
    have hσ1 := Rr.succ_sm he0 hσ (by simp [DComp.leaves, hs]) hn
    obtain ⟨u1, hF1⟩ := fired_cont hX hf hg hew hσ1 (by simp [ExitState])
    rw [Sm.shape_tmemWait (fired_sm hF1) rfl] at hew
    exact ⟨_, hew⟩
  · obtain ⟨vals', -, -, -, hev⟩ := Sm.shape_stO (fired_sm hF0) hs
    have hn : Sm.next L g d e0 = some (some { d with site := .waitStO }) := by
      rw [hev]
      simp [Sm.next, hs]
    have hσ1 := Rr.succ_sm he0 hσ (by simp [DComp.leaves, hs]) hn
    obtain ⟨u1, hF1⟩ := fired_cont hX hf hg hew hσ1 (by simp [ExitState])
    rw [Sm.shape_waitStO (fired_sm hF1) rfl] at hew
    exact ⟨_, hew⟩

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hD : ∀ c j, DecAgree Q L X c j)
include hpre hX hf hD

/-- The count of a softmax state of iteration `i` at a site after the rescale, with `RD`. -/
theorem cnt_at {g k : Nat} {d : Sm.D} (hg : g < L.threads) (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) :
    (cnt0 X g k : Int) = 2 + C0 Q L g + phi d.site d.i + RD (Dc Q L X (g / L.block)) d :=
  (Kk.cnt_val hpre hX hf hg (hD _) hk hσ).2

/-- **An exit of a default thread of the CTA comes after more barrier-0 events** than a state at
`bar21` of an iteration below `num_iters`. -/
theorem exit_bound {g k t j pcx : Nat} {d : Sm.D} (hg : g < L.threads)
    (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hs : d.site = .bar21) (hin : d.i < nIt Q L g) (htc : t / L.block = g / L.block)
    (htd : t % L.block < 128) (hj : X.get (t, j) = some ⟨pcx, .exit⟩) :
    cnt0 X g k < cnt0 X t j := by
  have hv := cnt_at hpre hX hf hD hg hk hσ
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

/-- **A barrier-0 event of a default thread at the count of `bar21` of an iteration is a
`bar.sync 0, 128`.** -/
theorem b128_of {g k t a pc : Nat} {cn : Option Nat} {d : Sm.D} (hg : g < L.threads)
    (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hs : d.site = .bar21) (hin : d.i < nIt Q L g) (htc : t / L.block = g / L.block)
    (htd : t % L.block < 128) (hb : X.IsBarrier (t, a) 0 cn pc)
    (hcnt : cnt0 X t a = cnt0 X g k) : cn = some 128 := by
  have hv := cnt_at hpre hX hf hD hg hk hσ
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

/-- **`StRdv`**: the rendezvous of the stores of every CTA, on every prefix. -/
theorem stRdv_of (c : Nat) : StRdv Q L X c := by
  intro t sk d ht htc hσ hst hsk hgd
  have hb2 : d.i % 2 < 2 := Nat.mod_lt _ (by omega)
  obtain ⟨hpc, hp0m⟩ := p0_div hpre c
  -- thread 0's arrival with `i / 2` earlier ones
  obtain ⟨kA, eA, heA, harrA, hcA⟩ := CtaBarrier.countP_index (xs := X.tr (p0Of L c))
    (p := arrivesOn (pReady L c (d.i % 2))) (n := d.i / 2) (by unfold arrivals at hgd; omega)
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
    have hmod : dA.i % 2 = d.i % 2 := by omega
    have harr := (Rr.arr_cnt hpre hX hf hg0 hp0m kA hkA.le _ hσA).2 dA rfl (d.i % 2) hb2
    rw [hpc, ← hmod, below2_mod] at harr
    have hcA' : arrivals (pReady L c (d.i % 2)) ((X.tr (p0Of L c)).take kA) = d.i / 2 := hcA
    rw [hmod] at harr
    have hiA : dA.i = d.i := by omega
    -- the state before: `bar21` of iteration `i`
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
    have htd : t % L.block < 128 := (hf.reach ht hσ).1
    have htc' : t / L.block = p0Of L c / L.block := by rw [htc, hpc]
    -- `t`'s barrier-0 event of the same count
    obtain ⟨a, pca, cna, hba, hcnta⟩ := Lk.member_of hpre hX hf hb1 (by simp only; omega)
      (by simp only; omega) htc' htd
      (fun hj => exit_bound hpre hX hf hD hg0 hk1l hσ1 hs1 hin htc' htd hj)
    have hcn := b128_of hpre hX hf hD hg0 hk1l hσ1 hs1 hin htc' htd hba hcnta
    subst hcn
    have hba' : X.get (t, a) = some ⟨pca, .bar 0 (some 128) .sync⟩ := hba
    have hal : a < (X.tr t).length := len_of_get hba'
    -- the counts
    have hC : C0 Q L t = C0 Q L (p0Of L c) := by simp only [C0, B0N.nbQ_cta (Q := Q) htc']
    have hDc : Dc Q L X (t / L.block) = Dc Q L X (p0Of L c / L.block) := by rw [htc']
    have hvt := cnt_at hpre hX hf hD ht hsk.le hσ
    have hv1 := cnt_at hpre hX hf hD hg0 hk1l hσ1
    rw [hC, hDc] at hvt
    have hRD : RD (Dc Q L X (p0Of L c / L.block)) d = RD (Dc Q L X (p0Of L c / L.block)) d1 := by
      rcases hst with hs | hs <;> simp [RD, postR, hs, hs1, ← hi1, hiA]
    have hcta : (cnt0 X t a : Int) = cnt0 X (p0Of L c) k1 := by exact_mod_cast hcnta
    have hle : (cnt0 X t sk : Int) ≤ cnt0 X t a := by
      rw [hcta, hvt, hv1, hRD, hs1, ← hi1, hiA]
      rcases hst with hs | hs <;> simp only [phi, hs] <;> omega
    have hbar : Execution.isBarId 0 ⟨pca, .bar 0 (some 128) .sync⟩ = true := by
      simp [Execution.isBarId]
    have hsa : sk < a := by
      by_contra hlt
      rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hlt) with hlt | heq
      · have h1 := cnt0_le (X := X) t (show a + 1 ≤ sk by omega)
        rw [cnt0_succ hba', hbar] at h1
        simp at h1
        omega
      · subst heq
        obtain ⟨e0, he0⟩ : ∃ e0, X.get (t, a) = some e0 := ⟨_, hba'⟩
        obtain ⟨u, hF⟩ := fired_cont hX hf ht hba' hσ (by simp [ExitState])
        rcases hst with hs | hs
        · obtain ⟨vals', -, -, -, hev'⟩ := Sm.shape_tmemSt (fired_sm hF) hs
          cases hev'
        · obtain ⟨vals', -, -, -, hev'⟩ := Sm.shape_stO (fired_sm hF) hs
          cases hev'
    have hk1' : sk + 1 < (X.tr t).length := by omega
    obtain ⟨pcw, hew⟩ := wait_after hX hf ht hk1' hσ hst
    have hwa : sk + 1 < a := by
      rcases Nat.lt_or_eq_of_le (show sk + 1 ≤ a by omega) with h | h
      · exact h
      · subst h
        rw [hba'] at hew
        cases hew
    have he1b : X.get (p0Of L c, k1) = some ⟨Sm.Site.bar21.pc, .bar 0 (some 128) .sync⟩ := by
      rw [he1', hev1]
    have hB := Bar.bar128Causal hpre hX hf.sound hf.tracked (g := t) (p := p0Of L c) (a := a)
      (y := k1) (before := sk + 1) (f := kA) ht hg0 htc' htd (by rw [hp0m]; omega) hba' he1b
      hcnta hwa (by omega) hkA
    exact ⟨sk + 1, pcw, kA, by omega, hew, hB, by rw [hcA']⟩
  | _ => simp [arrivesOn, sourceArrive] at harrA

/-- **The barrier-0 event of a default thread at the count of `bar21` of iteration `I`** is its
own `bar21` of iteration `I`. -/
theorem bar21_pos {g k h a pc : Nat} {cn : Option Nat} {d : Sm.D} (hg : g < L.threads)
    (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hs : d.site = .bar21) (hin : d.i < nIt Q L g) (hhc : h / L.block = g / L.block)
    (hhd : h % L.block < 128) (hb : X.IsBarrier (h, a) 0 cn pc)
    (hcnt : cnt0 X h a = cnt0 X g k) :
    ∃ d' : Sm.D, St Q L X h a = some (some (.d (.sm d'))) ∧ d'.site = .bar21 ∧ d'.i = d.i := by
  have hv := cnt_at hpre hX hf hD hg hk hσ
  rw [hs] at hv
  simp only [phi] at hv
  have hht : h < L.threads := event_thread_lt hX (show X.get (h, a) = _ from hb)
  have hC1 := B0N.c0_pos (Q := Q) (L := L) g
  have hC : C0 Q L h = C0 Q L g := by simp only [C0, B0N.nbQ_cta (Q := Q) hhc]
  have hN : nIt Q L h = nIt Q L g := by
    simp only [nIt, ProA.cta_eq_of_block hhc .z, ProA.cta_eq_of_block hhc .x]
  have hDc : Dc Q L X (h / L.block) = Dc Q L X (g / L.block) := by rw [hhc]
  have hcnt' : (cnt0 X h a : Int) = cnt0 X g k := by exact_mod_cast hcnt
  have hdu := rd_le_succ (Dc Q L X (g / L.block)) d
  have hdl := rd_ge (Dc Q L X (g / L.block)) d
  have hr1 := nResc_mono (Dc Q L X (g / L.block)) (show d.i + 1 ≤ nIt Q L g by omega)
  obtain ⟨s', hσ', hk', hz, hcn⟩ := B0N.bar_state hpre hX hf hhd hb
  rcases B0N.b0_state hz with ⟨d0, rfl, hn0⟩ | ⟨d0, rfl, hp⟩ | ⟨d0, rfl, hsm⟩ | ⟨d0, rfl, h3⟩
  · have := B0N.cnt_dstart hpre hX hf hht hk' hσ' hn0
    have hct : (cnt0 X h a : Int) ≤ 1 := this
    omega
  · have := B0N.cnt_pro hpre hX hf hht hk' hσ' hp
    have hct : (cnt0 X h a : Int) < 2 + C0 Q L h := this
    omega
  · refine ⟨d0, hσ', ?_⟩
    have hv' := cnt_at hpre hX hf hD hht hk' hσ'
    rw [hC, hDc] at hv'
    have hdu0 := rd_le_succ (Dc Q L X (g / L.block)) d0
    have hdl0 := rd_ge (Dc Q L X (g / L.block)) d0
    have hp := phi_b0 hsm d0.i
    rcases lt_trichotomy d0.i d.i with hlt | heq | hgt
    · exfalso
      have h2 := nResc_mono (Dc Q L X (g / L.block)) (show d0.i + 1 ≤ d.i by omega)
      rcases hp with ⟨-, hp⟩ | ⟨-, hp⟩ | ⟨-, -, hp, -⟩ <;> omega
    · refine ⟨?_, heq⟩
      have hRD : RD (Dc Q L X (g / L.block)) d0 = RD (Dc Q L X (g / L.block)) d ∨
          (postR d0.site = false ∧
            RD (Dc Q L X (g / L.block)) d0 = nResc (Dc Q L X (g / L.block)) d.i) := by
        cases hpo : postR d0.site
        · right
          refine ⟨rfl, ?_⟩
          simp [RD, hpo, heq]
        · left
          have h21 : postR d.site = true := by rw [hs]; rfl
          simp only [RD, hpo, h21, heq]
      cases hs0 : d0.site <;> simp only [smB0, hs0] at hsm
      all_goals first
        | rfl
        | (exfalso
           rw [hs0] at hv' hRD
           simp only [phi, postR] at hv' hRD
           rw [heq] at hv'
           rcases hRD with hRD | ⟨-, hRD⟩ <;> omega)
    · exfalso
      have h2 := nResc_mono (Dc Q L X (g / L.block)) (show d.i + 1 ≤ d0.i by omega)
      rcases hp with ⟨-, hp⟩ | ⟨-, hp⟩ | ⟨-, hp, -, -⟩ <;> omega
  · exfalso
    have h := B0N.cnt_epi hpre hX hf (I := nIt Q L h) hht (fun j _ => hD _ j) hk' hσ'
    rw [hC, hN, hDc, Nat.min_self] at h
    have hl := B0N.lfun_ge hin
    simp only [dN0, h3] at h
    omega

/-- **`Mbar.Route.soft_bar`** for every CTA. -/
theorem softBar_of (c : Nat) : SoftBar L X c := by
  intro i pc b h sc hb he hsoft
  obtain ⟨hht, hhc, hhd⟩ := hsoft
  obtain ⟨hpc, hp0m⟩ := p0_div hpre c
  have hg0 : p0Of L c < L.threads := event_thread_lt hX he
  have hkA : i < (X.tr (p0Of L c)).length := len_of_get he
  rcases arrive_event_state hpre hX hf.sound hf.tracked hf.ldRng hg0 he ⟨_, _, _, _, _, rfl⟩ with
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
  have hmod : dA.i % 2 = b := by omega
  have harr := (Rr.arr_cnt hpre hX hf hg0 hp0m i hkA.le _ hσA).2 dA rfl b hb
  rw [hpc, ← hmod, below2_mod] at harr
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
  have hhc' : h / L.block = p0Of L c / L.block := by rw [hhc, hpc]
  obtain ⟨a, pca, cna, hba, hcnta⟩ := Lk.member_of hpre hX hf hb1 (by simp only; omega)
    (by simp only; omega) hhc' hhd
    (fun hj => exit_bound hpre hX hf hD hg0 hk1l hσ1 hs1 hin hhc' hhd hj)
  have hcn := b128_of hpre hX hf hD hg0 hk1l hσ1 hs1 hin hhc' hhd hba hcnta
  subst hcn
  obtain ⟨d', hσ', hs', hi'⟩ := bar21_pos hpre hX hf hD hg0 hk1l hσ1 hs1 hin hhc' hhd hba hcnta
  have hal : a < (X.tr h).length := len_of_get (show X.get (h, a) = _ from hba)
  have hcnt := (Rd.sm_cnt hpre hX hf hht a hal.le _ hσ').2 d' rfl
  have hcs := hcnt.s b hb
  have hco := hcnt.o
  rw [hhc] at hcs hco
  have harr' : arrivals (pReady L c b) ((X.tr (p0Of L c)).take i) = dA.i / 2 := by
    rw [← hmod]; exact harr
  refine ⟨k1, a, Sm.Site.bar21.pc, pca, by omega, by rw [he1', hev1], hba, hcnta, ?_, ?_⟩
  · rw [harr', hcs]
    simp only [SO.smPolled, hs', SO.below2]
    omega
  · intro _
    rw [harr', hco]
    simp only [SO.smOPolled, hs']
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.Hs
