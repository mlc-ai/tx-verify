-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Progress.Lanes
public import Lemmas.Execution.ExecutionGrowth

@[expose] public section

/-! # Every maximal execution is complete

Descent over the pending threads (`Descent.progress_of_threads`), ranked by their progress
(`rankOf`). A pending thread whose last event is released (`released_steps`):

* at a site other than a shuffle, extends the execution (`Execution.NoTma.next_extends`);
* at a shuffle site, either a lane of its warp is pending with less progress (`lane_lower`), or
  every lane is at the site and the warp performs the shuffle (`shfl_batch`).

A pending thread blocked at a barrier arrival of number `n` (`thread_steps`):

* some thread of its CTA has fewer than `n + 1` arrivals on the barrier: it is pending with less
  progress;
* some thread of the CTA has passed its arrival `n`: generation `n` is released, and so is the
  blocked arrival, contrary to the premise;
* every thread of the CTA has its arrival `n` as its last event: the history's missing records
  are appended (`NamedBar.named_finish`), which releases the arrival, and the thread steps in the
  extended execution as a released thread. -/

namespace PTX.Kernels.RmsNorm.Proof

open PTX PTX.Proof PTX.Flow CtaBarrier

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem wf_all : ∀ a ∈ Prod, ∀ Y, a.wf L mem0 Y := by
  intro a ha Y
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;> trivial

theorem ext_wf (X : Execution) (g : Nat) : X.ExtWf Prod L mem0 g :=
  fun _ _ _ a ha => wf_all a ha _

/-- The template of a site other than a shuffle performs no shuffle. -/
theorem siteTmpl_not_shfl {g : Nat} {d : D} {t : TState} (hs : d.site.isShfl = false) :
    (siteTmpl P g d t).isShfl = false := by
  rcases hsd : d.site <;> simp only [hsd, Site.isShfl, Bool.true_eq_false] at hs <;>
    simp [siteTmpl, hsd, Tmpl.isShfl]

/-- The template of a site is neither an atomic read-modify-write nor a special-register read. -/
theorem siteTmpl_plain {g : Nat} {d : D} {t : TState} :
    (siteTmpl P g d t).isRmw = false ∧ (siteTmpl P g d t).SregBounded := by
  rcases hsd : d.site <;> simp [siteTmpl, hsd, Tmpl.isRmw, Tmpl.SregBounded]

/-- **A released pending thread steps.** -/
theorem released_steps (hpre : Pre P L mem0) (hsafe : SafeGoal kernel Prod L mem0)
    (hT : ∀ X, Consistent L kernel Prod mem0 X → ThreadFacts P L X)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    (hrel : LastReleased L X g) :
    Descent.Steps L kernel Prod mem0 (Frame.Pending L) (rankOf P L) X g := by
  have hX := hmax.1
  have ht := hT X hX
  have hub : ¬ HasUb X := fun h => hsafe.2 X hX (.inl h)
  have hn := noTma_of_consistent noTma hX
  obtain ⟨dg, hσ⟩ := pending_state hpre hX ht hp
  cases hs : dg.site.isShfl with
  | true =>
    by_cases hlow : ∃ h, SameWarp L g h ∧ ¬ ∃ dh, stateAt P L X h (X.tr h).length = some (some dh) ∧
        dh.site = dg.site ∧ (dg.site ≠ .shfl0 → dh.i = dg.i)
    · obtain ⟨h, hw, hne⟩ := hlow
      obtain ⟨hph, hr⟩ := lane_lower hpre hX ht hp hσ hs hw hne
      exact .inr ⟨X, h, hmax, hph, hr⟩
    · push Not at hlow
      exact .inl (shfl_batch hpre hX ht hub hp hσ hs hrel hlow)
  | false =>
    obtain ⟨t, hrun⟩ := Frame.run_some hX hub hp
    obtain ⟨t1, hl, -, hout⟩ := ht.fire hp.1 hrun hσ
    refine .inl (hn.next_extends hX hp.1 hrun hl hout (out_noTma noTma hout)
      (siteTmpl_not_shfl hs) siteTmpl_plain.1 siteTmpl_plain.2 ?_
      (fun _ _ _ hbar => ready_of_lastReleased hX hrel hbar) (ext_wf X g))
    intro id u c hb hnil
    have hidx := ht.index hp.1 le_rfl hσ
    rw [hnil] at hidx
    simp only [List.length_nil] at hidx
    obtain ⟨t', o, hf⟩ : SiteEvent P g dg ⟨dg.site.pc, .bar id c⟩ := ⟨t1, some u, by
      rw [hb]; exact ⟨rfl, rfl⟩⟩
    obtain ⟨-, hs'⟩ := bar_site (P := P) (g := g) (d := dg) ⟨t', o, hf⟩
    rcases hs' with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [D.idx, h1, rowBase] at hidx <;> omega

/-- The ranks of executions with the same traces agree. -/
theorem rankOf_congr {X Y : Execution} (h : Y.tr = X.tr) (g : Nat) :
    rankOf P L Y g = rankOf P L X g := by
  simp only [rankOf, stateAt, Frame.stateAt, h]

/-- The barrier counts of a thread blocked at an arrival, and of a state of its CTA without that
arrival: the state has made less progress. -/
theorem lag_vt {g h : Nat} {dg dh : D} (hig : Inv P g dg) (hih : Inv P h dh)
    (hxh : dh.site ≠ .exit) {id : Nat} (hid : id < 2)
    (hlt : (if id = 0 then dh.bc0 else dh.bc1) < (if id = 0 then dg.bc0 else dg.bc1))
    (hx1 : dg.site = .exit → id = 1) : dh.vt < dg.vt := by
  by_cases hxg : dg.site = .exit
  · have := hx1 hxg
    subst this
    simp only [Nat.one_ne_zero, ↓reduceIte, D.bc1, hxg] at hlt
    have h1 := hih.sub.1
    have hb := hih.bfa
    have hb' := hih.bfb
    rcases hs : dh.site <;>
      simp only [hs, D.vt, D.ord, hxg, Site.vec, reduceCtorEq, false_implies, forall_const,
        Site.bfa.injEq, Site.bfb.injEq, forall_eq', ne_eq,
        not_true_eq_false] at hlt h1 hb hb' hxh ⊢ <;>
      omega
  · rcases (by omega : id = 0 ∨ id = 1) with rfl | rfl
    · exact vt_lt_of_bc0 hig hih hxg hxh (by simpa using hlt)
    · exact vt_lt_of_bc1 hig hih hxg hxh (by simpa using hlt)

/-- **The descent step of a pending thread.** -/
theorem thread_steps (hpre : Pre P L mem0) (hsafe : SafeGoal kernel Prod L mem0)
    (hT : ∀ X, Consistent L kernel Prod mem0 X → ThreadFacts P L X)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g) :
    Descent.Steps L kernel Prod mem0 (Frame.Pending L) (rankOf P L) X g := by
  have hX := hmax.1
  have ht := hT X hX
  have hub : ¬ HasUb X := fun h => hsafe.2 X hX (.inl h)
  have hB := hpre.hyp.block
  by_cases hrel : LastReleased L X g
  · exact released_steps hpre hsafe hT hmax hp hrel
  simp only [LastReleased, not_forall, not_exists, not_and] at hrel
  obtain ⟨id, count, pc, hlen0, hbar, hnr⟩ := hrel
  obtain ⟨hg, rfl, dl, hAl, hsl⟩ := bar_facts hpre hX ht hbar
  have hid : id < 2 := by rcases hsl with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  set n := ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id) with hndef
  have htr : X.tr g = (X.tr g).take ((X.tr g).length - 1) ++ [⟨pc, .bar id none⟩] := by
    conv_lhs => rw [← List.take_append_drop ((X.tr g).length - 1) (X.tr g)]
    congr 1
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)]
    have : (X.tr g)[(X.tr g).length - 1]? = some ⟨pc, .bar id none⟩ := hbar
    rw [List.getElem?_eq_getElem (by omega)] at this
    rw [Option.some.inj this]
  have hcg : (X.tr g).countP (Execution.isBarId id) = n + 1 := by
    rw [htr, List.countP_append]; simp [Execution.isBarId, hndef]
  have hnl : n = if id = 0 then dl.bc0 else dl.bc1 := by
    rcases hsl with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · simp [hndef, hAl.bc0]
    · simp [hndef, hAl.bc0]
    · simp [hndef, hAl.bc1]
  have hrl := hAl.inv.row (by rcases hsl with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h, Site.inRow])
  simp only [row] at hrl
  -- a thread of the CTA with all the arrivals of its rows has the arrival `n`
  have hrows : ∀ R, P.Bt ≤ g / 256 + 152 * R →
      n < (if id = 0 then 2 * R else R) := by
    intro R hR
    have : dl.i < R := by omega
    rcases hsl with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> simp [hnl, D.bc0, D.bc1, h1] <;> omega
  obtain ⟨dg, hσ⟩ := pending_state hpre hX ht hp
  have hig := ht.inv hg hσ
  by_cases hlag : ∃ h, h / 256 = g / 256 ∧ h < L.threads ∧
      (X.tr h).countP (Execution.isBarId id) ≤ n
  · obtain ⟨h, hc, hh, hle⟩ := hlag
    have hex : ∀ pc, (X.tr h).getLast? ≠ some ⟨pc, .exit⟩ := by
      intro pcx hl
      have hx : X.get (h, (X.tr h).length - 1) = some ⟨pcx, .exit⟩ := by
        unfold Execution.get; rw [← List.getLast?_eq_getElem?]; exact hl
      obtain ⟨R, hR, h0, h1, -⟩ := exit_counts hpre hX ht hx
      rw [hc] at hR
      have := hrows R hR
      rcases (by omega : id = 0 ∨ id = 1) with rfl | rfl <;>
        simp only [↓reduceIte, Nat.one_ne_zero] at this <;> omega
    have hph : Frame.Pending L X h := ⟨hh, not_canceled hX, hex⟩
    obtain ⟨dh, hσh⟩ := pending_state hpre hX ht hph
    have hih := ht.inv hh hσh
    obtain ⟨eh0, eh1, -⟩ := end_counts ht hh hσh
    obtain ⟨eg0, eg1, -⟩ := end_counts ht hg hσ
    have hxh : dh.site ≠ .exit := by
      intro hx
      have hR := hih.exit hx
      rw [hc] at hR
      have := hrows dh.i hR
      simp only [D.bc0, D.bc1, hx] at eh0 eh1
      rcases (by omega : id = 0 ∨ id = 1) with rfl | rfl <;>
        simp only [↓reduceIte, Nat.one_ne_zero] at this <;> omega
    have hx1 : dg.site = .exit → id = 1 := by
      intro hxg
      obtain ⟨d1, hσ1⟩ := Frame.stateAt_live ht.tracked hg hσ (Nat.sub_le _ 1)
      have hd1 : d1 = dl := by
        have := hσ1.symm.trans hAl.state
        exact Option.some.inj (Option.some.inj this)
      subst hd1
      have h := Frame.stateAt_succ (C := codes P L) (X := X) (g := g)
        (k := (X.tr g).length - 1) hbar
      rw [Nat.sub_add_cancel hlen0, hσ1] at h
      have hn : next P g d1 ⟨pc, .bar id none⟩ = some (some dg) := by
        have : Frame.stateAt (codes P L) X g (X.tr g).length = some (some dg) := hσ
        rw [h] at this
        exact this
      rcases hsl with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩
      · simp only [next, h1] at hn
        split_ifs at hn <;> cases hn <;> simp at hxg
      · simp only [next, h1] at hn; cases hn; simp at hxg
      · rfl
    have hlt : (if id = 0 then dh.bc0 else dh.bc1) < (if id = 0 then dg.bc0 else dg.bc1) := by
      rcases (by omega : id = 0 ∨ id = 1) with rfl | rfl <;>
        simp only [↓reduceIte, Nat.one_ne_zero] <;> omega
    have hv := lag_vt hig hih hxh hid hlt hx1
    refine .inr ⟨X, h, hmax, hph, ?_⟩
    simp only [rankOf, hσ, hσh]
    omega
  push Not at hlag
  -- every thread of the CTA has its arrival `n`
  have harr : ∀ h, h / 256 = g / 256 → h < L.threads → ∃ j pcj, X.IsBarrier (h, j) id none pcj ∧
      ((X.tr h).take j).countP (Execution.isBarId id) = n := by
    intro h hc hh
    obtain ⟨j, ev, hj, hb, hcnt⟩ :=
      MbarRing.Slot.exists_nth_countP (Execution.isBarId id) (c := n) (hlag h hc hh)
    obtain ⟨pcj, kd⟩ := ev
    cases kd <;> simp only [Execution.isBarId, Bool.false_eq_true] at hb
    rename_i id' c' m'
    simp only [beq_iff_eq] at hb
    subst hb
    cases m'
    case arrive => exact (hX.noBarArrive Fact.out (h, j) _ _ _ hj).elim
    have hbj : X.IsBarrier (h, j) id' c' pcj := hj
    obtain ⟨-, rfl, -⟩ := bar_facts hpre hX ht hbj
    exact ⟨j, pcj, hbj, hcnt⟩
  have hid16 : id < 16 := by omega
  have hgb : g / L.block = g / 256 := by rw [hB]
  have hc : g / L.block < L.grid := cta_lt hpre hg
  by_cases hpass : ∃ h j pcj, h / 256 = g / 256 ∧ h < L.threads ∧ X.IsBarrier (h, j) id none pcj ∧
      ((X.tr h).take j).countP (Execution.isBarId id) = n ∧ j + 1 < (X.tr h).length
  · -- generation `n` is released, and so is the blocked arrival
    obtain ⟨h, j, pcj, hc', hh, hbh, hcnt, hpassed⟩ := hpass
    have hd := released hpre hX ht hbh hpassed
    rw [hcnt, show h / L.block = g / L.block by rw [hB]; exact hc'] at hd
    have hk := NamedBar.reached_key_of_release hX (n := 8) (by decide) (target_none hpre)
      (p := Finset.range 8) hid16 hbar hg (by rw [hB, Finset.mem_range]; omega) rfl hd
      (fun i _ => protocol_prefix hpre hX ht hc id (i + 1)) (Finset.card_range 8)
      (warps_bound hpre)
    refine absurd ?_ (hnr _ hk)
    unfold CtaBarDone
    rwa [show (id + 16 * n) % 16 = id by omega, show (id + 16 * n) / 16 = n by omega]
  push Not at hpass
  -- every thread of the CTA has its arrival `n` as its last event
  have hlast : ∀ h, h / 256 = g / 256 → h < L.threads → ∃ pcj,
      X.IsBarrier (h, (X.tr h).length - 1) id none pcj ∧
      ((X.tr h).take ((X.tr h).length - 1)).countP (Execution.isBarId id) = n := by
    intro h hc' hh
    obtain ⟨j, pcj, hbj, hcnt⟩ := harr h hc' hh
    have hl := len_of_get hbj
    have := hpass h j pcj hc' hh hbj hcnt
    simp only at hl
    rw [show (X.tr h).length - 1 = j by omega]
    exact ⟨pcj, hbj, hcnt⟩
  have hb0 : 0 < L.block := by rw [hB]; decide
  have hlane_lt : ∀ gl, gl < L.block → g / L.block * L.block + gl < L.threads := fun gl hgl =>
    NamedBar.cta_thread_lt hc hgl
  have hlane_c : ∀ gl, gl < L.block → (g / L.block * L.block + gl) / 256 = g / 256 := by
    intro gl hgl
    rw [← hB]
    exact (NamedBar.lane_cta hb0 hgl).1
  have hP : NamedBar.Part L X (g / L.block) none id (Finset.range 8) := by
    refine ⟨fun e pce cnt he hec => ?_, fun y hyc _ j pcx hx => ?_⟩
    · obtain ⟨e1, e2⟩ := e
      obtain ⟨-, hcnt, -⟩ := bar_facts hpre hX ht he
      refine ⟨?_, hcnt⟩
      rw [Finset.mem_range]
      have := Nat.mod_lt e1 hb0
      rw [hB] at this ⊢
      omega
    · have hy := Frame.lt_of_get hX hx
      have hyc' : y / 256 = g / 256 := by rw [← hB]; exact hyc
      obtain ⟨pcj, hbj, -⟩ := hlast y hyc' hy
      have := Execution.exit_last hX hy hx
      rw [← this] at hbj
      have h2 := hx.symm.trans hbj
      cases h2
  obtain ⟨Y, hmaxY, hle, hsz, htrY, hdone, hkeys⟩ := NamedBar.named_finish hmax hc (n := 8)
    (by decide) (target_none hpre) hid16 (Finset.card_range 8) (warps_bound hpre) hP (G := n)
    (fun gl hgl _ => hlast _ (hlane_c gl hgl) (hlane_lt gl hgl)) (fun Y a ha => wf_all a ha Y)
  have hYX : ∀ h, Y.tr h = X.tr h := fun h => congrFun htrY h
  have hgc : g / L.block * L.block + g % L.block = g := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod g L.block
  have hkey := hkeys (g % L.block) (Nat.mod_lt _ hb0)
    (by rw [Finset.mem_range]; have := Nat.mod_lt g hb0; rw [hB] at this ⊢; omega)
  rw [hgc] at hkey
  have hpY : Frame.Pending L Y g := ⟨hg, not_canceled hmaxY.1, by rw [hYX]; exact hp.2.2⟩
  have hrelY : LastReleased L Y g := by
    intro _ _ _ _ _
    refine ⟨id + 16 * n, ?_, hdone⟩
    rw [hYX]
    exact hkey
  rcases released_steps hpre hsafe hT hmaxY hpY hrelY with ⟨Z, hZ, hYZ, hlt⟩ |
    ⟨Y', o', hmax', hp', hr'⟩
  · exact .inl ⟨Z, hZ, Execution.le_trans hle hYZ, by omega⟩
  · exact .inr ⟨Y', o', hmax', hp', by rwa [rankOf_congr htrY] at hr'⟩

/-- **Every maximal execution is complete.** -/
theorem progress_goal (hpre : Pre P L mem0)
    (hT : ∀ X, Consistent L kernel Prod mem0 X → ThreadFacts P L X)
    (hsafe : SafeGoal kernel Prod L mem0) : ProgressGoal kernel Prod L mem0 :=
  Descent.progress_of_threads noTma (rankOf P L) fun _ _ hmax hp =>
    thread_steps hpre hsafe hT hmax hp

end
end PTX.Kernels.RmsNorm.Proof
