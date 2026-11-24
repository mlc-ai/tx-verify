-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.ProInit
public import Kernels.InklingRelDecode.Proof2.Lib.BarEarlyPhased
public import Kernels.InklingRelDecode.Proof2.Lib.MbarInit

@[expose] public section

/-! # The ring barriers are initialized first (`InitFirst`)

`SingleTmaRing.Decl.Events.full_init`/`empty_init`: each of the six ring barriers of a CTA
(`kv_ready s`, `kv_empty s`) has its initialization, with count 1, as its first record, without
fault, and no other initialization. `Proof.Mbar.initFirst_of_published` derives it from one
initialization event published to the issuer of every other record:

* `init_info`, `init_unique`: an initialization event is the prologue's `init j` of barrier `j`,
  fired by the lane of warp 0 its election returned, after two barrier-0 events and before any
  barrier-1 event; two initializations of one object are one event (one lane per warp is elected,
  `ElectOk`, and a thread initializes a barrier once, `pi_inv`);
* `bar0_upTo2`: barrier 0's first three instances hand off (`Handoff.of_barPhased` with the
  phased sources `bar0_phSources`: the startup's two whole-block instances, then the default
  partition's `bar.sync 0, 128`); every thread that exits has made three barrier-0 events
  (`exit_final_bar`);
* `pub_of`: an initialization is published (base causality) to a ring user (`UserAt`): to a
  prologue state after `bar2` through barrier 0's third instance, to a loader or MMA state through
  barrier 1's first (`bar1_handoff`);
* `init_exists`: once a ring user exists, thread 0 of warp 0 and the lane its elections returned
  have passed those instances (`D_member_arrival`, `member_arrival_any`), so that lane initialized
  every barrier;
* `kv_initFirst`. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame AsyncCopy MBarrier

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem get_of_take {k i : Nat} {x : Event} (h : ((X.tr g).take i)[k]? = some x) :
    k < i ∧ X.get (g, k) = some x := by
  have hk : k < i := by
    have := (List.getElem?_eq_some_iff.mp h).1
    simp only [List.length_take] at this
    omega
  refine ⟨hk, ?_⟩
  change (X.tr g)[k]? = some x
  rwa [List.getElem?_take, ite_eq_left hk] at h

theorem thread_lt_of_len (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    (hk : k < (X.tr g).length) : g < L.threads :=
  Frame.lt_of_get hX (show X.get (g, k) = some _ from List.getElem?_eq_getElem hk)

theorem take_succ_get {k : Nat} {e : Event} (he : X.get (g, k) = some e) :
    (X.tr g).take (k + 1) = (X.tr g).take k ++ [e] := by
  have he' : (X.tr g)[k]? = some e := he
  rw [List.take_add_one, he', Option.toList_some]

/-! ### The initialization events -/

/-- **An initialization event** is the prologue's `init j`: of barrier `j` of the thread's CTA,
count 1, by a lane of warp 0 whose election `el j` returned its lane, the thread's first
initialization of the barrier, after two barrier-0 events and no barrier-1 event. -/
theorem init_info (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k pc : Nat} {l : Loc} {c : Nat} (he : X.get (g, k) = some ⟨pc, .mbInit l c⟩) :
    ∃ j : Fin 12, l = (Proof.ProA.initBar j.val).loc L (g / L.block) ∧ c = 1 ∧
      g % L.block < 32 ∧
      (∃ k0 inst, k0 < k ∧
        X.get (g, k0) = some ⟨(ProA.Site.el j).pc, .elect 4294967295 inst (laneOf L g)⟩) ∧
      initN L g j ((X.tr g).take k) = 0 ∧
      ((X.tr g).take (k + 1)).countP (Execution.isBarId 0) = 2 ∧
      ((X.tr g).take (k + 1)).countP (Execution.isBarId 1) = 0 := by
  have hg := Frame.lt_of_get hX he
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
    have hpc := init_pc hc hf rfl
    have hPI := pi_inv hp hX hg k hlen σ hσ
    have hC1 := c1_inv hp hX hg k hlen σ hσ
    rw [take_succ_get he]
    obtain ⟨x, n⟩ := σ
    rcases x with st | ⟨_ | r, d⟩
    · exact (startup_init st.site hpc).elim
    · rename_i i
      cases i with
      | dp tm bw =>
        rcases d with d | ⟨_ | _, τ⟩
        · obtain ⟨j, hs⟩ := proA_init d.site hpc
          have hxd : d.site ≠ .exit := by rw [hs]; nofun
          have hF := ProA.fired_old (P := Startup.inh L g Q tm) hxd hat hi.1 hc hf
          have hev := Proof.ProA.shape_in (Proof.ProA.sharedOk_of_pre hp) (i := j.val) j.isLt hF
            (by simp only [ProA.D.old, hs, in_old])
          simp only [Event.mk.injEq, Kind.mbInit.injEq] at hev
          obtain ⟨-, rfl, rfl⟩ := hev
          obtain ⟨hP1, -, hP3, hP4⟩ := (hPI : PIP L g d _)
          obtain ⟨k0, inst, ld, hk0, hin, -⟩ := hP4 j (by rw [hs]; exact init_pc_lt j)
          obtain ⟨hl, hw⟩ := hin hs
          subst hl
          obtain ⟨hk0', hget0⟩ := get_of_take hk0
          have hN := hP3 j
          rw [hs] at hN
          simp only [lt_irrefl, ite_false, nonpos_iff_eq_zero] at hN
          have hc0 := hP1 (by rw [hs]; exact (init_strict j).2.le)
          have hc1 : ((X.tr g).take k).countP (Execution.isBarId 1) = 0 := by
            have : _ = Proof2.proPh d := hC1
            rw [this]
            simp [proPh, hs]
          refine ⟨j, rfl, rfl, hw, ⟨k0, inst, hk0', hget0⟩, hN, ?_, ?_⟩
          · simp [List.countP_append, hc0, Execution.isBarId]
          · simp [List.countP_append, hc1, Execution.isBarId]
        · exfalso
          cases τ with
          | sm d => exact sm_init d.site hpc
          | epi d => exact epi_init d.site hpc
        · exact hJ.elim
      | worker w =>
        exfalso
        cases d with
        | worker w => exact worker_init w.site hpc
        | idle d => exact idle_init d.site hpc
        | loader d P => exact loader_init d.site hpc
        | mma d P => exact mma_init d.site hpc
        | exit x => exact exitsite_init x.site hpc
    · exact hJ.elim

theorem laneOf_w0 {h : Nat} (hh : h % L.block < 32) : laneOf L h = h % L.block := by
  simp only [laneOf]
  omega

/-- **Two initializations of one object are one event**, with count 1. -/
theorem init_unique (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g1 g2 k1 k2 pc1 pc2 c1 c2 : Nat} {l : Loc}
    (h1 : X.get (g1, k1) = some ⟨pc1, .mbInit l c1⟩)
    (h2 : X.get (g2, k2) = some ⟨pc2, .mbInit l c2⟩) : (g1, k1) = (g2, k2) ∧ c1 = 1 := by
  have hb : L.block = 256 := hp.block
  obtain ⟨j1, hl1, rfl, hw1, ⟨a1, i1, -, he1⟩, hN1, -, -⟩ := init_info hp hX h1
  obtain ⟨j2, hl2, rfl, hw2, ⟨a2, i2, -, he2⟩, hN2, -, -⟩ := init_info hp hX h2
  refine ⟨?_, rfl⟩
  obtain ⟨rfl, hc⟩ := initBar_loc_inj (hl1.symm.trans hl2)
  have hg1 := Frame.lt_of_get hX h1
  have hg2 := Frame.lt_of_get hX h2
  have hsw : SameWarp L g1 g2 := ⟨⟨hg1, hg2, hc⟩, by omega⟩
  have hld := hX.elect.2.2 (g1, a1) (g2, a2) _ _ _ _ _ _ _ he1 he2 hsw
  rw [laneOf_w0 hw1, laneOf_w0 hw2] at hld
  have hgg : g1 = g2 := by
    have e1 := Nat.div_add_mod g1 L.block
    have e2 := Nat.div_add_mod g2 L.block
    rw [hc, hld] at e1
    omega
  subst hgg
  -- a thread initializes a barrier once
  have hpos : ∀ {ka kb : Nat} {pca pcb : Nat},
      X.get (g1, ka) = some ⟨pca, .mbInit l 1⟩ → ka < kb →
        0 < initN L g1 j1 ((X.tr g1).take kb) := by
    intro ka kb pca pcb hga hab
    have hga' : (X.tr g1)[ka]? = some ⟨pca, .mbInit l 1⟩ := hga
    unfold initN
    apply List.countP_pos_iff.mpr
    refine ⟨⟨pca, .mbInit l 1⟩, ?_, ?_⟩
    · apply List.mem_iff_getElem?.mpr
      exact ⟨ka, by rw [List.getElem?_take, ite_eq_left hab]; exact hga'⟩
    · simp [hl1]
  rcases lt_trichotomy k1 k2 with hlt | heq | hgt
  · have := hpos (pcb := 0) h1 hlt
    omega
  · rw [heq]
  · have := hpos (pcb := 0) h2 hgt
    rw [hl1] at hl2
    omega

/-! ### The facts of a thread at a barrier event -/

/-- **At a barrier-1 event, or a barrier-0 event after two others, of a thread of warps 0 to 3**,
the thread's trace has every election's facts. -/
theorem elF_at_bar (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {T i pc id : Nat} {cnt : Option Nat} {md : BarMode}
    (hget : X.get (T, i) = some ⟨pc, .bar id cnt md⟩) (hT : T % L.block < 128)
    (hid : id = 1 ∨ (id = 0 ∧ 2 ≤ ((X.tr T).take i).countP (Execution.isBarId 0))) :
    ∀ j, ElF L T j ((X.tr T).take i) := by
  have hb : L.block = 256 := hp.block
  have hg := Frame.lt_of_get hX hget
  have hlen : i < (X.tr T).length := (List.getElem?_eq_some_iff.mp hget).1
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX hget (fun f h => by cases h)
  have hPI := pi_inv hp hX hg i hlen σ hσ
  -- the barrier event's position
  have hbp : (id = 1 ∧ (thread Q L T).pc σ ∈ bar1Pcs) ∨
      (id = 0 ∧ ((thread Q L T).pc σ ∈ b0nPcs ∨ (thread Q L T).pc σ ∈ b0cPcs)) := by
    rcases hid with rfl | ⟨rfl, -⟩
    · left
      refine ⟨rfl, ?_⟩
      by_contra hn
      have := bar1_iff hc hf (by omega)
      simp [b1At, hn, Execution.isBarId] at this
    · right
      refine ⟨rfl, ?_⟩
      cases cnt with
      | none => exact .inl (b0n_pc hc hf rfl (by omega))
      | some c => exact .inr (b0c_pc hc hf rfl (by omega))
  obtain ⟨x, n⟩ := σ
  rcases x with st | ⟨_ | r, d⟩
  · exfalso
    rcases hbp with ⟨-, h1⟩ | ⟨rfl, h0 | h0⟩
    · exact startup_bar1 st.site h1
    · have hC := c0_inv hp hX hg i hlen _ hσ
      have hC' : _ = startC0 st := hC
      rcases startup_b0n st.site h0 with hs | hs <;>
        · simp only [startC0, hs] at hC'
          rcases hid with h | ⟨-, h⟩
          · cases h
          · omega
    · exact startup_b0c st.site h0
  · rename_i ix
    cases ix with
    | dp tm bw =>
      rcases d with d | ⟨_ | _, τ⟩
      · -- a prologue barrier is at position 180 or later
        have hge : 180 ≤ d.site.pc := by
          have hpc' : (thread Q L T).pc (.inr ⟨.inl (.dp tm bw), .inl d⟩, n) = d.site.pc := rfl
          rw [hpc'] at hbp
          rcases hbp with ⟨-, h1⟩ | ⟨-, h0 | h0⟩
          · rw [proA_site_bar1 d.site h1]; decide
          · exact (proA_b0n d.site h0).elim
          · simp only [b0cPcs, List.mem_cons, List.mem_nil_iff, or_false] at h0
            omega
        intro j
        obtain ⟨-, -, -, hP4⟩ := (hPI : PIP L T d _)
        have hel : (ProA.Site.el j).pc < 180 := (el_close j).2
        have hin : (ProA.Site.init j).pc < 180 := (init_strict j).2
        obtain ⟨k0, inst, ld, hk0, -, hpost⟩ := hP4 j (by omega)
        exact ⟨k0, inst, ld, hk0, hpost (by omega)⟩
      · exact hPI
      · exact hJ.elim
    | worker w =>
      exfalso
      have hw4 : 4 ≤ T % L.block / 32 := (tm_inv hp hX hg i hlen _ hσ).2
      omega
  · exact hJ.elim

/-! ### Barrier 0's first three instances -/

/-- Every thread that exits has made three barrier-0 events. -/
theorem exit_three (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {h j pc : Nat}
    (hE : X.get (h, j) = some ⟨pc, .exit⟩) :
    3 ≤ ((X.tr h).take j).countP (Execution.isBarId 0) := by
  obtain ⟨jW, pcW, hjW, hW, h2⟩ := exit_final_bar hp hX hE
  have hW' : (X.tr h)[jW]? = some ⟨pcW, .bar 0 none .sync⟩ := hW
  have := Handoff.countP_take_succ_ge (P := Execution.isBarId 0) (es := X.tr h) (e := j - 1) hW'
    (by simp [Execution.isBarId]) (by omega)
  rw [show j - 1 + 1 = j by omega] at this
  omega

/-- **Barrier 0's first three instances hand off** between threads of warps 0 to 3 (the third is
the default partition's `bar.sync 0, 128`). -/
theorem bar0_upTo2 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {h e f : Nat} (hsame : SameCta L g h) (hf : f < (X.tr h).length)
    (hlt : ((X.tr g).take (e + 1)).countP (Execution.isBarId 0) <
      ((X.tr h).take f).countP (Execution.isBarId 0))
    (hle : ((X.tr g).take (e + 1)).countP (Execution.isBarId 0) ≤ 2)
    (hg : g % L.block < 128) (hh : h % L.block < 128) :
    baseCausality L X (g, e) (h, f) := by
  have hb : L.block = 256 := hp.block
  have hgrp : ∀ x, x % L.block < 128 → ∀ q, (x % L.block) / 32 ∈
      NamedBar.PhGroup L loopGroup 2 q := by
    intro x hx q
    unfold NamedBar.PhGroup
    split
    · simp only [Finset.mem_range, CtaBarrier.warps, hb]; omega
    · simp only [loopGroup, Finset.mem_range]; omega
  exact Handoff.of_barPhased hX (bar0_phSources hp hX) (loopGroup_sub hp) loopGroup_card
    (loopGroup_ne hp) loopGroup_target (by omega) (by decide)
    (fun h _ j pc hE => exit_three hp hX hE) hsame hf hlt hle (hgrp g hg _) (hgrp h hh _)

/-! ### Publication -/

/-- **An initialization is published to a ring user.** -/
theorem pub_of (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {I kI pcI : Nat} {l : Loc} {c : Nat} (hI : X.get (I, kI) = some ⟨pcI, .mbInit l c⟩)
    {k : Nat} (hk : k < (X.tr g).length) (hU : UserAt Q L X g k)
    (hsame : SameCta L I g) : baseCausality L X (I, kI) (g, k) := by
  have hb : L.block = 256 := hp.block
  obtain ⟨j, -, -, hw, -, -, hc0, hc1⟩ := init_info hp hX hI
  have hg : g < L.threads := hsame.2.1
  rcases hU with ⟨tm, bw, d, n, hσ, h180⟩ | ⟨tm, d, P, n, hσ⟩ | ⟨tm, d, P, n, hσ⟩
  · -- a prologue user: barrier 0's third instance
    obtain ⟨-, hP2, -, -⟩ := (pi_inv hp hX hg k hk _ hσ : PIP L g d _)
    have h3 := hP2 h180
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
    obtain ⟨t, ins, o, hat, hi, -, -⟩ :=
      Frame.fired_site (fun g hg => thread_sound hp hg) hX he hσ
    have htid : g % L.block < 128 := hi.1.args.tid
    exact bar0_upTo2 hp hX hsame hk (by omega) (by omega) (by omega) htid
  · -- a loader user: barrier 1's first instance
    have h1 := role_count hp hX hg hk rfl hσ
    have h1' : 1 ≤ ((X.tr g).take k).countP (Execution.isBarId 1) := by rw [h1]; split <;> omega
    exact bar1_handoff hp hX I g kI k ⟨hsame, by
      simp only [Finset.mem_range, CtaBarrier.warps, hb]; omega, trivial⟩ hk (by dsimp only; omega)
  · -- an MMA user
    have h1 := role_count hp hX hg hk rfl hσ
    have h1' : 1 ≤ ((X.tr g).take k).countP (Execution.isBarId 1) := by rw [h1]; split <;> omega
    exact bar1_handoff hp hX I g kI k ⟨hsame, by
      simp only [Finset.mem_range, CtaBarrier.warps, hb]; omega, trivial⟩ hk (by dsimp only; omega)

/-! ### The initialization exists once a user does -/

/-- **A ring user's CTA has passed the instance that publishes the initializations**: every thread
of warps 0 to 3 of the CTA has a barrier event at which its trace has every election's facts. -/
theorem user_pass (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k : Nat} (hk : k < (X.tr g).length) (hU : UserAt Q L X g k) {T : Nat}
    (hT : T / L.block = g / L.block) (hT128 : T % L.block < 128) :
    ∃ i, ∀ j, ElF L T j ((X.tr T).take i) := by
  have hb : L.block = 256 := hp.block
  have hg := thread_lt_of_len hX hk
  rcases hU with ⟨tm, bw, d, n, hσ, h180⟩ | ⟨tm, d, P, n, hσ⟩ | ⟨tm, d, P, n, hσ⟩
  · -- barrier 0's ordinal 2
    obtain ⟨-, hP2, -, -⟩ := (pi_inv hp hX hg k hk _ hσ : PIP L g d _)
    have h3 := hP2 h180
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
    obtain ⟨t, ins, o, hat, hi, -, -⟩ :=
      Frame.fired_site (fun g hg => thread_sound hp hg) hX he hσ
    have htid : g % L.block < 128 := hi.1.args.tid
    obtain ⟨j0, pc0, c0', md0, hj0, hget0, hc0⟩ :=
      nth_bar (X := X) (g := g) (q := 2) (f := k) (id := 0) (by omega)
    have hmd : md0 = .sync := by
      cases md0 with
      | sync => rfl
      | arrive => exact absurd hget0 (Consistent.noBarArrive (Fact.out) hX _ _ _ _)
    subst hmd
    obtain ⟨i, pci, cnti, hbi, hci⟩ := NamedBar.D_member_arrival (f := (g, j0)) hX
      (bar0_phSources hp hX) (loopGroup_sub hp) loopGroup_card (loopGroup_ne hp)
      loopGroup_target hget0 (by dsimp only; omega)
      (by simp only [loopGroup, Finset.mem_range]; omega) hT
      (by simp only [loopGroup, Finset.mem_range]; omega)
      (by
        rintro ⟨jx, pcx, hex⟩
        obtain ⟨i, pci, cnti, mdi, -, hgeti, hci⟩ :=
          nth_bar (X := X) (g := T) (q := 2) (f := jx) (id := 0)
          (by have := exit_three hp hX hex; omega)
        have hmi : mdi = .sync := by
          cases mdi with
          | sync => rfl
          | arrive => exact absurd hgeti (Consistent.noBarArrive (Fact.out) hX _ _ _ _)
        subst hmi
        exact ⟨i, pci, cnti, hgeti, by dsimp only; omega⟩)
    exact ⟨i, elF_at_bar hp hX hbi hT128 (.inr ⟨rfl, by dsimp only at hci; omega⟩)⟩
  all_goals
    -- barrier 1's ordinal 0
    have h1 := role_count hp hX hg hk rfl hσ
    have h1' : 0 + 1 ≤ ((X.tr g).take k).countP (Execution.isBarId 1) := by
      rw [h1]; split <;> omega
    obtain ⟨j0, pc0, c0', md0, hj0, hget0, hc0⟩ :=
      nth_bar (X := X) (g := g) (q := 0) (f := k) (id := 1) h1'
    have hmd : md0 = .sync := by
      cases md0 with
      | sync => rfl
      | arrive => exact absurd hget0 (Consistent.noBarArrive (Fact.out) hX _ _ _ _)
    subst hmd
    have hcn : c0' = none := ((bar1_sources hp hX) (g, j0) pc0 c0' ⟨.sync, hget0⟩ hg).2
    subst hcn
    have hf : X.IsBarrier (g, j0) 1 none pc0 := hget0
    obtain ⟨i, pci, mi, hgeti, -⟩ := (bar1_sources hp hX).member_arrival_any hX
      (bar1_shape hp) hf (by dsimp only; omega) (g := T) hT
      (by simp only [Finset.mem_range, CtaBarrier.warps, hb]; omega)
      (fun hex => by
        obtain ⟨i, pc', hb', hc'⟩ := bar1Exits hp hX hf (by dsimp only; omega) hT hex
        exact ⟨i, pc', .sync, hb', hc'⟩)
    exact ⟨i, elF_at_bar hp hX hgeti hT128 (.inl rfl)⟩

/-- **The initialization of barrier `j` of a CTA exists once a ring user of the CTA exists**: the
lane of warp 0 that the warp's elections return made it. -/
theorem init_exists (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k : Nat} (hk : k < (X.tr g).length) (hU : UserAt Q L X g k) (j : Fin 12) :
    ∃ I kI, I / L.block = g / L.block ∧ X.get (I, kI) = some (initEv L I j) := by
  have hb : L.block = 256 := hp.block
  have hg : g < L.threads := thread_lt_of_len hX hk
  set c := g / L.block with hc
  have hcg : c < L.grid := (Nat.div_lt_iff_lt_mul (by omega)).mpr hg
  -- thread 0 of the CTA: its election `el j`
  have hT0 : c * L.block < L.threads := by
    unfold Launch.threads; nlinarith
  have hT0c : c * L.block / L.block = c := by
    rw [Nat.mul_div_cancel _ (by omega)]
  obtain ⟨i0, hE0⟩ := user_pass hp hX hk hU (T := c * L.block) (by rw [hT0c])
    (by rw [Nat.mul_mod_left]; omega)
  obtain ⟨k0, inst, ld, hk0, -⟩ := hE0 j
  obtain ⟨-, hget0⟩ := get_of_take hk0
  obtain ⟨-, -, hmem⟩ := hX.elect.1 _ _ _ _ _ hget0
  have hld : ld < 32 := hmem.1
  -- the lane `ld` of warp 0
  set I := c * L.block + ld with hI
  have hIt : I < L.threads := by
    unfold Launch.threads; nlinarith
  have hIc : I / L.block = c := by
    rw [hI, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]
    simp
  have hImod : I % L.block = ld := by
    rw [hI, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨i1, hE1⟩ := user_pass hp hX hk hU (T := I) (by rw [hIc]) (by omega)
  obtain ⟨k1, inst1, ld1, hk1, hpost⟩ := hE1 j
  obtain ⟨-, hget1⟩ := get_of_take hk1
  have hsw : SameWarp L (c * L.block) I :=
    ⟨⟨hT0, hIt, by rw [hT0c, hIc]⟩, by rw [Nat.mul_mod_left, hImod]; omega⟩
  have heq := hX.elect.2.2 _ _ _ _ _ _ _ _ _ hget0 hget1 hsw
  obtain ⟨kI, hkI⟩ := hpost (by rw [laneOf_w0 (by omega), hImod, heq]) (by omega)
  obtain ⟨-, hgetI⟩ := get_of_take hkI
  exact ⟨I, kI, hIc, hgetI⟩

/-! ### `InitFirst` for the ring barriers -/

theorem validCount_one' : validCount 1 := by unfold validCount limit; omega

/-- The issuer of a ring barrier's record other than its initialization is a ring user of the
barrier's CTA. -/
theorem rec_user (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {mo : Loc}
    (hr : InRing L mo) {r : MBarrier.Record AsyncCopy.Ref} (hm : r ∈ X.objects mo)
    (hna : ∀ n, r.action ≠ .init n) :
    r.id.issuer.2 < (X.tr r.id.issuer.1).length ∧ UserAt Q L X r.id.issuer.1 r.id.issuer.2 ∧
      mo.cta = r.id.issuer.1 / L.block := by
  have hlen : ∀ {i : EvId} {e : Event}, X.get i = some e → i.2 < (X.tr i.1).length :=
    fun he => (List.getElem?_eq_some_iff.mp he).1
  cases record_source hX.tma.2.2.1 hm with
  | init hid he ha => exact absurd ha (hna _)
  | inval hid he ha => exact absurd he (no_inval hX)
  | @arrive g j pc tx c rel sc hid he ha =>
    rw [hid]
    obtain ⟨⟨-, -, s, hs, hmo, -⟩, hU⟩ := arrive_ring hp hX he hr
    exact ⟨hlen he, hU, by rw [hmo]; rfl⟩
  | @wait g j pc p ok acq sc hid he ha =>
    rw [hid]
    obtain ⟨⟨-, -, s, hs, ⟨hmo, -⟩ | ⟨hmo, -⟩⟩, hU⟩ := wait_ring hp hX he hr
    · exact ⟨hlen he, hU, by rw [hmo]; rfl⟩
    · exact ⟨hlen he, hU, by rw [hmo]; rfl⟩
  | increment hid he ha => exact absurd he (no_asyncArrive hX)
  | @tensor i pc a sp hid he hm' ha =>
    obtain ⟨g, j⟩ := i
    rw [hid]
    obtain ⟨⟨-, s, hs, hmo, -⟩, hU⟩ := copy_ring_ev hp hX he
    exact ⟨hlen he, hU, by rw [← hm', hmo]; rfl⟩
  | arriveOn hid he hm' hn ha => exact absurd he (no_asyncArrive hX)
  | bulk hid he hc hn ha => exact absurd he (no_copy hX)
  | @commit i pc sp rank hid he ht ha =>
    obtain ⟨g, j⟩ := i
    rw [hid]
    obtain ⟨⟨-, -, s, hs, hmo, -⟩, hU⟩ := commit_ring hp hX he ht hr
    exact ⟨hlen he, hU, by rw [hmo]; rfl⟩
  | clc hid he hm' htg ha => exact absurd he (no_clc hX)

/-- **A ring barrier is initialized first**: barrier `j` of CTA `c`, in the ring. -/
theorem ring_initFirst (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {c : Nat} {j : Fin 12} (hr : InRing L ((Proof.ProA.initBar j.val).loc L c)) :
    PairTmaRing.InitFirst X ((Proof.ProA.initBar j.val).loc L c) 1 := by
  set mo := (Proof.ProA.initBar j.val).loc L c with hmo
  intro r hrm
  -- an initialization event of the object
  obtain ⟨E, pcE, hE⟩ : ∃ E pcE, X.get E = some ⟨pcE, .mbInit mo 1⟩ := by
    by_cases hi : ∃ n, r.action = .init n
    · obtain ⟨n, ha⟩ := hi
      cases record_source hX.tma.2.2.1 hrm with
      | @init g k pc c' hid he ha' =>
        obtain ⟨-, -, rfl, -⟩ := init_info hp hX he
        exact ⟨(g, k), pc, he⟩
      | _ => simp_all
    · push Not at hi
      obtain ⟨hk, hU, hcta⟩ := rec_user hp hX hr hrm hi
      obtain ⟨I, kI, hIc, hget⟩ := init_exists hp hX hk hU j
      refine ⟨(I, kI), (ProA.Site.init j).pc, ?_⟩
      rw [hget]
      simp only [initEv, hIc, ← hcta, hmo, Proof.EvD.Bar.loc]
  obtain ⟨g0, k0⟩ := E
  have hg0 := Frame.lt_of_get hX hE
  refine Proof.Mbar.initFirst_of_published hX ⟨pcE, hE⟩ validCount_one'
    (fun i pc n hi => by
      obtain ⟨i1, i2⟩ := i
      obtain ⟨h1, -⟩ := init_unique hp hX hi hE
      obtain ⟨-, h2⟩ := init_unique hp hX hi hi
      exact ⟨h1, h2⟩) (fun s hs hna => ?_) r hrm
  obtain ⟨hk, hU, hcta⟩ := rec_user hp hX hr hs hna
  obtain ⟨j', hl, -⟩ := init_info hp hX hE
  have hc0 : g0 / L.block = mo.cta := by rw [hl]; rfl
  exact .inl (pub_of hp hX hE hk hU ⟨hg0, thread_lt_of_len hX hk, by rw [hc0, hcta]; rfl⟩)

theorem initBar_kv (c : Nat) {s : Nat} (hs : s < 3) :
    (Proof.ProA.initBar (2 * s)).loc L c = Proof.EvW.kvReady L c s ∧
      (Proof.ProA.initBar (2 * s + 1)).loc L c = Proof.EvW.kvEmpty L c s := by
  interval_cases s <;> exact ⟨rfl, rfl⟩

/-- **The six ring barriers of a CTA are initialized first** (`SingleTmaRing.Decl.Events`'s
`full_init` and `empty_init`). -/
theorem kv_initFirst (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (c : Nat)
    {s : Nat} (hs : s < 3) :
    PairTmaRing.InitFirst X (Proof.EvW.kvReady L c s) 1 ∧
      PairTmaRing.InitFirst X (Proof.EvW.kvEmpty L c s) 1 := by
  obtain ⟨h1, h2⟩ := initBar_kv (L := L) c hs
  constructor
  · have := ring_initFirst hp hX (c := c) (j := ⟨2 * s, by omega⟩)
      (by simp only [h1]; exact inRing_kvReady c hs)
    simpa only [h1] using this
  · have := ring_initFirst hp hX (c := c) (j := ⟨2 * s + 1, by omega⟩)
      (by simp only [h2]; exact inRing_kvEmpty c hs)
    simpa only [h2] using this

end
end PTX.Kernels.InklingRelDecode.Proof2
