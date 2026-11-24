-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsTmemLife
public import Lemmas.Flow.NotTcData
public import Kernels.FlashAttn4Fwd.Proof.Interface

@[expose] public section

/-! # The lanes of the MMA warp agree on their barrier and Tensor Memory events

A lane of warp 12 makes no named-barrier event but its two `bar.sync 2, 416` and no
warp-collective `tcgen05` event but its three paired Tensor Memory operations: its prologue's
events are of other kinds, and of its role's sites only the two `bar.sync 2` are barrier
instructions and none is a Tensor Memory load, store or wait (`mma_event_class`). So the `n`-th
barrier event of every lane is the same `bar.sync` (`Cross.BarAgree_mma`), and every lane exits
after three collective events, more than the ordinal of any (`Cross.TcExitAgree_mma`,
`Cross.TcExitAbove_mma`). The `n`-th collective event of every lane is the same operation at
the same site; the deallocation frees the column every lane read back from the base word, which
is lane 0's address store when the base-word protocol gives the read value
(`TmemAlloc.BaseRead`; `Cross.TcAgree_mma`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- No site of the MMA role is a Tensor Memory load, store or wait. -/
theorem Mma.tcData_ops : Mma.OpsOff (fun _ => false) tcDataOp := by
  unfold Mma.OpsOff
  decide +kernel

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **An event of warp 12** is a barrier event exactly when it is one on barrier 2, and a
warp-collective `tcgen05` event exactly when it is a paired Tensor Memory operation. -/
theorem mma_event_class {g j : Nat} {x : Event} (hw : warpOf L g = 12) (he : X.get (g, j) = some x)
    :
    Execution.isBar x = Execution.isBarId 2 x ∧ isTcColl x = Tmem.Pair.isTmemOp x := by
  obtain ⟨pc, k⟩ := x
  by_cases hend : Ends ⟨pc, k⟩
  · rcases hend with ⟨f, h⟩ | h <;> simp only at h <;> subst h <;>
      simp [Execution.isBar, Execution.isBarId, isTcColl, Tmem.Pair.isTmemOp]
  by_cases hp : Prologue.ProKind k
  · cases k <;> simp_all [Prologue.ProKind, Execution.isBar, Execution.isBarId, isTcColl,
      Tmem.Pair.isTmemOp]
  obtain ⟨d, t, ins, u, -, -, -, -, -, -, hc, hf⟩ := mma_state_cont hpre hX ht he hw hp hend
  have hb := Mma.bar2_site hpre hc hf
  have hd := Mma.tcData_ops.op (s := d.site) rfl hc
  refine ⟨?_, ?_⟩
  · cases hx : Execution.isBar ⟨pc, k⟩
    · cases hy : Execution.isBarId 2 ⟨pc, k⟩
      · rfl
      · simp [Execution.isBar, Execution.isBarId] at hx hy
        cases k <;> simp_all
    · have hk : ∃ id c m, k = .bar id c m := by
        cases k <;> simp_all [Execution.isBar]
      obtain ⟨id, c, m, rfl⟩ := hk
      have hop := fires_bar_op hf rfl
      cases hs : d.site.isBar2
      · rw [Mma.bar_ops.op hs hc] at hop
        cases hop
      · have : Mma.bar2Ev d.site (Mma.outcome L g ⟨pc, .bar id c m⟩) = true := by
          obtain ⟨site, _⟩ := d
          cases site <;> simp_all [Mma.Site.isBar2, Mma.bar2Ev]
        rw [hb.1, this]
  · cases k with
    | tc kd =>
      cases kd
      all_goals first
        | rfl
        | (exfalso
           have := fires_tcData_op hf (by simp [isTcData])
           rw [hd] at this
           cases this)
    | _ => rfl

/-- The barrier events of warp 12 before a position are those on barrier 2, and its collective
`tcgen05` events its paired Tensor Memory operations. -/
theorem mma_counts_class {g : Nat} (hw : warpOf L g = 12) (k : Nat) :
    ((X.tr g).take k).countP Execution.isBar = ((X.tr g).take k).countP (Execution.isBarId 2) ∧
      ((X.tr g).take k).countP isTcColl = Tmem.Pair.tmemOps ((X.tr g).take k) := by
  have hcl : ∀ x ∈ (X.tr g).take k, Execution.isBar x = Execution.isBarId 2 x ∧
      isTcColl x = Tmem.Pair.isTmemOp x := fun x hx => by
    obtain ⟨j, -, hj⟩ := mem_take_get hx
    exact mma_event_class hpre hX ht hw hj
  refine ⟨List.countP_congr fun x hx => by rw [(hcl x hx).1], ?_⟩
  exact List.countP_congr fun x hx => by rw [(hcl x hx).2]

/-- A barrier event of warp 12 is its first or its second `bar.sync 2, 416`. -/
theorem mma_bar_event {g i : Nat} {x : Event} (hw : warpOf L g = 12) (he : X.get (g, i) = some x)
    (hb : Execution.isBar x = true) :
    (x = ⟨Mma.Site.bar0.pc, .bar 2 (some 416) .sync⟩ ∧
        ((X.tr g).take i).countP Execution.isBar = 0) ∨
      (x = ⟨Mma.Site.bar1.pc, .bar 2 (some 416) .sync⟩ ∧
        ((X.tr g).take i).countP Execution.isBar = 1) := by
  have h2 : Execution.isBarId 2 x = true := by
    rw [← (mma_event_class hpre hX ht hw he).1, hb]
  have hk : ∃ c m, x.kind = .bar 2 c m := by
    obtain ⟨pc, k⟩ := x
    cases k <;> simp_all [Execution.isBarId]
  obtain ⟨c, m, hk⟩ := hk
  obtain ⟨d, t, ins, u, -, hJ, -, -, -, -, hc, hf⟩ :=
    mma_state_cont hpre hX ht he hw (by rw [hk]; simp [Prologue.ProKind])
      (by rintro (⟨f, h⟩ | h) <;> rw [hk] at h <;> cases h)
  have hkind := (Mma.bar2_site hpre hc hf).2 h2
  have hpc := fires_pc hf
  have hcnt := hJ.bar2
  rw [← (mma_counts_class hpre hX ht hw i).1] at hcnt
  have hb2 := (Mma.bar2_site hpre hc hf).1
  rw [h2] at hb2
  obtain ⟨site, _⟩ := d
  obtain ⟨pc', k'⟩ := x
  simp only at hkind hpc
  subst hkind hpc
  cases site <;> simp [Mma.bar2Ev] at hb2
  · exact .inl ⟨rfl, hcnt⟩
  · exact .inr ⟨rfl, hcnt⟩

/-- **`Cross.BarAgree`, for warp 12.** -/
theorem Cross.BarAgree_mma :
    ∀ {g h i j : Nat} {x y : Event}, SameWarp L g h → warpOf L g = 12 → X.get (g, i) = some x →
      X.get (h, j) = some y → Execution.isBar x = true → Execution.isBar y = true →
      ((X.tr g).take i).countP Execution.isBar = ((X.tr h).take j).countP Execution.isBar →
      x = y := by
  intro g h i j x y hs hw he he' hx hy hc
  have hw' : warpOf L h = 12 := by rw [← hw]; exact hs.2.symm
  rcases mma_bar_event hpre hX ht hw he hx with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
    rcases mma_bar_event hpre hX ht hw' he' hy with ⟨rfl, h2⟩ | ⟨rfl, h2⟩ <;>
    first | rfl | omega

/-- **`Cross.TcExitAgree`, for warp 12.** -/
theorem Cross.TcExitAgree_mma :
    ∀ {g h k k' pc pc' : Nat} {d d' : ThreadD}, SameWarp L g h → warpOf L g = 12 →
      St L X g k = some (some d) → St L X h k' = some (some d') →
      X.get (g, k) = some ⟨pc, .exit⟩ → X.get (h, k') = some ⟨pc', .exit⟩ →
      ((X.tr g).take k).countP isTcColl = ((X.tr h).take k').countP isTcColl := by
  intro g h k k' pc pc' d d' hs hw _ _ he he'
  have hw' : warpOf L h = 12 := by rw [← hw]; exact hs.2.symm
  rw [(mma_counts_class hpre hX ht hw k).2, (mma_counts_class hpre hX ht hw' k').2,
    TmemFacts_exit hpre hX ht hs.1.1 hw he, TmemFacts_exit hpre hX ht hs.1.2.1 hw' he']

/-- **`Cross.TcExitAbove`, for warp 12.** -/
theorem Cross.TcExitAbove_mma :
    ∀ {g h k k' pc n : Nat} {d d' : ThreadD}, SameWarp L g h → warpOf L g = 12 →
      St L X g k = some (some d) → St L X h k' = some (some d') →
      X.get (h, k') = some ⟨pc, .exit⟩ → X.TcK (g, k) n →
      n < ((X.tr h).take k').countP isTcColl := by
  intro g h k k' pc n d d' hs hw _ _ he' ⟨⟨ev, hev, hcol⟩, hn⟩
  have hw' : warpOf L h = 12 := by rw [← hw]; exact hs.2.symm
  rw [(mma_counts_class hpre hX ht hw' k').2, TmemFacts_exit hpre hX ht hs.1.2.1 hw' he', ← hn,
    (mma_counts_class hpre hX ht hw k).2]
  rw [(mma_event_class hpre hX ht hw hev).2] at hcol
  obtain ⟨pce, ke⟩ := ev
  unfold Tmem.Pair.isTmemOp at hcol
  split at hcol
  · rename_i grp dst act hk
    simp only at hk
    subst hk
    exact Tmem.Pair.lt_of_tmemShape (TmemFacts_event hpre hX ht hs.1.1 hev).2.2.1
  · cases hcol

/-- **A warp-collective `tcgen05` event of warp 12** is its `n`-th paired Tensor Memory operation,
at the site `n` names; a deallocation frees the column its carried address register holds. -/
theorem mma_tc_coll {g k pc n : Nat} {kd : TcKind} (hw : warpOf L g = 12)
    (he : X.get (g, k) = some ⟨pc, .tc kd⟩) (hK : X.TcK (g, k) n) :
    ∃ (d : Mma.D) (t : TState), Mma.Counts L g d ((X.tr g).take k) ∧ n = Mma.tmemA d.site ∧
      pc = d.site.pc ∧
      ((d.site = .alloc ∧ kd = .resource .two (some (Mma.baseAt L g)) (.alloc 512)) ∨
        (d.site = .relinquish ∧ kd = .resource .two none .relinquish) ∨
        (d.site = .dealloc ∧ t.regs 379 = some d.base ∧ ∃ v,
          readBits L g t 32 (.reg 379) = .ok v ∧ kd = .resource .two none (.dealloc v.toNat 512)))
    := by
  obtain ⟨⟨ev, hev, hcol⟩, hn⟩ := hK
  rw [he] at hev
  obtain rfl := Option.some.inj hev
  rw [(mma_event_class hpre hX ht hw he).2] at hcol
  have hk : ∃ grp dst act, kd = .resource grp dst act := by
    cases kd <;> simp_all [Tmem.Pair.isTmemOp]
  obtain ⟨grp, dst, act, rfl⟩ := hk
  obtain ⟨-, d, t, ins, u, hJ, -, -, hs, h, hc, hf⟩ := tmem_state hpre hX ht he
  have hn' : n = Mma.tmemA d.site := by
    rw [← hn, (mma_counts_class hpre hX ht hw k).2, hJ.tmem]
  refine ⟨d, t, hJ, hn', fires_pc hf, ?_⟩
  rcases tmem_site hpre hs h hc hf with ⟨hd, rfl, rfl, rfl⟩ | ⟨hd, rfl, rfl⟩ | ⟨hd, rfl, -⟩
  · exact .inl ⟨hd, rfl⟩
  · refine .inr (.inl ⟨hd, ?_⟩)
    obtain ⟨site, i, tt, base, pro⟩ := d
    simp only at hd hc hf
    subst hd
    code_at hc
    subst hc
    have hk := fires_tcRelinquish_some hf
    simp only [Kind.tc.injEq] at hk
    exact hk
  · refine .inr (.inr ⟨hd, ?_⟩)
    obtain ⟨site, i, tt, base, pro⟩ := d
    simp only at hd h hc hf ⊢
    subst hd
    have hr : t.regs 379 = some base := Mma.reg_of h (by table_decide) (by mma_values)
    have hn := Mma.reg_b32 (r := 960) (x := 512) h (by table_decide) (by mma_values)
    code_at hc
    subst hc
    obtain ⟨-, rfl, -⟩ := fires_tcDealloc_resource hf rfl
    obtain ⟨a, n, ha, hn', hact⟩ := fires_tcDealloc_ops hf rfl
    rw [Mma.readBits_b32 hn] at hn'
    obtain rfl := (Except.ok.inj hn').symm
    refine ⟨hr, a, ha, ?_⟩
    rw [hact]
    simp [truncBits]

/-- Two allocations of a thread are one. -/
theorem alloc_unique' {q j j' pc pc' n n' : Nat} {grp grp' : CtaGroup} {dst dst' : Option Loc}
    (hq : q < L.threads) (h : X.get (q, j) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩)
    (h' : X.get (q, j') = some ⟨pc', .tc (.resource grp' dst' (.alloc n'))⟩) : j = j' := by
  have hz : ∀ {j pc n grp dst}, X.get (q, j) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ →
      Tmem.Pair.tmemOps ((X.tr q).take j) = 0 := fun h =>
    (Tmem.Pair.shape_alloc (TmemFacts_event hpre hX ht hq h).2.2.1).1
  have hs : ∀ {j pc n grp dst}, X.get (q, j) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ →
      Tmem.Pair.tmemOps ((X.tr q).take (j + 1)) = 1 := fun h => by
    unfold Tmem.Pair.tmemOps
    rw [PTX.Flow.countP_take_succ h rfl]
    exact congrArg (· + 1) (hz h)
  rcases Nat.lt_trichotomy j j' with hlt | heq | hgt
  · have := PTX.Flow.countP_take_mono Tmem.Pair.isTmemOp (X.tr q) (show j + 1 ≤ j' by omega)
    have h1 := hs h
    have h2 := hz h'
    unfold Tmem.Pair.tmemOps at h1 h2
    omega
  · exact heq
  · have := PTX.Flow.countP_take_mono Tmem.Pair.isTmemOp (X.tr q) (show j' + 1 ≤ j by omega)
    have h1 := hs h'
    have h2 := hz h
    unfold Tmem.Pair.tmemOps at h1 h2
    omega

/-- **The lanes of a CTA's warp 12 carry one base address** after their read-backs, when the
read-back returns lane 0's address store. -/
theorem base_agree (hbr : TmemAlloc.BaseRead L X) {g h k k' : Nat} {d d' : Mma.D}
    (hs : SameWarp L g h) (hw : warpOf L g = 12) (hJ : Mma.Counts L g d ((X.tr g).take k))
    (hJ' : Mma.Counts L h d' ((X.tr h).take k')) (h5 : 5 ≤ d.site.start) (h5' : 5 ≤ d'.site.start)
    : d.base = d'.base := by
  have hw' : warpOf L h = 12 := by rw [← hw]; exact hs.2.symm
  have hcta : ctaOf L g = ctaOf L h := hs.1.2.2
  obtain ⟨x, hx, ra, bs, hk, hloc, hsz, hreb⟩ := hJ.baseRead h5
  obtain ⟨x', hx', ra', bs', hk', hloc', hsz', hreb'⟩ := hJ'.baseRead h5'
  obtain ⟨j, -, hj⟩ := mem_take_get hx
  obtain ⟨j', -, hj'⟩ := mem_take_get hx'
  obtain ⟨ja, pca, grp, dst, n, pcw, wa, wbs, ha, hwr, hbs⟩ :=
    hbr hs.1.1 (get_kind hj hk) hloc hsz hw
  obtain ⟨ja', pca', grp', dst', n', pcw', wa', wbs', ha', hwr', hbs'⟩ :=
    hbr hs.1.2.1 (get_kind hj' hk') hloc' hsz' hw'
  rw [← hcta] at ha' hwr'
  have hq : TmemAlloc.lane0 L (ctaOf L g) < L.threads := Frame.lt_of_get hX ha
  obtain rfl := alloc_unique' hpre hX ht hq ha ha'
  rw [hwr] at hwr'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.wr.injEq] at hwr'
  rw [hbs, hwr'.2.2, ← hbs'] at hreb
  rw [hreb] at hreb'
  exact Except.ok.inj hreb'

/-- **`Cross.TcAgree`, for warp 12**, given the base-word protocol's read value. -/
theorem Cross.TcAgree_mma (hbr : TmemAlloc.BaseRead L X) :
    ∀ {g h k k' pc pc' n : Nat} {kd kd' : TcKind} {d d' : ThreadD}, SameWarp L g h →
      warpOf L g = 12 → St L X g k = some (some d) → St L X h k' = some (some d') →
      X.get (g, k) = some ⟨pc, .tc kd⟩ → X.get (h, k') = some ⟨pc', .tc kd'⟩ →
      X.TcK (g, k) n → X.TcK (h, k') n → pc = pc' ∧ tcStatic kd = tcStatic kd' := by
  intro g h k k' pc pc' n kd kd' _ _ hs hw _ _ he he' hK hK'
  have hw' : warpOf L h = 12 := by rw [← hw]; exact hs.2.symm
  obtain ⟨m, t, hJ, hn, hpc, hcase⟩ := mma_tc_coll hpre hX ht hw he hK
  obtain ⟨m', t', hJ', hn', hpc', hcase'⟩ := mma_tc_coll hpre hX ht hw' he' hK'
  have hcta : g / L.block = h / L.block := hs.1.2.2
  rcases hcase with ⟨hd, rfl⟩ | ⟨hd, rfl⟩ | ⟨hd, hr, v, hv, rfl⟩ <;>
    rcases hcase' with ⟨hd', rfl⟩ | ⟨hd', rfl⟩ | ⟨hd', hr', v', hv', rfl⟩ <;>
    rw [hd] at hn hpc <;> rw [hd'] at hn' hpc' <;>
    simp only [Mma.tmemA] at hn hn' <;> try omega
  · exact ⟨hpc.trans hpc'.symm, by simp [tcStatic, Mma.baseAt, hcta]⟩
  · exact ⟨hpc.trans hpc'.symm, rfl⟩
  · have hb := base_agree hpre hX ht hbr hs hw hJ hJ' (by rw [hd]; decide) (by rw [hd']; decide)
    rw [readBits_reg_congr (L' := L) (g' := h) (t' := t') (by rw [hr, hr', hb]), hv'] at hv
    obtain rfl := Except.ok.inj hv
    exact ⟨hpc.trans hpc'.symm, rfl⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof
