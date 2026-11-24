-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingInitSources
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingGateEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
public import Lemmas.Protocol.NamedBarSources

@[expose] public section

/-! # The prologue CTA gate publishes mbarrier initialization -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.InitCtaPublication

open PTX PTX.Flow

private def gateWarps : Finset Nat := Finset.range 12

private theorem gate_shape {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) : NamedBar.Shape L none gateWarps 0 := by
  refine ⟨by decide, ?_, ?_, by decide⟩
  · rw [hpre.block]
    rfl
  · intro w hw
    rw [hpre.block]
    exact Finset.mem_range.mp hw

private theorem all_warps_participate {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) (g : Nat) : g % L.block / 32 ∈ gateWarps := by
  have hlt : g % 384 < 384 := Nat.mod_lt _ (by decide)
  rw [hpre.block]
  exact Finset.mem_range.mpr (by omega)

private theorem gate_state {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g k : Nat} {e : Event} {c : Option Nat} {mode : BarMode}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (he : X.get (g, k) = some e)
    (hk : e.kind = .bar 0 c mode) :
    Frame.stateAt (Machine.code P L) X g k = some (some (.prologue .barrier)) ∧
      c = none ∧ mode = .sync := by
  obtain ⟨d, o, hst, hf⟩ :=
    RingSourceSites.fired_from_trace hX hs ht he (by intro f h; rw [hk] at h; cases h)
  obtain ⟨rfl, hc, hm⟩ := RingGateEvents.gate_source hf hk
  exact ⟨hst, hc, hm⟩

private theorem gate_sources {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) :
    NamedBar.Sources L X none gateWarps 0 := by
  rintro ⟨g, k⟩ site c ⟨mode, he⟩ hg
  exact ⟨all_warps_participate hpre g, (gate_state hX (hs g hg) ht he rfl).2.1⟩

private theorem gate_first {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (he : X.get (g, i) = some e)
    (hSt : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .barrier))) :
    ((X.tr g).take i).countP (Execution.isBarId 0) = 0 := by
  apply List.countP_eq_zero.mpr
  intro f hf
  cases hfbar : Execution.isBarId 0 f
  · decide
  obtain ⟨k, hk, hkf⟩ := List.mem_iff_getElem.mp hf
  have hki : k < i := by simp at hk; omega
  have hkg : k < (X.tr g).length := by simp at hk; omega
  have hget : X.get (g, k) = some f := by
    change (X.tr g)[k]? = some f
    rw [List.getElem?_eq_getElem hkg]
    simpa only [List.getElem_take] using congrArg some hkf
  obtain ⟨_, _, _, hkind⟩ := NamedBar.isBarId_form hfbar
  have hst := (gate_state hX hs ht hget (congrArg Event.kind hkind)).1
  have := RingInitSources.gate_state_unique hget he hst hSt
  omega

private theorem gate_roles {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {d : Machine.ThreadD} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (he : X.get (g, i) = some e)
    (hSt : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hrole : ∀ s, d ≠ .prologue s) :
    ∃ k site, k + 1 < i ∧ X.IsBarrier (g, k) 0 none site ∧
      ((X.tr g).take k).countP (Execution.isBarId 0) = 0 := by
  obtain ⟨k, f, hk, hf, hkind, hst⟩ := RingInitSources.gate_before_role hX hs ht he hSt hrole
  refine ⟨k, f.pc, hk, ?_, gate_first hX hs ht hf hst⟩
  change X.get (g, k) = some ⟨f.pc, .bar 0 none .sync⟩
  rw [hf, ← hkind]

private instance : Fact kernel.NoBarArrive := ⟨by
  unfold Kernel.NoBarArrive
  decide +kernel⟩

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem exited_has_gate {g : Nat} (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hexit : ∃ j site, X.get (g, j) = some ⟨site, .exit⟩) :
    ∃ k site, X.IsBarrier (g, k) 0 none site ∧
      ((X.tr g).take k).countP (Execution.isBarId 0) = 0 := by
  obtain ⟨j, site, he⟩ := hexit
  obtain ⟨d, _, hst, hf⟩ := RingSourceSites.fired_from_trace hX hs ht he (by
    intro f heq
    cases heq)
  obtain ⟨k, s, _, h, hcount⟩ := gate_roles hX hs ht he hst
    (RingGateEvents.exit_after_prologue hf rfl)
  exact ⟨k, s, h, hcount⟩

/-- A gate predecessor in any member lane is ordered before a role event in its CTA. -/
theorem on_prologue_before_role {g h i k : Nat} {d : Machine.ThreadD} {e f : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e) (hf : X.get (h, k) = some f)
    (hgate : ∀ x, Frame.stateAt (Machine.code P L) X g x = some (some (.prologue .barrier)) → i < x)
    (huser : Frame.stateAt (Machine.code P L) X h k = some (some d)) (hrole : ∀ s, d ≠ .prologue s)
    (hcta : ctaOf L g = ctaOf L h) :
    baseCausality L X (g, i) (h, k) := by
  have hg := Frame.lt_of_get hX he
  have hh := Frame.lt_of_get hX hf
  have hlen := (List.getElem?_eq_some_iff.mp hf).choose
  obtain ⟨y, site, hy, hybar, hycount⟩ := gate_roles hX (hs h hh) ht hf huser hrole
  have hypass : y + 1 < (X.tr h).length := Nat.lt_trans hy hlen
  have hS := gate_sources hpre hX hs ht
  have hG := gate_shape hpre
  obtain ⟨x, site', hxbar, hxcount⟩ :=
    hS.member_arrival hX hG hybar hypass hcta (all_warps_participate hpre g) (fun hex => by
      obtain ⟨x, site', hx, hc⟩ := exited_has_gate hX (hs g hg) ht hex
      exact ⟨x, site', hx, hc.trans hycount.symm⟩)
  have hxstate := (gate_state hX (hs g hg) ht hxbar rfl).1
  exact hS.same_ordinal_baseCausality hX hG ⟨hg, hh, hcta⟩ hxbar hybar hypass hxcount
    (hgate x hxstate) (by omega) hlen

/-- The prologue gate orders a CTA's initialization before the actual event of a role. -/
theorem init_published_before_role {g h i k : Nat} {j : Fin 23} {d : Machine.ThreadD} {e f : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e) (hf : X.get (h, k) = some f)
    (hinit : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue (.init j))))
    (huser : Frame.stateAt (Machine.code P L) X h k = some (some d)) (hrole : ∀ s, d ≠ .prologue s)
    (hcta : ctaOf L g = ctaOf L h) :
    baseCausality L X (g, i) (h, k) :=
  on_prologue_before_role hpre hX hs ht he hf
    (fun _ => RingInitSources.init_before_gate hinit) huser hrole hcta

/-- A CTA's allocation result is read before every role event in that CTA. -/
theorem alloc_read_before_role {g h i k : Nat} {d : Machine.ThreadD} {e f : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e) (hf : X.get (h, k) = some f)
    (hread : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .allocRead)))
    (huser : Frame.stateAt (Machine.code P L) X h k = some (some d)) (hrole : ∀ s, d ≠ .prologue s)
    (hcta : ctaOf L g = ctaOf L h) :
    baseCausality L X (g, i) (h, k) :=
  on_prologue_before_role hpre hX hs ht he hf
    (fun _ => RingInitSources.alloc_read_before_gate hread) huser hrole hcta

private theorem gate_member {g h k site : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ a < L.threads, (Machine.machine P L a).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hg : g < L.threads) (hbar : X.IsBarrier (h, k) 0 none site) (hpass : k + 1 < (X.tr h).length)
    (hord : ((X.tr h).take k).countP (Execution.isBarId 0) = 0) (hcta : ctaOf L g = ctaOf L h) :
    ∃ i s, X.IsBarrier (g, i) 0 none s ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .barrier)) := by
  obtain ⟨i, s, hi, _⟩ := (gate_sources hpre hX hs ht).member_arrival hX (gate_shape hpre)
    hbar hpass hcta (all_warps_participate hpre g) (fun hex => by
      obtain ⟨i, s, hi, hc⟩ := exited_has_gate hX (hs g hg) ht hex
      exact ⟨i, s, hi, hc.trans hord.symm⟩)
  exact ⟨i, s, hi, (gate_state hX (hs g hg) ht hi rfl).1⟩

/-- A role event implies the actual prologue-gate arrival of each of its CTA members. -/
theorem role_gate_member {g h k : Nat} {d : Machine.ThreadD} {f : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ a < L.threads, (Machine.machine P L a).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hf : X.get (h, k) = some f) (hd : Frame.stateAt (Machine.code P L) X h k = some (some d))
    (hrole : ∀ s, d ≠ .prologue s) (hg : g < L.threads) (hcta : ctaOf L g = ctaOf L h) :
    ∃ i s, X.IsBarrier (g, i) 0 none s ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .barrier)) := by
  obtain ⟨j, s, hj, hbar, hord⟩ := gate_roles hX (hs h (Frame.lt_of_get hX hf)) ht hf hd hrole
  exact gate_member hpre hX hs ht hg hbar (Nat.lt_trans hj (PTX.len_of_get hf)) hord hcta

/-- The full-CTA gate certifies completion of the elected lane's entire initialization table. -/
theorem completed_init_before_role {h k : Nat} {d : Machine.ThreadD} {f : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ a < L.threads, (Machine.machine P L a).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hf : X.get (h, k) = some f) (huser : Frame.stateAt (Machine.code P L) X h k = some (some d))
    (hrole : ∀ s, d ≠ .prologue s) (j : Fin 23) :
    ∃ init, X.MbInit init ⟨.shared, ctaOf L h, L.sharedBase + initOff j⟩ (initCount j) ∧
      baseCausality L X init (h, k) := by
  have hh := Frame.lt_of_get hX hf
  have hlen := (List.getElem?_eq_some_iff.mp hf).choose
  obtain ⟨y, sy, hy, hybar, hycount⟩ := gate_roles hX (hs h hh) ht hf huser hrole
  have hypass := Nat.lt_trans hy hlen
  let cta := ctaOf L h
  let base := cta * L.block
  have hgrid : cta < L.grid := NamedBar.cta_lt hh
  have hbaseLt : base < L.threads :=
    NamedBar.cta_thread_lt hgrid (by rw [hpre.block]; decide : 0 < L.block)
  have lanes {lane : Nat} (hlane : lane < 32) :
      ctaOf L (base + lane) = cta ∧ warpOf L (base + lane) = 0 ∧
        laneOf L (base + lane) = lane ∧ base + lane < L.threads := by
    have hsmall : lane < L.block := by rw [hpre.block]; omega
    have hmod : (base + lane) % L.block = lane := by
      simp only [base, Nat.add_comm (cta * L.block) lane, Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt hsmall
    have hdiv : (base + lane) / L.block = cta := by
      simp only [base, Nat.add_comm (cta * L.block) lane, Nat.add_mul_div_right _ _
        (by rw [hpre.block]; decide : 0 < L.block), Nat.div_eq_of_lt hsmall, Nat.zero_add]
    have htid : tidOf L (base + lane) = lane := by
      rw [tidOf_eq hpre, ← hpre.block, hmod]
    exact ⟨hdiv, by unfold warpOf; rw [htid, Nat.div_eq_of_lt hlane],
      by unfold laneOf; rw [htid, Nat.mod_eq_of_lt hlane], NamedBar.cta_thread_lt hgrid hsmall⟩
  obtain ⟨hcb, hw0, _, _⟩ := lanes (lane := 0) (by decide)
  rw [Nat.add_zero] at hcb hw0
  obtain ⟨b, sb, hb, hbst⟩ :=
    gate_member hpre hX hs ht hbaseLt hybar hypass hycount hcb
  obtain ⟨x, u, inst, leader, _, hx, hu, _⟩ :=
    RingInitSources.gate_election hX (hs base hbaseLt) ht hb hw0 hbst
  have help : ∀ {g x inst leader : Nat} {e : Event}, X.get (g, x) = some e →
      e.kind = .elect 4294967295 inst leader → X.Elect (g, x) e.pc 4294967295 inst leader := by
    intro g x inst leader e he hk
    change X.get (g, x) = some ⟨e.pc, .elect 4294967295 inst leader⟩
    rw [he, ← hk]
  have hE := help hx hu
  have hlead : leader < 32 := (hX.elect.1 (base, x) u.pc 4294967295 inst leader hE).2.2.1
  obtain ⟨hc, hw, hlane, hg⟩ := lanes hlead
  let g := base + leader
  obtain ⟨z, sz, hz, hzst⟩ := gate_member hpre hX hs ht hg hybar hypass hycount hc
  obtain ⟨w, v, inst', leader', _, hget, hkind, hst⟩ :=
    RingInitSources.gate_election hX (hs g hg) ht hz hw hzst
  have hE' := help hget hkind
  have hwarp : SameWarp L base g := by
    refine ⟨⟨hbaseLt, hg, hcb.trans hc.symm⟩, ?_⟩
    simpa [warpOf, tidOf_eq hpre, hpre.block] using hw0.trans hw.symm
  have heq := hX.elect.2.2 (base, x) (g, w) u.pc v.pc 4294967295 inst inst' leader leader' hE hE'
    hwarp
  rw [← heq, ← hlane] at hkind
  obtain ⟨i, e, _, he, hk, hi⟩ :=
    RingInitSources.gate_initializes hpre hX (hs g hg) hget hz hkind hst hzst j
  refine ⟨(g, i), ⟨e.pc, ?_⟩, init_published_before_role hpre hX hs ht he hf hi huser hrole hc⟩
  rw [hc] at hk
  rw [he, ← hk]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.InitCtaPublication
