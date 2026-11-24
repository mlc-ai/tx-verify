-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingGateMember
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingInitTable
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingInitSources

@[expose] public section

/-! # Publication of the actual initialization table -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- Release of the launch gate guarantees that the CTA's elected lane issued every table entry. -/
private theorem actual_init_of_gate_release {X : Execution} {h : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hh : h < L.threads)
    (hrelease : CtaBarrier.Released L.block (X.barriers (h / L.block)) 0 0) (j : Fin 23) :
    ∃ g i e, X.get (g, i) = some e ∧
      e.kind = .mbInit ⟨.shared, ctaOf L h, L.sharedBase + initOff j⟩ (initCount j) ∧
      ctaOf L g = ctaOf L h ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.prologue (.init j))) := by
  let cta := ctaOf L h
  let base := cta * L.block
  have hgrid : cta < L.grid := NamedBar.cta_lt hh
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
  obtain ⟨hcb, hw0, _, hbaseLt⟩ := lanes (lane := 0) (by decide)
  rw [Nat.add_zero] at hcb hw0 hbaseLt
  have hBaseRelease : CtaBarrier.Released L.block (X.barriers (base / L.block)) 0 0 := by
    rw [show base / L.block = cta from hcb]
    exact hrelease
  obtain ⟨b, hb, hbst, _⟩ := gate_member_zero hpre hX hs hbaseLt hBaseRelease
  obtain ⟨x, u, inst, leader, _, hx, hu, _⟩ :=
    RingInitSources.gate_election_followed hX (hs base hbaseLt).machine hb hw0 hbst
  have asElection {g x inst leader : Nat} {e : Event} (he : X.get (g, x) = some e)
      (hk : e.kind = .elect 4294967295 inst leader) :
      X.Elect (g, x) e.pc 4294967295 inst leader := by
    change X.get (g, x) = some ⟨e.pc, .elect 4294967295 inst leader⟩
    rw [he, ← hk]
  have hE := asElection hx hu
  have hlead : leader < 32 := (hX.elect.1 (base, x) u.pc 4294967295 inst leader hE).2.2.1
  obtain ⟨hc, hw, hlane, hg⟩ := lanes hlead
  let g := base + leader
  have hGRelease : CtaBarrier.Released L.block (X.barriers (g / L.block)) 0 0 := by
    rw [show g / L.block = cta from hc]
    exact hrelease
  obtain ⟨z, hz, hzst, _⟩ := gate_member_zero hpre hX hs hg hGRelease
  obtain ⟨w, v, inst', leader', _, hget, hkind, hst⟩ :=
    RingInitSources.gate_election_followed hX (hs g hg).machine hz hw hzst
  have hE' := asElection hget hkind
  have hwarp : SameWarp L base g := by
    refine ⟨⟨hbaseLt, hg, hcb.trans hc.symm⟩, ?_⟩
    simpa [warpOf, tidOf_eq hpre, hpre.block] using hw0.trans hw.symm
  have heq := hX.elect.2.2 (base, x) (g, w) u.pc v.pc 4294967295 inst inst' leader leader' hE hE'
    hwarp
  rw [← heq, ← hlane] at hkind
  obtain ⟨i, e, _, he, hk, hi⟩ :=
    RingInitSources.gate_initializes hpre hX (hs g hg).machine hget hz hkind hst hzst j
  rw [hc] at hk
  exact ⟨g, i, e, he, hk, hc, hi⟩

/-- A followed role event proves that the elected lane executed its CTA's entire initialization
table and that each entry precedes this event in base causality. -/
theorem completed_init_before_followed_role {X : Execution} {h k : Nat} {d : Machine.ThreadD}
    {f : Event} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hf : X.get (h, k) = some f)
    (huser : Frame.stateAt (Machine.code P L) X h k = some (some d)) (hrole : ∀ s, d ≠ .prologue s)
    (j : Fin 23) :
    ∃ init, X.MbInit init ⟨.shared, ctaOf L h, L.sharedBase + initOff j⟩ (initCount j) ∧
      baseCausality L X init (h, k) := by
  obtain ⟨_, _, _, hrelease⟩ := gate_of_followed_role hpre hX hs hf huser hrole
  obtain ⟨g, i, e, he, hk, hc, hi⟩ :=
    actual_init_of_gate_release hpre hX hs (Frame.lt_of_get hX hf) hrelease j
  refine ⟨(g, i), ⟨e.pc, ?_⟩, init_before_followed_role hpre hX hs he hf hi huser hrole hc⟩
  rw [he, ← hk]

/-- Every table entry has been issued when the followed trace is pending in a role. -/
theorem table_init_of_followed_tail {X : Execution} {g : Nat} {d : Machine.ThreadD}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hg : g < L.threads)
    (hd : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    (hrole : ∀ s, d ≠ .prologue s) (j : Fin 23) :
    ∃ init, X.MbInit init (Protocol.IndexRing.initTable.loc L (ctaOf L g) j) (initCount j) := by
  obtain ⟨i, hPast, he, hGate⟩ := gate_before_followed_state hX (hs g hg).machine hg hd hrole
  obtain ⟨_, hRelease⟩ := passed_gate_zero hpre hX hs he hGate hPast
  obtain ⟨h, k, e, he, hk, _, _⟩ := actual_init_of_gate_release hpre hX hs hg hRelease j
  refine ⟨(h, k), e.pc, ?_⟩
  change X.get (h, k) = some
    ⟨e.pc, .mbInit ⟨.shared, ctaOf L g, L.sharedBase + initOff j⟩ (initCount j)⟩
  rw [he, ← hk]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
