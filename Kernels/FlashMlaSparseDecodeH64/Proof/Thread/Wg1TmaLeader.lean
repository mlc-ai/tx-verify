-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Flow.TraceInduction
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # Warp 5's elected TMA issuer -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1TmaLeader

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch}

theorem full_mask {g : Nat} {d : Wg1Tma.D} {e : Event} {o : Option TState} {mask inst leader : Nat}
    (hd : d.site = .elect) (hf : (Machine.machine P L g).Fired (some (.tma d)) e o)
    (he : e.kind = .elect mask inst leader) : mask = 4294967295 := by
  obtain ⟨t, ⟨hat, _⟩, hf⟩ := hf
  change (Wg1Tma.code P L g).AtD d t at hat
  have hpc : d.site.pc = 2165 := by rw [hd]; rfl
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  rw [hpc, Flow.code_2165] at hf
  have ht : Holds t.regs (Wg1Tma.facts P L g d) := hat.2.2.2.2
  have hr : t.regs 663 = some (b32 4294967295) := by
    rw [Wg1Tma.facts, hpc] at ht
    exact holds_mem ht (mem_factsFrom (val := Wg1Tma.valueOf P L g d)
      (by decide +kernel : 663 ∈ (Flow.live 2165).filter Wg1Tma.tracked.contains))
  have hread := readBits_b32 (L := L) (g := g) hr (by decide)
  rcases fires_elect_mask hread hf with ⟨_, _, h⟩ | ⟨_, h⟩
  · rw [h] at he
    exact (Kind.elect.inj he).1.symm
  · rw [h] at he
    cases he

private theorem chosen {g : Nat} {d d' : Wg1Tma.D} {e : Event} (hd : d.site = .elect)
    (hn : Wg1Tma.next P L g d e = some (some d')) :
    ∃ mask inst, e.kind = .elect mask inst (PTX.laneOf L g) := by
  cases he : e.kind <;> simp only [Wg1Tma.next, hd, he, reduceCtorEq] at hn
  rename_i mask inst leader
  split_ifs at hn with hld <;> simp only [Option.some.injEq, reduceCtorEq] at hn
  exact ⟨mask, inst, by rw [hld]⟩

private def followsLeader (L : Launch) (g : Nat) :
    Option Machine.ThreadD → List Event → Prop
  | some (.tma d), es => warpOf L g = 5 ∧
      (d.site ≠ .elect → ∃ e ∈ es, ∃ inst, e.kind = .elect 4294967295 inst (PTX.laneOf L g))
  | _, _ => True

private theorem followsLeader_step {g : Nat} {d d' : Option Machine.ThreadD} {es : List Event}
    {e : Event} {o : Option TState} (h : followsLeader L g d es)
    (hf : (Machine.machine P L g).Fired d e o) (hn : (Machine.machine P L g).next d e = some d') :
    followsLeader L g d' (es ++ [e]) := by
  cases d
  case none =>
    change some none = some d' at hn
    cases hn
    trivial
  case some d =>
    change Machine.next P L g d e = some d' at hn
    cases d
    case prologue s =>
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        trivial
      · split at hn
        · rename_i w _
          split_ifs at hn
          · fin_cases w <;> cases hn <;> trivial
          · cases hn
            trivial
        · cases hn
          trivial
      · cases hn
    case head =>
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn <;> try trivial
      exact ⟨by assumption, fun h => (h rfl).elim⟩
    case tma d =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i d' hs
        cases hn
        refine ⟨h.1, fun _ => ?_⟩
        by_cases hd : d.site = .elect
        · obtain ⟨mask, inst, he⟩ := chosen hd hs
          have hm := full_mask hd hf he
          exact ⟨e, by simp, inst, hm ▸ he⟩
        · obtain ⟨f, hmem, inst, he⟩ := h.2 hd
          exact ⟨f, List.mem_append_left _ hmem, inst, he⟩
      · split_ifs at hn <;> cases hn <;> trivial
      · split at hn
        · cases hn
          trivial
        · cases hn
    all_goals
      simp only [Machine.next] at hn
      repeat' split at hn
      all_goals cases hn
      all_goals trivial

/-- A TMA body state has a prior full-mask election on its own lane in warp 5. -/
theorem body_elected {mem0 : Mem0} {X : Execution} {g i : Nat} {d : Wg1Tma.D}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (hst : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d))) (hd : d.site ≠ .elect) :
    warpOf L g = 5 ∧ ∃ k < i, ∃ e inst, X.get (g, k) = some e ∧
      e.kind = .elect 4294967295 inst (PTX.laneOf L g) := by
  have hg : g < L.threads := by
    by_contra hn
    unfold Frame.stateAt at hst
    rw [hX.outside g (by omega), List.take_nil] at hst
    change some (some (Machine.ThreadD.prologue .shfl0)) = some (some (.tma d)) at hst
    cases hst
  have h := ((hs g hg).produces (hX.thr g hg)).prefix_induction (followsLeader L g)
    trivial (fun _ _ _ _ _ => followsLeader_step) i (some (.tma d)) hst
  obtain ⟨e, hmem, inst, he⟩ := h.2 hd
  obtain ⟨k, hk, hget⟩ := List.mem_take_iff_getElem.mp hmem
  have hevent : (X.tr g)[k]? = some e :=
    List.getElem?_eq_some_iff.mpr ⟨by omega, hget⟩
  exact ⟨h.1, k, by omega, e, inst, hevent, he⟩

private theorem thread_eq {mem0 : Mem0} (hpre : Pre P L mem0) {g : Nat} (hw : warpOf L g = 5) :
    g = ctaOf L g * L.block + 160 + PTX.laneOf L g := by
  simp only [warpOf, PTX.laneOf, tidOf_eq hpre, ctaOf, hpre.block] at hw ⊢
  omega

/-- One lane agrees with every real election of warp 5. Before any such election the choice
may be any of its lanes. -/
theorem cta_election_lane {mem0 : Mem0} {X : Execution} {cta : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) :
    ∃ lane : Fin 32, ∀ {g i tag inst leader : Nat},
      ctaOf L g = cta → warpOf L g = 5 → X.Elect (g, i) tag 4294967295 inst leader →
        leader = lane.val := by
  classical
  by_cases h : ∃ g i tag inst leader, ctaOf L g = cta ∧ warpOf L g = 5 ∧
    X.Elect (g, i) tag 4294967295 inst leader
  · obtain ⟨g, i, tag, inst, leader, hc, hw, he⟩ := h
    have hE := hX.elect.1 _ _ _ _ _ he
    refine ⟨⟨leader, hE.2.2.1⟩, ?_⟩
    intro g' i' tag' inst' leader' hc' hw' he'
    have hE' := hX.elect.1 _ _ _ _ _ he'
    have hSame : SameWarp L g' g := by
      refine ⟨⟨hE'.1, hE.1, hc'.trans hc.symm⟩, ?_⟩
      simpa [warpOf, tidOf_eq hpre, hpre.block] using hw'.trans hw.symm
    exact hX.elect.2.2 _ _ _ _ _ _ _ _ _ he' he hSame
  · exact ⟨0, fun hc hw he => (h ⟨_, _, _, _, _, hc, hw, he⟩).elim⟩

/-- All TMA body states in a CTA belong to one issuer, including its coordinate release and its
raw-ring issues and publication. -/
theorem cta_issuer {mem0 : Mem0} {X : Execution} {cta : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) :
    ∃ leader : Fin 32, ∀ g i (d : Wg1Tma.D), ctaOf L g = cta →
      Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)) →
      d.site ≠ .elect → g = cta * L.block + 160 + leader.val := by
  classical
  by_cases hb : ∃ (g i : Nat) (d : Wg1Tma.D), ctaOf L g = cta ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)) ∧ d.site ≠ .elect
  · obtain ⟨g, i, d, hc, hstate, hd⟩ := hb
    obtain ⟨hw, k, _, e, inst, he, hk⟩ := body_elected hX hs hstate hd
    have ha : X.Elect (g, k) e.pc 4294967295 inst (PTX.laneOf L g) := by
      change X.get (g, k) = some ⟨e.pc, .elect 4294967295 inst (PTX.laneOf L g)⟩
      rw [he, ← hk]
    have hlt : PTX.laneOf L g < 32 := (hX.elect.1 _ _ _ _ _ ha).2.1.1
    refine ⟨⟨PTX.laneOf L g, hlt⟩, ?_⟩
    intro g' i' d' hc' hst' hd'
    obtain ⟨hw', k', _, e', inst', he', hk'⟩ := body_elected hX hs hst' hd'
    have ha' : X.Elect (g', k') e'.pc 4294967295 inst' (PTX.laneOf L g') := by
      change X.get (g', k') = some ⟨e'.pc, .elect 4294967295 inst' (PTX.laneOf L g')⟩
      rw [he', ← hk']
    have hWarp : SameWarp L g g' := by
      refine ⟨⟨Frame.lt_of_get hX he, Frame.lt_of_get hX he', hc.trans hc'.symm⟩, ?_⟩
      simpa [warpOf, tidOf_eq hpre, hpre.block] using hw.trans hw'.symm
    have hsame := hX.elect.2.2 _ _ _ _ _ _ _ _ _ ha ha' hWarp
    rw [thread_eq hpre hw', hc', ← hsame]
  · exact ⟨0, fun g i d hc hst hd => (hb ⟨g, i, d, hc, hst, hd⟩).elim⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1TmaLeader
