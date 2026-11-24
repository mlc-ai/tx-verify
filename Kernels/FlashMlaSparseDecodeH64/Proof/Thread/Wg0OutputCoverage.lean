-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputVisits
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierCount
public import Lemmas.Protocol.NamedBarSources

@[expose] public section

/-! # The elected output issuers of a complete execution -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0OutputCoverage

open PTX PTX.Flow Wg0

private theorem before_done {P : Params} {L : Launch} {X : Execution} {g k i : Nat} {d : D}
    (hn : k ≤ i) (hdone : Frame.stateAt (Machine.code P L) X g i = some (some .done))
    (hk : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d))) : k < i := by
  by_contra hlt
  obtain rfl : k = i := by omega
  rw [hdone] at hk
  cases hk

variable {P : Params} {L : Launch}

private theorem next_not_none {X : Execution} {g k i : Nat} {d : D} {e : Event} (hk : k < i)
    (hdone : Frame.stateAt (Machine.code P L) X g i = some (some .done))
    (he : X.get (g, k) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d))) :
    Machine.next P L g (.wg0 d) e ≠ none := by
  intro hn
  have hst' : Frame.stateAt (Machine.code P L) X g (k + 1) = none := by
    rw [Frame.stateAt_succ he, hst]
    exact hn
  rw [Frame.stateAt_none_mono hst' (by omega)] at hdone
  cases hdone

private theorem electionContinues {g : Nat} {d : D} {e : Event} {o : Option TState}
    {mask inst leader : Nat} (hf : (Wg0.code P L g).toMachine.Fired (some d) e o)
    (hk : e.kind = .elect mask inst leader) : ∃ u, o = some u := by
  obtain ⟨t, _, hf⟩ := hf
  generalize (Wg0.code P L g).toMachine.tmpl (some d) t = tm at hf
  cases tm <;> simp only [Fires] at hf <;> aesop

private theorem laneHasElection {mem0 : Mem0} {X : Execution} {g : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hcomplete : Complete L X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hg : g < L.threads) (hwg : wgOf L g = 0) (hw : warpOf L g < 2) (j : Fin 4) :
    ∃ (k site inst leader : Nat), X.Elect (g, k) site (2 ^ 32 - 1) inst leader ∧
      (leader = PTX.laneOf L g →
        ∃ (i : Nat) (d : D) (a : Nat) (sp : TensorStore.Spec),
          X.TensorStoreIssue (g, i) a sp ∧
          Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) ∧
          d.site = .tmaStore j) := by
  obtain ⟨ex, _, hex, _, hend⟩ := Wg0OutputVisits.completeDone hX hcomplete hs ht hg hwg
  have hlen : ex < (X.tr g).length := (List.getElem?_eq_some_iff.mp hex).1
  obtain ⟨b, hb, d, e, hst, hd, he, hk⟩ :=
    Wg0OutputVisits.barrierBeforeDone hpre hX hg (hs g hg) hwg hend j
  let de : D := {d with site := .elect j}
  have helect : Frame.stateAt (Machine.code P L) X g (b + 1) = some (some (.wg0 de)) := by
    rw [Frame.stateAt_succ he, hst]
    change Machine.next P L g (.wg0 d) e = some (some (.wg0 de))
    simp [Machine.next, Wg0.next, Wg0.nextSite, hd, hk, epiAfterBar, de,
      show ¬ 2 ≤ warpOf L g by omega]
  have hbe := before_done (by omega : b + 1 ≤ ex) hend helect
  have hbel : b + 1 < (X.tr g).length := by omega
  let f := (X.tr g)[b + 1]
  have hget : X.get (g, b + 1) = some f := List.getElem?_eq_getElem hbel
  have hn := next_not_none hbe hend hget helect
  have hkind : ∃ mask inst leader, f.kind = .elect mask inst leader := by
    cases h : f.kind <;>
      simp only [Machine.next, Wg0.next, Wg0.nextSite, de, h, ne_eq, not_true_eq_false] at hn
    exact ⟨_, _, _, rfl⟩
  obtain ⟨mask, unit, ld, hkind⟩ := hkind
  have htrace := (hs g hg).produces (hX.thr g hg)
  obtain ⟨o, hf⟩ := htrace.fired_at hget helect
  have hf0 : (Wg0.code P L g).toMachine.Fired (some de) f o := hf
  obtain ⟨u, rfl⟩ := electionContinues hf0 hkind
  obtain ⟨inst, leader, hkind'⟩ := fired_outputElection (show de.site = .elect j from rfl) hf0
  have hevent : X.Elect (g, b + 1) f.pc (2 ^ 32 - 1) inst leader := by
    change X.get (g, b + 1) = some ⟨f.pc, .elect (2 ^ 32 - 1) inst leader⟩
    rw [hget, ← hkind']
  refine ⟨b + 1, f.pc, inst, leader, hevent, ?_⟩
  intro hleader
  have hlane : leader = laneOf L g := hleader.trans (laneOf_core hpre)
  let ds : D := {de with site := .tmaStore j}
  have hit : Frame.stateAt (Machine.code P L) X g (b + 1 + 1) = some (some (.wg0 ds)) := by
    rw [Frame.stateAt_succ hget, helect]
    change Machine.next P L g (.wg0 de) f = some (some (.wg0 ds))
    simp [Machine.next, Wg0.next, Wg0.nextSite, de, ds, hkind', hlane]
  have hbt := before_done (by omega : b + 1 + 1 ≤ ex) hend hit
  have hbtl : b + 1 + 1 < (X.tr g).length := by omega
  let event := (X.tr g)[b + 1 + 1]
  have hget' : X.get (g, b + 1 + 1) = some event := List.getElem?_eq_getElem hbtl
  have hn := next_not_none hbt hend hget' hit
  have hik : ∃ a sp, event.kind = .tensorStore a sp := by
    cases h : event.kind <;>
      simp only [Machine.next, Wg0.next, Wg0.nextSite, ds, h, ne_eq, not_true_eq_false] at hn
    exact ⟨_, _, rfl⟩
  obtain ⟨a, sp, hik⟩ := hik
  refine ⟨b + 1 + 1, ds, a, sp, ⟨event.pc, ?_⟩, hit, rfl⟩
  rw [← hik]
  exact hget'

private theorem laneGeometry {mem0 : Mem0} {cta : Nat} (hpre : Pre P L mem0) (hcta : cta < L.grid)
    (w : Fin 2) (l : Fin 32) :
    let g := cta * L.block + 32 * w.val + l.val
    g < L.threads ∧ ctaOf L g = cta ∧ wgOf L g = 0 ∧
      warpOf L g = w.val ∧ PTX.laneOf L g = l.val := by
  let g := cta * L.block + 32 * w.val + l.val
  have hw := w.isLt
  have hl := l.isLt
  have ht : tidOf L g = 32 * w.val + l.val := by
    rw [tidOf_eq hpre]
    unfold g
    rw [hpre.block]
    omega
  have hc : ctaOf L g = cta := by
    unfold ctaOf g
    rw [hpre.block]
    omega
  have hlaunch : g < L.threads := by
    unfold g
    rw [Nat.add_assoc]
    exact NamedBar.cta_thread_lt hcta (by rw [hpre.block]; omega)
  refine ⟨hlaunch, hc, ?_, ?_, ?_⟩
  · unfold wgOf
    rw [ht]
    omega
  · unfold warpOf
    rw [ht]
    omega
  · unfold PTX.laneOf
    rw [hpre.block]
    omega

/-- Every output warp issues every tile of its CTA in a complete execution. -/
theorem tileOfWarp {mem0 : Mem0} {X : Execution} {cta : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hcomplete : Complete L X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hcta : cta < L.grid) (j : Fin 4) (w : Fin 2) :
    ∃ (g i : Nat) (d : D) (a : Nat) (sp : TensorStore.Spec),
      ctaOf L g = cta ∧ warpOf L g = w.val ∧ X.TensorStoreIssue (g, i) a sp ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) ∧ d.site = .tmaStore j := by
  let g0 := cta * L.block + 32 * w.val + (0 : Fin 32).val
  obtain ⟨hg0, hc0, hgw0, hw0, _⟩ := laneGeometry hpre hcta w 0
  have hw0' : warpOf L g0 < 2 := by rw [hw0]; exact w.isLt
  obtain ⟨k0, s0, inst0, leader0, he0, _⟩ :=
    laneHasElection hpre hX hcomplete hs ht hg0 hgw0 hw0' j
  have hl := (hX.elect.1 _ _ _ _ _ he0).2.2.1
  let lead : Fin 32 := ⟨leader0, hl⟩
  let g := cta * L.block + 32 * w.val + lead.val
  obtain ⟨hg, hc, hgw, hw, hlane⟩ := laneGeometry hpre hcta w lead
  have hw' : warpOf L g < 2 := by rw [hw]; exact w.isLt
  obtain ⟨k, s, inst, leader, he, htake⟩ :=
    laneHasElection hpre hX hcomplete hs ht hg hgw hw' j
  have hsame : SameWarp L g0 g := by
    refine ⟨⟨hg0, hg, hc0.trans hc.symm⟩, ?_⟩
    simpa only [warpOf, tidOf_eq hpre, hpre.block, g0, g] using hw0.trans hw.symm
  have heq := hX.elect.2.2 _ _ _ _ _ _ _ _ _ he0 he hsame
  obtain ⟨i, d, a, sp, hi, hst, hd⟩ := htake (heq.symm.trans hlane.symm)
  exact ⟨g, i, d, a, sp, hc, hw, hi, hst, hd⟩

private theorem issueElection {mem0 : Mem0} {X : Execution} {g i : Nat} {d : D} {j : Fin 4}
    {e : Event} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hj : d.site = .tmaStore j) :
    ∃ k site inst, X.Elect (g, k) site (2 ^ 32 - 1) inst (PTX.laneOf L g) := by
  have hg := Frame.lt_of_get hX he
  have hi : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hw := Wg0OutputControl.outputWarp hX hs he hst hj
  obtain ⟨b, bar, db, hb, hget, hbkind, hbstate, hbsite⟩ :=
    Wg0OutputControl.barrierBeforeIssue hpre hX hs hi hst hj
  let de : D := {db with site := .elect j}
  have hestate : Frame.stateAt (Machine.code P L) X g (b + 1) = some (some (.wg0 de)) := by
    rw [Frame.stateAt_succ hget, hbstate]
    change Machine.next P L g (.wg0 db) bar = some (some (.wg0 de))
    simp [Machine.next, Wg0.next, Wg0.nextSite, hbsite, hbkind, epiAfterBar, de,
      show ¬ 2 ≤ warpOf L g by omega]
  have hbel : b + 1 < (X.tr g).length := by omega
  let el := (X.tr g)[b + 1]
  have heget : X.get (g, b + 1) = some el := List.getElem?_eq_getElem hbel
  have hn := hst
  have hbi : b + 1 + 1 = i := by omega
  rw [← hbi, Frame.stateAt_succ heget, hestate] at hn
  change Machine.next P L g (.wg0 de) el = some (some (.wg0 d)) at hn
  have hk : ∃ mask inst, el.kind = .elect mask inst (laneOf L g) := by
    cases h : el.kind <;>
      simp only [Machine.next, Wg0.next, Wg0.nextSite, de, h, reduceCtorEq] at hn
    rename_i mask inst leader
    by_cases hl : leader = laneOf L g
    · exact ⟨mask, inst, by rw [hl]⟩
    · simp only [hl, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq,
          Machine.ThreadD.wg0.injEq] at hn
      have hs' := congrArg Wg0.D.site hn
      simp only at hs'
      split_ifs at hs' <;> rw [hj] at hs' <;> cases hs'
  obtain ⟨mask, inst, hk⟩ := hk
  obtain ⟨o, hf⟩ := (hs.produces (hX.thr g hg)).fired_at heget hestate
  have hf0 : (Wg0.code P L g).toMachine.Fired (some de) el o := hf
  obtain ⟨u, rfl⟩ := electionContinues hf0 hk
  obtain ⟨inst', leader, hkind⟩ := fired_outputElection (show de.site = .elect j from rfl) hf0
  have hl := (Kind.elect.inj (hkind.symm.trans hk)).2.2
  refine ⟨b + 1, el.pc, inst', ?_⟩
  change X.get (g, b + 1) = some ⟨el.pc, .elect (2 ^ 32 - 1) inst' (PTX.laneOf L g)⟩
  rw [laneOf_core hpre, ← hl, heget, ← hkind]

private theorem is_barrier {X : Execution} {g i : Nat} {e : Event}
    (he : X.get (g, i) = some e) (hk : e.kind = .bar 9 (some 128) .sync) :
    ∃ site, X.IsBarrier (g, i) 9 (some 128) site := by
  obtain ⟨site, _⟩ := e
  cases hk
  exact ⟨site, he⟩

/-- A CTA has at most one output issue for a given tile and output warp. -/
theorem tileUnique {mem0 : Mem0} {X : Execution} {g h i k : Nat} {d d' : D} {j : Fin 4}
    {e f : Event} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hf : X.get (h, k) = some f) (hc : ctaOf L g = ctaOf L h) (hw : warpOf L g = warpOf L h)
    (hst : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hst' : Frame.stateAt (Machine.code P L) X h k = some (some (.wg0 d')))
    (hj : d.site = .tmaStore j) (hj' : d'.site = .tmaStore j) : (g, i) = (h, k) := by
  have hg := Frame.lt_of_get hX he
  have hh := Frame.lt_of_get hX hf
  obtain ⟨el, site, inst, hel⟩ := issueElection hpre hX (hs g hg) he hst hj
  obtain ⟨el', site', inst', hel'⟩ := issueElection hpre hX (hs h hh) hf hst' hj'
  have hWarp : SameWarp L g h := by
    refine ⟨⟨hg, hh, hc⟩, ?_⟩
    simpa only [warpOf, tidOf_eq hpre, hpre.block] using hw
  have hlane := hX.elect.2.2 (g, el) (h, el') site site' (2 ^ 32 - 1) inst inst'
    (PTX.laneOf L g) (PTX.laneOf L h) hel hel' hWarp
  have hthread : g = h := by
    simp only [ctaOf, warpOf, PTX.laneOf, tidOf_eq hpre, hpre.block] at hc hw hlane
    omega
  subst h
  have hi : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hf).1
  obtain ⟨b, bar, db, hb, hget, hkind, hstate, hsite⟩ :=
    Wg0OutputControl.barrierBeforeIssue hpre hX (hs g hg) hi hst hj
  obtain ⟨b', bar', db', hb', hget', hkind', hstate', hsite'⟩ :=
    Wg0OutputControl.barrierBeforeIssue hpre hX (hs g hg) hk hst' hj'
  obtain ⟨_, hbar⟩ := is_barrier hget hkind
  obtain ⟨_, hbar'⟩ := is_barrier hget' hkind'
  have ho := Wg0BarrierCount.epiOrdinal hpre hX (hs g hg) hget hstate hsite
  have ho' := Wg0BarrierCount.epiOrdinal hpre hX (hs g hg) hget' hstate' hsite'
  have hbEq := NamedBar.source_ordinal_unique hbar hbar' (ho.trans ho'.symm)
  congr 1
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0OutputCoverage
