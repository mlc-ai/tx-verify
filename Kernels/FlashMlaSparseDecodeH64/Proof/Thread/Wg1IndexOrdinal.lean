-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueShuffleTrace
public import Lemmas.Flow.TraceInduction
import Lemmas.Flow.NotShfl

@[expose] public section

/-! # The shuffle ordinal along a followed index path -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1Index

open PTX PTX.Flow PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- The two prologue broadcasts and role dispatch precede the two butterflies in each block. -/
def shuffleCount (d : D) : Nat :=
  3 + 2 * d.block + match d.site with
    | .quad2 _ => 1
    | .coord .. | .valid _ | .ready _ | .barrier => 2
    | _ => 0

private theorem ready_count {d : D} {extra : Bool} (hs : d.site = .ready extra) :
    shuffleCount (afterReady d) = shuffleCount d := by
  unfold afterReady
  dsimp only
  repeat' split_ifs <;> simp [shuffleCount, hs] <;> omega

/-- Each tracked transition advances the shuffle count exactly at a butterfly. -/
theorem shuffleCount_next {g : Nat} {d d' : D} {e : Event}
    (hn : next P L g d e = some (some d')) :
    shuffleCount d' = shuffleCount d + (if Execution.isShfl e then 1 else 0) := by
  obtain ⟨pc, kind⟩ := e
  cases hsite : d.site <;> simp only [next, nextSite, hsite] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals try (rw [ready_count hsite]; simp_all [Execution.isShfl])
  all_goals
    simp only [shuffleCount, hsite, afterPairFirst]
    repeat' split_ifs
    all_goals simp_all [Execution.isShfl]

/-- The count at the first abstract index state is the three dispatch broadcasts. -/
theorem shuffleCount_init {g : Nat} : shuffleCount (init P L g) = 3 := by
  unfold init firstSite shuffleCount
  split_ifs <;> rfl

private def indexPrefix (pre : List Event) :
    Option Machine.ThreadD → Prop
  | some (.index d) => pre.countP Execution.isShfl = shuffleCount d
  | some .done | none => True
  | _ => False

private theorem indexPrefix_next {g : Nat} {q q' : Option Machine.ThreadD} {pre : List Event}
    {e : Event} (h : indexPrefix pre q)
    (hn : (Machine.machine P L g).next q e = some q') :
    indexPrefix (pre ++ [e]) q' := by
  cases q
  case none =>
    change some none = some q' at hn
    cases hn
    trivial
  case some q =>
    change Machine.next P L g q e = some q' at hn
    cases q <;> try exact h.elim
    case index d =>
      change pre.countP Execution.isShfl = shuffleCount d at h
      simp only [Machine.next] at hn
      split at hn
      · rename_i d' hnext
        cases hn
        change (pre ++ [e]).countP Execution.isShfl = shuffleCount d'
        rw [List.countP_append, h, shuffleCount_next hnext]
        simp
      · split_ifs at hn <;> cases hn <;> trivial
      · cases hn
    case done => cases hn

private def indexFrame (pre : List Event) : Option (Option Machine.ThreadD) → Prop
  | none => True
  | some s => indexPrefix pre s

variable {X : Execution}

private theorem indexFrame_at {g start : Nat}
    (hstart : Frame.stateAt (Machine.code P L) X g start = some (some (.index (init P L g))))
    (hcount : ((X.tr g).take start).countP Execution.isShfl = 3) :
    ∀ n, start + n ≤ (X.tr g).length →
      indexFrame ((X.tr g).take (start + n))
        (Frame.stateAt (Machine.code P L) X g (start + n)) := by
  intro n
  induction n with
  | zero =>
    intro _
    simp only [Nat.add_zero, hstart, indexFrame, indexPrefix, shuffleCount_init]
    exact hcount
  | succ n ih =>
    intro hlen
    have hlt : start + n < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[start + n]? = some e :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    simp only [Nat.add_succ, List.take_add_one, he, Option.toList_some, Frame.stateAt_succ he]
    have hlast := ih hlt.le
    cases hs : Frame.stateAt (Machine.code P L) X g (start + n) with
    | none => trivial
    | some s =>
      cases hn : (Machine.machine P L g).next s e with
      | none =>
        change indexFrame _ ((Machine.machine P L g).next s e)
        rw [hn]
        trivial
      | some s' =>
        change indexFrame _ ((Machine.machine P L g).next s e)
        rw [hn]
        rw [hs] at hlast
        exact indexPrefix_next hlast hn

/-- Counts the actual shuffle events preceding a followed index stage, from the dispatch prefix. -/
theorem shuffleCount_at {g k j : Nat} {d : D}
    (hstart : Frame.stateAt (Machine.code P L) X g k = some (some (.index (init P L g))))
    (hcount : ((X.tr g).take k).countP Execution.isShfl = 3) (hkj : k ≤ j)
    (hj : j ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.index d))) :
    ((X.tr g).take j).countP Execution.isShfl = shuffleCount d := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hkj
  have h := indexFrame_at hstart hcount n hj
  rw [hd] at h
  exact h

private theorem count_succ {g k : Nat} {e : Event} (he : X.get (g, k) = some e) :
    ((X.tr g).take (k + 1)).countP Execution.isShfl =
      ((X.tr g).take k).countP Execution.isShfl + if Execution.isShfl e then 1 else 0 := by
  rw [List.take_add_one, show (X.tr g)[k]? = some e from he, Option.toList_some, List.countP_append]
  simp

set_option maxRecDepth 10000 in
/-- The actual warp-7 prefix reaches the first index load after its third broadcast. -/
theorem shuffle_dispatch_prefix {g : Nat} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hw : warpOf L g = 7) (he : X.get (g, 4) = some e) :
    Frame.stateAt (Machine.code P L) X g 5 = some (some (.index (init P L g))) ∧
      ((X.tr g).take 5).countP Execution.isShfl = 3 := by
  have hgroup : wgOf L g = 1 := by unfold wgOf warpOf at *; omega
  have hg := Frame.lt_of_get hX he
  have hlen : 4 < (X.tr g).length := PTX.len_of_get he
  have hb (i : Nat) (hi : i < 4) : ∃ e, X.get (g, i) = some e := by
    exact ⟨_, List.getElem?_eq_getElem (by omega : i < (X.tr g).length)⟩
  obtain ⟨e0, h0⟩ := hb 0 (by decide)
  obtain ⟨e1, h1⟩ := hb 1 (by decide)
  obtain ⟨e2, h2⟩ := hb 2 (by decide)
  obtain ⟨e3, h3⟩ := hb 3 (by decide)
  have h2n : Execution.isShfl e2 = false := by
    have hr := PrologueShuffleTrace.state_two hpre hX hs h1
    simp only [hw, Nat.reduceEqDiff, ↓reduceIte] at hr
    obtain ⟨o, t, ⟨ha, _⟩, hf⟩ := RingEvents.fired_of_trace hX (hs g hg) h2 hr
    have hpc : t.pc = 97 := ha.1
    change Fires t.pc (match kernel.code[97]? with
      | some ins => eventTmpl asms L g t ins.op
      | none => .ub .pcOutOfRange) e2 o at hf
    rw [hpc, Flow.code_bar_0] at hf
    have he' : e2 = ⟨97, .bar 0 none .sync⟩ := hf.1
    rw [he']
    rfl
  have h3n : Execution.isShfl e3 = false := by
    have hr := PrologueShuffleTrace.state_three hpre hX hs h2 hgroup
    obtain ⟨o, t, ⟨ha, _⟩, hf⟩ := RingEvents.fired_of_trace hX (hs g hg) h3 hr
    have hpc : t.pc = 1842 := ha.1
    change Fires t.pc (match kernel.code[1842]? with
      | some ins => eventTmpl asms L g t ins.op
      | none => .ub .pcOutOfRange) e3 o at hf
    rw [hpc, Flow.code_setMaxReg_1] at hf
    have hf' : ∃ inst, e3 = ⟨1842, .setMaxReg false 72 inst⟩ ∧
        o = some (PTX.next t) := hf
    obtain ⟨_, rfl, _⟩ := hf'
    rfl
  constructor
  · have h := PrologueShuffleTrace.state_five hpre hX hs he hgroup
    rw [Machine.headStart, hw] at h
    exact h
  · rw [show (5 : Nat) = 4 + 1 by decide, count_succ he,
      show (4 : Nat) = 3 + 1 by decide, count_succ h3,
      show (3 : Nat) = 2 + 1 by decide, count_succ h2,
      show (2 : Nat) = 1 + 1 by decide, count_succ h1,
      show (1 : Nat) = 0 + 1 by decide, count_succ h0]
    rw [PrologueShuffleTrace.first_event hpre hX hs h0,
      PrologueShuffleTrace.second_event hpre hX hs h1,
      PrologueShuffleTrace.head_event hpre hX hs he hgroup, h2n, h3n]
    rfl

private def butterflySite : Site → Bool
  | .quad1 _ | .quad2 _ => true
  | _ => false

private theorem butterfly_opcode (s : Site) :
    (kernel.code[s.pc]?).any (·.op.isShfl) = butterflySite s := by
  cases s with
  | lenOrig | lenExtra | barrier => decide +kernel
  | pair extra first hi => cases extra <;> cases first <;> cases hi <;> decide +kernel
  | coord extra hi => cases extra <;> cases hi <;> decide +kernel
  | quad1 extra | quad2 extra | valid extra | ready extra | waitFree extra =>
    cases extra <;> decide +kernel

private theorem fired_butterfly_site {g : Nat} {d : D} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some (.index d)) e o)
    (hk : Execution.isShfl e = true) :
    butterflySite d.site = true := by
  obtain ⟨t, ⟨ha, _⟩, hf⟩ := hf
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl asms L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  have h := butterfly_opcode d.site
  cases hc : kernel.code[d.site.pc]? with
  | none =>
    rw [hc] at hf
    have he := congrArg Event.kind hf.1
    obtain ⟨tag, kind⟩ := e
    change kind = _ at he
    subst kind
    cases hk
  | some ins =>
    rw [hc] at hf h
    exact h.symm.trans (fires_shfl_op hf hk)

/-- An actual followed index shuffle has ordinal `3+2*b` or `4+2*b`, according to its stage. -/
theorem trace_shuffle_ordinal {g i : Nat} {d : D} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hw : warpOf L g = 7) (hi : 5 ≤ i) (he : X.get (g, i) = some e) (hk : Execution.isShfl e = true)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.index d))) :
    (∃ extra, d.site = .quad1 extra ∧ X.ShflK (g, i) (3 + 2 * d.block)) ∨
      ∃ extra, d.site = .quad2 extra ∧ X.ShflK (g, i) (4 + 2 * d.block) := by
  have hlen : i < (X.tr g).length := PTX.len_of_get he
  obtain ⟨first, hfirst⟩ : ∃ e, X.get (g, 4) = some e :=
    ⟨_, List.getElem?_eq_getElem (by omega : (4 : Nat) < (X.tr g).length)⟩
  obtain ⟨hstart, hn⟩ := shuffle_dispatch_prefix hpre hX hs hw hfirst
  have hcount := shuffleCount_at hstart hn hi hlen.le hd
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hf⟩ := RingEvents.fired_of_trace hX (hs g hg) he hd
  have hsite := fired_butterfly_site hf hk
  have hordinal : X.ShflK (g, i) (shuffleCount d) := by
    exact ⟨by
      obtain ⟨tag, kind⟩ := e
      cases kind <;> try cases hk
      exact ⟨_, _, _, _, _, _, _, he⟩, hcount⟩
  cases h : d.site <;> simp only [h, butterflySite] at hsite
  all_goals try cases hsite
  case quad1 extra =>
    exact .inl ⟨extra, rfl, by simpa [shuffleCount, h] using hordinal⟩
  case quad2 extra =>
    have hsum : shuffleCount d = 4 + 2 * d.block := by simp [shuffleCount, h]; omega
    exact .inr ⟨extra, rfl, hsum ▸ hordinal⟩

/-- Equal block numbers in the same warp use the same cache. -/
theorem same_cache_of_block {g h : Nat} {d d' : D} {extra extra' : Bool}
    (hw : SameWarp L g h) (hi : Inv P L g d) (hi' : Inv P L h d')
    (hx : d.site.extra = some extra) (hx' : d'.site.extra = some extra')
    (hb : d.block = d'.block) : extra = extra' := by
  have hcta : ctaOf L g = ctaOf L h := hw.1.2.2
  have hm : d.len0 = d'.len0 := by rw [hi.len0, hi'.len0, eOf, eOf, ctaidY, ctaidY, hcta]
  cases extra <;> cases extra' <;> try rfl
  · exact (Nat.not_lt_of_ge (hi'.tagExtra hx') (by rw [← hb, ← hm]; exact hi.tagMain hx)).elim
  · exact (Nat.not_lt_of_ge (hi.tagExtra hx) (by rw [hb, hm]; exact hi'.tagMain hx')).elim

/-- Two followed index shuffles with the same warp ordinal act on the same block and stage. -/
theorem same_index_shuffle_stage {g h i j n : Nat} {d d' : D} {e e' : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (hs : ∀ k < L.threads, (Machine.machine P L k).Sound)
    (hw : SameWarp L g h) (hwg : warpOf L g = 7) (hwh : warpOf L h = 7) (hi : 5 ≤ i) (hj : 5 ≤ j)
    (he : X.get (g, i) = some e) (he' : X.get (h, j) = some e') (hn : X.ShflK (g, i) n)
    (hn' : X.ShflK (h, j) n) (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (hd' : Frame.stateAt (Machine.code P L) X h j = some (some (.index d'))) :
    d'.site = d.site ∧ d'.block = d.block := by
  have hk : Execution.isShfl e = true := by
    obtain ⟨_, _, _, _, _, _, _, hg⟩ := hn.1
    rw [he] at hg
    cases hg
    rfl
  have hk' : Execution.isShfl e' = true := by
    obtain ⟨_, _, _, _, _, _, _, hh⟩ := hn'.1
    rw [he'] at hh
    cases hh
    rfl
  obtain ⟨o, hf⟩ := RingEvents.fired_of_trace hX (hs _ hw.1.1) he hd
  obtain ⟨o', hf'⟩ := RingEvents.fired_of_trace hX (hs _ hw.1.2.1) he' hd'
  have hinv : Inv P L g d := hf.choose_spec.1.2
  have hinv' : Inv P L h d' := hf'.choose_spec.1.2
  rcases trace_shuffle_ordinal hpre hX hs hwg hi he hk hd with
    ⟨extra, hsite, hc⟩ | ⟨extra, hsite, hc⟩
  all_goals
    rcases trace_shuffle_ordinal hpre hX hs hwh hj he' hk' hd' with
      ⟨extra', hsite', hc'⟩ | ⟨extra', hsite', hc'⟩
    all_goals
      have hcount := (hc.2.symm.trans hn.2).trans (hn'.2.symm.trans hc'.2)
      first
      | omega
      | have hb : d.block = d'.block := by omega
        have htag := same_cache_of_block hw hinv hinv' (by rw [hsite]; rfl) (by rw [hsite']; rfl) hb
        exact ⟨by rw [hsite, hsite', htag], hb.symm⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1Index
