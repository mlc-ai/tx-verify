-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.NcInputFootprint
public import Lemmas.Kernel.Frame
import Lemmas.Flow.Final

@[expose] public section

/-! # The combined MMA role always follows its actual events -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaTracking

open PTX PTX.Proof PTX.Flow Wg1Mma

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private def admissible (L : Launch) : Wg1Mma.Site → Prop
  | .head => False
  | .loadTopk => ptrIsNull L 80 = false
  | .loadExtra => ptrIsNull L 144 = false
  | _ => True

private theorem admissible_start (g : Nat) : admissible L (startSite P L g) := by
  unfold startSite
  repeat' split
  all_goals simp_all [admissible]

private theorem admissible_after_topk : admissible L (afterTopk L) := by
  unfold afterTopk
  split
  · trivial
  · have hnull : ptrIsNull L 144 ≠ true := by assumption
    exact Bool.eq_false_of_not_eq_true hnull

private def admissibleResult (L : Launch) : Option (Option D) → Prop
  | some (some d) => admissible L d.site
  | _ => True

set_option maxHeartbeats 1000000 in
private theorem role_result {g : Nat} (d : D) (e : Event) :
    admissibleResult L (Wg1Mma.next P L g d e) := by
  obtain ⟨site, i⟩ := d
  cases site <;> simp only [Wg1Mma.next]
  case elect =>
    split
    · split
      · exact admissible_start (P := P) (L := L) g
      · exact True.intro
    · exact True.intro
  case loadTopk =>
    split
    · rename_i a bs he
      cases rebuild 3 bs with
      | error => exact True.intro
      | ok v =>
        dsimp only
        by_cases hv : v = b32 (P.topkLen (eOf L g))
        · rw [ite_eq_left hv]
          exact admissible_after_topk (L := L)
        · rw [ite_eq_right hv]
          exact True.intro
    · exact True.intro
  case head =>
    split
    · rename_i m a b c recv ok he
      by_cases hv : recv = b32 (warpOf L g)
      · rw [ite_eq_left hv]
        exact True.intro
      · rw [ite_eq_right hv]
        exact True.intro
    · exact True.intro
  case loadExtra =>
    split
    · rename_i a bs he
      cases rebuild 3 bs with
      | error => exact True.intro
      | ok v =>
        dsimp only
        by_cases hv : v = b32 (P.extraTopkLen (eOf L g))
        · rw [ite_eq_left hv]
          exact True.intro
        · rw [ite_eq_right hv]
          exact True.intro
    · exact True.intro
  case qWait | qCopyWait | kvWait | soWait =>
    split
    · split <;> exact True.intro
    · exact True.intro
  case pvCommit => split <;> exact True.intro
  case qCopyFence =>
    by_cases hb : total P L g < 64 <;> simp only [admissibleResult, admissible, hb, ↓reduceIte]
  all_goals first
    | exact True.intro
    | (simp only [admissibleResult, nextSite]; split <;> exact True.intro)

private theorem admissible_role_next {g : Nat} {d d' : D} {e : Event}
    (hn : Wg1Mma.next P L g d e = some (some d')) : admissible L d'.site := by
  have hh := role_result (P := P) (L := L) (g := g) d e
  rw [hn] at hh
  exact hh

private theorem admissible_combined_next {g : Nat} {u : Machine.ThreadD} {d : D} {e : Event}
    (hn : Machine.next P L g u e = some (some (.mma d))) : admissible L d.site := by
  cases u
  case mma d0 =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i d' hs
      cases hn
      exact admissible_role_next hs
    · split at hn <;> cases hn
    · split at hn <;> cases hn
  case head =>
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals try contradiction
    all_goals rename_i heq
    all_goals
      cases hn
      all_goals unfold Machine.headStart at heq
      repeat' split at heq
      all_goals cases heq
      all_goals trivial
  all_goals
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals try cases hn
    all_goals rename_i wg hnext hgroup
    all_goals fin_cases wg <;> cases hn

private theorem admissible_at {g i : Nat} {d : D} (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d))) :
    admissible L d.site := by
  cases i with
  | zero =>
    rw [Frame.stateAt_zero] at hd
    cases hd
  | succ k =>
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := by
      change ∃ e, (X.tr g)[k]? = some e
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hn := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hd] at hn
    cases hst : Frame.stateAt (Machine.code P L) X g k with
    | none => rw [hst] at hn; cases hn
    | some o =>
      cases o with
      | none => rw [hst] at hn; cases hn
      | some u =>
        rw [hst] at hn
        exact admissible_combined_next hn.symm

private theorem topk_event {g : Nat} {d : D} {e : Event} {o : Option TState} {ptr : Nat}
    (hpre : Pre P L mem0) (hp : P.topkLenBase = some ptr) (hd : d.site = .loadTopk)
    (hf : (Machine.machine P L g).Fired (some (.mma d)) e o) :
    ∃ bs, LaunchReads.ReadsLaunchWord e (ptr + 4 * eOf L g) bs := by
  obtain ⟨t, ⟨hat, _⟩, hf⟩ := hf
  change (Wg1Mma.code P L g).AtD d t at hat
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  rw [hd, show Wg1Mma.Site.loadTopk.pc = 1876 from rfl, Flow.code_load_15] at hf
  have hat' : At t 1876 (Wg1Mma.factsAt P L g 1876 d) := by
    change At t d.site.pc (Wg1Mma.factsAt P L g d.site.pc d) at hat
    rw [hd] at hat
    exact hat
  change Fires t.pc (eventTmpl asms L g t (.mem ncLoadTopk)) e o at hf
  rw [event_loadTopk hpre hat'] at hf
  have hbatch : batchOf L g < P.b := batchOf_lt_of_pre hpre g
  have hspan := (hpre.topkLenAddressable ptr hp).2.2
  have hptr := hpre.topkLenBaseLt ptr hp
  have hadd : ptr + 4 * batchOf L g < 2 ^ 64 := by omega
  rw [show paramWord L 80 8 = ptr % 2 ^ 64 from Thread.paramWord_80_some hpre hp,
    Nat.mod_eq_of_lt hptr, Nat.mod_eq_of_lt hadd] at hf
  obtain ⟨bs, _, he, _⟩ := hf
  refine ⟨bs, congrArg Event.kind he, ?_⟩
  rw [he]
  change ncLoads.contains t.pc = true
  rw [hat'.1]
  decide +kernel

private theorem extra_event {g : Nat} {d : D} {e : Event} {o : Option TState} {ptr : Nat}
    (hpre : Pre P L mem0) (hp : P.extraTopkLenBase = some ptr) (hd : d.site = .loadExtra)
    (hf : (Machine.machine P L g).Fired (some (.mma d)) e o) :
    ∃ bs, LaunchReads.ReadsLaunchWord e (ptr + 4 * eOf L g) bs := by
  obtain ⟨t, ⟨hat, _⟩, hf⟩ := hf
  change (Wg1Mma.code P L g).AtD d t at hat
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  rw [hd, show Wg1Mma.Site.loadExtra.pc = 1886 from rfl, Flow.code_load_16] at hf
  have hat' : At t 1886 (Wg1Mma.factsAt P L g 1886 d) := by
    change At t d.site.pc (Wg1Mma.factsAt P L g d.site.pc d) at hat
    rw [hd] at hat
    exact hat
  change Fires t.pc (eventTmpl asms L g t (.mem ncLoadExtra)) e o at hf
  rw [event_loadExtra hpre hat'] at hf
  have hbatch : batchOf L g < P.b := batchOf_lt_of_pre hpre g
  have hspan := (hpre.extraTopkLenAddressable ptr hp).2.2
  have hptr := hpre.extraTopkLenBaseLt ptr hp
  have hadd : ptr + 4 * batchOf L g < 2 ^ 64 := by omega
  rw [show paramWord L 144 8 = ptr % 2 ^ 64 from Thread.paramWord_144_some hpre hp,
    Nat.mod_eq_of_lt hptr, Nat.mod_eq_of_lt hadd] at hf
  obtain ⟨bs, _, he, _⟩ := hf
  refine ⟨bs, congrArg Event.kind he, ?_⟩
  rw [he]
  change ncLoads.contains t.pc = true
  rw [hat'.1]
  decide +kernel

/-- Warp dispatch precedes entry to the MMA role. -/
theorem site_ne_head {g i : Nat} {d : D} (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d))) :
    d.site ≠ .head := by
  intro he
  have h := admissible_at hi hd
  rw [he] at h
  exact h

/-- The combined MMA role follows every event at a live role state. -/
theorem next_tracked (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    {g i : Nat} {d : D} {e : Event} (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d))) :
    Machine.next P L g (.mma d) e ≠ some none := by
  have ha := admissible_at (PTX.len_of_get he).le hd
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hf⟩ := (hs.produces (hX.thr g hg)).fired_at he hd
  cases hsite : d.site
  case head =>
    rw [hsite] at ha
    exact ha.elim
  case loadTopk =>
    have hnull : ptrIsNull L 80 = false := by simpa only [hsite, admissible] using ha
    cases hp : P.topkLenBase with
    | none => rw [ptrIsNull_80_none hpre hp] at hnull; cases hnull
    | some ptr =>
      obtain ⟨bs, hword⟩ := topk_event hpre hp hsite hf
      have hr := LaunchReads.rebuild_main (g := g) hpre hX (eOf_lt_b hpre) hp he hword
      have hvalue : Wg0.eOf L g = eOf L g := rfl
      simp [Machine.next, Wg1Mma.next, hsite, hword.1, hr, hvalue]
  case loadExtra =>
    have hnull : ptrIsNull L 144 = false := by simpa only [hsite, admissible] using ha
    cases hp : P.extraTopkLenBase with
    | none => rw [ptrIsNull_144_none hpre hp] at hnull; cases hnull
    | some ptr =>
      obtain ⟨bs, hword⟩ := extra_event hpre hp hsite hf
      have hr := LaunchReads.rebuild_extra (g := g) hpre hX (eOf_lt_b hpre) hp he hword
      have hvalue : Wg0.eOf L g = eOf L g := rfl
      simp [Machine.next, Wg1Mma.next, hsite, hword.1, hr, hvalue]
  all_goals
    intro h
    simp only [Machine.next, Wg1Mma.next, hsite] at h
    repeat' split at h
    all_goals cases h
    all_goals
      rename_i hk guard
      first | exact guard trivial | (split at hk; all_goals cases hk)

/-- An actual optional length read stays within its declared global input. -/
theorem length_footprint (hpre : Pre P L mem0) {g i : Nat} {d : D} {e : Event}
    {o : Option TState} (hLen : i < (X.tr g).length)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hSite : d.site = .loadTopk ∨ d.site = .loadExtra)
    (hFire : (Machine.machine P L g).Fired (some (.mma d)) e o) :
    NcInputEvent P e := by
  have ha := admissible_at hLen.le hState
  have hb := Wg1Mma.eOf_lt_b (g := g) hpre
  rcases hSite with hSite | hSite
  · have hNonNull : ptrIsNull L 80 = false := by simpa only [hSite, admissible] using ha
    cases hp : P.topkLenBase with
    | none => rw [ptrIsNull_80_none hpre hp] at hNonNull; cases hNonNull
    | some ptr =>
      obtain ⟨_, hr⟩ := topk_event hpre hp hSite hFire
      exact NcInputEvent.mainLength hp hb hr.1
  · have hNonNull : ptrIsNull L 144 = false := by simpa only [hSite, admissible] using ha
    cases hp : P.extraTopkLenBase with
    | none => rw [ptrIsNull_144_none hpre hp] at hNonNull; cases hNonNull
    | some ptr =>
      obtain ⟨_, hr⟩ := extra_event hpre hp hSite hFire
      exact NcInputEvent.extraLength hp hb hr.1

/-- Each returned election or optional length load continues through the checked MMA entry. -/
theorem entry_next (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    {g i : Nat} {d : D} {e : Event}
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hSite : d.site = .elect ∨ d.site = .loadTopk ∨ d.site = .loadExtra)
    (hReturns : ¬ Ends e) :
    ∃ u, Frame.stateAt (Machine.code P L) X g (i + 1) = some (some u) := by
  have ha := admissible_at (PTX.len_of_get he).le hd
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hf⟩ := ((hs g hg).machine.produces (hX.thr g hg)).fired_at he hd
  suffices ∃ u, Machine.next P L g (.mma d) e = some (some u) by
    obtain ⟨u, hu⟩ := this
    exact ⟨u, by rw [Frame.stateAt_succ he, hd]; exact hu⟩
  rcases hSite with hSite | hSite | hSite
  · obtain ⟨t, ins, o', hat, hinv, hcode, hfire⟩ := Frame.fired_site hs hX he hd
    cases o' with
    | none => exact (hReturns (fires_none_ends hfire)).elim
    | some u =>
      have hd' : d = ⟨.elect, d.i⟩ := by cases d; simp_all
      rw [hd'] at hat hinv hcode hfire ⊢
      obtain ⟨_, leader, hk, _⟩ := Wg1Mma.fires_elect hpre hat hinv hcode hfire
      by_cases hl : laneOf L g = leader
      · exact ⟨.mma ⟨startSite P L g, d.i⟩, by simp [Machine.next, Wg1Mma.next, hk, hl]⟩
      · exact ⟨.idle (Thread.startSite L g), by simp [Machine.next, Wg1Mma.next, hk, hl]⟩
  · have hNull : ptrIsNull L 80 = false := by simpa only [hSite, admissible] using ha
    cases hp : P.topkLenBase with
    | none => rw [ptrIsNull_80_none hpre hp] at hNull; cases hNull
    | some ptr =>
      obtain ⟨bs, hword⟩ := topk_event hpre hp hSite hf
      have hr := LaunchReads.rebuild_main (g := g) hpre hX (eOf_lt_b hpre) hp he hword
      have hvalue : Wg0.eOf L g = eOf L g := rfl
      exact ⟨.mma ⟨afterTopk L, d.i⟩, by
        simp [Machine.next, Wg1Mma.next, hSite, hword.1, hr, hvalue]⟩
  · have hNull : ptrIsNull L 144 = false := by simpa only [hSite, admissible] using ha
    cases hp : P.extraTopkLenBase with
    | none => rw [ptrIsNull_144_none hpre hp] at hNull; cases hNull
    | some ptr =>
      obtain ⟨bs, hword⟩ := extra_event hpre hp hSite hf
      have hr := LaunchReads.rebuild_extra (g := g) hpre hX (eOf_lt_b hpre) hp he hword
      have hvalue : Wg0.eOf L g = eOf L g := rfl
      exact ⟨.mma ⟨.qLoad 0, d.i⟩, by simp [Machine.next, Wg1Mma.next, hSite, hword.1, hr, hvalue]⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaTracking
