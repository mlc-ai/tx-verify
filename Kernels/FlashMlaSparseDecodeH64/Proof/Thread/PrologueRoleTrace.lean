-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueShuffleTrace

@[expose] public section

/-! # The predecessors of the prologue's role entries -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PrologueRoleTrace

open PTX PTX.Flow PTX.Proof Machine

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private def pastBroadcast : Option (Option ThreadD) → Prop
  | some (some (.prologue _)) | some (some .head) => False
  | _ => True

private theorem after_role {g : Nat} (d : ThreadD) (e : Event)
    (h : ∀ s, d ≠ .prologue s) : pastBroadcast (Machine.next P L g d e) := by
  cases d
  case prologue s => exact (h s rfl).elim
  all_goals simp only [Machine.next]
  all_goals repeat' split
  all_goals try trivial
  all_goals rename_i heq
  all_goals
    simp only [headStart] at heq
    repeat' split at heq
    all_goals cases heq
    all_goals exact True.intro

private theorem transition_to_prologue {g : Nat} {d : ThreadD} {target : Site} {e : Event}
    (hn : Machine.next P L g d e = some (some (.prologue target))) :
    ∃ source, d = .prologue source ∧
      PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next L g source e = some (some target) := by
  by_cases hd : ∃ s, d = .prologue s
  swap
  · have := after_role (P := P) (L := L) (g := g) d e (fun s he => hd ⟨s, he⟩)
    rw [hn] at this
    exact this.elim
  obtain ⟨s, rfl⟩ := hd
  cases hp : PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next L g s e with
  | none => simp [Machine.next, hp] at hn
  | some o =>
    cases o with
    | none =>
      cases s <;> simp only [Machine.next, hp, Option.some.injEq, reduceCtorEq] at hn
      rename_i u
      split at hn
      · fin_cases u <;> cases hn
      · cases hn
    | some q =>
      simp only [Machine.next, hp, Option.some.injEq, ThreadD.prologue.injEq] at hn
      subst q
      exact ⟨s, rfl, hp⟩

private theorem transition_to_handoff (hpre : Pre P L mem0)
    {g : Nat} {d : ThreadD} {wg : Fin 3} {e : Event}
    (hn : Machine.next P L g d e = some (some (.prologue (.handoff wg)))) :
    d = .prologue .barrier ∧ wgOf L g = wg.val := by
  obtain ⟨s, rfl, hp⟩ := transition_to_prologue hn
  cases s
  case barrier =>
    simp only [PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next, Option.some.injEq] at hp
    split at hp
    · rename_i hw
      injection hp with he
      subst wg
      exact ⟨rfl, hw⟩
    split at hp
    · rename_i hw
      injection hp with he
      subst wg
      exact ⟨rfl, hw⟩
    rename_i h1 h0
    injection hp with he
    subst wg
    refine ⟨rfl, ?_⟩
    have hpreBlock : wgOf L g < 3 := by
      simp only [wgOf, tidOf_eq hpre]
      omega
    change wgOf L g = 2
    omega
  all_goals
    simp only [PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next] at hp
    repeat' split at hp
    all_goals cases hp

private theorem transition_to_head {g : Nat} {d : ThreadD} {e : Event}
    (hn : Machine.next P L g d e = some (some .head)) :
    d = .prologue (.handoff 1) ∧ wgOf L g = 1 := by
  by_cases hd : ∃ s, d = .prologue s
  swap
  · have := after_role (P := P) (L := L) (g := g) d e (fun s he => hd ⟨s, he⟩)
    rw [hn] at this
    exact this.elim
  obtain ⟨s, rfl⟩ := hd
  cases hp : PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next L g s e with
  | none => simp [Machine.next, hp] at hn
  | some o =>
    cases o with
    | none =>
      cases s <;> simp only [Machine.next, hp, Option.some.injEq, reduceCtorEq] at hn
      rename_i u
      split at hn
      · rename_i hgroup
        fin_cases u
        · cases hn
        · exact ⟨rfl, hgroup⟩
        · cases hn
      · cases hn
    | some q => simp [Machine.next, hp] at hn

private theorem previous {g i : Nat} {d : ThreadD}
    (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hpos : 0 < i) :
    ∃ k u e, k + 1 = i ∧ X.get (g, k) = some e ∧
      Frame.stateAt (Machine.code P L) X g k = some (some u) ∧
      Machine.next P L g u e = some (some d) := by
  cases i with
  | zero => omega
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
      | none =>
        rw [hst] at hn
        cases hn
      | some u =>
        rw [hst] at hn
        exact ⟨k, u, e, rfl, he, hst, hn.symm⟩

/-- A live prologue state can only follow another prologue state. -/
theorem previous_prologue {g i : Nat} {s : Site}
    (hi : i + 1 ≤ (X.tr g).length)
    (hs : Frame.stateAt (Machine.code P L) X g (i + 1) = some (some (.prologue s))) :
    ∃ p e, X.get (g, i) = some e ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.prologue p)) ∧
      PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next L g p e = some (some s) := by
  obtain ⟨k, d, e, hk, he, hd, hn⟩ := previous hi hs (Nat.zero_lt_succ i)
  obtain rfl : k = i := Nat.succ.inj hk
  obtain ⟨p, hp, hlocal⟩ := transition_to_prologue hn
  exact ⟨p, e, he, hp ▸ hd, hlocal⟩

private theorem pos_of_noninitial {g i : Nat} {d : ThreadD}
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hne : d ≠ .prologue .shfl0) : 0 < i := by
  by_contra! h
  obtain rfl : i = 0 := by omega
  rw [Frame.stateAt_zero] at hd
  cases hd
  exact hne rfl

private theorem transition_to_initial_shuffle {g : Nat} {d : ThreadD} {e : Event} {s : Site}
    (hs : s = .shfl0 ∨ s = .shfl1)
    (hn : Machine.next P L g d e = some (some (.prologue s))) :
    d = .prologue .shfl0 ∧ s = .shfl1 := by
  obtain ⟨u, rfl, h⟩ := transition_to_prologue hn
  rcases hs with rfl | rfl <;> cases u <;> try exact ⟨rfl, rfl⟩
  all_goals simp only [PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next] at h
  all_goals repeat' split at h
  all_goals cases h

/-- A live first broadcast occurs only at the initial position of its trace. -/
theorem first_shuffle_position {g i : Nat} (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .shfl0))) :
    i = 0 := by
  by_contra hne
  obtain ⟨_, _, _, _, _, _, hn⟩ := previous hi hd (by omega)
  have hh := (transition_to_initial_shuffle (Or.inl rfl) hn).2
  cases hh

/-- A live second broadcast occurs only at the second position of its trace. -/
theorem second_shuffle_position {g i : Nat} (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .shfl1))) :
    i = 1 := by
  obtain ⟨k, u, _, hk, _, hu, hn⟩ :=
    previous hi hd (pos_of_noninitial hd (by intro h; cases h))
  obtain ⟨rfl, _⟩ := transition_to_initial_shuffle (Or.inr rfl) hn
  have hzero := first_shuffle_position (show k ≤ (X.tr g).length by omega) hu
  omega

/-- Each real hand-off follows the CTA gate immediately and selects the thread's warpgroup. -/
theorem handoff_source (hpre : Pre P L mem0) {g i : Nat} {wg : Fin 3}
    (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue (.handoff wg)))) :
    wgOf L g = wg.val ∧ ∃ k e, k + 1 = i ∧ X.get (g, k) = some e ∧
      Frame.stateAt (Machine.code P L) X g k = some (some (.prologue .barrier)) := by
  obtain ⟨k, u, e, hk, he, hst, hn⟩ := previous hi hd (pos_of_noninitial hd (by intro h; cases h))
  obtain ⟨rfl, hg⟩ := transition_to_handoff hpre hn
  exact ⟨hg, k, e, hk, he, hst⟩

/-- The broadcast that dispatches warpgroup one follows its own hand-off immediately. -/
theorem head_source {g i : Nat}
    (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some .head)) :
    wgOf L g = 1 ∧ ∃ k e, k + 1 = i ∧ X.get (g, k) = some e ∧
      Frame.stateAt (Machine.code P L) X g k = some (some (.prologue (.handoff 1))) := by
  obtain ⟨k, u, e, hk, he, hst, hn⟩ := previous hi hd (pos_of_noninitial hd (by intro h; cases h))
  obtain ⟨rfl, hg⟩ := transition_to_head hn
  exact ⟨hg, k, e, hk, he, hst⟩

private theorem remains_past_broadcast {g i k : Nat}
    (hi : i ≤ k) (hk : k ≤ (X.tr g).length)
    (hp : pastBroadcast (Frame.stateAt (Machine.code P L) X g i)) :
    pastBroadcast (Frame.stateAt (Machine.code P L) X g k) := by
  induction k with
  | zero =>
    have h : i = 0 := by omega
    simpa only [h] using hp
  | succ k ih =>
    by_cases heq : i = k + 1
    · simpa only [heq] using hp
    have hpk := ih (by omega) (by omega)
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := by
      change ∃ e, (X.tr g)[k]? = some e
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [Frame.stateAt_succ he]
    cases hst : Frame.stateAt (Machine.code P L) X g k with
    | none => trivial
    | some o =>
      cases o with
      | none => trivial
      | some d =>
        rw [hst] at hpk
        exact after_role d e (by rintro s rfl; exact hpk)

private theorem event_before {g i k : Nat} (hi : i ≤ (X.tr g).length) (hk : k < i) :
    ∃ e, X.get (g, k) = some e := by
  change ∃ e, (X.tr g)[k]? = some e
  exact ⟨_, List.getElem?_eq_getElem (by omega)⟩

private theorem election_predecessor {g : Nat} {s p : Site} {e : Event} {second : Bool}
    (hs : s = (if second then .elect1 else .elect0))
    (hn : PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next L g p e = some (some s)) :
    p = (if second then .elect0 else .shfl1) := by
  subst s
  cases second <;> cases p
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at hn ⊢
  all_goals simp only [PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next] at hn
  all_goals repeat' split at hn
  all_goals cases hn

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
include hpre hX hs

/-- The two prologue elections are the third and fourth events of warp zero. -/
theorem election_position {g i : Nat} {second : Bool} (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i =
      some (some (.prologue (if second then .elect1 else .elect0)))) :
    i = (if second then 3 else 2) ∧ warpOf L g = 0 := by
  cases second
  · have hp := pos_of_noninitial hd (by simp)
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    subst i
    obtain ⟨p, e, he, hP, hN⟩ := previous_prologue hi hd
    obtain rfl := election_predecessor (second := false) rfl hN
    obtain rfl := second_shuffle_position (by omega) hP
    have hTwo := PrologueShuffleTrace.state_two hpre hX hs he
    change Frame.stateAt (Machine.code P L) X g 2 = some (some (.prologue .elect0)) at hd
    rw [hd] at hTwo
    by_cases hw : warpOf L g = 0
    · exact ⟨rfl, hw⟩
    · simp [hw] at hTwo
      cases hTwo
  · have hp := pos_of_noninitial hd (by simp)
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    subst i
    obtain ⟨p, e, he, hP, hN⟩ := previous_prologue hi hd
    obtain rfl := election_predecessor (second := true) rfl hN
    have hp' := pos_of_noninitial hP (by simp)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp')
    subst j
    obtain ⟨p, f, hf, hPrev, hNext⟩ := previous_prologue (by omega) hP
    obtain rfl := election_predecessor (second := false) rfl hNext
    obtain rfl := second_shuffle_position (by omega) hPrev
    have hTwo := PrologueShuffleTrace.state_two hpre hX hs hf
    change Frame.stateAt (Machine.code P L) X g 2 = some (some (.prologue .elect0)) at hP
    rw [hP] at hTwo
    by_cases hw : warpOf L g = 0
    · exact ⟨rfl, hw⟩
    · simp [hw] at hTwo
      cases hTwo

/-- A live warpgroup-one dispatch is precisely the fifth event position of its thread trace. -/
theorem head_position {g i : Nat} (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some .head)) :
    i = 4 ∧ wgOf L g = 1 := by
  have hwg := (head_source hi hd).1
  refine ⟨?_, hwg⟩
  rcases lt_trichotomy i 4 with h | h | h
  · interval_cases i
    · rw [Frame.stateAt_zero] at hd
      cases hd
    · obtain ⟨e, he⟩ := event_before hi (show 0 < 1 by decide)
      rw [PrologueShuffleTrace.state_one hpre hX hs he] at hd
      cases hd
    · obtain ⟨e, he⟩ := event_before hi (show 1 < 2 by decide)
      rw [PrologueShuffleTrace.state_two hpre hX hs he] at hd
      cases hd
    · obtain ⟨e, he⟩ := event_before hi (show 2 < 3 by decide)
      rw [PrologueShuffleTrace.state_three hpre hX hs he hwg] at hd
      cases hd
  · exact h
  · obtain ⟨e, he⟩ := event_before hi h
    have h5 := PrologueShuffleTrace.state_five hpre hX hs he hwg
    have hp : pastBroadcast (Frame.stateAt (Machine.code P L) X g 5) := by
      rw [h5]
      unfold headStart
      repeat' split
      all_goals trivial
    have hn := remains_past_broadcast (show 5 ≤ i by omega) hi hp
    rw [hd] at hn
    exact hn.elim

omit hpre hX hs in
/-- A warp of warpgroup one always has a role entry. -/
theorem headStart_isSome {g : Nat} (hgroup : wgOf L g = 1) :
    (headStart P L g).isSome = true := by
  have hw : 4 ≤ warpOf L g ∧ warpOf L g ≤ 7 := by
    unfold wgOf at hgroup
    unfold warpOf
    omega
  obtain ⟨hlo, hhi⟩ := hw
  interval_cases h : warpOf L g <;> simp [headStart, h]

/-- The actual event at a live dispatch uses the current thread's warp and reaches its role. -/
theorem dispatch {g i : Nat} {e : Event} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some .head)) :
    e.kind = .shfl .idx (b32 (warpOf L g)) 0 31 (b32 (warpOf L g)) true ∧
      Frame.stateAt (Machine.code P L) X g (i + 1) = some (headStart P L g) := by
  obtain ⟨rfl, hgroup⟩ := head_position hpre hX hs (PTX.len_of_get he).le hd
  exact ⟨congrArg Event.kind (PrologueShuffleTrace.head_event hpre hX hs he hgroup),
    PrologueShuffleTrace.state_five hpre hX hs he hgroup⟩

/-- Passing the dispatch shuffle always retains the assigned warpgroup-one role. -/
theorem dispatch_next_tracked {g i : Nat} {e : Event} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some .head)) :
    Machine.next P L g .head e ≠ some none := by
  have hw := (head_position hpre hX hs (PTX.len_of_get he).le hd).2
  have hnext := Frame.stateAt_succ (C := Machine.code P L) he
  rw [hd, (dispatch hpre hX hs he hd).2] at hnext
  change some (headStart P L g) = Machine.next P L g .head e at hnext
  intro hnone
  rw [hnone] at hnext
  have hp := headStart_isSome (P := P) hw
  rw [Option.some.inj hnext] at hp
  cases hp

/-- The prologue preserves tracking, including a read that leads to a dead thread. -/
theorem prologue_next_tracked {g i : Nat} {e : Event} {s : Site} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue s))) :
    Machine.next P L g (.prologue s) e ≠ some none := by
  have hi : i ≤ (X.tr g).length := (PTX.len_of_get he).le
  cases s
  case shfl0 =>
    obtain rfl := first_shuffle_position hi hd
    rw [PrologueShuffleTrace.first_event hpre hX hs he]
    simp [Machine.next, PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next, b32]
  case shfl1 =>
    obtain rfl := second_shuffle_position hi hd
    rw [PrologueShuffleTrace.second_event hpre hX hs he]
    simp [Machine.next, PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next, b32]
  case allocRead =>
    intro h
    cases hk : e.kind <;> simp only [Machine.next,
      PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next, hk] at h
    case rd a bs =>
      cases hread : rebuild 3 bs >>= allocWord L g <;> simp only [hread] at h
      case error => cases h
      case ok v => by_cases hz : v.toNat = 0 <;> simp [hz] at h
    all_goals cases h
  case handoff w =>
    have hw := (handoff_source hpre hi hd).1
    simp [Machine.next, PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next, hw]
  all_goals
    intro h
    simp only [Machine.next, PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next] at h
    repeat' split at h
    all_goals cases h
    all_goals
      rename_i hkind
      split at hkind
      all_goals cases hkind

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PrologueRoleTrace
