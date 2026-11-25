-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Contract

@[expose] public section

/-! # The counts at the exit of the startup phase, per mbarrier and per class

The ledger of the startup phase counts events by kind (`Led`, `ledExit`). The phases after it
count per mbarrier (`okPolls m`, `arrivals m`, `issuesTo m` for the eleven mbarriers `Bar.loc L
c b` of the protocol layer) and count classes of events that the startup phase does not have
(the named barrier, matrix events, tensor stores, group commits and waits, writes). This file
gives the values of those counts over the thread's events before its exit from the phase.

* `FirstOut P L X g j`: the thread leaves the phase at position `j`: the exit condition `Out`
  holds at `j` and the invariant `Inv` holds at every position before it. `out_first`,
  `left_first`: an exit position (`Out`, `Left`) has a first one at or before it;
  `startup_first`: the invariant in this form (`Inv`, or a first exit at or before `k`).
* `first_event`: every event before the first exit is the closed-form event (`Ev`) of a
  position of the phase, with the position's ledger before it.
* `out_bar_counts`: **at every position where `Out` holds**, for every mbarrier `b` of the
  thread's block: the successful polls of `b` are 1 for the state barrier and 0 otherwise; the
  arrivals on `b` are 1 for the state barrier in the load leader (thread 128 of its block) and
  0 otherwise; the loads completing on `b` are 16 for the state barrier in the load leader and
  0 otherwise. (Between the first exit and a later position where `Out` holds the ledger by
  kind is unchanged, so no poll succeeds, no arrival and no load is issued there.)
* `first_count_zero`: **at the first exit**, a class of events that contains no closed-form
  event of the phase has count 0; `first_kind_zero` is the same for a class that contains no
  event of the nine kinds of the phase (`phaseKind`: election, shuffle, `mbarrier.init`, its
  fence, barrier, read, arrival, tensor load issue, poll), which is immediate to check for a
  class defined by a `match` on the kind. Instances: `first_named_zero` (no named barrier
  `bar.sync 8`), `first_matrix_zero`, `first_tensorStore_zero`, `first_commit_zero`. For a
  class of another phase (bulk-group waits, writes of global memory) use `first_kind_zero`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Protocol
open PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The thread leaves the startup phase at position `j`**: the exit condition holds at `j`
and the invariant holds at every position before it. -/
def FirstOut (P : Params) (L : Launch) (X : Execution) (g j : Nat) : Prop :=
  ∃ s0, Frame.stateAt (code L) X g j = some (some s0) ∧ Out P X g j s0 ∧
    ∀ i < j, ∀ si, Frame.stateAt (code L) X g i = some (some si) → Inv P X g i si

theorem FirstOut.left {j : Nat} (h : FirstOut P L X g j) : Left P L X g j :=
  let ⟨s0, h1, h2, _⟩ := h
  ⟨j, le_rfl, s0, h1, h2⟩

/-- The kinds of events of the startup phase. -/
def phaseKind : Kind → Bool
  | .elect .. | .shfl .. | .mbInit .. | .fenceMbarInit | .bar .. | .rd .. | .arrive ..
  | .tensorIssue .. | .wait .. => true
  | _ => false

/-- A closed-form event of the phase has one of the nine kinds. -/
theorem Ev.phaseKind {pos : Pos} {e : Event} (h : Ev P L g pos e) :
    phaseKind e.kind = true := by
  rcases pos with j | j | j | j | j | j | _ | j | _ <;> simp only [Ev] at h
  · obtain ⟨inst, ld, rfl⟩ := h
    rfl
  · obtain ⟨v, ok, rfl⟩ := h
    rfl
  · subst h
    rfl
  · subst h
    rfl
  · subst h
    rfl
  · obtain ⟨i, hi, bs, hbs, rfl⟩ := h
    rfl
  · subst h
    rfl
  · subst h
    rfl
  · obtain ⟨ok, rfl⟩ := h
    rfl

/-- The count of a class that is a kind class restricted by a condition `b`. -/
theorem countP_obj {cK cO : Event → Bool} {es : List Event} {b : Bool}
    (h : ∀ x ∈ es, cO x = (cK x && b)) : es.countP cO = if b then es.countP cK else 0 := by
  cases b with
  | true =>
    refine List.countP_congr fun x hx => ?_
    rw [h x hx, Bool.and_true]
  | false =>
    refine List.countP_eq_zero.mpr fun x hx => ?_
    rw [h x hx, Bool.and_false]
    simp

/-- Equal counts over two prefixes: no event of the class in between. -/
theorem none_between (c : Event → Bool) {j k i : Nat} {e : Event}
    (h : ((X.tr g).take j).countP c = ((X.tr g).take k).countP c) (hji : j ≤ i) (hik : i < k)
    (he : X.get (g, i) = some e) : c e = false := by
  have h1 := Flow.countP_take_mono c (X.tr g) hji
  have h2 := Flow.countP_take_mono c (X.tr g) (show i + 1 ≤ k by omega)
  have h3 := count_snoc c he
  cases hc : c e with
  | false => rfl
  | true =>
    rw [hc] at h3
    simp only [↓reduceIte] at h3
    omega

theorem okPoll_isOkPoll {m : Loc} {e : Event} (h : okPoll m e = true) : isOkPoll e = true := by
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | wait m' q ok acq sc =>
    cases ok with
    | false => cases h
    | true => rfl
  | _ => cases h

theorem arrivesOn_isArr {m : Loc} {e : Event} (h : arrivesOn m e = true) : isArr e = true := by
  obtain ⟨pc, kd⟩ := e
  cases kd <;> first | rfl | cases h

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

open Classical in
/-- **A position where the exit condition holds has a first one at or before it.** -/
theorem out_first {j : Nat} {s0 : D} (hσ : Frame.stateAt (code L) X g j = some (some s0))
    (ho : Out P X g j s0) : ∃ j0 ≤ j, FirstOut P L X g j0 := by
  have hex : ∃ j, ∃ s, Frame.stateAt (code L) X g j = some (some s) ∧ Out P X g j s :=
    ⟨j, s0, hσ, ho⟩
  obtain ⟨s1, hσ1, ho1⟩ := Nat.find_spec hex
  have hle : Nat.find hex ≤ j := Nat.find_min' hex ⟨s0, hσ, ho⟩
  have hlen : Nat.find hex ≤ (X.tr g).length := by
    by_contra hgt
    have hlt : (X.tr g).length < Nat.find hex := by omega
    refine Nat.find_min hex hlt ⟨s1, ?_, ?_⟩
    · rw [← Frame.stateAt_of_le (by omega : (X.tr g).length ≤ Nat.find hex)]
      exact hσ1
    · refine ⟨ho1.1, ?_⟩
      have h2 := ho1.2
      rwa [List.take_of_length_le (by omega), ← List.take_length (l := X.tr g)] at h2
  refine ⟨Nat.find hex, hle, s1, hσ1, ho1, fun i hi si hσi => ?_⟩
  rcases startup_inv hpre hX hg (by omega) hσi with hI | ⟨j', hj', s', h1, h2⟩
  · exact hI
  · exact absurd ⟨s', h1, h2⟩ (Nat.find_min hex (show j' < Nat.find hex by omega))

/-- A thread that has left the phase left it at a first position. -/
theorem left_first {k : Nat} (h : Left P L X g k) : ∃ j ≤ k, FirstOut P L X g j := by
  obtain ⟨j, hj, s0, hσ, ho⟩ := h
  obtain ⟨j0, hj0, hf⟩ := out_first hpre hX hg hσ ho
  exact ⟨j0, by omega, hf⟩

/-- **The invariant of the startup phase, with the first exit**: before each event of a
launched thread its machine is inside the phase, or the thread left the phase at a first
position at or before this one. -/
theorem startup_first {k : Nat} {s : D} (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    Inv P X g k s ∨ ∃ j ≤ k, FirstOut P L X g j := by
  rcases startup_inv hpre hX hg hk hσ with h | h
  · exact .inl h
  · exact .inr (left_first hpre hX hg h)

/-- **Every event before the first exit is the closed-form event of a position of the
phase**, with the position's ledger before it. -/
theorem first_event {j i : Nat} {e : Event} (hf : FirstOut P L X g j) (hi : i < j)
    (he : X.get (g, i) = some e) :
    ∃ pos, Ev P L g pos e ∧ ledOf ((X.tr g).take i) = led g pos := by
  obtain ⟨s0, hσ0, -, hinv⟩ := hf
  obtain ⟨si, hσi⟩ := followed_of_le hσ0 (show i ≤ j by omega)
  obtain ⟨pos, hr, hl⟩ := hinv i hi si hσi
  obtain ⟨site, w, p, x⟩ := si
  obtain rfl : site = pos.site := hr.site
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσi
  exact ⟨pos, ev_full hpre hg pos hr hat hc hf, hl⟩

/-- **At the first exit, a class that contains no closed-form event of the phase has count
0.** -/
theorem first_count_zero {j : Nat} (hf : FirstOut P L X g j) (c : Event → Bool)
    (hc : ∀ pos e, Ev P L g pos e → c e = false) : ((X.tr g).take j).countP c = 0 := by
  refine List.countP_eq_zero.mpr fun x hx => ?_
  obtain ⟨i, hi, hxi⟩ := mem_take hx
  obtain ⟨pos, hev, -⟩ := first_event hpre hX hg hf hi hxi
  rw [hc pos x hev]
  simp

/-- **At the first exit, a class that contains no event of the nine kinds of the phase has
count 0.** -/
theorem first_kind_zero {j : Nat} (hf : FirstOut P L X g j) (c : Event → Bool)
    (hc : ∀ e, phaseKind e.kind = true → c e = false) : ((X.tr g).take j).countP c = 0 :=
  first_count_zero hpre hX hg hf c fun _ e hev => hc e hev.phaseKind

/-- No named barrier (`bar.sync 8`) before the first exit. -/
theorem first_named_zero {j : Nat} (hf : FirstOut P L X g j) :
    ((X.tr g).take j).countP (Execution.isBarId 8) = 0 := by
  refine first_count_zero hpre hX hg hf _ fun pos e hev => ?_
  rcases pos with j | j | j | j | j | j | _ | j | _ <;> simp only [Ev] at hev
  · obtain ⟨inst, ld, rfl⟩ := hev
    rfl
  · obtain ⟨v, ok, rfl⟩ := hev
    rfl
  · subst hev
    rfl
  · subst hev
    rfl
  · subst hev
    rfl
  · obtain ⟨i, hi, bs, hbs, rfl⟩ := hev
    rfl
  · subst hev
    rfl
  · subst hev
    rfl
  · obtain ⟨ok, rfl⟩ := hev
    rfl

/-- No matrix event before the first exit. -/
theorem first_matrix_zero {j : Nat} (hf : FirstOut P L X g j) :
    ((X.tr g).take j).countP isMatrix = 0 := by
  refine first_kind_zero hpre hX hg hf _ ?_
  rintro ⟨pc, kd⟩ h
  cases kd <;> first | rfl | cases h

/-- No tensor store before the first exit. -/
theorem first_tensorStore_zero {j : Nat} (hf : FirstOut P L X g j) :
    ((X.tr g).take j).countP isTensorStore = 0 := by
  refine first_kind_zero hpre hX hg hf _ ?_
  rintro ⟨pc, kd⟩ h
  cases kd <;> first | rfl | cases h

/-- No bulk-group commit before the first exit. -/
theorem first_commit_zero {j : Nat} (hf : FirstOut P L X g j) :
    ((X.tr g).take j).countP isCommit = 0 := by
  refine first_kind_zero hpre hX hg hf _ ?_
  rintro ⟨pc, kd⟩ h
  cases kd <;> first | rfl | cases h

/-- **The counts per mbarrier at the first exit**, as conditions on the mbarrier's location:
the phase's only successful poll, arrival and load issues are on the state barrier of the
thread's block. -/
theorem first_obj_counts {j : Nat} (hf : FirstOut P L X g j) (m : Loc) :
    let m0 : Loc := ⟨.shared, g / L.block, P.sharedBase + 98384⟩
    okPolls m ((X.tr g).take j) = (if decide (m0 = m) then 1 else 0) ∧
      arrivals m ((X.tr g).take j) =
        (if decide (m0 = m) then (if tid g = 128 then 1 else 0) else 0) ∧
      ((X.tr g).take j).countP (issuesTo m) =
        (if decide (m0 = m) then (if tid g = 128 then 16 else 0) else 0) := by
  intro m0
  obtain ⟨s0, hσ0, ho, hinv⟩ := id hf
  have hpolls : ((X.tr g).take j).countP isOkPoll = 1 := congrArg Led.polls ho.2
  have harrs : ((X.tr g).take j).countP isArr = if tid g = 128 then 1 else 0 :=
    congrArg Led.arrs ho.2
  have hiss : ((X.tr g).take j).countP isIssue = if tid g = 128 then 16 else 0 :=
    congrArg Led.issues ho.2
  refine ⟨?_, ?_, ?_⟩
  · have h := countP_obj (cK := isOkPoll) (cO := okPoll m) (es := (X.tr g).take j)
      (b := decide (m0 = m)) fun x hx => by
        obtain ⟨i, hi, hxi⟩ := mem_take hx
        obtain ⟨pos, hev, -⟩ := first_event hpre hX hg hf hi hxi
        rcases pos with j | j | j | j | j | j | _ | j | _ <;> simp only [Ev] at hev
        · obtain ⟨inst, ld, rfl⟩ := hev
          rfl
        · obtain ⟨v, ok, rfl⟩ := hev
          rfl
        · subst hev
          rfl
        · subst hev
          rfl
        · subst hev
          rfl
        · obtain ⟨i', hi', bs, hbs, rfl⟩ := hev
          rfl
        · subst hev
          rfl
        · subst hev
          rfl
        · obtain ⟨ok, rfl⟩ := hev
          rw [okPoll_wait rfl]
          cases ok <;> rfl
    rw [okPolls, h, hpolls]
  · have h := countP_obj (cK := isArr) (cO := arrivesOn m) (es := (X.tr g).take j)
      (b := decide (m0 = m)) fun x hx => by
        obtain ⟨i, hi, hxi⟩ := mem_take hx
        obtain ⟨pos, hev, -⟩ := first_event hpre hX hg hf hi hxi
        rcases pos with j | j | j | j | j | j | _ | j | _ <;> simp only [Ev] at hev
        · obtain ⟨inst, ld, rfl⟩ := hev
          rfl
        · obtain ⟨v, ok, rfl⟩ := hev
          rfl
        · subst hev
          rfl
        · subst hev
          rfl
        · subst hev
          rfl
        · obtain ⟨i', hi', bs, hbs, rfl⟩ := hev
          rfl
        · subst hev
          rw [arrivesOn_arrive rfl]
          rfl
        · subst hev
          rfl
        · obtain ⟨ok, rfl⟩ := hev
          rfl
    rw [arrivals, h, harrs]
  · have h := countP_obj (cK := isIssue) (cO := issuesTo m) (es := (X.tr g).take j)
      (b := decide (m0 = m)) fun x hx => by
        obtain ⟨i, hi, hxi⟩ := mem_take hx
        obtain ⟨pos, hev, -⟩ := first_event hpre hX hg hf hi hxi
        rcases pos with j | j | j | j | j | j | _ | j | _ <;> simp only [Ev] at hev
        · obtain ⟨inst, ld, rfl⟩ := hev
          rfl
        · obtain ⟨v, ok, rfl⟩ := hev
          rfl
        · subst hev
          rfl
        · subst hev
          rfl
        · subst hev
          rfl
        · obtain ⟨i', hi', bs, hbs, rfl⟩ := hev
          rfl
        · subst hev
          rfl
        · subst hev
          rw [issuesTo_tensorIssue]
          rfl
        · obtain ⟨ok, rfl⟩ := hev
          rfl
    rw [h, hiss]

/-- **The counts per mbarrier at a position where the exit condition holds**: for every
mbarrier `b` of the thread's block, one successful poll of the state barrier and none of the
others; in the load leader (thread 128 of the block) one arrival on the state barrier and 16
loads completing on it, and none of either on the others or in the other threads. -/
theorem out_bar_counts {j : Nat} {s0 : D}
    (hσ : Frame.stateAt (code L) X g j = some (some s0)) (ho : Out P X g j s0) (b : Bar) :
    okPolls (b.loc L (g / L.block)) ((X.tr g).take j) = (if b = .state then 1 else 0) ∧
      arrivals (b.loc L (g / L.block)) ((X.tr g).take j) =
        (if b = .state ∧ tid g = 128 then 1 else 0) ∧
      ((X.tr g).take j).countP (issuesTo (b.loc L (g / L.block))) =
        (if b = .state ∧ tid g = 128 then 16 else 0) := by
  obtain ⟨j0, hj0, hf⟩ := out_first hpre hX hg hσ ho
  obtain ⟨s1, hσ1, ho1, -⟩ := id hf
  have hled : ledOf ((X.tr g).take j0) = ledOf ((X.tr g).take j) := ho1.2.trans ho.2.symm
  obtain ⟨h1, h2, h3⟩ := first_obj_counts hpre hX hg hf (b.loc L (g / L.block))
  have hb : decide ((⟨.shared, g / L.block, P.sharedBase + 98384⟩ : Loc) =
      b.loc L (g / L.block)) = decide (b = .state) := by
    have hst : (⟨.shared, g / L.block, P.sharedBase + 98384⟩ : Loc) =
        Bar.state.loc L (g / L.block) := by
      simp only [Bar.loc, Bar.off, hpre.sharedBase]
    rw [hst]
    by_cases hbs : b = .state
    · subst hbs
      simp
    · have : Bar.state.loc L (g / L.block) ≠ b.loc L (g / L.block) :=
        fun h => hbs (Bar.loc_inj h).1.symm
      simp [hbs, this]
  rw [hb] at h1 h2 h3
  -- between the first exit and `j` the ledger by kind does not change
  have e1 : ((X.tr g).take j).countP (okPoll (b.loc L (g / L.block))) =
      ((X.tr g).take j0).countP (okPoll (b.loc L (g / L.block))) :=
    countP_take_eq _ hj0 fun i e h1 h2 he => by
      have := none_between isOkPoll (congrArg Led.polls hled) h1 h2 he
      cases hc : okPoll (b.loc L (g / L.block)) e with
      | false => rfl
      | true => rw [okPoll_isOkPoll hc] at this; cases this
  have e2 : ((X.tr g).take j).countP (arrivesOn (b.loc L (g / L.block))) =
      ((X.tr g).take j0).countP (arrivesOn (b.loc L (g / L.block))) :=
    countP_take_eq _ hj0 fun i e h1 h2 he => by
      have := none_between isArr (congrArg Led.arrs hled) h1 h2 he
      cases hc : arrivesOn (b.loc L (g / L.block)) e with
      | false => rfl
      | true => rw [arrivesOn_isArr hc] at this; cases this
  have e3 : ((X.tr g).take j).countP (issuesTo (b.loc L (g / L.block))) =
      ((X.tr g).take j0).countP (issuesTo (b.loc L (g / L.block))) :=
    countP_take_eq _ hj0 fun i e h1 h2 he => by
      have := none_between isIssue (congrArg Led.issues hled) h1 h2 he
      cases hc : issuesTo (b.loc L (g / L.block)) e with
      | false => rfl
      | true => rw [issuesTo_isIssue hc] at this; cases this
  refine ⟨?_, ?_, ?_⟩
  · have h1' : ((X.tr g).take j0).countP (okPoll (b.loc L (g / L.block))) = _ := h1
    rw [okPolls, e1, h1']
    simp
  · have h2' : ((X.tr g).take j0).countP (arrivesOn (b.loc L (g / L.block))) = _ := h2
    rw [arrivals, e2, h2']
    by_cases hbs : b = .state <;> by_cases ht : tid g = 128 <;> simp [hbs, ht]
  · rw [e3, h3]
    by_cases hbs : b = .state <;> by_cases ht : tid g = 128 <;> simp [hbs, ht]

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
