-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.PollRounds
public import Lemmas.Flow.Elect
public import Lemmas.Order.ElectOrdinal
public import Lemmas.Step.WarpShfl
public import Lemmas.Flow.WarpUniform

@[expose] public section

/-! # Rounds of a poll met through warp collectives

At a poll whose rounds a kernel's lanes separate by warp collectives, two lanes of a warp in
different rounds are ordered in the execution-dependency order (EXT-DEPENDENCY-ORDER, `PollBefore`)
through the collectives' waiting (DEP-ORDER): the issue of one lane's collective is a witness of
the return of the other lane's collective of the instance, and that return precedes the later
events of its thread. That follows from facts of each thread's own events
(`PollRoundsMet.of_collectives`), at the positions a set `S` names: a collective ordinal (`CollAt`:
the `n`-th shuffle, or a full-mask election with `n` elections before it) that is a function `C`
of the warp, the position and the round, such that

* after its poll of round `r` at the position, a lane performs the collective of ordinal
  `C key pc r`, when another lane of its warp polls at the position in a later round (`after`;
  without such a lane the thread's trace may end at a failed poll);
* before a poll of a later round at the position, a lane has performed the collective of ordinal
  `C key pc r` for each earlier round `r` (`before`).

Two lanes' collectives of one ordinal are one instance, so the issue of one precedes the return of
the other (`coll_depStep`): shuffles by DEP-WARP-INSTANCE (`shfl_witness`), elections by
DEP-WARP-ELECT and `ElectOrdinal`. At the other positions whose next instruction is a poll branch
the rounds must be ordered in the execution-dependency order (`rest`). -/

namespace PTX

noncomputable section

/-- Thread `g`'s event `a` is its collective of ordinal `c`: its `c.2`-th shuffle (`c.1 = false`),
or a full-mask election with `c.2` elections of the thread before it (`c.1 = true`). -/
def CollAt (X : Execution) (g a : Nat) : Bool × Nat → Prop
  | (false, n) => X.ShflK (g, a) n
  | (true, n) => (∃ pc inst l, X.Elect (g, a) pc 4294967295 inst l) ∧ elections X g a = n

/-- Two threads of a warp with the same lane are the same thread. -/
theorem SameWarp.eq_of_lane {L : Launch} {g h : Nat} (hw : SameWarp L g h)
    (hl : laneOf L g = laneOf L h) : g = h := by
  obtain ⟨⟨-, -, hc⟩, hwp⟩ := hw
  unfold laneOf at hl
  have h1 : g % L.block = h % L.block := by
    rw [← Nat.div_add_mod (g % L.block) 32, ← Nat.div_add_mod (h % L.block) 32, hwp, hl]
  rw [← Nat.div_add_mod g L.block, ← Nat.div_add_mod h L.block, hc, h1]

/-- Two elections of one thread with equally many elections before them are one event. -/
theorem elect_eq_of_elections {X : Execution} {h j b pc pc' mask mask' inst inst' l l' : Nat}
    (hj : X.Elect (h, j) pc mask inst l) (hb : X.Elect (h, b) pc' mask' inst' l')
    (he : elections X h j = elections X h b) : j = b := by
  have mono : ∀ {x y pc mask inst l}, X.Elect (h, x) pc mask inst l → x < y →
      elections X h x < elections X h y := fun {x y _ _ _ _} hx hxy => by
    have h1 := ElectOrd.elections_succ hx
    have h2 : elections X h (x + 1) ≤ elections X h y :=
      (List.take_sublist_take_left (by omega)).countP_le
    omega
  rcases Nat.lt_trichotomy j b with hlt | rfl | hgt
  · exact absurd he (Nat.ne_of_lt (mono hj hlt))
  · rfl
  · exact absurd he.symm (Nat.ne_of_lt (mono hb hgt))

/-- The shuffle count grows by one over a shuffle. -/
theorem shfl_count_succ {X : Execution} {g a n : Nat} (h : X.ShflK (g, a) n) :
    ((X.tr g).take (a + 1)).countP Execution.isShfl = n + 1 := by
  obtain ⟨⟨pc, m, x, b, c, r, o, hs⟩, hk⟩ := h
  have hp : (X.tr g)[a]? = some ⟨pc, .shfl m x b c r o⟩ := hs
  rw [List.take_add_one, hp, Option.toList_some, List.countP_append]
  simp only at hk
  rw [hk]
  simp [Execution.isShfl]

/-- Two shuffles of one thread with one ordinal are one event. -/
theorem ShflK.eq_of_ord {X : Execution} {g j a n : Nat} (hj : X.ShflK (g, j) n)
    (ha : X.ShflK (g, a) n) : j = a := by
  have mono : ∀ {x y nx ny}, X.ShflK (g, x) nx → X.ShflK (g, y) ny → x < y → nx < ny :=
    fun {x y _ _} hx hy hxy => by
      have h1 := shfl_count_succ hx
      have h2 := Flow.countP_take_mono Execution.isShfl (X.tr g) (show x + 1 ≤ y by omega)
      have h3 := hy.2
      simp only at h3
      omega
  rcases Nat.lt_trichotomy j a with hlt | rfl | hgt
  · exact absurd (mono hj ha hlt) (Nat.lt_irrefl _)
  · rfl
  · exact absurd (mono ha hj hgt) (Nat.lt_irrefl _)

/-- **A shuffle is a witness of the return of each shuffle of its ordinal in its warp**: the
return waits for each lane's shuffle of the instance (DEP-WARP-INSTANCE, DEP-ORDER), and the lane
of the issuing shuffle has not exited before it. -/
theorem shfl_witness {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X) {g h a b n : Nat} (hw : SameWarp L g h)
    (hg : X.ShflK (g, a) n) (hh : X.ShflK (h, b) n) : Witness L X (.thread (g, a)) (h, b) := by
  obtain ⟨⟨pc, md, x, bb, c, r, o, hget⟩, -⟩ := id hh
  have hr : Ready L X (h, b) := hX.dependency.ready _ (by simp [Returned, hget, Kind.resume])
  have hl : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have hmem := maskNeeds_mem L shflClass X (h, b) hget rfl hl
    (Nat.testBit_two_pow_sub_one 32 _ ▸ decide_eq_true hl)
  have hneed : Need.node (fun x => ∃ j, x = .thread (warpLane L (h, b).1 (laneOf L g), j) ∧
      MaskWait L shflClass X (warpLane L (h, b).1 (laneOf L g), j) (h, b)) ∈ Needs L X (h, b) := by
    simpa only [Needs, hget, KindNeeds] using hmem
  obtain ⟨-, -, j, rfl, hmw⟩ := hr _ hneed
  have hwl : warpLane L h (laneOf L g) = g := Step.warpLane_of_sameWarp (sameWarp_symm hw)
  have hja : j = a := by
    obtain ⟨-, m', n', q, hat, hx⟩ := hmw
    rw [hwl] at hx
    obtain ⟨hm', hk'⟩ := (maskK_shflClass _ _ _ _).mp hat.1
    have hn' : n' = n := hk'.2.symm.trans hh.2
    subst hn' hm'
    rcases hx with hx | ⟨-, hx⟩
    · exact ShflK.eq_of_ord ((maskK_shflClass _ _ _ _).mp hx.1).2 hg
    · obtain ⟨pce, hex, hc⟩ := (maskExitK_shflClass _ _ _ _).mp hx
      have hlast := Execution.exit_last hX hw.1.1 hex
      have hal := hg.lt
      have hne : a ≠ j := by
        rintro rfl
        obtain ⟨⟨_, _, _, _, _, _, _, hs⟩, -⟩ := hg
        rw [hs] at hex
        simp at hex
      have h1 := shfl_count_succ hg
      have h2 := Flow.countP_take_mono Execution.isShfl (X.tr g) (show a + 1 ≤ j by
        simp only at hal; omega)
      omega
  subst hja
  obtain ⟨⟨_, _, _, _, _, _, _, hs⟩, -⟩ := hg
  refine Witness.of_need L hneed ⟨_, hs⟩ ⟨j, by rw [hwl], ?_⟩
  exact hwl ▸ hmw

/-- **Two lanes' collectives of one ordinal are one instance**: the issue of one precedes the
return of the other in the dependency order. -/
theorem coll_depStep {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X) (hord : ElectOrdinal L X) {g h a b : Nat}
    {c : Bool × Nat} (hw : SameWarp L g h) (hg : CollAt X g a c) (hh : CollAt X h b c) :
    DepStep L K X (.thread (g, a), false) (.thread (h, b), true) := by
  obtain ⟨e, n⟩ := c
  cases e with
  | false => exact DepStep.of_witness L (shfl_witness hX hw hg hh)
  | true =>
    obtain ⟨⟨pc, inst, l, hga⟩, hgn⟩ := hg
    obtain ⟨⟨pc', inst', l', hhb⟩, hhn⟩ := hh
    have hm : electMember 4294967295 (laneOf L h) := by
      have hl : laneOf L h < 32 := Nat.mod_lt _ (by decide)
      revert hl
      generalize laneOf L h = lane
      revert lane
      decide
    obtain ⟨j, pj, pj', mj, mj', ij, lj, lj', hga', hj⟩ := ElectOrd.partner hX hw hga hm
    have ho := hord hw hga' hj
    have hjb : j = b := elect_eq_of_elections hj hhb (by
      change elections X g a = elections X h j at ho
      omega)
    subst hjb
    exact ElectOrd.depStep hX hw ⟨pj, pj', mj, mj', ij, lj, lj', hga', hj⟩

/-- Two lanes' collectives of one ordinal: the issue of one precedes each later event of the
other's thread in the execution-dependency order. -/
theorem coll_depBefore {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X) (hord : ElectOrdinal L X) {g h a b k : Nat}
    {c : Bool × Nat} (hw : SameWarp L g h) (hg : CollAt X g a c) (hh : CollAt X h b c)
    (hbk : b < k) (hk : k < (X.tr h).length) : DepBefore L K X (g, a) (h, k) := by
  have hret : ∃ ev b', X.get (h, b) = some ev ∧ ev.kind.resume = .blocking b' := by
    obtain ⟨e, n⟩ := c
    cases e with
    | false =>
      obtain ⟨⟨pc, m, x, bb, cc, r, o, hs⟩, -⟩ := hh
      exact ⟨_, _, hs, rfl⟩
    | true =>
      obtain ⟨⟨pc, inst, l, hs⟩, -⟩ := hh
      exact ⟨_, _, hs, rfl⟩
  obtain ⟨ev, b', hget, hres⟩ := hret
  exact .tail (.single (.inl (coll_depStep hX hord hw hg hh)))
    (.inl (DepStep.of_resumes L (Resumes.of_blocking hget hres ⟨rfl, hbk, hk⟩)))

/-- **Rounds of a poll are met** when, at the positions `S` names, each lane performs after its
poll of a round, and before each poll of a later round, the collective of an ordinal fixed by its
warp, the position and the round, and at the other positions followed by a poll branch the rounds
are ordered in the execution-dependency order (`PollBefore`), except polls of one object at the
branches an assumption selects with `uniPoll`. -/
theorem PollRoundsMet.of_collectives {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} {κ : Type} (hX : Consistent L K A mem0 X)
    (hord : ElectOrdinal L X) (S : Nat → Bool)
    (key : Nat → κ) (hkey : ∀ {g h}, SameWarp L g h → key g = key h)
    (C : κ → Nat → Nat → Bool × Nat)
    (after : ∀ {g h k k' pc m m' p p' ok ok' acq acq' sc sc'}, g < L.threads → h < L.threads →
      g ≠ h → SameWarp L g h → X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
      X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩ → S (pc + 1) = true →
      pollRound pc ((X.tr g).take k) < pollRound pc ((X.tr h).take k') →
      ∃ a, k < a ∧ CollAt X g a (C (key g) pc (pollRound pc ((X.tr g).take k))))
    (before : ∀ {g k pc m p ok acq sc r}, g < L.threads →
      X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ → S (pc + 1) = true →
      r < pollRound pc ((X.tr g).take k) → ∃ b, b < k ∧ CollAt X g b (C (key g) pc r))
    (rest : ∀ g h k k' pc m m' p p' ok ok' acq acq' sc sc', g < L.threads → h < L.threads →
      g ≠ h → SameWarp L g h → X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
      X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩ → K.pollBranch (pc + 1) = true →
      S (pc + 1) = false → (m ≠ m' ∨ A.any (·.uniPoll (pc + 1)) = false) →
      pollRound pc ((X.tr g).take k) < pollRound pc ((X.tr h).take k') →
      PollBefore L K X (g, k) (h, k')) :
    PollRoundsMet L K A X := by
  intro g h k k' pc m m' p p' ok ok' acq acq' sc sc' hg hh hgh hw he he' hpb hd hlt
  cases hs : S (pc + 1) with
  | false =>
    exact rest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg hh hgh hw he he' hpb hs hd hlt
  | true =>
    obtain ⟨a, ha, hca⟩ := after hg hh hgh hw he he' hs hlt
    obtain ⟨b, hb, hcb⟩ := before hh he' hs hlt
    rw [hkey hw] at hca
    exact ⟨a, ha, coll_depBefore hX hord hw hca hcb hb (List.getElem?_eq_some_iff.mp he').1⟩

end

end PTX
