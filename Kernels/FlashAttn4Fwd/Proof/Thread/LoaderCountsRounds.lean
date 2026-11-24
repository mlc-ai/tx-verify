-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderCountsElect
public import Lemmas.Flow.PollRounds
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Flow.NotWait

@[expose] public section

/-! # The loader's counts: the rounds of its polls

The loader's run invariant `Counts` is its ledger of counts (`Ledger`: polls, arrivals and copies
per barrier, the copy identities, the ring registers) and the rounds of its six item polls
(`rounds`): the successful polls at the position of use `u`'s poll are the uses `u` whose poll
completed, a closed formula in the item `i`, the trip `t` and the site of the state (`roundOf`):
one per item for the item's first four uses, one per trip for the trip's two (`n - 1` trips per
item). The site's position in an item (`Site.ord`) tells whether the state is past the use's poll
(`UseK.word`).

A successful poll counts only at its own position: the poll positions are listed
(`kernel_wait_pcs`) and each names one site (`wait_pc_inj`). Every other event keeps the rounds:
an item's last copy completes its trips (`round_itemEnd`), so the rounds pass continuously into
the next item and into the drain (`rounds_step`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Work

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-! ### The poll positions -/

/-- Whether an instruction is an mbarrier poll. -/
def waitOp : Op → Bool
  | .mbarWait .. => true
  | _ => false

abbrev waitPcs : List Nat := Flow.mbarWait.toList

theorem kernel_wait_pcs : OpPcsFast kernel.code waitOp waitPcs = true := by
  decide +kernel

/-- A poll fires at a poll instruction. -/
theorem waitOp_of {A : List Assumption} {t : TState} {op : Op} {pc : Nat}
    {e : Event} {o : Option TState} {m : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hf : Fires pc (eventTmpl A L g t op) e o) (hk : e.kind = .wait m p ok acq sc) :
    waitOp op = true := by
  by_contra hne
  refine fires_notWait (eventTmpl_notWait ?_) hf m p ok acq sc hk
  intro p b o par a s h
  subst h
  simp [waitOp] at hne

/-- The event of a firing is at its position. -/
theorem fires_pc {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState} (hf : Fires pc m e o) :
    e.pc = pc := by
  cases m <;> simp only [Fires] at hf <;> aesop

theorem site_wait (s : Site) (h : s.pc ∈ waitPcs) :
    (∃ u, s = .wait u) ∨ (∃ k, s = .drain k) ∨ s = .drainQ := by
  cases s
  case wait u => exact .inl ⟨u, rfl⟩
  case drain k => exact .inr (.inl ⟨k, rfl⟩)
  case drainQ => exact .inr (.inr rfl)
  all_goals (exfalso; revert h)
  all_goals (try cases ‹UseK›)
  all_goals (repeat' (first | revert ‹Fin _›))
  all_goals decide

/-- A poll site at use `u`'s poll position is that poll. -/
theorem wait_pc_inj (s : Site) (u : UseK) (h : s.pc ∈ waitPcs) (hp : s.pc = (Site.wait u).pc) :
    s = .wait u := by
  rcases site_wait s h with ⟨u', rfl⟩ | ⟨k, rfl⟩ | rfl
  · cases u <;> cases u' <;> first | rfl | (exfalso; revert hp; decide)
  · exfalso; revert hp; revert k; cases u <;> decide
  · exfalso; revert hp; cases u <;> decide

/-- **A successful poll at use `u`'s poll position** fires at that poll's site. -/
theorem okPollAt_site {A : List Assumption} {d : D} {e : Event} {t : TState} {ins : Instr}
    {o : Option TState} (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl A L g t ins.op) e o) {u : UseK}
    (hok : okPollAt (Site.wait u).pc e = true) :
    d.site = .wait u ∧ ∃ m p acq sc, e.kind = .wait m p true acq sc := by
  have hpc := fires_pc hf
  obtain ⟨epc, k⟩ := e
  cases k with
  | wait m p ok acq sc =>
    cases ok
    · simp [okPollAt] at hok
    · simp only [okPollAt, beq_iff_eq] at hok
      simp only at hpc
      have hw := waitOp_of hf rfl
      exact ⟨wait_pc_inj d.site u (OpPcsFast.mem kernel_wait_pcs hc hw) (hpc ▸ hok),
        m, p, acq, sc, rfl⟩
  | _ => simp [okPollAt] at hok

/-! ### The rounds -/

/-- The position of a site in its item, from the item's rank broadcast. -/
def Site.ord : Site → Nat
  | .head => 0
  | .wait .k0 => 1 | .elA .k0 => 2 | .arrive .k0 => 3 | .elC .k0 _ | .copy .k0 _ => 4
  | .wait .q0 => 5 | .elA .q0 => 6 | .arrive .q0 => 7 | .elC .q0 _ | .copy .q0 _ => 8
  | .wait .q1 => 9 | .elA .q1 => 10 | .arrive .q1 => 11 | .elC .q1 _ | .copy .q1 _ => 12
  | .wait .v0 => 13 | .elA .v0 => 14 | .arrive .v0 => 15 | .elC .v0 _ | .copy .v0 _ => 16
  | .wait .k => 17 | .elA .k => 18 | .arrive .k => 19 | .elC .k _ | .copy .k _ => 20
  | .wait .v => 21 | .elA .v => 22 | .arrive .v => 23 | .elC .v _ | .copy .v _ => 24
  | _ => 0

/-- The position of use `u`'s poll in its item. -/
def UseK.word : UseK → Nat
  | .k0 => 1 | .q0 => 5 | .q1 => 9 | .v0 => 13 | .k => 17 | .v => 21

/-- Whether use `u` is a use of each trip. -/
def UseK.trip : UseK → Bool
  | .k | .v => true
  | _ => false

/-- The completed polls of use `u` at state `d`: per item for the item's first four uses, per
trip (`n - 1` per item) for the trip's two. -/
def roundOf (L : Launch) (g : Nat) (d : D) (u : UseK) : Nat :=
  match d.site with
  | .setMaxReg => 0
  | .drain _ | .drainQ | .elTail | .arriveTail | .exit =>
    if u.trip then T L g * (n L - 1) else T L g
  | s => if u.trip then
      d.i * (n L - 1) + (if s.inTrip then d.t + (if u.word < s.ord then 1 else 0) else 0)
    else d.i + (if u.word < s.ord then 1 else 0)

/-- The loader's counts at state `d` after the events `es`: its ledger, and the rounds of its
item polls. -/
structure Counts (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop extends Ledger L g d es
    where
  /-- The successful polls at use `u`'s poll position are the completed polls of the use. -/
  rounds : ∀ u : UseK, pollRound (Site.wait u).pc es = roundOf L g d u
  /-- The elections of every lane (`LoaderCountsElect`; none in the prologue). -/
  elects : es.countP isElectE = electOf L g d

/-- At the role's start, before any of its counted events. -/
theorem Counts.init {es : List Event}
    (h0 : ∀ e ∈ es, ∀ m, okPoll m e = false ∧ arrivesOn m e = false ∧ issuesTo m e = false)
    (hel : es.countP isElectE = 0) :
    Counts L g ⟨.setMaxReg, 0, 0, 0, 1, 1⟩ es where
  toLedger := Ledger.init h0
  rounds u := by
    simp only [roundOf, pollRound]
    refine List.countP_eq_zero.mpr fun e he => ?_
    have h := (h0 e he)
    obtain ⟨pc, k⟩ := e
    cases k with
    | wait m p ok acq sc =>
      cases ok
      · simp [okPollAt]
      · have := (h m).1
        simp [okPoll, sourceWaitSuccess] at this
    | _ => simp [okPollAt]
  elects := hel

/-- An item's end completes the item's polls. -/
theorem round_itemEnd (d : D) (u : UseK) (hi : d.i < T L g) :
    roundOf L g (afterUse.itemEndOf L g d) u =
      if u.trip then d.i * (n L - 1) + (n L - 1) else d.i + 1 := by
  unfold afterUse.itemEndOf
  by_cases h1 : d.i + 1 < T L g
  · simp only [h1, ↓reduceIte]
    cases u <;> simp [roundOf, Site.inTrip, Site.ord, UseK.word, UseK.trip, Nat.add_mul]
  · simp only [h1, ↓reduceIte]
    have hT : T L g = d.i + 1 := by omega
    cases u <;> simp [roundOf, UseK.trip, hT, Nat.add_mul]

/-- The rounds after a copy or a skipped election: those of the use's block. -/
theorem round_afterCopy {d : D} {u : UseK} {j : Fin 2} (hs : d.site = .elC u j ∨ d.site = .copy u j)
    (hi : Inv L g d) (u' : UseK) :
    roundOf L g (afterCopy L g d u j) u' = roundOf L g d u' := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  have hit : i < T L g := hi.item (by rcases hs with h | h <;> (simp only at h; rw [h]; rfl))
  rcases hs with hs | hs <;> simp only at hs <;> subst hs <;>
  · unfold afterCopy
    split_ifs with hj
    · cases u <;> cases u' <;> rfl
    · cases u <;> simp only [afterUse]
      · cases u' <;> rfl
      · cases u' <;> rfl
      · cases u' <;> rfl
      · split_ifs with hn
        · cases u' <;> simp [roundOf, Site.inTrip, Site.ord, UseK.word, UseK.trip]
        · rw [round_itemEnd _ _ hit]
          have hn0 : n L - 1 = 0 := by omega
          cases u' <;> simp [roundOf, Site.inTrip, Site.ord, UseK.word, UseK.trip, hn0]
      · cases u' <;> rfl
      · have htr := hi.trip rfl
        simp only at htr
        split_ifs with hn
        · cases u' <;> simp [roundOf, Site.inTrip, Site.ord, UseK.word, UseK.trip]
        · rw [round_itemEnd _ _ hit]
          cases u' <;> simp [roundOf, Site.inTrip, Site.ord, UseK.word, UseK.trip] <;> omega

/-- **Every event but a successful poll of use `u` keeps its rounds.** -/
theorem round_next {d d' : D} {e : Event} (hi : Inv L g d) (hn : next L g d e = some (some d'))
    (u : UseK) (hne : d.site = .wait u → ∀ m p acq sc, e.kind ≠ .wait m p true acq sc) :
    roundOf L g d' u = roundOf L g d u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  cases site with
  | setMaxReg =>
    simp only [next, Option.some.injEq] at hn
    subst hn
    split_ifs with h
    · cases u <;> simp [roundOf, Site.ord, Site.inTrip, UseK.word, UseK.trip]
    · have hT : T L g = 0 := by omega
      cases u <;> simp [roundOf, UseK.trip, hT]
  | exit => simp [next] at hn
  | elC u0 j =>
    simp only [next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      split_ifs
      · cases u0 <;> cases u <;> rfl
      · exact round_afterCopy (.inl rfl) hi u
    · cases hn
  | copy u0 j =>
    simp only [next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      exact round_afterCopy (.inr rfl) hi u
    · cases hn
  | wait u0 =>
    simp only [next] at hn
    split at hn
    · rename_i m p ok acq sc hk
      simp only [Option.some.injEq] at hn
      subst hn
      cases ok
      · simp
      · have hu : u0 ≠ u := fun h => hne (by rw [h]) m p acq sc hk
        split_ifs <;> cases u0 <;> cases u <;>
          simp_all [roundOf, Site.ord, Site.inTrip, UseK.word, UseK.trip]
    · cases hn
  | _ =>
    cases u
    all_goals simp only [next] at hn
    all_goals (repeat' split at hn)
    all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
    all_goals subst hn
    all_goals (try cases ‹UseK›)
    all_goals simp [roundOf, Site.ord, Site.inTrip, UseK.word, UseK.trip]

/-- **The rounds after an event fired at a loader state.** -/
theorem rounds_step {A : List Assumption} {d d' : D} {pre : List Event} {e : Event} {t : TState}
    {ins : Instr} {o : Option TState}
    (hJ : ∀ u, pollRound (Site.wait u).pc pre = roundOf L g d u) (hi : Inv L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl A L g t ins.op) e o) (hn : next L g d e = some (some d')) :
    ∀ u, pollRound (Site.wait u).pc (pre ++ [e]) = roundOf L g d' u := by
  intro u
  have hu := hJ u
  simp only [pollRound, List.countP_append, List.countP_singleton] at hu ⊢
  rw [hu]
  by_cases hok : okPollAt (Site.wait u).pc e = true
  · obtain ⟨hs, m, p, acq, sc, hk⟩ := okPollAt_site hc hf hok
    simp only [hok, ↓reduceIte]
    obtain ⟨site, i, tt, s, ph, qp⟩ := d
    simp only at hs
    subst hs
    simp only [next, hk, ↓reduceIte, Option.some.injEq] at hn
    subst hn
    split_ifs <;> cases u <;> simp [roundOf, Site.ord, Site.inTrip, UseK.word, UseK.trip] <;>
      omega
  · simp only [Bool.not_eq_true] at hok
    simp only [hok, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    refine (round_next hi hn u fun hs m p acq sc hk => ?_).symm
    have hpc := fires_pc hf
    obtain ⟨epc, k⟩ := e
    simp only at hk hpc
    subst hk
    rw [hs] at hpc
    simp [okPollAt, hpc] at hok

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Loader
