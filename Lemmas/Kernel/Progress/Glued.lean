-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Sched
public import Lemmas.Kernel.Roles
public import Lemmas.Kernel.Source.WarpColl

@[expose] public section

/-! # Time tables of glued, counted thread machines

A proof tool, generic over the kernel (the kernel-independent part of tml-fa4's progress tree,
`Proof2/Progress/Time.lean`, `MmaPoll.lean`, `OutputColl.lean`, `StartAll.lean`). The descent
ranks a pending thread by the time of its machine state (`Sched.Timed`). For a thread machine
glued from a first fragment and roles with a ghost ledger (`Code.glue`, `Code.counted`,
`Code.roleThread`):

* `gluedTime tP tR`: the time of a state is the first fragment's table at its states and the
  role's table at a role's states, each reading the ghost counts; `gluedTimed` is the
  `Sched.Timed` of the family. The per-role tables are what a kernel writes.
* `passTime base c coll`: a scan state with `c` collectives before it, at `base + 2 c` when its
  event is the `c`-th collective and one earlier otherwise. A table with these times meets the
  time premise of `Sched.collSched_of` for the schedule `passSched base` (`passTime_sched`), so
  the lag premise of a collective class follows from `Sched.lag_of_sched` once the counts are
  the ledger's.
* `ub_count_zero`: in an execution without undefined behaviour the ledger's count of
  undefined-behaviour events is zero at every state (the guard of reference invariants that the
  progress layer discharges).
* `okPolls_count`: the successful polls of a barrier are the ledger's count of a class that counts
  them (`Sched.PollsOn`'s parity).
* `shfl_le_collUpTo`: a position's collectives so far bound the shuffles before it (the order
  `Frame.collUpTo` against the ledger's shuffle count). -/

namespace PTX.Sched
open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {X : Execution}

/-! ### The time of a glued, counted state -/

/-- **The time of a state of a glued, counted thread machine**: the first fragment's table at its
states, the role's table at a role's states, each reading the ghost counts. -/
def gluedTime {g : Nat} (P : Flow.Code K A L g) {ι : Type} (R : ι → Flow.Code K A L g)
    (exit : P.D → Option ι) {κ : Type} (cls : κ → Event → Bool)
    (tP : P.D → (κ → Nat) → Nat) (tR : (i : ι) → (R i).D → (κ → Nat) → Nat) :
    ((Flow.Code.glue P R exit).counted cls).D → Nat
  | (.inl s, n) => tP s n
  | (.inr ⟨i, d⟩, n) => tR i d n

/-- **The time table of a glued, counted machine family.** -/
def gluedTimed (P : (g : Nat) → Flow.Code K A L g) {ι : Nat → Type}
    (R : (g : Nat) → ι g → Flow.Code K A L g) (exit : (g : Nat) → (P g).D → Option (ι g))
    {κ : Type} (cls : Nat → κ → Event → Bool)
    (tP : (g : Nat) → (P g).D → (κ → Nat) → Nat)
    (tR : (g : Nat) → (i : ι g) → (R g i).D → (κ → Nat) → Nat) : Timed K A L :=
  ⟨fun g => (Flow.Code.glue (P g) (R g) (exit g)).counted (cls g),
    fun g => gluedTime (P g) (R g) (exit g) (cls g) (tP g) (tR g)⟩

theorem gluedTime_inl {g : Nat} {P : Flow.Code K A L g} {ι : Type} {R : ι → Flow.Code K A L g}
    {exit : P.D → Option ι} {κ : Type} {cls : κ → Event → Bool} {tP tR} (s : P.D)
    (n : κ → Nat) : gluedTime P R exit cls tP tR (.inl s, n) = tP s n := rfl

theorem gluedTime_inr {g : Nat} {P : Flow.Code K A L g} {ι : Type} {R : ι → Flow.Code K A L g}
    {exit : P.D → Option ι} {κ : Type} {cls : κ → Event → Bool} {tP tR} (i : ι) (d : (R i).D)
    (n : κ → Nat) : gluedTime P R exit cls tP tR (.inr ⟨i, d⟩, n) = tR i d n := rfl

/-! ### Scan times against a collective schedule -/

/-- A scan state with `c` collectives before it: at `base + 2 c` when its event is the `c`-th
collective, one earlier otherwise. -/
def passTime (base c : Nat) (coll : Bool) : Nat :=
  if coll then base + 2 * c else base + 2 * c - 1

/-- The schedule of a scan: the `n`-th collective at `base + 2 n`. -/
def passSched (base n : Nat) : Nat := base + 2 * n

theorem passSched_mono (base n : Nat) : passSched base n < passSched base (n + 1) := by
  simp only [passSched]; omega

/-- **A scan state is on its schedule**: at the schedule's time of its count when its event is a
collective, earlier otherwise (for a base above zero). -/
theorem passTime_sched {base c : Nat} (hb : 1 ≤ base) (coll : Bool) :
    (coll = true → passTime base c coll = passSched base c) ∧
      (coll = false → passTime base c coll < passSched base c) := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h
  · simp only [passTime, passSched, ↓reduceIte]
  · simp only [passTime, passSched, Bool.false_eq_true, ↓reduceIte]
    omega

theorem passTime_le {base c : Nat} (coll : Bool) : passTime base c coll ≤ base + 2 * c := by
  cases coll <;> simp only [passTime, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem le_passTime {base c : Nat} (coll : Bool) : base + 2 * c - 1 ≤ passTime base c coll := by
  cases coll <;> simp only [passTime, Bool.false_eq_true, ↓reduceIte] <;> omega

/-! ### Ledger counts in the progress layer -/

/-- **No undefined behaviour, no counted undefined behaviour**: in an execution without
undefined-behaviour events, the ledger's count of a class of undefined-behaviour events is zero
at every state. -/
theorem ub_count_zero {g : Nat} {C : (g : Nat) → Flow.Code K A L g} {κ : Type}
    {cls : Nat → κ → Event → Bool} {c : κ}
    (hcls : ∀ e, cls g c e = true → ∃ pc f, e = ⟨pc, .ub f⟩) (hub : ¬ HasUb X) {k : Nat}
    {dn : ((C g).counted (cls g)).D}
    (h : Frame.stateAt (fun g => (C g).counted (cls g)) X g k = some (some dn)) : dn.2 c = 0 := by
  rw [Frame.count_eq h c, List.countP_eq_zero]
  intro e he hc
  obtain ⟨pc, f, rfl⟩ := hcls e hc
  obtain ⟨j, hj, hje⟩ := List.getElem_of_mem he
  have hjk : j < k := by rw [List.length_take] at hj; omega
  refine hub ⟨(g, j), pc, f, ?_⟩
  show (X.tr g)[j]? = _
  rw [← List.getElem?_take_of_lt hjk, List.getElem?_eq_getElem hj, hje]

/-- **The successful polls of a barrier are the ledger's count** of a class that counts them. -/
theorem okPolls_count {g : Nat} {C : (g : Nat) → Flow.Code K A L g} {κ : Type}
    {cls : Nat → κ → Event → Bool} {c : κ} {l : Loc} (hcls : cls g c = okPoll l) {k : Nat}
    {dn : ((C g).counted (cls g)).D}
    (h : Frame.stateAt (fun g => (C g).counted (cls g)) X g k = some (some dn)) :
    okPolls l ((X.tr g).take k) = dn.2 c := by
  rw [Frame.count_eq h c, hcls]
  rfl

/-- **A position's collectives so far bound the shuffles before it**, for a ledger whose classes
`cs` and `cv` count the shuffles and the full-mask ballots. -/
theorem shfl_le_collUpTo {h i : Nat} {C : (g : Nat) → Flow.Code K A L g} {κ : Type}
    {cls : Nat → κ → Event → Bool} {cs : κ} (hs : cls h cs = Execution.isShfl)
    {dn : ((C h).counted (cls h)).D}
    (hσ : Frame.stateAt (fun g => (C g).counted (cls g)) X h i = some (some dn)) :
    dn.2 cs ≤ Frame.collUpTo X (h, i) := by
  have h1 := countP_take_mono Frame.isColl (X.tr h) (show i ≤ i + 1 by omega)
  rw [Frame.countColl] at h1
  have h2 := Frame.count_eq hσ cs
  rw [hs] at h2
  simp only [Frame.collUpTo]
  omega

end
end PTX.Sched
