-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Followed
public import Lemmas.Kernel.FrameStop

@[expose] public section

/-! # Safety from a role table

A proof skeleton, generic over the kernel. A kernel's threads are followed by a family of
machines `C` (the glued role machines, `Code.roleThread`). A **role table** gives, for every
thread `g` and state `d`, the reference invariant `J g d` of the role the state belongs to and the
shape table `Ev g d` of the events the state may fire. Its obligations (`RoleTable.Ok`), each at a
state satisfying `J`, are the fragment obligations the safety classes need:

* `shape`: an event fired from the state has the state's shape (`site_shape`; `RoleTable.ShapeOk`
  alone);
* `safe`: no shape is undefined behaviour (`ref_safe`);
* `death`: the machine dies only at an exit (the `none` conjunct of `ref_next`).

For the threads `S` whose machines are followed with `J` (`RoleTable.Followed`: every state of
the thread satisfies `J`, from `Frame.followed_of_sources` or a kernel's `good_migrated`), every
event of such a thread that is no undefined behaviour is fired from a `J` state with that state's
shape, by the shape obligation alone (`RoleTable.ev_of_ne_ub`, `RoleTable.forall_kind`: the frames
of `Classes.lean` need no more). With `safe` and `death` too, every event is (`RoleTable.ev`), none
is undefined behaviour (`RoleTable.noUb`), and the machine is dead only after an exit
(`RoleTable.dead`). A safety class is then discharged by facts about the shape tables:

* a predicate of every event (`RoleTable.forall_ev`): the class's per-event condition, stated
  once per shape (a write's location in the role's frame, no tensor load, an access inside the
  allocation);
* the instruction at the state's site (`RoleTable.ins`, `RoleTable.sites`, for events that are no
  undefined behaviour, from the shape obligation alone): a class that names an instruction kind is
  closed by one evaluated check of the code at the sites the role table can reach (the tml-fa4
  `migrated_fires` pattern).

The classes of Core's `Unsafe` stated this way are in `Lemmas/Kernel/Safety/Classes.lean`. -/

namespace PTX.Frame

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}

/-- **A role table** of a machine family: the reference invariant of the role each state belongs
to, and the shape table of the events each state may fire. -/
structure RoleTable (C : (g : Nat) → Code K A L g) where
  /-- The reference invariant of the state's role. -/
  J : ∀ g, (C g).D → Prop
  /-- The shape table: the events the state may fire. -/
  Ev : ∀ g, (C g).D → Event → Prop

variable {C : (g : Nat) → Code K A L g}

/-- **The shape obligation of a role table** at the states that satisfy the invariant, for the
threads `S`: an event fired from such a state has the state's shape (`Code.ShapeAt`). -/
structure RoleTable.ShapeOk (T : RoleTable C) (S : Nat → Prop) : Prop where
  /-- An event fired from a state has the state's shape (`Code.ShapeAt`). -/
  shape : ∀ g, S g → ∀ d t ins e o, T.J g d → (C g).AtD d t → (C g).inv d →
    K.code[(C g).pc d]? = some ins → Fires ((C g).pc d) (eventTmpl A L g t ins.op) e o →
    T.Ev g d e

/-- **The obligations of a role table** at the states that satisfy the invariant, for the threads
`S`: the shape, `ref_safe` and the death clause. -/
structure RoleTable.Ok (T : RoleTable C) (S : Nat → Prop) : Prop extends T.ShapeOk S where
  /-- No shape is undefined behaviour (`ref_safe`). -/
  safe : ∀ g, S g → ∀ d e, (C g).inv d → T.J g d → T.Ev g d e → ∀ f, e.kind ≠ .ub f
  /-- The machine dies only at an exit (`ref_next`'s `none` conjunct). -/
  death : ∀ g, S g → ∀ d e, (C g).inv d → T.J g d → T.Ev g d e → (C g).next d e = none →
    e.kind = .exit

/-- The threads `S` are followed with the table's invariant at every state. -/
def RoleTable.Followed (T : RoleTable C) (X : Execution) (S : Nat → Prop) : Prop :=
  ∀ g, S g → ∀ k, FollowedAt C T.J X g k

variable {T : RoleTable C} {S : Nat → Prop} {X : Execution}

section shape
variable (hC : ∀ g < L.threads, (C g).Sound) (hX : Consistent L K A mem0 X) (hT : T.ShapeOk S)
  (hF : T.Followed X S)
include hC hX hT hF

/-- An event fired from a followed state of a thread of `S` has the state's shape. -/
theorem RoleTable.ev_at {g k : Nat} {d : (C g).D} {e : Event} (hg : S g)
    (he : X.get (g, k) = some e) (hσ : stateAt C X g k = some (some d)) :
    T.J g d ∧ (C g).inv d ∧ T.Ev g d e := by
  have hJ := (hF g hg k).2 d hσ
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ := fired_site hC hX he hσ
  exact ⟨hJ, hi, hT.shape g hg d t ins e o hJ hat hi hc hf⟩

/-- **An event of a thread of `S` that is no undefined behaviour is fired from a followed state,
with its shape** (the shape obligation alone: a dead machine fires only undefined behaviour). -/
theorem RoleTable.ev_of_ne_ub {g k : Nat} {e : Event} (hg : S g) (he : X.get (g, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) :
    ∃ d, stateAt C X g k = some (some d) ∧ T.J g d ∧ (C g).inv d ∧ T.Ev g d e := by
  rcases fired (C := C) hC hX he with ⟨σ, o, hσ, -⟩ | ⟨-, pc, f, rfl⟩
  · cases σ with
    | none => exact absurd hσ (hF g hg k).1
    | some d => exact ⟨d, hσ, RoleTable.ev_at hC hX hT hF hg he hσ⟩
  · exact absurd rfl (hub f)

/-- **A per-shape condition holds of every event of a thread of `S` of a kind `P` that excludes
undefined behaviour** (a write, an access, an issue): the form of the frames, which need the shape
obligation alone. -/
theorem RoleTable.forall_kind {P : Event → Prop} {Q : Nat → Event → Prop}
    (hP : ∀ e, P e → ∀ f, e.kind ≠ .ub f)
    (hQ : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → P e → Q g e) {g k : Nat}
    {e : Event} (hg : S g) (he : X.get (g, k) = some e) (hpe : P e) : Q g e := by
  obtain ⟨d, -, hJ, hi, hev⟩ := RoleTable.ev_of_ne_ub hC hX hT hF hg he (hP e hpe)
  exact hQ g hg d e hJ hi hev hpe

/-- **A per-state condition holds of every event of a thread of `S` of a kind `P` that excludes
undefined behaviour**, with the event's position: the condition may read the state the event is
fired from and the thread's trace before it (a use count by `Frame.count_eq`, the position of a
barrier or a request among the thread's events). -/
theorem RoleTable.forall_at {P : Event → Prop} {Q : EvId → Event → Prop}
    (hP : ∀ e, P e → ∀ f, e.kind ≠ .ub f)
    (hQ : ∀ g k d e, S g → stateAt C X g k = some (some d) → T.J g d → (C g).inv d →
      T.Ev g d e → P e → Q (g, k) e)
    {g k : Nat} {e : Event} (hg : S g) (he : X.get (g, k) = some e) (hpe : P e) : Q (g, k) e := by
  obtain ⟨d, hσ, hJ, hi, hev⟩ := RoleTable.ev_of_ne_ub hC hX hT hF hg he (hP e hpe)
  exact hQ g k d e hg hσ hJ hi hev hpe

/-- **Every event of a thread of `S` that is no undefined behaviour is fired by the instruction
at its state's site.** -/
theorem RoleTable.ins {g k : Nat} {e : Event} (hg : S g) (he : X.get (g, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) :
    ∃ d t ins o, T.J g d ∧ K.code[(C g).pc d]? = some ins ∧
      Fires ((C g).pc d) (eventTmpl A L g t ins.op) e o := by
  obtain ⟨d, hσ, hJ, -, -⟩ := RoleTable.ev_of_ne_ub hC hX hT hF hg he hub
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := fired_site hC hX he hσ
  exact ⟨d, t, ins, o, hJ, hc, hf⟩

/-- **The sites check** (tml-fa4's `migrated_fires`): when every state satisfying `J` sits at a
pc of `sites` and the instruction at every such pc satisfies `p`, every event of a thread of `S`
that is no undefined behaviour is fired by an instruction satisfying `p`. With `p` decidable the
second premise is one evaluated check of the code (`List.all`, by `decide`). -/
theorem RoleTable.sites (sites : List Nat) (p : Instr → Prop)
    (hpc : ∀ g, S g → ∀ d, T.J g d → (C g).pc d ∈ sites)
    (hp : ∀ pc ∈ sites, ∀ ins, K.code[pc]? = some ins → p ins) {g k : Nat} {e : Event}
    (hg : S g) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) :
    ∃ pc t ins o, pc ∈ sites ∧ p ins ∧ K.code[pc]? = some ins ∧
      Fires pc (eventTmpl A L g t ins.op) e o := by
  obtain ⟨d, t, ins, o, hJ, hc, hf⟩ := RoleTable.ins hC hX hT hF hg he hub
  have hm := hpc g hg d hJ
  exact ⟨_, t, ins, o, hm, hp _ hm ins hc, hc, hf⟩

end shape

variable (hC : ∀ g < L.threads, (C g).Sound) (hX : Consistent L K A mem0 X) (hT : T.Ok S)
  (hF : T.Followed X S)
include hC hX hT hF

/-- **The machine of a thread of `S` is dead only after an exit.** -/
theorem RoleTable.dead {g k : Nat} (hg : S g) (hσ : stateAt C X g k = none) :
    ∃ j < k, ∃ pc, X.get (g, j) = some ⟨pc, .exit⟩ := by
  obtain ⟨i, d, hik, hi, hi'⟩ := first_stop_any (C := C) (X := X) (g := g) (.inl hσ)
  have hlen : i < (X.tr g).length := by
    by_contra hn
    rw [stateAt_of_le (by omega)] at hi
    rw [stateAt_of_le (by omega), hi] at hi'
    simp at hi'
  obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e := ⟨_, List.getElem?_eq_getElem hlen⟩
  obtain ⟨hJ, hinv, hev⟩ := RoleTable.ev_at hC hX hT.toShapeOk hF hg he hi
  rcases hi' with hn | hn
  · rw [stateAt_succ he, hi] at hn
    obtain ⟨pc, kd⟩ := e
    exact ⟨i, hik, pc, by rw [he, show kd = .exit from hT.death g hg d _ hinv hJ hev hn]⟩
  · exact absurd hn (hF g hg (i + 1)).1

/-- **Every event of a thread of `S` is fired from a followed state, with its shape.** -/
theorem RoleTable.ev {g k : Nat} {e : Event} (hg : S g) (he : X.get (g, k) = some e) :
    ∃ d, stateAt C X g k = some (some d) ∧ T.J g d ∧ (C g).inv d ∧ T.Ev g d e := by
  rcases fired (C := C) hC hX he with ⟨σ, o, hσ, -⟩ | ⟨hσ, -⟩
  · cases σ with
    | none => exact absurd hσ (hF g hg k).1
    | some d => exact ⟨d, hσ, RoleTable.ev_at hC hX hT.toShapeOk hF hg he hσ⟩
  · obtain ⟨i, hij, pc, hx⟩ := RoleTable.dead hC hX hT hF hg hσ
    obtain ⟨r, hr⟩ := hX.thr g (lt_of_get hX he)
    have h1 := Flow.Run.end_last hr hx (.inr rfl)
    have h2 : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    omega

/-- **No event of a thread of `S` is undefined behaviour.** -/
theorem RoleTable.noUb {g k : Nat} {e : Event} (hg : S g) (he : X.get (g, k) = some e) (f : Fault) :
    e.kind ≠ .ub f := by
  obtain ⟨d, -, hJ, hi, hev⟩ := RoleTable.ev hC hX hT hF hg he
  exact hT.safe g hg d e hi hJ hev f

/-- **A per-shape condition holds of every event of a thread of `S`**: the form in which a
safety class is discharged by the shape tables. -/
theorem RoleTable.forall_ev {Q : Nat → Event → Prop}
    (hQ : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → Q g e) {g k : Nat} {e : Event}
    (hg : S g) (he : X.get (g, k) = some e) : Q g e := by
  obtain ⟨d, -, hJ, hi, hev⟩ := RoleTable.ev hC hX hT hF hg he
  exact hQ g hg d e hJ hi hev

end

end PTX.Frame
