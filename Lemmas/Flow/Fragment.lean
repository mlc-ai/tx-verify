-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Glue
public import Lemmas.Flow.Ledger

@[expose] public section

/-! # Role fragments: what a role exports

A proof tool, generic over the kernel. A fragment is a site machine (`code`) together with the
tables the layers above read:

* `Ev d e`: the shape of every event fired at the site of state `d` (kind, object, operands as
  functions of the state);
* `ret d`: the kind of value the site of `d` returns into its registers (`RetKind`); the machine
  stops (`some none`) exactly when an event returns a value of another kind;
* `Ref d`: the reference invariant of the role (loop invariants over the recorded values and the
  counters);
* `Expect d e`: what the value an event returns must be for `Ref` to continue.

`Fragment.Ok` is the fragment's obligations, one state at a time (`OkAt`): the step obligations
of the machine, the shape of the site's events, the stop condition, that a state satisfying
`Ref` steps on an expected event to a state satisfying `Ref` without stopping or dying
(except after an event that ends the thread), and that no site faults under `Ref`. The machine
therefore follows every value whose kind fits (rule M1): its stops depend on kinds only, and the
content of a value is constrained only through `Ref` and `Expect`.

Fragments glue (`Fragment.glue`, `glue_ok`) like their machines (`Code.glue`): the first
fragment's obligations are needed at its states that are not exits only. The execution-level
conclusions (every machine followed, no undefined behaviour) are in `Lemmas/Kernel/Fragment`. -/

namespace PTX.Flow

noncomputable section

open PTX.Proof

/-- One element of a packed pair of format `fmt` as a load rebuilds it: a payload of `fmt`, its
NaN, or a word of the format's width (an element stored as bits, such as a masked `-∞`). -/
def packedElem (fmt : FloatFmt) : Value → Bool
  | .float f _ => decide (f = fmt)
  | .nan f => decide (f = fmt)
  | .bits w _ => w == 8 * fmt.bytes
  | _ => false

/-- A value a load of two packed elements of format `fmt` rebuilds: two elements
(`packedElem`), or one word of twice the format's width (both elements stored as bits, which the
load merges). -/
def packedVal (fmt : FloatFmt) : Value → Bool
  | .pair a b => packedElem fmt a && packedElem fmt b
  | .bits w _ => w == 16 * fmt.bytes
  | _ => false

/-- A value a load of two packed elements of format `fmt` rebuilds, each element accepted by `p`:
a pair of two elements, or one word of twice the format's width whose two halves (as an unpack
splits it, `splitValue`) are. -/
def packedWithVal (fmt : FloatFmt) (p : Value → Bool) : Value → Bool
  | .pair a b => p a && p b
  | .bits w x => w == 16 * fmt.bytes && p (splitValue w (.bits w x)).1 &&
      p (splitValue w (.bits w x)).2
  | _ => false

/-- The kind of value a site returns into its registers: nothing, a `w`-bit word, a float of a
format (a payload or its NaN), a real number of a format (a payload only), two packed elements of
a format (`packedVal`: a `.bf16x2` word loaded from elements stored as payloads or bits), two
packed elements each accepted by a predicate (`packedWithVal`: a payload or one masked pattern,
`Lemmas/Flow/MaskedPack.lean`), a value of `n` bytes, or anything (a data-plane value the role
makes no claim about). A site that returns several values (a Tensor Memory load) returns each of
this kind. -/
inductive RetKind where
  | none
  | word (w : Nat)
  | float (fmt : FloatFmt)
  | real (fmt : FloatFmt)
  | packed (fmt : FloatFmt)
  | packedWith (fmt : FloatFmt) (p : Value → Bool)
  | bytes (n : Nat)
  | any

/-- The values a return kind accepts. -/
def RetKind.acceptsVal : RetKind → Value → Prop
  | .none, _ => True
  | .word w, v => ∃ x, v = .bits w x
  | .float fmt, v => (∃ x, v = .float fmt x) ∨ v = .nan fmt
  | .real fmt, v => ∃ x, v = .float fmt x
  | .packed fmt, v => packedVal fmt v = true
  | .packedWith fmt p, v => packedWithVal fmt p v = true
  | .bytes n, v => v.bytes = n
  | .any, _ => True

/-- The value an event returns to its thread, when it returns one value: the value a read's bytes
rebuild to (`BYTES`), or the value a shuffle receives. -/
def recv (e : Event) : Option Value :=
  match e.kind with
  | .rd _ bs | .nc _ bs =>
    match rebuild 3 bs with
    | .ok v => some v
    | .error _ => none
  | .shfl _ _ _ _ v _ => some v
  | _ => none

/-- The values an event returns to its thread: the one value of `recv`, or the elements a
Tensor Memory load returns (`tcgen05.ld`). -/
def recvAll (e : Event) : List Value :=
  match e.kind with
  | .tc (.ld _ vals _) => vals
  | _ => (recv e).toList

/-- An event whose returned values, if any, have kind `k`. -/
def RetKind.accepts (k : RetKind) (e : Event) : Prop := ∀ v ∈ recvAll e, k.acceptsVal v

theorem RetKind.accepts_none (e : Event) : RetKind.none.accepts e := fun _ _ => trivial

theorem RetKind.accepts_any (e : Event) : RetKind.any.accepts e := fun _ _ => trivial

/-- An event that returns one value (`recv`) is accepted when that value is. -/
theorem RetKind.accepts_recv {k : RetKind} {e : Event} {v : Value}
    (hk : ∀ a vals sh, e.kind ≠ .tc (.ld a vals sh)) (hv : recv e = some v) :
    k.accepts e ↔ k.acceptsVal v := by
  unfold RetKind.accepts recvAll
  split
  · exact absurd ‹_› (hk _ _ _)
  · simp [hv]

/-- A Tensor Memory load is accepted when every element it returns is. -/
theorem RetKind.accepts_tcLd {k : RetKind} {e : Event} {a : Nat} {vals : List Value}
    {sh : TcShape} (he : e.kind = .tc (.ld a vals sh)) :
    k.accepts e ↔ ∀ v ∈ vals, k.acceptsVal v := by
  simp only [RetKind.accepts, recvAll, he]

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- A role fragment: a site machine with its shape table, return kinds, reference invariant and
expected values. -/
structure Fragment (K : Kernel) (A : List Assumption) (L : Launch) (g : Nat) where
  code : Code K A L g
  Ev : code.D → Event → Prop
  ret : code.D → RetKind
  Ref : code.D → Prop
  Expect : code.D → Event → Prop

namespace Fragment

/-- The obligations of a fragment at one state. -/
structure OkAt (F : Fragment K A L g) (d : F.code.D) : Prop where
  /-- The step obligations of the machine (`site_cases`). -/
  step : F.code.StepAt d
  /-- Every event fired at the state's site has the state's shape (`site_shape`). -/
  shape : ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState}, F.code.AtD d t →
    F.code.inv d → K.code[F.code.pc d]? = some ins →
    Fires (F.code.pc d) (eventTmpl A L g t ins.op) e o → F.Ev d e
  /-- The machine stops exactly on a returned value of another kind. -/
  stop_iff : ∀ {e : Event}, F.code.inv d → F.Ev d e →
    (F.code.next d e = some none ↔ ¬ (F.ret d).accepts e)
  /-- Under `Ref`, an expected event neither stops the machine nor kills the thread (except an
  event that ends it: an exit, or undefined behaviour, which `ref_safe` excludes), and leads to a
  state satisfying `Ref`. -/
  ref_next : ∀ {e : Event}, F.code.inv d → F.Ref d → F.Expect d e → F.Ev d e →
    F.code.next d e ≠ some none ∧ (F.code.next d e = none → Ends e) ∧
      ∀ d', F.code.next d e = some (some d') → F.Ref d'
  /-- No site faults under `Ref`. -/
  ref_safe : ∀ {e : Event}, F.code.inv d → F.Ref d → F.Ev d e → ∀ f, e.kind ≠ .ub f

/-- The obligations of a fragment. -/
def Ok (F : Fragment K A L g) : Prop := ∀ d, F.OkAt d

variable {F : Fragment K A L g}

theorem Ok.steps (h : F.Ok) : ∀ d, F.code.StepAt d := fun d => (h d).step

theorem Ok.shape (h : F.Ok) : F.code.Shape F.Ev := fun hat hi hc hf => (h _).shape hat hi hc hf

/-- A fragment whose machine starts is sound. -/
theorem Ok.sound (h : F.Ok)
    (hstart : ∃ t, Relation.ReflTransGen (Tau K A L g) {} t ∧ F.code.AtD F.code.init t ∧
      F.code.inv F.code.init) : F.code.Sound :=
  ⟨hstart, h.steps⟩

/-! ### Glue -/

/-- One fragment from a first fragment and the fragments its exits enter. -/
@[reducible] def glue (P : Fragment K A L g) {ι : Type} (R : ι → Fragment K A L g)
    (exit : P.code.D → Option ι) : Fragment K A L g where
  code := Code.glue P.code (fun i => (R i).code) exit
  Ev := fun | .inl d => P.Ev d | .inr ⟨i, d⟩ => (R i).Ev d
  ret := fun | .inl d => P.ret d | .inr ⟨i, d⟩ => (R i).ret d
  Ref := fun | .inl d => P.Ref d | .inr ⟨i, d⟩ => (R i).Ref d
  Expect := fun | .inl d => P.Expect d | .inr ⟨i, d⟩ => (R i).Expect d

variable {P : Fragment K A L g} {ι : Type} {R : ι → Fragment K A L g}
  {exit : P.code.D → Option ι}

theorem map_enter_none (o : Option (Option P.code.D)) :
    o.map (Option.map (Code.enter P.code (fun i => (R i).code) exit)) = some none ↔
      o = some none := by
  rcases o with _ | _ | _ <;> simp

theorem map_enter_eq_none (o : Option (Option P.code.D)) :
    o.map (Option.map (Code.enter P.code (fun i => (R i).code) exit)) = none ↔ o = none := by
  rcases o with _ | _ | _ <;> simp

/-- **The glued fragment's obligations**: the first fragment's at its states that are not exits,
every role's, the hand-off of concrete states at the exits, and `Ref` at an exit gives the role's
first `Ref`. -/
theorem glue_ok (hP : ∀ d, exit d = none → P.OkAt d) (hR : ∀ i, (R i).Ok)
    (hglue : Code.Handoff P.code (fun i => (R i).code) exit)
    (href : ∀ d i, exit d = some i → P.Ref d → (R i).Ref (R i).code.init) : (glue P R exit).Ok := by
  have hsteps := Code.glue_steps (fun d hx => (hP d hx).step) (fun i d => (hR i d).step) hglue
  intro d
  cases d with
  | inl d =>
    refine ⟨hsteps _, ?_, ?_, ?_, ?_⟩
    · intro t ins e o hat hi hc hf
      exact (hP d hi.2).shape hat hi.1 hc hf
    · intro e hi hev
      exact (map_enter_none _).trans ((hP d hi.2).stop_iff hi.1 hev)
    · intro e hi hJ hE hev
      obtain ⟨h1, h2, h3⟩ := (hP d hi.2).ref_next hi.1 hJ hE hev
      refine ⟨fun h => h1 ((map_enter_none _).mp h), fun h => h2 ((map_enter_eq_none _).mp h),
        ?_⟩
      intro d' hn
      change (P.code.next d e).map _ = _ at hn
      cases hx : P.code.next d e with
      | none => rw [hx] at hn; cases hn
      | some σ =>
        cases σ with
        | none => rw [hx] at hn; cases hn
        | some d₁ =>
          rw [hx] at hn
          cases hn
          have hJ₁ := h3 d₁ hx
          cases he : exit d₁ with
          | none => rw [Code.enter_none he]; exact hJ₁
          | some i => rw [Code.enter_some he]; exact href d₁ i he hJ₁
    · intro e hi hJ hev
      exact (hP d hi.2).ref_safe hi.1 hJ hev
  | inr s =>
    obtain ⟨i, d⟩ := s
    have h := hR i d
    refine ⟨hsteps _, fun hat hi hc hf => h.shape hat hi hc hf, ?_, ?_, ?_⟩
    · intro e hi hev
      refine Iff.trans ?_ (h.stop_iff hi hev)
      change ((R i).code.next d e).map _ = _ ↔ _
      rcases (R i).code.next d e with _ | _ | _ <;> simp
    · intro e hi hJ hE hev
      obtain ⟨h1, h2, h3⟩ := h.ref_next hi hJ hE hev
      change ((R i).code.next d e).map _ ≠ _ ∧ (((R i).code.next d e).map _ = none → _) ∧
        ∀ d', ((R i).code.next d e).map _ = some (some d') → _
      refine ⟨fun hn => h1 ?_, fun hn => h2 ?_, ?_⟩
      · rcases hx : (R i).code.next d e with _ | _ | _ <;> rw [hx] at hn <;> simp_all
      · rcases hx : (R i).code.next d e with _ | _ | _ <;> rw [hx] at hn <;> simp_all
      · intro d' hn
        rcases hx : (R i).code.next d e with _ | _ | d₁ <;> rw [hx] at hn <;> cases hn
        exact h3 d₁ hx
    · exact fun hi hJ hev => h.ref_safe hi hJ hev

end Fragment
end
end PTX.Flow
