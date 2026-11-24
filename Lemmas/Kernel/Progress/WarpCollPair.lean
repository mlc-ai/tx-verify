-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotWarpColl
public import Lemmas.Kernel.Progress.Issue
public import Lemmas.Kernel.Progress.WarpCollRel

@[expose] public section

/-! # A kernel's warp collectives from facts of two lanes of a warp

`WarpCollRel` (`WarpCollRel.lean`) gives the static part and the position of a warp's `n`-th
collective, and the collectives at its exit, as functions of the warp and `n`. Here they follow
from facts of two lanes of one warp (`WarpPair`), so a kernel proves them warp by warp: two lanes at
their `n`-th collective are at one program counter with one static part (`S`, a function of the
state; the instruction's when its operands are immediates, `warpOp_tmpl`), and a lane exits after
more collectives than a lane at one has made. -/

namespace PTX.Sched

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution} {κ : Type}

/-- Lane `g`'s state `d` before its `k`-th event is at a warp collective: the event is one, or the
trace ends there and the state is at one. -/
def CollPos (M : Timed K A L) (X : Execution) (AtColl : ∀ g, (M.code g).D → Prop) (g k : Nat)
    (d : (M.code g).D) : Prop :=
  Frame.stateAt M.code X g k = some (some d) ∧
    ((∃ e, X.get (g, k) = some e ∧ isWarpColl e = true) ∨ (k = (X.tr g).length ∧ AtColl g d))

/-- **The facts of two lanes `g` and `h` of a warp.** -/
structure WarpPair (mem0 : Mem0) (M : Timed K A L) (X : Execution)
    (AtColl : ∀ g, (M.code g).D → Prop) (S : ∀ g, (M.code g).D → CollShape) (g h : Nat) :
    Prop where
  /-- Two lanes at their `n`-th collective are at one position, with one static part. -/
  pc : ∀ {k k' : Nat} {d : (M.code g).D} {d' : (M.code h).D}, CollPos M X AtColl g k d →
    CollPos M X AtColl h k' d' →
    ((X.tr g).take k).countP isWarpColl = ((X.tr h).take k').countP isWarpColl →
    (M.code g).pc d = (M.code h).pc d' ∧ S g d = S h d'
  /-- Of two lanes at one collective, when one is released, the other is. -/
  released : ∀ {d : (M.code g).D} {d' : (M.code h).D},
    Frame.stateAt M.code X g (X.tr g).length = some (some d) → AtColl g d →
    Frame.stateAt M.code X h (X.tr h).length = some (some d') → AtColl h d' →
    (X.tr h).countP isWarpColl = (X.tr g).countP isWarpColl → Step.Released L X g →
    Step.Released L X h ∨ ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L
  /-- A lane exits after more collectives than a lane at one has made. -/
  exit : ∀ {k pc : Nat} {d : (M.code g).D} {d' : (M.code h).D},
    Frame.stateAt M.code X g (X.tr g).length = some (some d) → AtColl g d →
    Frame.stateAt M.code X h k = some (some d') → X.get (h, k) = some ⟨pc, .exit⟩ →
    (X.tr g).countP isWarpColl < ((X.tr h).take k).countP isWarpColl
  /-- A lane with at most as many collectives that is not at the collective is earlier. -/
  lag : ∀ {d : (M.code g).D},
    Frame.stateAt M.code X g (X.tr g).length = some (some d) → AtColl g d →
    (X.tr h).countP isWarpColl ≤ (X.tr g).countP isWarpColl →
    ¬ ((X.tr h).countP isWarpColl = (X.tr g).countP isWarpColl ∧
      ∃ d', Frame.stateAt M.code X h (X.tr h).length = some (some d') ∧ AtColl h d') →
    Frame.stateAt M.code X h (X.tr h).length ≠ none →
    threadTime M X h < M.time g d
  /-- A pending lane whose machine stopped is released. -/
  dead : Frame.Pending L X h → Frame.stateAt M.code X h (X.tr h).length = none →
    Step.Released L X h

/-- **The static part of a state at a warp collective** is `S`: its instruction's template is
undefined behaviour or has that static part, which names the whole warp. -/
def ShapeAt (M : Timed K A L) (S : ∀ g, (M.code g).D → CollShape) (g : Nat) (d : (M.code g).D) :
    Prop :=
  (S g d).Full ∧ ∀ t ins, (M.code g).AtD d t → (M.code g).inv d →
    K.code[(M.code g).pc d]? = some ins → ins.op.isLocal = false ∧
      ((∃ f, eventTmpl A L g t ins.op = .ub f) ∨
        tmplShape (eventTmpl A L g t ins.op) = some (S g d))

/-- The template at a warp instruction with a static part. -/
theorem warpOp_tmpl {g : Nat} {t : TState} {op : Op} {s : CollShape} (hs : opShape op = some s) :
    (∃ f, eventTmpl A L g t op = .ub f) ∨ tmplShape (eventTmpl A L g t op) = some s := by
  cases op <;> simp only [opShape, reduceCtorEq] at hs
  rename_i w
  rcases eventTmpl_opTmpl (A := A) (L := L) (g := g) (t := t) (.warp w) with hf | hm
  · exact .inl hf
  · right
    have key : ∃ s', tmplShape (eventTmpl A L g t (.warp w)) = some s' := by
      simp only [OpEv] at hm
      cases hk : w.kind <;> simp only [hk] at hm
      case shfl | elect | barWarp =>
        all_goals first
          | (obtain ⟨_, _, _, _, _, hm⟩ := hm; rw [hm]; exact ⟨_, rfl⟩)
          | (obtain ⟨_, _, hm⟩ := hm; rw [hm]; exact ⟨_, rfl⟩)
      case vote md neg =>
        cases md <;> simp only at hm
        case ballot => obtain ⟨_, _, _, hm⟩ := hm; rw [hm]; exact ⟨_, rfl⟩
        all_goals simp [hk] at hs
      all_goals simp [hk] at hs
    obtain ⟨s', hs'⟩ := key
    rw [hs', warpTmpl_shape (L := L) (g := g) (t := t) hs hs']

/-- A fired template's static part is its event's. -/
theorem fires_shape {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState} (hf : Fires pc m e o)
    (hc : isWarpColl e = true) : ∃ s, tmplShape m = some s ∧ kindShape e.kind = some s := by
  obtain ⟨epc, ek⟩ := e
  cases m <;> simp only [Fires] at hf <;>
    aesop (add norm simp [tmplShape, kindShape, isWarpColl])

variable {key : Nat → κ} {AtColl : ∀ g, (M.code g).D → Prop}
  {S : ∀ g, (M.code g).D → CollShape}

open Classical in
/-- The position and the static part of the `n`-th collective of the warp of key `c`. -/
def collAt (M : Timed K A L) (X : Execution) (key : Nat → κ) (AtColl : ∀ g, (M.code g).D → Prop)
    (S : ∀ g, (M.code g).D → CollShape) (c : κ) (n : Nat) : Nat × CollShape :=
  if h : ∃ g k, ∃ d : (M.code g).D, g < L.threads ∧ key g = c ∧ CollPos M X AtColl g k d ∧
      ((X.tr g).take k).countP isWarpColl = n then
    let g := Classical.choose h
    let d : (M.code g).D := Classical.choose (Classical.choose_spec h).choose_spec
    ((M.code g).pc d, S g d)
  else (0, .shfl .up 0 0)

/-- **The warp collectives' facts from the facts of two lanes of a warp.** -/
theorem warpCollRel_of_pairs
    (hkey : ∀ {g h : Nat}, g < L.threads → h < L.threads → key g = key h → SameWarp L g h)
    (hsound : ∀ g < L.threads, (M.code g).Sound) (hX : Consistent L K A mem0 X)
    (hS : ∀ {g k : Nat} {d : (M.code g).D}, g < L.threads → CollPos M X AtColl g k d →
      ShapeAt M S g d)
    (hp : ∀ {g h : Nat}, SameWarp L g h → WarpPair mem0 M X AtColl S g h) :
    WarpCollRel mem0 M X key AtColl := by
  -- the common value at a position
  have hF : ∀ {g k : Nat} {d : (M.code g).D}, g < L.threads → CollPos M X AtColl g k d →
      collAt M X key AtColl S (key g) (((X.tr g).take k).countP isWarpColl) =
        ((M.code g).pc d, S g d) := by
    intro g k d hg hd
    have hex : ∃ g' k', ∃ d' : (M.code g').D, g' < L.threads ∧ key g' = key g ∧
        CollPos M X AtColl g' k' d' ∧ ((X.tr g').take k').countP isWarpColl =
          ((X.tr g).take k).countP isWarpColl := ⟨g, k, d, hg, rfl, hd, rfl⟩
    unfold collAt
    simp only [hex, dite_true]
    obtain ⟨h1, h2, h3, h4⟩ := Classical.choose_spec (Classical.choose_spec hex).choose_spec
    obtain ⟨e1, e2⟩ := (hp (hkey h1 hg h2)).pc h3 hd h4
    simp only [e1, e2]
  refine ⟨⟨collAt M X key AtColl S, fun c n => ?_, fun {g k e d} hg hσ he hc => ?_,
    fun {g d t m} hg hσ hd hAt hinv hout => ?_⟩, fun {g h d d'} hg hs => (hp hs).released, ?_,
    fun {h} hh => (hp ⟨⟨hh.1, hh.1, rfl⟩, rfl⟩ : WarpPair mem0 M X AtColl S h h).dead hh,
    fun {g h d} _ _ hs => (hp hs).lag⟩
  · unfold collAt
    split
    · rename_i h
      obtain ⟨h1, h2, h3, h4⟩ := Classical.choose_spec (Classical.choose_spec h).choose_spec
      exact (hS h1 h3).1
    · trivial
  · have hpos : CollPos M X AtColl g k d := ⟨hσ, .inl ⟨e, he, hc⟩⟩
    rw [hF hg hpos]
    obtain ⟨t, ins, o, hAt, hinv', hins, hf⟩ := Frame.fired_site hsound hX he hσ
    obtain ⟨s, hs, hk⟩ := fires_shape hf hc
    rcases ((hS hg hpos).2 t ins hAt hinv' hins).2 with ⟨f, h⟩ | h
    · rw [h] at hs; cases hs
    · rw [hk, ← hs, h]
  · have hpos : CollPos M X AtColl g (X.tr g).length d := ⟨hσ, .inr ⟨rfl, hd⟩⟩
    obtain ⟨hpc, -, -, hfault, -⟩ := id hAt
    rw [show ((X.tr g).countP isWarpColl) = ((X.tr g).take (X.tr g).length).countP isWarpColl by
      rw [List.take_length], hF hg hpos]
    unfold out at hout
    rw [hfault] at hout
    simp only [hpc] at hout ⊢
    cases hins : K.code[(M.code g).pc d]? with
    | none => rw [hins] at hout; cases hout; exact .inl ⟨_, rfl⟩
    | some ins =>
      rw [hins] at hout
      obtain ⟨hloc, hsh⟩ := (hS hg hpos).2 t ins hAt hinv hins
      simp only [hloc, Bool.false_eq_true, ite_false] at hout
      split at hout
      · cases hout; exact .inl ⟨_, rfl⟩
      · cases hout
      · simp only [Out.ev.injEq] at hout
        subst hout
        rcases hsh with h | h
        · exact .inl h
        · exact .inr ⟨trivial, h⟩
  · classical
    let Ex : κ → Nat → Prop := fun c n => ∃ g k pc, ∃ d : (M.code g).D, g < L.threads ∧ key g = c ∧
      Frame.stateAt M.code X g k = some (some d) ∧ X.get (g, k) = some ⟨pc, .exit⟩ ∧
      ((X.tr g).take k).countP isWarpColl = n
    refine ⟨fun c => if h : ∃ n, Ex c n then Nat.find h else
      ((Finset.range L.threads).sup fun g => (X.tr g).countP isWarpColl) + 1, ?_, ?_⟩
    · intro g d hg hσ hd
      by_cases h : ∃ n, Ex (key g) n
      · simp only [h, dite_true]
        obtain ⟨h', k, pc, d', hh, hk, hσ', he, hn⟩ := Nat.find_spec h
        rw [← hn]
        exact (hp (hkey hg hh hk.symm)).exit hσ hd hσ' he
      · simp only [h, dite_false]
        have := Finset.le_sup (f := fun g => (X.tr g).countP isWarpColl) (Finset.mem_range.mpr hg)
        omega
    · intro g k pc d hg hσ he
      have h : ∃ n, Ex (key g) n := ⟨_, g, k, pc, d, hg, rfl, hσ, he, rfl⟩
      simp only [h, dite_true]
      exact Nat.find_min' h ⟨g, k, pc, d, hg, rfl, hσ, he, rfl⟩

end
end PTX.Sched
