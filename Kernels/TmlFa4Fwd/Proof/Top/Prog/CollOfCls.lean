-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Start0
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.CollCommon
import Kernels.TmlFa4Fwd.Proof.Common.NoUb
import Kernels.TmlFa4Fwd.Proof.Common.NoUb0
import Kernels.TmlFa4Fwd.Proof.Common.Sound

@[expose] public section

/-! # The collectives of two lanes of a warp, from a classification of its states

`warpPair_of_cls`: the facts of two lanes (`Sched.WarpPair`) from the collective a state is at
(`tag`), a relation of the number of collectives, the time and the tag that orders the lanes
(`cls`, `order`), and the facts of a lane's blocking events. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

/-- A lane whose last event is a register request it does not wait for is released. -/
theorem released_of_setMax (hX : Consistent L kernel Assumptions.all m X) (hh : h < L.threads)
    {pc i n : Nat} {inc : Bool}
    (he : X.get (h, (X.tr h).length - 1) = some ⟨pc, .setMaxReg inc n i⟩)
    (hr : ¬ Sched.RegWait L X h) : Step.Released L X h := by
  by_contra hnr
  rcases Sched.thread_cases hX hh (fun pc n hk' => by
      rw [he] at hk'; cases hk') hnr with h | h | h | h | h | h | h
  · obtain ⟨pc, op, hk', -⟩ := h
    rw [he] at hk'; cases hk'
  · exact hr h
  · obtain ⟨pc, grp, dst, act, hk', -⟩ := h
    rw [he] at hk'; cases hk'
  · obtain ⟨id, c', pc, -, hk', -⟩ := h
    change X.get _ = _ at hk'
    rw [he] at hk'; cases hk'
  · obtain ⟨k, -, ⟨⟨ev, hk', hcl⟩, -⟩, -⟩ := h
    rw [he] at hk'; cases hk'
    cases hcl
  · obtain ⟨pc, id, c', hk', -⟩ := h
    rw [he] at hk'; cases hk'
  · obtain ⟨pc, md, n, hk', -⟩ := h
    rw [he] at hk'; cases hk'

/-- A blocking event of a released lane is ready. -/
theorem ready_of_rel (hX : Consistent L kernel Assumptions.all m X) {y j : Nat} {e : Event}
    (he : X.get (y, j) = some e) (hk : e.kind.resume = .blocking false)
    (hrel : Step.Released L X y) : Ready L X (y, j) := by
  have hl : j < (X.tr y).length := (List.getElem?_eq_some_iff.mp he).1
  rcases Nat.lt_or_ge (j + 1) (X.tr y).length with h1 | h1
  · refine hX.dependency.ready _ ?_
    unfold Returned
    rw [he]
    split
    · rename_i heq
      obtain rfl := Option.some.inj heq
      cases hk
    · rename_i ev _ heq
      obtain rfl := Option.some.inj heq
      rw [hk]
      exact h1
    · rename_i heq
      cases heq
  · obtain rfl : j = (X.tr y).length - 1 := by omega
    exact hrel.ready _ _ he hk

/-- The startup does not exit. -/
theorem start_not_exit {y pc : Nat} {s : Startup.D} (hx : exit L y s = none)
    (hev : Startup.Ev L y s ⟨pc, .exit⟩) : False := by
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site
  case enter r => simp [exit] at hx
  case sh j => fin_cases j <;> simp [Startup.Ev] at hev
  all_goals simp [Startup.Ev] at hev

/-- **A blocking event of the startup** of a warp but 0: the startup goes on past its shuffles, or
enters its role. -/
theorem start_last (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {w : Nat}
    (hw : Prologue.warpIndex L h = w) (h0 : w ≠ 0) (h16 : w < 2 ^ 31) {i : Nat} {s : Startup.D}
    {n : Cls → Nat} {e : Event}
    (he : X.get (h, i) = some e) (hσ : Frame.stateAt (thread p L) X h i = some (some (.inl s, n)))
    (hS : StartAt L w s n) (hb : ¬ Sched.Unblocking e.kind) :
    (thread p L h).next (.inl s, n) e ≠ none ∧
      ∀ σ', (thread p L h).next (.inl s, n) e = some (some σ') →
        (∃ s', σ'.1 = .inl s' ∧ ∀ j, s'.site ≠ .sh j) ∨
        ∃ i, σ'.1 = .inr ⟨i, (frag p L h i).init⟩ := by
  obtain ⟨hev, -⟩ := start_fired hp hX he hσ
  have hbar : s.site = .bar := by
    obtain ⟨site, x1, x2, x3⟩ := s
    by_contra hnb
    cases site <;> simp only [StartAt] at hS
    case sh j =>
      apply hb
      fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk⟩ := hev <;> rw [hk] <;>
        trivial
    case fence =>
      apply hb
      simp only [Startup.Ev] at hev
      rw [hev]; trivial
    case bar => exact hnb rfl
  refine ⟨fun hn => hb ?_, fun σ' hσ' => ?_⟩
  · have := start_live hp hX he hσ hS hn
    rw [this]; trivial
  · rcases (start_next hp hw h0 h16 hS hev
      (fun j hj => by rw [hbar] at hj; cases hj)).2 σ' hσ' with ⟨s', hs', hS'⟩ | ⟨-, hen⟩
    · left
      obtain ⟨-, hbump⟩ := Code.counted_next_some (C := glued p L h) hσ'
      obtain ⟨σ', n'⟩ := σ'
      simp only at hs' hS' hbump
      subst hs'
      refine ⟨s', rfl, fun j hj => ?_⟩
      obtain ⟨site, x1, x2, x3⟩ := s
      obtain ⟨site', y1, y2, y3⟩ := s'
      simp only at hbar hj
      subst hbar
      subst hj
      simp only [StartAt] at hS hS'
      have h3 : n .shfl ≤ n' .shfl := by
        rw [hbump]; simp only [Code.bump]; omega
      have := j.isLt
      omega
    · rw [hen]
      unfold Code.enter
      cases exit L h (Startup.enterOf s) with
      | none =>
        refine .inl ⟨_, rfl, fun j hj => ?_⟩
        obtain ⟨r, hr⟩ := enterOf_isEnter s
        rw [hr] at hj; cases hj
      | some r => exact .inr ⟨r, rfl⟩

/-- The barrier enters a role, from its startup state. -/
theorem bar_last {s : Startup.D} {n : Cls → Nat} {e : Event} (hs : s.site = .bar)
    {σ' : (thread p L h).D} (hn : (thread p L h).next (.inl s, n) e = some (some σ')) :
    (∃ s' : Startup.D, σ'.1 = .inl s' ∧ ∃ r, s'.site = .enter r) ∨
      ∃ i, σ'.1 = .inr ⟨i, (frag p L h i).init⟩ := by
  obtain ⟨h1, -⟩ := Code.counted_next_some (C := glued p L h) hn
  have hsu : Startup.succ L h s e = some (some (Startup.enterOf s)) := by
    obtain ⟨site, x1, x2, x3⟩ := s
    simp only at hs
    subst hs
    rfl
  simp only [glued, Code.glue, Startup.code, hsu, Option.map_some, Option.some.injEq] at h1
  rw [← h1]
  unfold Code.enter
  split
  · exact .inr ⟨_, rfl⟩
  · exact .inl ⟨_, rfl, enterOf_isEnter s⟩

/-- **A blocking event of the startup of warp 0**: the barrier, which enters a role. -/
theorem start_last0 (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {i : Nat} {s : Startup.D} {n : Cls → Nat} {e : Event}
    (he : X.get (h, i) = some e) (hσ : Frame.stateAt (thread p L) X h i = some (some (.inl s, n)))
    (hS : StartAt0 L s n) (hne : ∀ f, e.kind ≠ .ub f) (hb : ¬ Sched.Unblocking e.kind) :
    (thread p L h).next (.inl s, n) e ≠ none ∧ s.site = .bar := by
  refine ⟨fun hn => hb ?_, ?_⟩
  · rw [start0_live hp hX he hσ hS hne hn]; trivial
  · obtain ⟨hev, -⟩ := start_fired hp hX he hσ
    by_contra hnb
    apply hb
    obtain ⟨site, x1, x2, x3⟩ := s
    obtain ⟨pc, kind⟩ := e
    cases site with
    | sh j =>
      fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk⟩ := hev <;> rw [hk] <;>
        trivial
    | fence => simp only [Startup.Ev] at hev; rw [hev]; trivial
    | bar => exact absurd rfl hnb
    | elect j =>
      simp only [Startup.Ev] at hev
      rcases hev with ⟨_, _, -, hk⟩ | ⟨_, hk⟩ <;> rw [hk] <;> trivial
    | init q =>
      simp only [Startup.Ev] at hev
      rcases hev with ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> rw [hk] <;> trivial
    | enter r => simp [StartAt0] at hS

/-- **The classification of the states of the lanes `A` of one warp** by their collectives. -/
structure CollCls (p : Params) (L : Launch) (X : Execution) (A : Nat → Prop)
    (S : ∀ g, (thread p L g).D → Sched.CollShape) (T : Type) where
  /-- The collective a state is at. -/
  tag : ∀ x, (thread p L x).D → Option T
  /-- Whether a collective is of the role, past its entry. -/
  role : T → Prop
  /-- What a state's number of collectives, time and collective satisfy. -/
  cls : Nat → Nat → Nat → Option T → Prop
  at_ : ∀ {x k σ}, A x → Frame.stateAt (thread p L) X x k = some (some σ) →
    (CollAt p L x σ ↔ (tag x σ).isSome = true)
  pos : ∀ {x k σ}, A x → Sched.CollPos (Progress.timed p L) X (CollAt p L) x k σ →
    (tag x σ).isSome = true
  ok : ∀ {x k σ}, A x → Frame.stateAt (thread p L) X x k = some (some σ) →
    cls x (((X.tr x).take k).countP Sched.isWarpColl) (Progress.time p L x σ) (tag x σ)
  order : ∀ {x y N N' t t' a o}, A x → A y → cls x N t (some a) → cls y N' t' o → N' ≤ N →
    t' < t ∨ (N' = N ∧ o = some a ∧ t' = t)
  static : ∀ {x y k k' σ σ' a}, A x → A y → Frame.stateAt (thread p L) X x k = some (some σ) →
    Frame.stateAt (thread p L) X y k' = some (some σ') → tag x σ = some a → tag y σ' = some a →
    (thread p L x).pc σ = (thread p L y).pc σ' ∧ S x σ = S y σ'
  exit : ∀ {x y N t a k pc σ}, A x → A y → cls x N t (some a) →
    Frame.stateAt (thread p L) X y k = some (some σ) → X.get (y, k) = some ⟨pc, .exit⟩ →
    N < ((X.tr y).take k).countP Sched.isWarpColl
  entry : ∀ {x k σ a}, A x → Frame.stateAt (thread p L) X x k = some (some σ) →
    tag x σ = some a → role a → ∃ i d n, σ = (.inr ⟨i, d⟩, n) ∧ ¬ IsEntry i d
  last : ∀ {x k σ e}, A x → X.get (x, k) = some e →
    Frame.stateAt (thread p L) X x k = some (some σ) → ¬ Sched.Unblocking e.kind →
    (thread p L x).next σ e ≠ none ∧ ∀ σ', (thread p L x).next σ e = some (some σ') →
      tag x σ' = none ∨ ∃ a, tag x σ' = some a ∧ role a ∧
        ((∃ inc n i, e.kind = .setMaxReg inc n i) ∨
          ∀ y σy, A y → SameWarp L y x → k + 1 = (X.tr x).length →
            Frame.stateAt (thread p L) X y (X.tr y).length = some (some σy) → tag y σy = some a →
            (X.tr x).countP Sched.isWarpColl = (X.tr y).countP Sched.isWarpColl →
            Step.Released L X y → (∀ i pc, X.get (x, i) ≠ some ⟨pc, .exit⟩) →
            Ready L X (x, k))

/-- **The collectives of two lanes of a warp**, from a classification. -/
theorem warpPair_of_cls (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hub : ¬ HasUb X) {A : Nat → Prop}
    {S : ∀ g, (thread p L g).D → Sched.CollShape} {T : Type} (C : CollCls p L X A S T)
    (hs : SameWarp L g h) (hAg : A g) (hAh : A h) :
    Sched.WarpPair m (Progress.timed p L) X (CollAt p L) S g h := by
  have hg := hs.1.1
  have hh := hs.1.2.1
  refine ⟨fun {k k' σ σ'} hP hP' hn => ?_, fun {σ σ'} hσ hcg hσ' hch hn hrel => ?_,
    fun {k pc σ σ'} hσ hcg hσ' he => ?_, fun {σ} hσ hcg hle hno hnn => ?_, fun hph hσ' => ?_⟩
  · -- one position, one static part
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (C.pos hAg hP)
    obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.mp (C.pos hAh hP')
    have c1 := C.ok hAg hP.1
    have c2 := C.ok hAh hP'.1
    rw [hx] at c1
    rw [hx'] at c2
    have hxx : x' = x := by
      rcases C.order hAg hAh c1 c2 hn.ge with h1 | ⟨-, h1, -⟩
      · rcases C.order hAh hAg c2 c1 hn.le with h2 | ⟨-, h2, -⟩
        · omega
        · exact (Option.some.inj h2).symm
      · exact Option.some.inj h1
    subst hxx
    exact C.static hAg hAh hP.1 hP'.1 hx hx'
  · -- released
    left
    by_contra hnr
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ((C.at_ hAg hσ).mp hcg)
    obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.mp ((C.at_ hAh hσ').mp hch)
    have hlen : 0 < (X.tr h).length := by
      by_contra h0
      exact hnr (Sched.released_nil (List.length_eq_zero_iff.mp
        (show (X.tr h).length = 0 by omega)))
    obtain ⟨e, he⟩ : ∃ e, X.get (h, (X.tr h).length - 1) = some e :=
      ⟨_, List.getElem?_eq_getElem
        (show (X.tr h).length - 1 < (X.tr h).length by omega)⟩
    have hne : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := fun pc f hf => hub ⟨_, pc, f, by rw [he, hf]⟩
    obtain ⟨σ0, hσ0, -⟩ := good_state hp hX he hne (goodR' hp hX hh _)
    have hun : ¬ Sched.Unblocking e.kind := fun hu => hnr (Sched.released_of_unblocking he hu)
    have hσ1 : Frame.stateAt (thread p L) X h ((X.tr h).length - 1 + 1) = some (some σ') := by
      rw [show (X.tr h).length - 1 + 1 = (X.tr h).length by omega]; exact hσ'
    rw [Frame.stateAt_succ (C := thread p L) (show (X.tr h)[(X.tr h).length - 1]? = some e
        from he), hσ0] at hσ1
    rcases (C.last hAh he hσ0 hun).2 σ' hσ1 with h1 | ⟨a, ha, hr, hcase⟩
    · rw [hx'] at h1; cases h1
    · have c1 := C.ok hAg hσ
      have c2 := C.ok hAh hσ'
      rw [List.take_length, hx] at c1
      rw [List.take_length, ha, hn] at c2
      have hxa : x = a := by
        rcases C.order hAg hAh c1 c2 le_rfl with h1 | ⟨-, h1, -⟩
        · rcases C.order hAh hAg c2 c1 le_rfl with h2 | ⟨-, h2, -⟩
          · omega
          · exact Option.some.inj h2
        · exact (Option.some.inj h1).symm
      subst hxa
      rcases hcase with ⟨inc, nn, i, hk⟩ | hrd
      · obtain ⟨i', d, n, rfl, hE⟩ := C.entry hAg hσ hx hr
        obtain ⟨pc, kd⟩ := e
        simp only at hk
        subst hk
        exact hnr (released_of_setMax hX hh he (not_regWait hp hX hub hs hσ hE hrel))
      · refine hnr ⟨fun _ _ _ _ => ?_⟩
        refine hrd g σ hAg hs (by omega) hσ hx hn hrel fun i pc hi => ?_
        obtain ⟨σi, hσi, -⟩ := good_state hp hX hi (fun _ _ h => by cases h) (goodR' hp hX hh i)
        have h1 := C.exit hAh hAh c2 hσi hi
        have h2 := (List.take_sublist i (X.tr h)).countP_le (p := Sched.isWarpColl)
        omega
  · -- exit
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ((C.at_ hAg hσ).mp hcg)
    have c1 := C.ok hAg hσ
    rw [List.take_length, hx] at c1
    exact C.exit hAg hAh c1 hσ' he
  · -- lag
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ((C.at_ hAg hσ).mp hcg)
    have c1 := C.ok hAg hσ
    rw [List.take_length, hx] at c1
    cases hσ' : Frame.stateAt (thread p L) X h (X.tr h).length with
    | none => exact absurd hσ' hnn
    | some o =>
      cases o with
      | none => exact absurd hσ' (goodR' hp hX hh _).1
      | some σ' =>
        have c2 := C.ok hAh hσ'
        rw [List.take_length] at c2
        refine lt_of_eq_of_lt (Sched.threadTime_of (M := Progress.timed p L) hσ') ?_
        rcases C.order hAg hAh c1 c2 hle with h1 | ⟨h1, h2, -⟩
        · exact h1
        · exact (hno ⟨h1, σ', hσ', (C.at_ hAh hσ').mpr (by rw [h2]; rfl)⟩).elim
  · -- a stopped lane is released
    by_contra hnr
    obtain ⟨i, σ, hi, h1, h2⟩ := Frame.first_stop (C := thread p L)
      (fun x k hx => (goodR' hp hX hx k).1) hh hσ'
    have hlt : i + 1 = (X.tr h).length := by
      by_contra hne
      obtain ⟨e, he⟩ : ∃ e, X.get (h, i + 1) = some e :=
        ⟨_, List.getElem?_eq_getElem (show i + 1 < (X.tr h).length by omega)⟩
      rcases Frame.firedU (C := thread p L) (fun g hg => thread_sound hp hg) hX he with
        ⟨σ', o, h3, -⟩ | ⟨-, pc, f, rfl⟩
      · rw [h2] at h3; cases h3
      · exact hub ⟨_, pc, f, he⟩
    obtain ⟨e, he⟩ : ∃ e, X.get (h, i) = some e := ⟨_, List.getElem?_eq_getElem hi⟩
    have hun : ¬ Sched.Unblocking e.kind := fun hu => hnr (Sched.released_of_unblocking
      (show X.get (h, (X.tr h).length - 1) = some e by
        rw [show (X.tr h).length - 1 = i by omega]; exact he) hu)
    rw [Frame.stateAt_succ (C := thread p L) (show (X.tr h)[i]? = some e from he), h1] at h2
    exact (C.last hAh he h1 hun).1 h2

end
end PTX.Kernels.TmlFa4Fwd.Proof.Top
