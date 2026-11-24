-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Basic

@[expose] public section

/-! # From pairwise agreement of lanes to functions of the warp

A proof tool for facts stated with a function of a warp's key ("the object of a poll is
`R key pc round`"). Such a function exists as soon as any two threads with one key that both
relate a point to a value relate it to the same value (`exists_fun_of_agree`): it picks the
value of some thread. Two lists that agree at every index where both have an entry are one a
prefix of the other (`prefix_of_agree`). A bound fixed by the key that a thread's exit count
reaches and every ordinal stays below exists when the threads' exit counts agree and each exceeds
every ordinal of the key's threads (`exists_bound_of_exit`). -/

namespace PTX.Flow

/-- **A function of the key** exists when threads with one key relate each point to one
value. -/
theorem exists_fun_of_agree {κ α β : Type} [Inhabited β] (key : Nat → κ)
    (R : Nat → α → β → Prop)
    (hagree : ∀ {g h a b b'}, key g = key h → R g a b → R h a b' → b = b') :
    ∃ F : κ → α → β, ∀ {g a b}, R g a b → F (key g) a = b := by
  classical
  refine ⟨fun k a => if h : ∃ g b, key g = k ∧ R g a b then h.choose_spec.choose else default,
    fun {g a b} hR => ?_⟩
  beta_reduce
  split
  · rename_i hex
    obtain ⟨hk, hR'⟩ := hex.choose_spec.choose_spec
    exact hagree hk hR' hR
  · rename_i hne
    exact absurd ⟨g, b, rfl, hR⟩ hne

/-- **Two lists that agree where both have entries are one a prefix of the other.** -/
theorem prefix_of_agree {α : Type} {l1 l2 : List α}
    (h : ∀ (n : Nat) (x y : α), l1[n]? = some x → l2[n]? = some y → x = y) :
    l1 <+: l2 ∨ l2 <+: l1 := by
  induction l1 generalizing l2 with
  | nil => exact .inl (List.nil_prefix)
  | cons a l1 ih =>
    cases l2 with
    | nil => exact .inr (List.nil_prefix)
    | cons b l2 =>
      have hab : a = b := h 0 a b rfl rfl
      subst hab
      rcases ih (fun n x y hx hy => h (n + 1) x y hx hy) with hp | hp
      · exact .inl (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
      · exact .inr (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)

/-- **A bound fixed by the key**: when the threads of a key that reach their exit reach it with
one count, above every ordinal of the key's threads, some number fixed by the key is above every
ordinal of its threads and at most each exit count. Threads are those below `n`; `ord g o` says
thread `g` has an event of ordinal `o`, each thread's ordinals being below `top g`. -/
theorem exists_bound_of_exit {κ : Type} (key : Nat → κ) (n : Nat) (ord : Nat → Nat → Prop)
    (top : Nat → Nat) (htop : ∀ {g o}, g < n → ord g o → o < top g)
    (exitc : Nat → Nat → Prop)
    (hagree : ∀ {g h c c'}, g < n → h < n → key g = key h → exitc g c → exitc h c' →
      c = c')
    (habove : ∀ {g h c o}, g < n → h < n → key g = key h → exitc h c → ord g o →
      o < c) :
    ∃ T : κ → Nat, (∀ {g o}, g < n → ord g o → o < T (key g)) ∧
      (∀ {g c}, g < n → exitc g c → T (key g) ≤ c) := by
  classical
  let M : Nat := (Finset.range n).sup top
  refine ⟨fun k => if h : ∃ g c, g < n ∧ key g = k ∧ exitc g c then h.choose_spec.choose
      else M,
    fun {g o} hg ho => ?_, fun {g c} hg hc => ?_⟩
  · beta_reduce
    split
    · rename_i hex
      obtain ⟨hg', hk, hc⟩ := hex.choose_spec.choose_spec
      exact habove hg hg' hk.symm hc ho
    · have h1 := htop hg ho
      have h2 : top g ≤ M := Finset.le_sup (f := top) (Finset.mem_range.mpr hg)
      omega
  · beta_reduce
    split
    · rename_i hex
      obtain ⟨hg', hk, hc'⟩ := hex.choose_spec.choose_spec
      exact (hagree hg' hg hk hc' hc).le
    · rename_i hne
      exact absurd ⟨g, c, hg, rfl, hc⟩ hne

end PTX.Flow
