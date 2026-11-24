-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Output
public import Kernels.InklingRelDecode.Proof.Interface.LockBar0

@[expose] public section

/-!
# Warp lockstep: the skeleton of the synchronizing states

The lanes of a warp run one program. The machine of a lane differs from its neighbour's only
through `laneOf` (the `elect.sync` guards), the thread index (the lane that arrives on
`p_ready`, the masks of the bias loads) and values the lanes read or exchange (the role byte, the
loop counters, the shuffle minimum). Between two *synchronizing* events (a barrier, a warp
collective, a `tcgen05` collective, a register request, the dispatch of a role) every lane runs a
stretch of states that fire no synchronizing event, and the stretch ends at the same synchronizing
site for all lanes.

`Skel` is the data of that argument for a machine family: the synchronizing states `sy`, a `key`
of every state (the site of the next synchronizing state), and three obligations: a state
that is not synchronizing keeps the key through any step (`silent`), a synchronizing state is its
own key (`pc_key`), and the keys of two lanes' synchronizing states that have the same key and
agree on what steers the successor (`agree`) have successors with the same key (`step`). The first
state of the lanes of a warp have one key (`init`).

`lock_all` is the induction: the lanes' `n`-th synchronizing states are at one site. The agreement
at the `n`-th synchronizing event may use the equal sites of all lanes up to the `n`-th (the
values a shuffle returns are the operands of other lanes' instances at the same position).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow
open Classical

noncomputable section

/-- **The skeleton of a machine family.** -/
structure Skel (Q : Params) (L : Launch) (κ : Type) where
  /-- The state's event is a synchronizing event. -/
  sy : TSt → Prop
  /-- The site (program counter) of the next synchronizing state, for any state. -/
  key : Nat → TSt → κ
  /-- The program position a key stands for. -/
  pcOf : κ → Nat
  /-- The relation two lanes' synchronizing events must satisfy for their successors to agree:
  the lanes `g`, `h`, their states and events. -/
  agree : Nat → Nat → TSt → TSt → Event → Event → Prop
  init : ∀ {g h : Nat}, SameWarp L g h →
    key g (threadCode L g Q).init = key h (threadCode L h Q).init
  pc_key : ∀ {g : Nat} {s : TSt}, sy s → pcOf (key g s) = TSt.pc s
  silent : ∀ {g : Nat} {s : TSt} {e : Event} {t : TSt}, g < L.threads → ¬ sy s →
    (threadCode L g Q).next s e = some (some t) → key g t = key g s
  step : ∀ {g h : Nat} {s s' : TSt} {e e' : Event} {t t' : TSt}, SameWarp L g h →
    (s.isD ↔ g % L.block < 128) → (s'.isD ↔ h % L.block < 128) → sy s → sy s' →
    key g s = key h s' → agree g h s s' e e' →
    (threadCode L g Q).next s e = some (some t) → (threadCode L h Q).next s' e' = some (some t') →
    key g t = key h t'

variable {Q : Params} {L : Launch} {X : Execution} {κ : Type}

/-- Thread `g`'s state before its `k`-th event is a synchronizing state. -/
def IsSy (sk : Skel Q L κ) (X : Execution) (g k : Nat) : Prop :=
  ∃ s, St Q L X g k = some (some s) ∧ sk.sy s

/-- The number of synchronizing states among the first `k` states of thread `g`. -/
def syN (sk : Skel Q L κ) (X : Execution) (g k : Nat) : Nat :=
  ((Finset.range k).filter (fun j => IsSy sk X g j)).card

theorem syN_succ (sk : Skel Q L κ) (g k : Nat) :
    syN sk X g (k + 1) = syN sk X g k + if IsSy sk X g k then 1 else 0 := by
  unfold syN
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : IsSy sk X g k
  · simp only [h, ↓reduceIte]
    rw [Finset.card_insert_of_notMem]
    simp
  · simp [h]

theorem syN_mono (sk : Skel Q L κ) (g : Nat) {j k : Nat} (h : j ≤ k) :
    syN sk X g j ≤ syN sk X g k := by
  induction k, h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => rw [syN_succ]; omega

/-- A stretch without a synchronizing state does not change the count. -/
theorem syN_stretch (sk : Skel Q L κ) (g : Nat) {j k : Nat} (h : j ≤ k)
    (hn : ∀ i, j ≤ i → i < k → ¬ IsSy sk X g i) : syN sk X g k = syN sk X g j := by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    have hk' := hn k hk (by omega)
    rw [syN_succ]
    simp only [hk', ↓reduceIte]
    exact ih (fun i h1 h2 => hn i h1 (by omega))

/-- The synchronizing state before the one with count `n + 1` is the one with count `n`, and the
states between are not synchronizing. -/
theorem exists_prev (sk : Skel Q L κ) (g : Nat) {a n : Nat} (_hs : IsSy sk X g a)
    (hn : syN sk X g a = n + 1) :
    ∃ a', a' < a ∧ IsSy sk X g a' ∧ syN sk X g a' = n ∧
      ∀ i, a' < i → i < a → ¬ IsSy sk X g i := by
  have hex : ∃ j, j < a ∧ IsSy sk X g j := by
    by_contra hc
    push Not at hc
    have : syN sk X g a = 0 := by
      unfold syN
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j hj
      exact hc j (Finset.mem_range.mp hj)
    omega
  have hex' : ∃ j, j ≤ a - 1 ∧ IsSy sk X g j := by
    obtain ⟨j, hj, hp⟩ := hex
    exact ⟨j, by omega, hp⟩
  refine ⟨Nat.findGreatest (fun j => IsSy sk X g j) (a - 1), ?_, ?_, ?_, ?_⟩
  · have := Nat.findGreatest_le (P := fun j => IsSy sk X g j) (a - 1)
    obtain ⟨j, hj, -⟩ := hex
    omega
  · obtain ⟨j, hj, hp⟩ := hex'
    exact Nat.findGreatest_spec (P := fun j => IsSy sk X g j) hj hp
  · have hsp : IsSy sk X g (Nat.findGreatest (fun j => IsSy sk X g j) (a - 1)) := by
      obtain ⟨j, hj, hp⟩ := hex'
      exact Nat.findGreatest_spec (P := fun j => IsSy sk X g j) hj hp
    set a' := Nat.findGreatest (fun j => IsSy sk X g j) (a - 1) with ha'
    have hle : a' ≤ a - 1 := Nat.findGreatest_le _
    have h1 := syN_stretch sk (X := X) g (j := a' + 1) (k := a) (by omega) (fun i h1 h2 => by
      have := Nat.findGreatest_is_greatest (P := fun j => IsSy sk X g j) (n := a - 1)
        (k := i) (by omega) (by omega)
      exact this)
    have h2 := syN_succ sk (X := X) g a'
    simp only [hsp, ↓reduceIte] at h2
    omega
  · intro i hi1 hi2
    exact Nat.findGreatest_is_greatest (P := fun j => IsSy sk X g j) (n := a - 1) (k := i)
      (by omega) (by omega)

/-! ### The states along the trace -/

theorem next_of_st_succ {g k : Nat} {e : Event} {s t : TSt} (he : (X.tr g)[k]? = some e)
    (hs : St Q L X g k = some (some s)) (ht : St Q L X g (k + 1) = some (some t)) :
    (threadCode L g Q).next s e = some (some t) := by
  have h := Frame.stateAt_succ (C := code L Q) (X := X) (g := g) he
  have ht' : Frame.stateAt (code L Q) X g (k + 1) = some (some t) := ht
  have hs' : Frame.stateAt (code L Q) X g k = some (some s) := hs
  rw [h, hs'] at ht'
  exact ht'

/-- **The key is constant along a stretch of states that are not synchronizing.** -/
theorem chain (sk : Skel Q L κ) (ht : Frame.Tracked (code L Q) X) {g j0 : Nat} (hg : g < L.threads)
    {s0 : TSt} (h0 : St Q L X g j0 = some (some s0)) :
    ∀ a, j0 ≤ a → a ≤ (X.tr g).length → (∀ i, j0 ≤ i → i < a → ¬ IsSy sk X g i) →
      ∀ s, St Q L X g a = some (some s) → sk.key g s = sk.key g s0 := by
  intro a hle
  induction a, hle using Nat.le_induction with
  | base =>
    intro _ _ s hs
    rw [h0] at hs
    cases hs
    rfl
  | succ a hle ih =>
    intro ha hno s hs
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[a]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨sa, hsa⟩ : ∃ sa, St Q L X g a = some (some sa) := by
      obtain ⟨d', hd'⟩ := Frame.stateAt_live (C := code L Q) ht hg hs (show a ≤ a + 1 by omega)
      exact ⟨d', hd'⟩
    have hk := ih (by omega) (fun i h1 h2 => hno i h1 (by omega)) sa hsa
    have hn := next_of_st_succ he hsa hs
    have hnsy : ¬ sk.sy sa := fun h => hno a hle (by omega) ⟨sa, hsa, h⟩
    rw [sk.silent hg hnsy hn]
    exact hk

/-- The lanes' synchronizing states with count `n` have one key. -/
def Lock (sk : Skel Q L κ) (X : Execution) (n : Nat) : Prop :=
  ∀ {g h a b : Nat} {s s' : TSt}, SameWarp L g h → a ≤ (X.tr g).length → b ≤ (X.tr h).length →
    St Q L X g a = some (some s) → St Q L X h b = some (some s') → sk.sy s → sk.sy s' →
    syN sk X g a = n → syN sk X h b = n → sk.key g s = sk.key h s'

theorem no_sy_of_zero (sk : Skel Q L κ) (g : Nat) {a : Nat} (h : syN sk X g a = 0) :
    ∀ i, 0 ≤ i → i < a → ¬ IsSy sk X g i := by
  intro i _ hi hsi
  have h1 := syN_succ sk (X := X) g i
  have h2 := syN_mono sk (X := X) g (show i + 1 ≤ a by omega)
  simp only [hsi, ↓reduceIte] at h1
  omega

/-- The lanes of a warp are at one synchronizing site at each synchronizing event. -/
theorem lock_all (sk : Skel Q L κ) (ht : Frame.Tracked (code L Q) X)
    (hag : ∀ n, (∀ m, m ≤ n → Lock sk X m) → ∀ {g h a b : Nat} {s s' : TSt} {e e' : Event},
      SameWarp L g h → (X.tr g)[a]? = some e → (X.tr h)[b]? = some e' →
      St Q L X g a = some (some s) → St Q L X h b = some (some s') → sk.sy s → sk.sy s' →
      syN sk X g a = n → syN sk X h b = n → sk.key g s = sk.key h s' →
      sk.agree g h s s' e e') :
    ∀ n, Lock sk X n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g h a b s s' hw ha hb hs hs' hsy hsy' hn hn'
    have hg : g < L.threads := hw.1.1
    have hh : h < L.threads := hw.1.2.1
    cases n with
    | zero =>
      have h0g : St Q L X g 0 = some (some (threadCode L g Q).init) := Frame.stateAt_zero
      have h0h : St Q L X h 0 = some (some (threadCode L h Q).init) := Frame.stateAt_zero
      have k1 := chain sk ht hg h0g a (Nat.zero_le _) ha (no_sy_of_zero sk g hn) s hs
      have k2 := chain sk ht hh h0h b (Nat.zero_le _) hb (no_sy_of_zero sk h hn') s' hs'
      rw [k1, k2]
      exact sk.init hw
    | succ n =>
      obtain ⟨a', ha', hsa', hna', hno⟩ := exists_prev sk (X := X) g ⟨s, hs, hsy⟩ hn
      obtain ⟨b', hb', hsb', hnb', hno'⟩ := exists_prev sk (X := X) h ⟨s', hs', hsy'⟩ hn'
      obtain ⟨sa, hsa, hsya⟩ := hsa'
      obtain ⟨sb, hsb, hsyb⟩ := hsb'
      obtain ⟨e, he⟩ : ∃ e, (X.tr g)[a']? = some e :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨e', he'⟩ : ∃ e', (X.tr h)[b']? = some e' :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hpc : sk.key g sa = sk.key h sb :=
        ih n (by omega) hw (by omega) (by omega) hsa hsb hsya hsyb hna' hnb'
      have hag' := hag n (fun m hm => ih m (by omega)) hw he he' hsa hsb hsya hsyb hna' hnb' hpc
      -- the successors
      obtain ⟨ta, hta⟩ : ∃ ta, St Q L X g (a' + 1) = some (some ta) := by
        obtain ⟨d', hd'⟩ := Frame.stateAt_live (C := code L Q) ht hg hs
          (show a' + 1 ≤ a by omega)
        exact ⟨d', hd'⟩
      obtain ⟨tb, htb⟩ : ∃ tb, St Q L X h (b' + 1) = some (some tb) := by
        obtain ⟨d', hd'⟩ := Frame.stateAt_live (C := code L Q) ht hh hs'
          (show b' + 1 ≤ b by omega)
        exact ⟨d', hd'⟩
      have hna := next_of_st_succ he hsa hta
      have hnb := next_of_st_succ he' hsb htb
      have hk := sk.step hw (cls_inv a' sa (by omega) hsa) (cls_inv b' sb (by omega) hsb) hsya
        hsyb hpc hag' hna hnb
      have k1 := chain sk ht hg hta a (by omega) ha (fun i h1 h2 => hno i (by omega) h2) s hs
      have k2 := chain sk ht hh htb b (by omega) hb (fun i h1 h2 => hno' i (by omega) h2) s' hs'
      rw [k1, k2]
      exact hk

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
