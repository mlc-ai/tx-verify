-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LkSkel

@[expose] public section

/-!
# Warp lockstep: a value of the state at the synchronizing ordinals

`Lock` (`LkSkel.lean`) says that the lanes of a warp are at one position at their `n`-th
synchronizing states. A state also carries values that steer the program (the loader's and the
MMA warp's iteration counters). A function `xs` of the state that is constant along the silent
steps (`hsil`) and whose value after a synchronizing step is a function `stepF` of the
synchronizing state (`hstp`) has, at the next synchronizing state of a thread, the value `stepF`
of the previous one (`next_sync_field`). `field_lock` is the induction over the ordinals: if the
lanes of a warp are at one position at every ordinal up to `n` and agree on `stepF` where their
states agree on `xs`, their `xs` agree at the `n`-th synchronizing states.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow
open Classical

noncomputable section

variable {Q : Params} {L : Launch} {X : Execution} {κ : Type}

/-- **A function of the state that is constant along silent steps is constant along a stretch of
states that are not synchronizing.** -/
theorem chainF (sk : Skel Q L κ) (ht : Frame.Tracked (code L Q) X) {β : Type} (xs : TSt → β)
    (hsil : ∀ {g : Nat} {s : TSt} {e : Event} {t : TSt}, g < L.threads → ¬ sk.sy s →
      (threadCode L g Q).next s e = some (some t) → xs t = xs s)
    {g j0 : Nat} (hg : g < L.threads) {s0 : TSt} (h0 : St Q L X g j0 = some (some s0)) :
    ∀ a, j0 ≤ a → a ≤ (X.tr g).length → (∀ i, j0 ≤ i → i < a → ¬ IsSy sk X g i) →
      ∀ s, St Q L X g a = some (some s) → xs s = xs s0 := by
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
    rw [hsil hg hnsy hn]
    exact hk

variable (sk : Skel Q L κ) (ht : Frame.Tracked (code L Q) X) {β : Type} (xs stepF : TSt → β)
    (hsil : ∀ {g : Nat} {s : TSt} {e : Event} {t : TSt}, g < L.threads → ¬ sk.sy s →
      (threadCode L g Q).next s e = some (some t) → xs t = xs s)
    (hstp : ∀ {g : Nat} {s : TSt} {e : Event} {t : TSt}, g < L.threads → sk.sy s →
      (threadCode L g Q).next s e = some (some t) → xs t = stepF s)
include sk ht xs stepF hsil hstp

/-- **The value at the next synchronizing state is the successor value of the synchronizing
state before it.** The synchronizing state `sa` is at `a'`, the next one `s` at `a`. -/
theorem next_sync_field {g a' a : Nat} (hg : g < L.threads) {sa s : TSt} {e : Event}
    (hsa : St Q L X g a' = some (some sa)) (hsy : sk.sy sa) (he : (X.tr g)[a']? = some e)
    (hs : St Q L X g a = some (some s)) (ha : a ≤ (X.tr g).length) (hlt : a' < a)
    (hno : ∀ i, a' < i → i < a → ¬ IsSy sk X g i) : xs s = stepF sa := by
  obtain ⟨ta, hta⟩ : ∃ ta, St Q L X g (a' + 1) = some (some ta) := by
    obtain ⟨d', hd'⟩ := Frame.stateAt_live (C := code L Q) ht hg hs (show a' + 1 ≤ a by omega)
    exact ⟨d', hd'⟩
  have hn := next_of_st_succ he hsa hta
  have h1 := chainF sk ht xs hsil hg hta a (by omega) ha (fun i h1 h2 => hno i (by omega) h2) s hs
  rw [h1]
  exact hstp hg hsy hn

/-- **The induction over the ordinals**: if the lanes of a warp are at one position at every
ordinal up to `n`, start with equal values, and agree on the successor value whenever their
states at a synchronizing event agree on the value, their values agree at the `n`-th
synchronizing states. -/
theorem field_lock
    (hinit : ∀ {g h : Nat}, SameWarp L g h →
      xs (threadCode L g Q).init = xs (threadCode L h Q).init)
    (hpair : ∀ {g h a b : Nat} {sa sb t t' : TSt} {e e' : Event}, SameWarp L g h →
      a ≤ (X.tr g).length → b ≤ (X.tr h).length → St Q L X g a = some (some sa) →
      St Q L X h b = some (some sb) → (X.tr g)[a]? = some e → (X.tr h)[b]? = some e' →
      (threadCode L g Q).next sa e = some (some t) →
      (threadCode L h Q).next sb e' = some (some t') →
      sk.sy sa → sk.sy sb → sk.key g sa = sk.key h sb → xs sa = xs sb → stepF sa = stepF sb) :
    ∀ n, (∀ m, m ≤ n → Lock sk X m) → ∀ {g h a b : Nat} {s s' : TSt}, SameWarp L g h →
      a ≤ (X.tr g).length → b ≤ (X.tr h).length → St Q L X g a = some (some s) →
      St Q L X h b = some (some s') → sk.sy s → sk.sy s' → syN sk X g a = n → syN sk X h b = n →
      xs s = xs s' := by
  intro n
  induction n with
  | zero =>
    intro _ g h a b s s' hw ha hb hs hs' _ _ hn hn'
    have hg : g < L.threads := hw.1.1
    have hh : h < L.threads := hw.1.2.1
    have h0g : St Q L X g 0 = some (some (threadCode L g Q).init) := Frame.stateAt_zero
    have h0h : St Q L X h 0 = some (some (threadCode L h Q).init) := Frame.stateAt_zero
    have k1 := chainF sk ht xs hsil hg h0g a (Nat.zero_le _) ha (no_sy_of_zero sk g hn) s hs
    have k2 := chainF sk ht xs hsil hh h0h b (Nat.zero_le _) hb (no_sy_of_zero sk h hn') s' hs'
    rw [k1, k2]
    exact hinit hw
  | succ n ih =>
    intro hL g h a b s s' hw ha hb hs hs' hsy hsy' hn hn'
    have hg : g < L.threads := hw.1.1
    have hh : h < L.threads := hw.1.2.1
    obtain ⟨a', ha', hsa', hna', hno⟩ := exists_prev sk (X := X) g ⟨s, hs, hsy⟩ hn
    obtain ⟨b', hb', hsb', hnb', hno'⟩ := exists_prev sk (X := X) h ⟨s', hs', hsy'⟩ hn'
    obtain ⟨sa, hsa, hsya⟩ := hsa'
    obtain ⟨sb, hsb, hsyb⟩ := hsb'
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[a']? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨e', he'⟩ : ∃ e', (X.tr h)[b']? = some e' :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hkey : sk.key g sa = sk.key h sb :=
      hL n (by omega) hw (by omega) (by omega) hsa hsb hsya hsyb hna' hnb'
    have hih := ih (fun m hm => hL m (by omega)) hw (by omega) (by omega) hsa hsb hsya hsyb hna'
      hnb'
    obtain ⟨ta, hta⟩ : ∃ ta, St Q L X g (a' + 1) = some (some ta) := by
      obtain ⟨d', hd'⟩ := Frame.stateAt_live (C := code L Q) ht hg hs (show a' + 1 ≤ a by omega)
      exact ⟨d', hd'⟩
    obtain ⟨tb, htb⟩ : ∃ tb, St Q L X h (b' + 1) = some (some tb) := by
      obtain ⟨d', hd'⟩ := Frame.stateAt_live (C := code L Q) ht hh hs' (show b' + 1 ≤ b by omega)
      exact ⟨d', hd'⟩
    have hp := hpair hw (by omega) (by omega) hsa hsb he he' (next_of_st_succ he hsa hta)
      (next_of_st_succ he' hsb htb) hsya hsyb hkey hih
    have k1 := next_sync_field sk ht xs stepF hsil hstp hg hsa hsya he hs ha ha' hno
    have k2 := next_sync_field sk ht xs stepF hsil hstp hh hsb hsyb he' hs' hb hb' hno'
    rw [k1, k2]
    exact hp

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
