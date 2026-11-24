-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LkSkel

@[expose] public section

/-!
# Warp lockstep: the events of a class at the same ordinal

A class of events (`c`: the barrier events, the `tcgen05` collectives) is a class of states
(`Cs`): the event fired from a state is in the class exactly when the state is. If the states of
the class are synchronizing and the class of a synchronizing state is a function of its key, then
the lanes of a warp, at synchronizing states of one ordinal, have made the same number of events
of the class (`lock_count`). So their `k`-th events of the class are the events of one ordinal,
at one key (`class_nth`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow
open Classical

noncomputable section

variable {Q : Params} {L : Launch} {X : Execution} {κ : Type}

/-- The number of events of the class before event `k` of a thread. -/
def cnt (c : Event → Bool) (X : Execution) (g k : Nat) : Nat := ((X.tr g).take k).countP c

theorem cnt_succ (c : Event → Bool) {g k : Nat} {e : Event} (he : (X.tr g)[k]? = some e) :
    cnt c X g (k + 1) = cnt c X g k + if c e = true then 1 else 0 := by
  unfold cnt
  rw [List.take_add_one, he]
  simp [List.countP_append]

/-- **The class's events and states agree**: the event fired from a state is in the class
exactly when the state is. -/
def ClassEv (c : Event → Bool) (Cs : TSt → Bool) (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event} {s : TSt}, g < L.threads → X.get (g, k) = some e →
    St Q L X g k = some (some s) → c e = Cs s

theorem cnt_stretch (sk : Skel Q L κ) (ht : Frame.Tracked (code L Q) X) {c : Event → Bool}
    {Cs : TSt → Bool} (hev : ClassEv c Cs Q L X) (hsy : ∀ {s}, Cs s = true → sk.sy s)
    {g a' aend : Nat} (hg : g < L.threads) {se : TSt} (hend : St Q L X g aend = some (some se))
    (hlen : aend ≤ (X.tr g).length) (hno : ∀ i, a' < i → i < aend → ¬ IsSy sk X g i) :
    ∀ a, a' + 1 ≤ a → a ≤ aend → cnt c X g a = cnt c X g (a' + 1) := by
  intro a hle
  induction a, hle using Nat.le_induction with
  | base => intro _; rfl
  | succ a hle ih =>
    intro ha
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[a]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨sa, hsa⟩ : ∃ sa, St Q L X g a = some (some sa) :=
      Frame.stateAt_live (C := code L Q) ht hg hend (show a ≤ aend by omega)
    rw [cnt_succ c he, ih (by omega)]
    have hnsy : ¬ sk.sy sa := fun h => hno a hle (by omega) ⟨sa, hsa, h⟩
    have hcs : Cs sa = false := by
      cases h : Cs sa
      · rfl
      · exact absurd (hsy h) hnsy
    have hge : X.get (g, a) = some e := he
    rw [hev hg hge hsa, hcs]
    simp

theorem cnt_zero (sk : Skel Q L κ) (ht : Frame.Tracked (code L Q) X) {c : Event → Bool}
    {Cs : TSt → Bool} (hev : ClassEv c Cs Q L X) (hsy : ∀ {s}, Cs s = true → sk.sy s)
    {g aend : Nat} (hg : g < L.threads) {se : TSt} (hend : St Q L X g aend = some (some se))
    (hlen : aend ≤ (X.tr g).length) (hno : ∀ i, i < aend → ¬ IsSy sk X g i) :
    ∀ a, a ≤ aend → cnt c X g a = 0 := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro ha
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[a]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨sa, hsa⟩ : ∃ sa, St Q L X g a = some (some sa) :=
      Frame.stateAt_live (C := code L Q) ht hg hend (show a ≤ aend by omega)
    rw [cnt_succ c he, ih (by omega)]
    have hnsy : ¬ sk.sy sa := fun h => hno a (by omega) ⟨sa, hsa, h⟩
    have hcs : Cs sa = false := by
      cases h : Cs sa
      · rfl
      · exact absurd (hsy h) hnsy
    have hge : X.get (g, a) = some e := he
    rw [hev hg hge hsa, hcs]
    simp

/-- **The lanes of a warp at synchronizing states of one ordinal have made the same number of
events of a class of synchronizing states.** -/
theorem lock_count (sk : Skel Q L κ) (ht : Frame.Tracked (code L Q) X)
    (hL : ∀ n, Lock sk X n) {c : Event → Bool} {Cs : TSt → Bool} (hev : ClassEv c Cs Q L X)
    (hsy : ∀ {s}, Cs s = true → sk.sy s)
    (hkey : ∀ {g h : Nat} {s s' : TSt}, SameWarp L g h → sk.sy s → sk.sy s' →
      sk.key g s = sk.key h s' → Cs s = Cs s') :
    ∀ n {g h a b : Nat} {s s' : TSt}, SameWarp L g h → a ≤ (X.tr g).length →
      b ≤ (X.tr h).length → St Q L X g a = some (some s) → St Q L X h b = some (some s') →
      sk.sy s → sk.sy s' → syN sk X g a = n → syN sk X h b = n →
      cnt c X g a = cnt c X h b := by
  intro n
  induction n with
  | zero =>
    intro g h a b s s' hw ha hb hs hs' hsy1 hsy2 hn hn'
    rw [cnt_zero sk ht hev hsy hw.1.1 hs ha
        (fun i hi => (no_sy_of_zero sk g hn) i (Nat.zero_le _) hi) a le_rfl,
      cnt_zero sk ht hev hsy hw.1.2.1 hs' hb
        (fun i hi => (no_sy_of_zero sk h hn') i (Nat.zero_le _) hi) b le_rfl]
  | succ n ih =>
    intro g h a b s s' hw ha hb hs hs' hsy1 hsy2 hn hn'
    have hg : g < L.threads := hw.1.1
    have hh : h < L.threads := hw.1.2.1
    obtain ⟨a', ha', hsa', hna', hno⟩ := exists_prev sk (X := X) g ⟨s, hs, hsy1⟩ hn
    obtain ⟨b', hb', hsb', hnb', hno'⟩ := exists_prev sk (X := X) h ⟨s', hs', hsy2⟩ hn'
    obtain ⟨sa, hsa, hsya⟩ := hsa'
    obtain ⟨sb, hsb, hsyb⟩ := hsb'
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[a']? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨e', he'⟩ : ∃ e', (X.tr h)[b']? = some e' := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hih := ih hw (by omega) (by omega) hsa hsb hsya hsyb hna' hnb'
    have hk := hL n hw (by omega) (by omega) hsa hsb hsya hsyb hna' hnb'
    have hcs := hkey hw hsya hsyb hk
    have h1 := cnt_stretch sk ht hev hsy hg hs ha (fun i h1 h2 => hno i h1 h2) a
      (by omega) le_rfl
    have h2 := cnt_stretch sk ht hev hsy hh hs' hb (fun i h1 h2 => hno' i h1 h2) b
      (by omega) le_rfl
    rw [h1, h2, cnt_succ c he, cnt_succ c he', hih, hev hg (show X.get (g, a') = some e from he)
      hsa, hev hh (show X.get (h, b') = some e' from he') hsb, hcs]

theorem cnt_mono (c : Event → Bool) (g : Nat) {j k : Nat} (h : j ≤ k) :
    cnt c X g j ≤ cnt c X g k := by
  unfold cnt
  have : (X.tr g).take j = ((X.tr g).take k).take j := by
    rw [List.take_take, Nat.min_eq_left h]
  rw [this]
  exact (List.take_sublist _ _).countP_le

/-- **A synchronizing state of every smaller ordinal precedes a synchronizing state.** -/
theorem exists_ordinal (sk : Skel Q L κ) (g : Nat) :
    ∀ d {a n : Nat}, IsSy sk X g a → syN sk X g a = n + d →
      ∃ a0, a0 ≤ a ∧ IsSy sk X g a0 ∧ syN sk X g a0 = n := by
  intro d
  induction d with
  | zero => intro a n hs hn; exact ⟨a, le_rfl, hs, by simpa using hn⟩
  | succ d ih =>
    intro a n hs hn
    obtain ⟨a', ha', hsa', hna', -⟩ := exists_prev sk (X := X) g hs
      (show syN sk X g a = (n + d) + 1 by omega)
    obtain ⟨a0, h1, h2, h3⟩ := ih hsa' hna'
    exact ⟨a0, by omega, h2, h3⟩

variable (sk : Skel Q L κ) (ht : Frame.Tracked (code L Q) X) (hL : ∀ n, Lock sk X n)
    {c : Event → Bool} {Cs : TSt → Bool} (hev : ClassEv c Cs Q L X)
    (hsy : ∀ {s}, Cs s = true → sk.sy s)
    (hkey : ∀ {g h : Nat} {s s' : TSt}, SameWarp L g h → sk.sy s → sk.sy s' →
      sk.key g s = sk.key h s' → Cs s = Cs s') {g h a b : Nat} {s s' : TSt} (hw : SameWarp L g h)
    (ha : a ≤ (X.tr g).length) (hb : b ≤ (X.tr h).length) (hs : St Q L X g a = some (some s))
include sk ht hL hev hsy hkey hw ha hb hs

/-- **A lane with a state of the class at a smaller ordinal has made more events of the class.**
If lane `g`'s state `a` of the class has ordinal `n` and lane `h` has a state `b` with a larger
ordinal, then `h` has made more events of the class before `b` than `g` before `a`. -/
theorem class_more (hs' : St Q L X h b = some (some s')) (hc : Cs s = true) (hsy2 : sk.sy s')
    (hlt : syN sk X g a < syN sk X h b) : cnt c X g a < cnt c X h b := by
  have hsy1 := hsy hc
  have hh : h < L.threads := hw.1.2.1
  obtain ⟨b0, hb0, hsy0, hn0⟩ := exists_ordinal sk (X := X) h
    (syN sk X h b - syN sk X g a) (a := b) (n := syN sk X g a) ⟨s', hs', hsy2⟩ (by omega)
  obtain ⟨s0, hs0, hsy0'⟩ := hsy0
  have hb0lt : b0 < b := by
    by_contra hge
    have : b0 = b := by omega
    subst this
    omega
  obtain ⟨e0, he0⟩ : ∃ e0, (X.tr h)[b0]? = some e0 :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hk := hL (syN sk X g a) hw ha (by omega) hs hs0 hsy1 hsy0' rfl hn0
  have hcs := hkey hw hsy1 hsy0' hk
  have hcnt := lock_count sk ht hL hev hsy hkey (syN sk X g a) hw ha (by omega) hs hs0 hsy1 hsy0'
    rfl hn0
  have hc0 : c e0 = true := by
    rw [hev hh (show X.get (h, b0) = some e0 from he0) hs0, ← hcs]
    exact hc
  have h1 := cnt_succ (X := X) c he0
  have h2 := cnt_mono (X := X) c h (show b0 + 1 ≤ b by omega)
  rw [hc0] at h1
  simp only [↓reduceIte] at h1
  omega

omit sk ht hL hev hsy hkey hw ha hb hs in
theorem sameWarp_symm {g h : Nat} (hw : SameWarp L g h) : SameWarp L h g :=
  ⟨⟨hw.1.2.1, hw.1.1, hw.1.2.2.symm⟩, hw.2.symm⟩

/-- **Two lanes of a warp at states of a class with as many earlier events of the class are at
one key.** -/
theorem class_key (hs' : St Q L X h b = some (some s')) (hc : Cs s = true) (hc' : Cs s' = true)
    (hcnt : cnt c X g a = cnt c X h b) : sk.key g s = sk.key h s' := by
  have hord : syN sk X g a = syN sk X h b := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := class_more sk ht hL hev hsy hkey hw ha hb hs hs' hc (hsy hc') hlt
      omega
    · have := class_more sk ht hL hev hsy hkey (sameWarp_symm hw) hb ha hs' hs hc' (hsy hc) hgt
      omega
  exact hL _ hw ha hb hs hs' (hsy hc) (hsy hc') rfl hord.symm

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
