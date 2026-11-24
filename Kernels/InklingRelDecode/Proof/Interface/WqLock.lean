-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.WqKx

@[expose] public section

/-!
# The lockstep at every state, and of the key time

`lock_kernel` relates the lanes' synchronizing states of one ordinal. Its induction says more:
the key of a state is the key of the synchronizing state its stretch ends at, so two lanes'
states of one synchronizing ordinal (`syN`) have one key, synchronizing or not (`lock_any`).

`kx_lock` is the same for the key time `kx`: for the default partition it is a function of the
key; for the worker warps it follows the same induction, with the steps of `kx_step_w` at the
synchronizing states, given that the lanes' synchronizing states are valid (`WValid`, with a
number `c` of the thread's warp).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow
open Classical

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {X : Execution} {κ : Type}

/-- The synchronizing state before a state with count `n + 1` (synchronizing or not) has count
`n`, and the states between are not synchronizing. -/
theorem exists_prev_any (sk : Skel Q L κ) (g : Nat) {a n : Nat}
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
  have hsp : IsSy sk X g (Nat.findGreatest (fun j => IsSy sk X g j) (a - 1)) := by
    obtain ⟨j, hj, hp⟩ := hex'
    exact Nat.findGreatest_spec (P := fun j => IsSy sk X g j) hj hp
  refine ⟨Nat.findGreatest (fun j => IsSy sk X g j) (a - 1), ?_, hsp, ?_, ?_⟩
  · have := Nat.findGreatest_le (P := fun j => IsSy sk X g j) (a - 1)
    obtain ⟨j, hj, -⟩ := hex
    omega
  · set a' := Nat.findGreatest (fun j => IsSy sk X g j) (a - 1) with ha'
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

/-- **Two lanes' states of one synchronizing ordinal have one key.** -/
theorem lock_any (ht : Frame.Tracked (code L Q) X) (hA : LaneAgree Q L X) :
    ∀ n {g h a b : Nat} {s s' : TSt}, SameWarp L g h → a ≤ (X.tr g).length →
      b ≤ (X.tr h).length → St Q L X g a = some (some s) → St Q L X h b = some (some s') →
      syN (kernelSkel Q L) X g a = n → syN (kernelSkel Q L) X h b = n →
      (kernelSkel Q L).key g s = (kernelSkel Q L).key h s' := by
  have hL := lock_kernel ht hA
  intro n g h a b s s' hw ha hb hs hs' hn hn'
  have hg : g < L.threads := hw.1.1
  have hh : h < L.threads := hw.1.2.1
  cases n with
  | zero =>
    have h0g : St Q L X g 0 = some (some (threadCode L g Q).init) := Frame.stateAt_zero
    have h0h : St Q L X h 0 = some (some (threadCode L h Q).init) := Frame.stateAt_zero
    have k1 := chain (kernelSkel Q L) ht hg h0g a (Nat.zero_le _) ha
      (no_sy_of_zero (kernelSkel Q L) g hn) s hs
    have k2 := chain (kernelSkel Q L) ht hh h0h b (Nat.zero_le _) hb
      (no_sy_of_zero (kernelSkel Q L) h hn') s' hs'
    rw [k1, k2]
    exact (kernelSkel Q L).init hw
  | succ n =>
    obtain ⟨a', ha', hsa', hna', hno⟩ := exists_prev_any (kernelSkel Q L) (X := X) g hn
    obtain ⟨b', hb', hsb', hnb', hno'⟩ := exists_prev_any (kernelSkel Q L) (X := X) h hn'
    obtain ⟨sa, hsa, hsya⟩ := hsa'
    obtain ⟨sb, hsb, hsyb⟩ := hsb'
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[a']? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨e', he'⟩ : ∃ e', (X.tr h)[b']? = some e' :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hpc : (kernelSkel Q L).key g sa = (kernelSkel Q L).key h sb :=
      hL n hw (by omega) (by omega) hsa hsb hsya hsyb hna' hnb'
    have hag := hA n (fun m _ => hL m) hw he he' hsa hsb hsya hsyb hna' hnb' hpc
    obtain ⟨ta, hta⟩ : ∃ ta, St Q L X g (a' + 1) = some (some ta) := by
      obtain ⟨d', hd'⟩ := Frame.stateAt_live (C := code L Q) ht hg hs (show a' + 1 ≤ a by omega)
      exact ⟨d', hd'⟩
    obtain ⟨tb, htb⟩ : ∃ tb, St Q L X h (b' + 1) = some (some tb) := by
      obtain ⟨d', hd'⟩ := Frame.stateAt_live (C := code L Q) ht hh hs' (show b' + 1 ≤ b by omega)
      exact ⟨d', hd'⟩
    have hna := next_of_st_succ he hsa hta
    have hnb := next_of_st_succ he' hsb htb
    have hk := (kernelSkel Q L).step hw (cls_inv a' sa (by omega) hsa)
      (cls_inv b' sb (by omega) hsb) hsya hsyb hpc hag hna hnb
    have k1 := chain (kernelSkel Q L) ht hg hta a (by omega) ha
      (fun i h1 h2 => hno i (by omega) h2) s hs
    have k2 := chain (kernelSkel Q L) ht hh htb b (by omega) hb
      (fun i h1 h2 => hno' i (by omega) h2) s' hs'
    rw [k1, k2]
    exact hk

/-- **The key time is constant along a stretch of states that are not synchronizing.** -/
theorem kx_chain (ht : Frame.Tracked (code L Q) X) {g j0 : Nat} (hg : g < L.threads)
    {s0 : TSt} (h0 : St Q L X g j0 = some (some s0)) :
    ∀ a, j0 ≤ a → a ≤ (X.tr g).length → (∀ i, j0 ≤ i → i < a → ¬ IsSy (kernelSkel Q L) X g i) →
      ∀ s, St Q L X g a = some (some s) → kx L g s = kx L g s0 := by
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
    have hnsy : ¬ tSy sa := fun h => hno a hle (by omega) ⟨sa, hsa, h⟩
    rw [kx_silent hnsy hn]
    exact hk

/-- **Two lanes' states of one synchronizing ordinal have one key time**, given that the worker
lanes' synchronizing states are valid with a number `c` of the warp. -/
theorem kx_lock (ht : Frame.Tracked (code L Q) X) (hA : LaneAgree Q L X) (c : Nat → Nat)
    (hc : ∀ {g h : Nat}, SameWarp L g h → c g = c h)
    (hV : ∀ {g k : Nat} {s : WComp.WSt}, g < L.threads → k < (X.tr g).length →
      St Q L X g k = some (some (.w s)) → tSy (.w s) →
      PTX.Kernels.InklingRelDecode.Proof.Lk.WValid (c g) s) :
    ∀ n {g h a b : Nat} {s s' : TSt}, SameWarp L g h → a ≤ (X.tr g).length →
      b ≤ (X.tr h).length → St Q L X g a = some (some s) → St Q L X h b = some (some s') →
      syN (kernelSkel Q L) X g a = n → syN (kernelSkel Q L) X h b = n →
      kx L g s = kx L h s' := by
  have hL := lock_kernel ht hA
  intro n
  induction n with
  | zero =>
    intro g h a b s s' hw ha hb hs hs' hn hn'
    have hg : g < L.threads := hw.1.1
    have hh : h < L.threads := hw.1.2.1
    have h0g : St Q L X g 0 = some (some (threadCode L g Q).init) := Frame.stateAt_zero
    have h0h : St Q L X h 0 = some (some (threadCode L h Q).init) := Frame.stateAt_zero
    have k1 := kx_chain ht hg h0g a (Nat.zero_le _) ha
      (no_sy_of_zero (kernelSkel Q L) g hn) s hs
    have k2 := kx_chain ht hh h0h b (Nat.zero_le _) hb
      (no_sy_of_zero (kernelSkel Q L) h hn') s' hs'
    rw [k1, k2]
    have hw2 : g % L.block / 32 = h % L.block / 32 := hw.2
    show kx L g (if g % L.block < 128 then .d (DComp.code L g Q).init
        else .w (WComp.code L g Q).init) =
      kx L h (if h % L.block < 128 then .d (DComp.code L h Q).init
        else .w (WComp.code L h Q).init)
    split <;> split
    · show PTX.Kernels.InklingRelDecode.Proof.Lk.ktD
          (PTX.Kernels.InklingRelDecode.Proof.Lk.dKey L g (DComp.code L g Q).init) =
        PTX.Kernels.InklingRelDecode.Proof.Lk.ktD
          (PTX.Kernels.InklingRelDecode.Proof.Lk.dKey L h (DComp.code L h Q).init)
      rw [PTX.Kernels.InklingRelDecode.Proof.Lk.d_init Q hw]
    · exfalso; omega
    · exfalso; omega
    · rfl
  | succ n ih =>
    intro g h a b s s' hw ha hb hs hs' hn hn'
    have hg : g < L.threads := hw.1.1
    have hh : h < L.threads := hw.1.2.1
    by_cases hd : g % L.block < 128
    · -- the default partition: a function of the key
      have hd' : h % L.block < 128 := by
        have hw2 : g % L.block / 32 = h % L.block / 32 := hw.2
        omega
      have hk := lock_any ht hA (n + 1) hw ha hb hs hs' hn hn'
      have c1 := (cls_inv a s ha hs).mpr hd
      have c2 := (cls_inv b s' hb hs').mpr hd'
      cases s with
      | w s => exact c1.elim
      | d s =>
        cases s' with
        | w s' => exact c2.elim
        | d s' =>
          show PTX.Kernels.InklingRelDecode.Proof.Lk.ktD
              (PTX.Kernels.InklingRelDecode.Proof.Lk.dKey L g s) =
            PTX.Kernels.InklingRelDecode.Proof.Lk.ktD
              (PTX.Kernels.InklingRelDecode.Proof.Lk.dKey L h s')
          have : PTX.Kernels.InklingRelDecode.Proof.Lk.dKey L g s =
              PTX.Kernels.InklingRelDecode.Proof.Lk.dKey L h s' := hk
          rw [this]
    · -- the worker warps
      have hd' : ¬ h % L.block < 128 := by
        have hw2 : g % L.block / 32 = h % L.block / 32 := hw.2
        omega
      obtain ⟨a', ha', hsa', hna', hno⟩ := exists_prev_any (kernelSkel Q L) (X := X) g hn
      obtain ⟨b', hb', hsb', hnb', hno'⟩ := exists_prev_any (kernelSkel Q L) (X := X) h hn'
      obtain ⟨sa, hsa, hsya⟩ := hsa'
      obtain ⟨sb, hsb, hsyb⟩ := hsb'
      obtain ⟨e, he⟩ : ∃ e, (X.tr g)[a']? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨e', he'⟩ : ∃ e', (X.tr h)[b']? = some e' :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hpc : (kernelSkel Q L).key g sa = (kernelSkel Q L).key h sb :=
        hL n hw (by omega) (by omega) hsa hsb hsya hsyb hna' hnb'
      have hag := hA n (fun m _ => hL m) hw he he' hsa hsb hsya hsyb hna' hnb' hpc
      have hx := ih hw (by omega) (by omega) hsa hsb hna' hnb'
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
      have c1 := cls_inv a' sa (by omega) hsa
      have c2 := cls_inv b' sb (by omega) hsb
      have hstep : kx L g ta = kx L h tb := by
        cases sa with
        | d sa => exact absurd (c1.mp trivial) hd
        | w sa =>
          cases sb with
          | d sb => exact absurd (c2.mp trivial) hd'
          | w sb =>
            have hv := hV hg (by omega) hsa hsya
            have hv' := hV hh (by omega) hsb hsyb
            rw [hc hw] at hv
            exact kx_step_w hsya hsyb hpc hx hv hv' hag hna hnb
      have k1 := kx_chain ht hg hta a (by omega) ha
        (fun i h1 h2 => hno i (by omega) h2) s hs
      have k2 := kx_chain ht hh htb b (by omega) hb
        (fun i h1 h2 => hno' i (by omega) h2) s' hs'
      rw [k1, k2]
      exact hstep

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
