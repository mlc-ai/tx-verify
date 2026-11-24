-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk4Class
public import Kernels.InklingRelDecode.Proof.Interface.LkCount
public import Kernels.InklingRelDecode.Proof.Interface.ExitFacts

@[expose] public section

/-!
# Warp lockstep: a lane that exits has made every synchronizing state of its warp's lanes

If a lane of a warp is at a state whose key is no synchronizing key (`Ex`: the state of the
program's exit), then no lane of the warp has a synchronizing state at a larger ordinal than the
number of synchronizing states of that lane before it (`sy_lt_exit`). The proof is the lockstep's
step at the last synchronizing state: the lanes' successors have one key, the other lane's
successor stretch runs to its next synchronizing state, whose key is a synchronizing position,
and the exit's key is not.

For the kernel (`kernelSkel`) the states of the exit are the epilogue's `ret` and the exit role's
`ret` (`ExitState`): the key of such a state is the position of the exit
(`Thread/Lk4Class.lean`), which is not the position of a synchronizing state.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {X : Execution} {κ : Type}

/-- The last synchronizing state before a state with `n + 1` synchronizing states before it. -/
theorem exists_last (sk : Skel Q L κ) (g : Nat) :
    ∀ k n, syN sk X g k = n + 1 →
      ∃ b, b < k ∧ IsSy sk X g b ∧ syN sk X g b = n ∧ ∀ i, b < i → i < k → ¬ IsSy sk X g i := by
  intro k
  induction k with
  | zero => intro n h; simp [syN] at h
  | succ k ih =>
    intro n h
    have h1 := syN_succ sk (X := X) g k
    by_cases hk : IsSy sk X g k
    · refine ⟨k, Nat.lt_succ_self k, hk, ?_, fun i h1 h2 => by omega⟩
      simp only [hk, ↓reduceIte] at h1
      omega
    · simp only [hk, ↓reduceIte] at h1
      obtain ⟨b, hb, hsb, hnb, hno⟩ := ih n (by omega)
      refine ⟨b, by omega, hsb, hnb, fun i hi1 hi2 => ?_⟩
      by_cases hik : i = k
      · subst hik; exact hk
      · exact hno i hi1 (by omega)

/-- **A lane that is at a state with no synchronizing key has more synchronizing states before it
than the ordinal of any other lane's synchronizing state of its warp.** -/
theorem sy_lt_exit (sk : Skel Q L κ) (ht : Frame.Tracked (code L Q) X) (hL : ∀ n, Lock sk X n)
    (hag : ∀ n, (∀ m, m ≤ n → Lock sk X m) → ∀ {g h a b : Nat} {s s' : TSt} {e e' : Event},
      SameWarp L g h → (X.tr g)[a]? = some e → (X.tr h)[b]? = some e' →
      St Q L X g a = some (some s) → St Q L X h b = some (some s') → sk.sy s → sk.sy s' →
      syN sk X g a = n → syN sk X h b = n → sk.key g s = sk.key h s' →
      sk.agree g h s s' e e')
    {Ex : TSt → Prop} (hex : ∀ {g h : Nat} {s s' : TSt}, Ex s → sk.sy s' →
      sk.key g s ≠ sk.key h s')
    {g h a j : Nat} {s se : TSt} (hw : SameWarp L g h) (ha : a ≤ (X.tr g).length)
    (hj : j ≤ (X.tr h).length) (hsa : St Q L X g a = some (some s)) (hsy : sk.sy s)
    (hse : St Q L X h j = some (some se)) (hx : Ex se) : syN sk X g a < syN sk X h j := by
  by_contra hge
  have hg : g < L.threads := hw.1.1
  have hh : h < L.threads := hw.1.2.1
  have hge' : syN sk X h j ≤ syN sk X g a := by omega
  cases hN : syN sk X h j with
  | zero =>
    obtain ⟨a0, ha0, hs0, hn0⟩ := exists_ordinal sk (X := X) g (syN sk X g a) (a := a) (n := 0)
      ⟨s, hsa, hsy⟩ (by omega)
    obtain ⟨s0, hs0', hsy0⟩ := hs0
    have h0g : St Q L X g 0 = some (some (threadCode L g Q).init) := Frame.stateAt_zero
    have h0h : St Q L X h 0 = some (some (threadCode L h Q).init) := Frame.stateAt_zero
    have k1 := chain sk ht hg h0g a0 (Nat.zero_le _) (by omega)
      (no_sy_of_zero sk g hn0) s0 hs0'
    have k2 := chain sk ht hh h0h j (Nat.zero_le _) hj (no_sy_of_zero sk h hN) se hse
    exact hex (g := h) (h := g) hx hsy0 (by rw [k2, k1]; exact (sk.init hw).symm)
  | succ m =>
    obtain ⟨b, hbj, hsyb, hnb, hnob⟩ := exists_last sk (X := X) h j m hN
    obtain ⟨sb, hsb, hsyb'⟩ := hsyb
    obtain ⟨a1, ha1, hs1, hn1⟩ := exists_ordinal sk (X := X) g (syN sk X g a - (m + 1)) (a := a)
      (n := m + 1) ⟨s, hsa, hsy⟩ (by omega)
    obtain ⟨s1, hs1', hsy1⟩ := hs1
    obtain ⟨a', ha', hsya, hna, hnoa⟩ := exists_prev sk (X := X) g ⟨s1, hs1', hsy1⟩ hn1
    obtain ⟨sa, hsa', hsya'⟩ := hsya
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[a']? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨e', he'⟩ : ∃ e', (X.tr h)[b]? = some e' := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hk := hL m hw (by omega) (by omega) hsa' hsb hsya' hsyb' hna hnb
    have hag' := hag m (fun m' _ => hL m') hw he he' hsa' hsb hsya' hsyb' hna hnb hk
    obtain ⟨ta, hta⟩ : ∃ ta, St Q L X g (a' + 1) = some (some ta) := by
      obtain ⟨d', hd'⟩ := Frame.stateAt_live (C := code L Q) ht hg hs1' (show a' + 1 ≤ a1 by omega)
      exact ⟨d', hd'⟩
    obtain ⟨tb, htb⟩ : ∃ tb, St Q L X h (b + 1) = some (some tb) := by
      obtain ⟨d', hd'⟩ := Frame.stateAt_live (C := code L Q) ht hh hse (show b + 1 ≤ j by omega)
      exact ⟨d', hd'⟩
    have hna' := next_of_st_succ he hsa' hta
    have hnb' := next_of_st_succ he' hsb htb
    have hstep := sk.step hw (cls_inv a' sa (by omega) hsa') (cls_inv b sb (by omega) hsb)
      hsya' hsyb' hk hag' hna' hnb'
    have k1 := chain sk ht hg hta a1 (by omega) (by omega)
      (fun i h1 h2 => hnoa i (by omega) h2) s1 hs1'
    have k2 := chain sk ht hh htb j (by omega) hj (fun i h1 h2 => hnob i (by omega) h2) se hse
    exact hex (g := h) (h := g) hx hsy1 (by rw [k2, k1]; exact hstep.symm)

/-- **The key of a state of the program's exit is no synchronizing key.** -/
theorem exit_key_ne {g h : Nat} {s s' : TSt} (hx : ExitState s) (hs' : (kernelSkel Q L).sy s') :
    (kernelSkel Q L).key g s ≠ (kernelSkel Q L).key h s' := by
  intro hk
  have h2 := (kernelSkel Q L).pc_key (g := h) hs'
  have h1 : ((kernelSkel Q L).key g s).1 = Epi.Site.exit.pc := by
    cases s with
    | d s =>
      cases s with
      | epi d => exact PTX.Kernels.InklingRelDecode.Proof.Lk.d_exit_key L g d hx
      | _ => exact hx.elim
    | w s =>
      cases s with
      | exit x => exact PTX.Kernels.InklingRelDecode.Proof.Lk.w_exit_key L g x hx
      | _ => exact hx.elim
  have h3 : TSt.pc s' = Epi.Site.exit.pc := by
    rw [← h2]
    exact congrArg (fun k => k.1) hk.symm |>.trans h1
  cases s' with
  | d s' => exact PTX.Kernels.InklingRelDecode.Proof.Lk.dSy_ne_exit hs' h3
  | w s' => exact PTX.Kernels.InklingRelDecode.Proof.Lk.wSy_ne_exit hs' h3

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
