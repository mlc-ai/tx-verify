-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.WkLdRdv

@[expose] public section

/-!
# The loader's polls at the end of its trace

`Lp.loader_anchor` reads the loader's anchored run at a state before an event
(`k < length`). The blocker of a loader poll needs the count at the state after the last event,
`k = length`. Every loader state but the entry follows a loader state at the previous event
(`ld_pred_le`), which has an event, so its anchored run extends by one step: the successful polls
of `kv_empty s` before a loader state of the loop other than `bar0` are
`below s (polled d) - below s num_pre` (`ld_polls_le`, `Ring.loader_polls`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wk
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Lp (PreSite)
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty)
open PTX.Kernels.InklingRelDecode.Proof.Ring (wAt)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The state before a loader state at an index up to the trace's length.** Like
`Lp.loader_state_pred_adj`, for `k ≤ length`. -/
theorem ld_pred_le (hX : Consistent L kernel asms mem0 X) {k : Nat} {d : Loader.D}
    {P : Loader.Pro} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.loader d P)))) (hs : d.site ≠ .setMaxDec) :
    ∃ (k0 : Nat) (e : Event) (d0 : Loader.D), k0 + 1 = k ∧ g < L.threads ∧
      X.get (g, k0) = some e ∧ St Q L X g k0 = some (some (.w (.loader d0 P))) ∧
      Loader.next L g d0 e = some (some d) := by
  have hk1 : k ≠ 0 := by
    rintro rfl
    have h0 := hσ
    rw [St, Frame.stateAt_zero] at h0
    exact Lp.loader_ne_init d P (Option.some.inj (Option.some.inj h0)).symm
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k0]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hs' := hσ
  rw [St, Frame.stateAt_succ he] at hs'
  cases hk0 : St Q L X g k0 with
  | none => simp [St] at hk0 hs'; simp [hk0] at hs'
  | some σ =>
    cases σ with
    | none =>
      have : Frame.stateAt (code L Q) X g k0 = some none := hk0
      rw [this] at hs'
      simp [Code.toMachine] at hs'
    | some s0 =>
      have : Frame.stateAt (code L Q) X g k0 = some (some s0) := hk0
      rw [this] at hs'
      have hn : (threadCode L g Q).next s0 e = some (some (.w (.loader d P))) := hs'
      cases s0 with
      | d s =>
        rw [next_d] at hn
        obtain ⟨a, -, h⟩ := map_map_eq_some_some hn
        cases h
      | w s =>
        rw [next_w] at hn
        obtain ⟨a, ha, h⟩ := map_map_eq_some_some hn
        cases h
        obtain ⟨d0, rfl, hd0⟩ := Lp.wcomp_next_loader ha hs
        have hge : X.get (g, k0) = some e := he
        exact ⟨k0, e, d0, rfl, Frame.lt_of_get hX hge, hge, hk0, hd0⟩

/-- **The loader's successful polls at a state up to the trace's end**: for a loop state other
than `bar0`, `okPolls (kv_empty s) + below s num_pre = below s (polled d)`. -/
theorem ld_polls_le (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hp : NumPreRead Q L X) {k : Nat}
    {d : Loader.D} {P : Loader.Pro} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.loader d P)))) (hnp : ¬ PreSite d.site)
    (hb : d.site ≠ .bar0) :
    ∀ s < 3, okPolls (kvEmpty L (g / L.block) s) ((X.tr g).take k) +
      Ring.below s (np Q L g) = Ring.below s (Ring.Ld.polled d) := by
  intro s hs
  obtain ⟨k1, e, d1, hadj, hg, he, hσ1, hn⟩ := ld_pred_le hX hk hσ (fun h => hnp (.inl h))
  have hk1 : k1 < (X.tr g).length := by omega
  obtain ⟨-, -, -, h4, h5, h6⟩ := Lp.next_pre hn
  have hp1 : ¬ PreSite d1.site := by
    rintro (h | h | h)
    · exact hnp (.inr (.inl (h4 h)))
    · exact hnp (.inr (.inr (h5 h)))
    · exact hb (h6 h)
  obtain ⟨hw, k0, d0, hk0, h0, hd1, hs0, hi0, hin, -, hP, -⟩ :=
    Lp.loader_anchor hpre hX hf hR hp hk1 hσ1 hp1
  have hd : wAt Q L X g k = some (some (.loader d P)) := Rd.wAt_of_st _ hk hσ
  have hin2 : ∀ j, k0 ≤ j → j < k → ∃ d', wAt Q L X g j = some (some (.loader d' P)) ∧
      Ring.Ld.InLoop d' ∧ d'.site ≠ .setMaxInc := by
    intro j hj1 hj2
    by_cases hj : j = k1
    · subst hj
      exact ⟨d1, hd1, ⟨fun h => hp1 (.inl h), fun h => hp1 (.inr (.inl h)),
        fun h => hp1 (.inr (.inr h)), hf.ldRng hg hσ1⟩, (Lp.next_ne_setMaxDec hn).2⟩
    · exact hin j hj1 (by omega)
  have hkk : k0 ≤ k := by omega
  have hrun := Ring.run_from hpre hw hg hX k h0
  obtain ⟨hend, hmid⟩ := Ring.run_states hkk h0 hd
  have hin' : ∀ j < (((X.tr g).drop k0).take (k - k0)).length, ∃ d',
      (WComp.code L g Q).toMachine.after (some (.loader d0 P))
        ((((X.tr g).drop k0).take (k - k0)).take j) = some (some (.loader d' P)) ∧
      Ring.Ld.InLoop d' ∧ d'.site ≠ .setMaxInc := by
    intro j hj
    have hj' : j < k - k0 := lt_of_lt_of_le hj (List.length_take_le _ _)
    obtain ⟨d', h1, h2, h3⟩ := hin2 (k0 + j) (by omega) (by omega)
    exact ⟨d', (hmid j hj').trans h1, h2, h3⟩
  have hmap : EvW.MapReg P := EvW.after_mapReg hd
  have h := Ring.loader_polls hpre hmap hrun hin' hend s hs
  have hpo : Ring.Ld.polled d0 = d0.i := by simp [Ring.Ld.polled, Ring.Ld.afterWait, hs0]
  rw [hpo, hi0] at h
  unfold okPolls at h ⊢
  rw [Ring.countP_take_split _ _ hkk]
  have := hP (kvEmpty L (g / L.block) s)
  unfold okPolls at this
  rw [this, Nat.zero_add]
  exact h

end
end PTX.Kernels.InklingRelDecode.Proof.Wk
