-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LpQVal
public import Kernels.InklingRelDecode.Proof.Interface.LpPreProof

@[expose] public section

/-!
# The masked query loads leave zero

At every prologue state of the query region (`ProA.InR`), every load before the state's site whose
guard is false left the 16-bit zero `ProA.qZero` (the `mov.b16 %rs18, 0` before the loads) in its
value: `qz_inv`. The induction is the one of `Lp.q_inv`: a load at site `j0` has a true guard
(`ProA.Inv.guard` at a state with an event), so it does not change a value whose guard is false; a
jump over loads (`ProA.qSite_skip`) leaves them at the zero the machine's invariant keeps for the
loads to come (`ProA.Inv.qz`); the region is entered at `qSite 0` from a site before it, whose
invariant keeps every value at zero. At the fence `fnc1` the 64 values are the loaded element where
the guard holds (`Lp.q_at_fnc1`) and zero elsewhere (`qz_at_fnc1`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The loads before a region state whose guard is false left zero. -/
def QZInv (L : Launch) (g : Nat) (d : ProA.D) : Prop :=
  ProA.InR d.site → ∀ j < ProA.qBound d.site, ProA.guardVal L g d.dt (ProA.ldqSite j) = false →
    d.dt.q j = ProA.qZero

/-- A site outside the query region and before it has no load behind it. -/
theorem qIdx_cases : ∀ s : ProA.Site, s.qIdx = 0 ∨ (∃ k < 64, s = ProA.ldqSite k) ∨
    (∃ i < 32, s = ProA.stqSite i) ∨
    s = .fnc1 ∨ s = .st8 ∨ s = .st9_0 ∨ s = .st9_1 ∨ s = .bar18 := by
  intro s; cases s <;> decide

theorem qIdx_before (s : ProA.Site) (h1 : s ∉ ProA.ldqSites) (h2 : s ∉ ProA.stqSites)
    (h3 : s ≠ .fnc1) (h4 : s ≠ .st8) (h5 : s ≠ .st9_0) (h6 : s ≠ .st9_1) (h7 : s ≠ .bar18) :
    s.qIdx = 0 := by
  rcases qIdx_cases s with h | h | h | h | h | h | h | h
  · exact h
  · obtain ⟨k, hk, rfl⟩ := h; exact absurd (ProA.ldqSite_mem k hk) h1
  · obtain ⟨i, hi, rfl⟩ := h
    exact absurd ((show ∀ i < 32, ProA.stqSite i ∈ ProA.stqSites by decide) i hi) h2
  · exact absurd h h3
  · exact absurd h h4
  · exact absurd h h5
  · exact absurd h h6
  · exact absurd h h7

/-- The site of load `j` has index `j`. -/
theorem qIdx_ldq : ∀ j < 64, (ProA.ldqSite j).qIdx = j := by decide

/-- **Every prologue state of the query region has zero at its masked loads.** -/
theorem qz_inv (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X) :
    ∀ k, k ≤ (X.tr g).length → ∀ d : ProA.D,
      St Q L X g k = some (some (.d (.pro d))) → QZInv L g d := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk d hσ hR
    rcases pred_d hk hσ with ⟨rfl, h0⟩ | ⟨k0, e, s0, rfl, he, hσ0, hn⟩
    · exfalso
      have : (DComp.code L g Q).init = .dstart (DStart.D.start L g) := rfl
      rw [this] at h0
      cases h0
    · cases s0 with
      | dstart dd =>
        exfalso
        change DComp.dstartNext L g Q dd e = _ at hn
        unfold DComp.dstartNext at hn
        obtain ⟨d', -, hs'⟩ := map_map_eq_some_some hn
        split at hs'
        · cases hs'
          simp only [ProA.D.start] at hR
          revert hR; decide
        · cases hs'
      | sm d0 =>
        exfalso
        change DComp.smNext L g d0 e = _ at hn
        unfold DComp.smNext at hn
        split at hn
        · unfold DComp.exitNext at hn
          split at hn <;> cases hn
        · obtain ⟨a, -, ha⟩ := map_map_eq_some_some hn
          cases ha
      | epi de =>
        exfalso
        change (Epi.next de e).map (Option.map DComp.St.epi) = _ at hn
        obtain ⟨a, -, ha⟩ := map_map_eq_some_some hn
        cases ha
      | pro dp =>
        change DComp.proNext L g Q dp e = _ at hn
        unfold DComp.proNext at hn
        split at hn
        · split at hn <;> cases hn
        rename_i hb18
        obtain ⟨d3, hd3, h3⟩ := map_map_eq_some_some hn
        cases h3
        have hge : X.get (g, k0) = some e := he
        obtain ⟨hinv, -⟩ := pro_inv_at hX hf hge hσ0
        have ih0 := ih k0 (by omega) (by omega) dp hσ0
        obtain ⟨site, dt0⟩ := dp
        by_cases hl : site ∈ ProA.ldqSites
        · obtain ⟨j0, hj0, rfl⟩ := ProA.ldqSites_idx hl
          obtain ⟨a, bs, v, -, -, -, hdt⟩ := ProA.next_ldq hj0 hd3
          have hsite := ProA.next_ldq_site hj0 hd3
          have hR0 : ProA.InR (ProA.ldqSite j0) := .inl (ProA.ldqSite_mem j0 hj0)
          have hb0 := ProA.qBound_ldq j0 hj0
          have hg0 : ProA.guardVal L g dt0 (ProA.ldqSite j0) = true := hinv.guard
          intro j hj hgd
          rw [hdt, ProA.guardVal_qUpd] at hgd
          by_cases hjj : j = j0
          · subst hjj; rw [hg0] at hgd; cases hgd
          have hq : d.dt.q j = dt0.q j := by
            rw [hdt]; simp [ProA.qUpd, Function.update_of_ne hjj]
          rw [hq]
          by_cases hlt : j < j0
          · exact ih0 hR0 j (by rw [hb0]; exact hlt) hgd
          · exact hinv.qz j (by simp only; rw [qIdx_ldq j0 hj0]; omega)
        by_cases hs : site ∈ ProA.stqSites
        · obtain ⟨i, hi, rfl⟩ := ProA.stqSites_idx hs
          rw [ProA.next_stq_fwd hi] at hd3
          cases hd3
          have hR0 : ProA.InR (ProA.stqSite i) := by
            have key : ∀ i < 32, ProA.InR (ProA.stqSite i) := by decide
            exact key i hi
          intro j hj hgd
          have hb : ProA.qBound (ProA.chainSite (i + 1)) = 64 := by
            have key : ∀ i < 32, ProA.qBound (ProA.chainSite (i + 1)) = 64 := by decide
            exact key i hi
          rw [hb] at hj
          exact ih0 hR0 j (by rw [ProA.qBound_stq i hi]; exact hj) hgd
        · by_cases hf1 : site = .fnc1
          · subst hf1
            rw [ProA.next_fnc1_fwd] at hd3
            cases hd3
            exact absurd hR (show ¬ ProA.InR .st8 by decide)
          by_cases h8 : site = .st8
          · subst h8
            rw [ProA.next_st8_fwd] at hd3
            cases hd3
            exact absurd hR (show ¬ ProA.InR .st9_0 by decide)
          by_cases h90 : site = .st9_0
          · subst h90
            rw [ProA.next_st90_fwd] at hd3
            cases hd3
            exact absurd hR (show ¬ ProA.InR .st9_1 by decide)
          by_cases h91 : site = .st9_1
          · subst h91
            rw [ProA.next_st91_fwd] at hd3
            cases hd3
            exact absurd hR (show ¬ ProA.InR .bar18 by decide)
          obtain ⟨hsite, hq⟩ := ProA.next_enter_R hd3 hl hs hR
          intro j hj hgd
          rw [hq]
          exact hinv.qz j (by
            simp only
            rw [qIdx_before site hl hs hf1 h8 h90 h91 hb18]
            omega)

/-- **At the fence `fnc1` every load whose guard is false left zero.** -/
theorem qz_at_fnc1 (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    {k : Nat} {dt : ProA.Dat} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.pro ⟨.fnc1, dt⟩)))) :
    ∀ j < 64, ProA.guardVal L g dt (ProA.ldqSite j) = false → dt.q j = ProA.qZero :=
  fun j hj hgd => qz_inv hX hf k hk _ hσ (.inr (.inr rfl)) j
    (by rw [ProA.qBound_fnc1]; exact hj) hgd

end
end PTX.Kernels.InklingRelDecode.Proof.Lp
