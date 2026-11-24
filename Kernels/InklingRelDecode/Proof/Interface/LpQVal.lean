-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LpQLoad
public import Kernels.InklingRelDecode.Proof.Interface.LpQStore
public import Kernels.InklingRelDecode.Proof.Interface.ClassQLoad

@[expose] public section

/-!
# The loaded query values at the query stores

`qVal Q L g k` is the bf16 query element that load `k` of thread `g` reads (`ldq_loaded`). At every
prologue state of the query region (`ProA.InR`: the loads, the stores, the fence `fnc1`), every load
before the state's site whose guard holds has stored its element: `q_inv`. The induction is over
the thread's states (`pred_d`): a load stores its element (`ldq_loaded`) and goes to the next load
or jumps over loads whose guard is false (`ProA.qSite_skip`); the stores keep the data; the region
is entered only at `qSite 0`, before which no load has a true guard. At the fence all 64 loads are
before the site (`q_at_fnc1`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The query element load `k` of thread `g` reads. -/
def qVal (Q : Params) (L : Launch) (g k : Nat) : Value :=
  Value.float .bf16 (Q.q (Q.qStart (ProA.cta L g .z) +
    (ProA.tidOf L g / 8 % 16 + 16 * (k / 16)) / 6)
    (ProA.cta L g .y * 6 + (ProA.tidOf L g / 8 % 16 + 16 * (k / 16)) % 6)
    (8 * (ProA.tidOf L g % 8) + 64 * (k % 16 / 8) + k % 8))

/-- The loads before a region state have stored their elements. -/
def QInv (Q : Params) (L : Launch) (g : Nat) (d : ProA.D) : Prop :=
  ProA.InR d.site → ∀ j < ProA.qBound d.site, ProA.guardVal L g d.dt (ProA.ldqSite j) = true →
    d.dt.q j = qVal Q L g j

/-- **Every prologue state of the query region has its loaded elements.** -/
theorem q_inv (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) :
    ∀ k, k ≤ (X.tr g).length → ∀ d : ProA.D,
      St Q L X g k = some (some (.d (.pro d))) → QInv Q L g d := by
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
        obtain ⟨d3, hd3, h3⟩ := map_map_eq_some_some hn
        cases h3
        have ih0 := ih k0 (by omega) (by omega) dp hσ0
        obtain ⟨site, dt0⟩ := dp
        by_cases hl : site ∈ ProA.ldqSites
        · obtain ⟨j0, hj0, rfl⟩ := ProA.ldqSites_idx hl
          have hge : X.get (g, k0) = some e := he
          obtain ⟨d'', hn'', hq''⟩ := ldq_loaded hpre hX hf hj0 hg hge hσ0
          rw [hd3] at hn''
          cases hn''
          obtain ⟨a, bs, v, -, -, -, hdt⟩ := ProA.next_ldq hj0 hd3
          have hsite := ProA.next_ldq_site hj0 hd3
          have hR0 : ProA.InR (ProA.ldqSite j0) := .inl (ProA.ldqSite_mem j0 hj0)
          have hb0 := ProA.qBound_ldq j0 hj0
          intro j hj hgd
          rw [hdt, ProA.guardVal_qUpd] at hgd
          by_cases hjj : j = j0
          · subst hjj; exact hq''
          have hq : d.dt.q j = dt0.q j := by
            rw [hdt]; simp [ProA.qUpd, Function.update_of_ne hjj]
          rw [hq]
          by_cases hlt : j < j0
          · exact ih0 hR0 j (by rw [hb0]; exact hlt) hgd
          · exfalso
            by_cases h16 : (j0 + 1) % 16 = 0
            · simp only [h16, ↓reduceIte] at hsite
              obtain ⟨-, -, hsk⟩ := ProA.qSite_skip L g d.dt (n := (j0 + 1) / 16) (by omega)
              rw [← hsite] at hsk
              have := hsk j (by omega) hj
              rw [hdt, ProA.guardVal_qUpd] at this
              rw [this] at hgd
              cases hgd
            · simp only [h16, ↓reduceIte] at hsite
              rw [hsite, ProA.qBound_ldq (j0 + 1) (by omega)] at hj
              omega
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
        · obtain ⟨hsite, hq⟩ := ProA.next_enter_R hd3 hl hs hR
          obtain ⟨-, -, hsk⟩ := ProA.qSite_skip L g d.dt (n := 0) (by omega)
          rw [← hsite] at hsk
          intro j hj hgd
          rw [hsk j (by omega) hj] at hgd
          cases hgd

/-- **At the fence `fnc1` every load whose guard holds has stored its element.** -/
theorem q_at_fnc1 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) {k : Nat} {dt : ProA.Dat}
    (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some (.d (.pro ⟨.fnc1, dt⟩)))) :
    ∀ j < 64, ProA.guardVal L g dt (ProA.ldqSite j) = true → dt.q j = qVal Q L g j :=
  fun j hj hgd => q_inv hpre hX hf hg k hk _ hσ (.inr (.inr rfl)) j
    (by rw [ProA.qBound_fnc1]; exact hj) hgd

end
end PTX.Kernels.InklingRelDecode.Proof.Lp
