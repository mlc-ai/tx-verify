-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LpQCross
public import Kernels.InklingRelDecode.Proof.Thread.ClassQNext
public import Kernels.InklingRelDecode.Proof.Thread.ClassQAddr

@[expose] public section

/-!
# The prologue's query loads, as a region of sites

The query loads (`ldqSite k`), the query stores and the fence `fnc1` form a region `InR` that the
prologue enters only through `qSite _ _ _ 0` (the first load of the first group whose rows are
valid, or the first store). Inside it, a load `k` stores its value in `q k` and goes to load
`k + 1`, or after the last load of a group to `qSite (G + 1)`; the stores and the fence keep the
data. `qBound s` is the number of loads before the site `s` (`k` at load `k`, 64 at the stores and
the fence). `qSite_skip`: the loads `qSite n` jumps over have a false guard. The guard of a load
depends neither on the loaded values nor on the elections (`guardVal_qUpd`, `guardVal_elDt`), and
a row of a valid token below row 60 has a true guard (`ldq_guard_of_valid`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The sites of the query region: the loads, the stores and the fence after them. -/
def InR (s : Site) : Prop := s ∈ ldqSites ∨ s ∈ stqSites ∨ s = .fnc1

instance (s : Site) : Decidable (InR s) := by unfold InR; infer_instance

/-- The number of query loads before a site of the region. -/
def qBound (s : Site) : Nat := if s ∈ ldqSites then ldqSites.idxOf s else 64

theorem qBound_ldq : ∀ k < 64, qBound (ldqSite k) = k := by decide

theorem qBound_stq : ∀ i < 32, qBound (stqSite i) = 64 := by decide

theorem qBound_fnc1 : qBound .fnc1 = 64 := by decide

theorem ldqSite_mem : ∀ k < 64, ldqSite k ∈ ldqSites := by decide

theorem ldqSites_idx {s : Site} (h : s ∈ ldqSites) : ∃ k < 64, s = ldqSite k := by
  revert h; revert s; decide

theorem stqSites_idx {s : Site} (h : s ∈ stqSites) : ∃ i < 32, s = stqSite i := by
  revert h; revert s; decide

/-- The site after load `k`. -/
theorem next_ldq_site {L : Launch} {g : Nat} {k : Nat} (hk : k < 64) {dt : Dat} {d' : D}
    {e : Event} (h : next L g ⟨ldqSite k, dt⟩ e = some (some d')) :
    d'.site = if (k + 1) % 16 = 0 then qSite L g d'.dt ((k + 1) / 16) else ldqSite (k + 1) := by
  interval_cases k
  all_goals
    simp only [ldqSite, ldqSites, List.getD_cons_zero, List.getD_cons_succ] at h
    simp only [next] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (simp only [Option.some.injEq] at h; subst h; rfl)

/-- **A step into the query region from outside it** goes to `qSite 0`, with the same loaded
values. -/
theorem next_enter_R {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨s, dt⟩ e = some (some d')) (hs1 : s ∉ ldqSites) (hs2 : s ∉ stqSites)
    (hR : InR d'.site) : d'.site = qSite L g d'.dt 0 ∧ d'.dt.q = dt.q := by
  cases s <;>
    (first
      | (exfalso; revert hs1 hs2; decide)
      | (simp only [next] at h
         repeat' split at h
         all_goals first
           | (cases h; done)
           | (simp only [Option.some.injEq] at h
              subst h
              simp only at hR ⊢
              first
                | (exfalso; revert hR; decide)
                | (constructor <;> trivial))))

/-- **The loads `qSite n` jumps over have a false guard**, and it lands at a bound at least
`16 n`. -/
theorem qSite_skip (L : Launch) (g : Nat) (dt : Dat) {n : Nat} (hn : n ≤ 4) :
    16 * n ≤ qBound (qSite L g dt n) ∧ InR (qSite L g dt n) ∧
      ∀ j, 16 * n ≤ j → j < qBound (qSite L g dt n) →
        guardVal L g dt (ldqSite j) = false := by
  have hq : qBound .ldq0 = 0 ∧ qBound .ldq16 = 16 ∧ qBound .ldq32 = 32 ∧ qBound .ldq48 = 48 ∧
      qBound .stq0_0 = 64 := by decide
  obtain ⟨q0, q16, q32, q48, q64⟩ := hq
  have hR : InR .ldq0 ∧ InR .ldq16 ∧ InR .ldq32 ∧ InR .ldq48 ∧ InR .stq0_0 := by decide
  obtain ⟨r0, r16, r32, r48, r64⟩ := hR
  have key : 16 * n ≤ qBound (qSite L g dt n) ∧ InR (qSite L g dt n) ∧
      ∀ j, 16 * n ≤ j → j < qBound (qSite L g dt n) → j < 64 →
        (if j / 16 = 0 then v_p81 L g dt else if j / 16 = 1 then v_p82 L g dt
          else if j / 16 = 2 then v_p83 L g dt else v_p84 L g dt) = false := by
    unfold qSite
    generalize v_p81 L g dt = a1
    generalize v_p82 L g dt = a2
    generalize v_p83 L g dt = a3
    generalize v_p84 L g dt = a4
    interval_cases n <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;>
      simp only [Bool.false_eq_true, ↓reduceIte, q0, q16, q32, q48, q64, r0, r16, r32, r48, r64,
        true_and] <;>
      (refine ⟨by omega, ?_⟩
       intro j h1 h2 h3
       split <;> (try split) <;> (try split) <;> first | rfl | omega)
  refine ⟨key.1, key.2.1, fun j h1 h2 => ?_⟩
  have h64 : j < 64 := by
    have : qBound (qSite L g dt n) ≤ 64 := by
      unfold qBound; split
      · rename_i hm
        have := List.idxOf_lt_length_of_mem hm
        rw [ldqSites_length] at this
        omega
      · omega
    omega
  rw [guardVal_ldq L g dt j h64]
  exact key.2.2 j h1 h2 h64

/-- The guard of a load does not read the loaded values. -/
theorem guardVal_qUpd (L : Launch) (g : Nat) (dt : Dat) (k : Nat) (v : Value) (s : Site) :
    guardVal L g (qUpd dt k v) s = guardVal L g dt s := by
  cases s <;> rfl

theorem p38_val (L : Launch) (g : Nat) (dt : Dat) (h : tidOf L g < 128) :
    v_p38 L g dt = decide (tidOf L g / 8 % 16 + 48 < 60) := by
  simp only [v_p38, v_r178, v_r177, v_r1]
  generalize tidOf L g = t at *
  revert t
  decide +kernel

/-- **A load of a row of a valid token below row 60 has a true guard.** -/
theorem ldq_guard_of_valid (L : Launch) (g : Nat) (dt : Dat) (hb : Bnd dt)
    (ht : tidOf L g < 128) {k : Nat} (hk : k < 64)
    (htok : (tidOf L g / 8 % 16 + 16 * (k / 16)) / 6 < dt.cu1 - dt.cu0)
    (h60 : tidOf L g / 8 % 16 + 16 * (k / 16) < 60) :
    guardVal L g dt (ldqSite k) = true := by
  rw [guardVal_ldq L g dt k hk]
  have hq : dt.cu1 - dt.cu0 < 2 ^ 31 := by obtain ⟨-, h2, -⟩ := hb; omega
  have hG4 : k / 16 = 0 ∨ k / 16 = 1 ∨ k / 16 = 2 ∨ k / 16 = 3 := by omega
  rcases hG4 with h | h | h | h
  · simp only [h, ↓reduceIte]
    simp only [v_p81, r20_val L g dt hb, r183_val L g dt ht,
      pGt_ofNat (dt.cu1 - dt.cu0) (tidOf L g / 8 % 16 / 6) hq (by omega), decide_eq_true_eq]
    simp only [h] at htok; omega
  · simp only [h, ↓reduceIte, show ¬ (1 = 0) by omega]
    simp only [v_p82, r20_val L g dt hb, r182_val L g dt ht,
      pGt_ofNat (dt.cu1 - dt.cu0) ((tidOf L g / 8 % 16 + 16) / 6) hq (by omega),
      decide_eq_true_eq]
    simp only [h] at htok; omega
  · simp only [h, ↓reduceIte, show ¬ (2 = 0) by omega, show ¬ (2 = 1) by omega]
    simp only [v_p83, r20_val L g dt hb, r181_val L g dt ht,
      pGt_ofNat (dt.cu1 - dt.cu0) ((tidOf L g / 8 % 16 + 32) / 6) hq (by omega),
      decide_eq_true_eq]
    simp only [h] at htok; omega
  · simp only [h, ↓reduceIte, show ¬ (3 = 0) by omega, show ¬ (3 = 1) by omega,
      show ¬ (3 = 2) by omega]
    simp only [v_p84, v_p39, Bool.and_eq_true, r20_val L g dt hb, r180_val L g dt ht,
      pGt_ofNat (dt.cu1 - dt.cu0) ((tidOf L g / 8 % 16 + 48) / 6) hq (by omega),
      decide_eq_true_eq, p38_val L g dt ht]
    simp only [h] at htok h60
    omega

/-- A store site or the fence keeps the data and steps along the chain. -/
theorem next_stq_fwd {L : Launch} {g : Nat} {i : Nat} (hi : i < 32) (dt : Dat) (e : Event) :
    next L g ⟨stqSite i, dt⟩ e = some (some ⟨chainSite (i + 1), dt⟩) := by
  interval_cases i <;> rfl

theorem next_fnc1_fwd {L : Launch} {g : Nat} (dt : Dat) (e : Event) :
    next L g ⟨.fnc1, dt⟩ e = some (some ⟨.st8, dt⟩) := rfl

theorem next_st8_fwd {L : Launch} {g : Nat} (dt : Dat) (e : Event) :
    next L g ⟨.st8, dt⟩ e = some (some ⟨.st9_0, dt⟩) := rfl

theorem next_st90_fwd {L : Launch} {g : Nat} (dt : Dat) (e : Event) :
    next L g ⟨.st9_0, dt⟩ e = some (some ⟨.st9_1, dt⟩) := rfl

theorem next_st91_fwd {L : Launch} {g : Nat} (dt : Dat) (e : Event) :
    next L g ⟨.st9_1, dt⟩ e = some (some ⟨.bar18, dt⟩) := rfl

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
