-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Measure
public import Kernels.InklingRelDecode.Proof.Loader.RefNext

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof

private theorem last_left {lo hi : Nat} {i n a b : Value} {s : Site}
    (hh : hi < 2 ^ 31) (hr : Ref lo hi ⟨s,i,n,a,b⟩) (hs : s.inLoop) :
    iterationsLeft (.bits 32 (truncBits 32 (bits i + 1))) n + 1 = iterationsLeft i n := by
  apply iterationsLeft_inc
  obtain ⟨j, _, hj, rfl, rfl⟩ := ref_loop (d := ⟨s,i,n,a,b⟩) hr hs
  rw [bits_b32 (by omega : j < 2 ^ 32), bits_b32 (by omega : hi < 2 ^ 32)]
  intro eq
  have hn := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : hi < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)] at hn
  omega

private theorem finish_decreases {lo hi : Nat} (hh : hi < 2 ^ 31) {s : Site} {i n a b : Value}
    (hr : Ref lo hi ⟨s,i,n,a,b⟩) (p : Fin 4) (hs : s = .elect p ∨ s = .copy p true) :
    measure (finishPair ⟨s,i,n,a,b⟩ p) < measure ⟨s,i,n,a,b⟩ := by
  obtain rfl | rfl := hs
  all_goals
    have dec := last_left hh hr (by rfl)
    fin_cases p
    all_goals by_cases h : truncBits 32 (bits i + 1) = bits n <;>
      norm_num [finishPair, measure, Site.position, h] <;> omega

/-- Every continuing transition decreases the local bound, apart from a failed poll,
which leaves the loader state unchanged. -/
theorem measure_next {L : Launch} {g lo hi : Nat} {d d' : D} {e : Event} (hh : hi < 2 ^ 31)
    (hr : Ref lo hi d) (hn : next L g d e = some (some d')) :
    measure d' < measure d ∨
      (d' = d ∧ d.site = .poll ∧ ∃ m q ac sc, e.kind = .wait m q false ac sc) := by
  obtain ⟨s,i,n,a,b⟩ := d
  cases s with
  | dispatch => cases hn
  | endBar | inc | dec => cases hn; exact .inl (by simp [measure])
  | first | second =>
    obtain ⟨_, _, _, _, _, rfl⟩ := read_next hn
    exact .inl (by simp [measure])
  | beginBar =>
    cases hn
    left
    have hlt : iterationsLeft i n < 2 ^ 32 := Nat.mod_lt _ (by decide)
    split <;> simp only [measure, Site.position] <;> omega
  | poll =>
    simp only [next] at hn
    split at hn
    · rename_i m q ok ac sc hk
      cases ok <;> cases hn
      · exact .inr ⟨rfl,rfl,_,_,_,_,hk⟩
      · exact .inl (by dsimp [measure, Site.position]; omega)
    · contradiction
  | readyBar =>
    simp only [next] at hn
    split at hn <;> cases hn <;> left <;> dsimp [measure, Site.position] <;> omega
  | arrive => cases hn; left; dsimp [measure, Site.position]; omega
  | page upper =>
    cases upper <;> obtain ⟨_,_,_,_,_,rfl⟩ := read_next hn <;> left <;>
      dsimp [measure, Site.position] <;> omega
  | warpBar p =>
    cases hn
    fin_cases p <;> left <;> dsimp [measure, Site.position] <;> omega
  | elect p =>
    simp only [next] at hn
    split at hn
    · split at hn
      · cases hn
        fin_cases p <;> left <;> dsimp [measure, Site.position] <;> omega
      · cases hn
        exact .inl (finish_decreases hh hr p (.inl rfl))
    · contradiction
  | copy p upper =>
    cases upper <;> cases hn
    · fin_cases p <;> left <;> dsimp [measure, Site.position] <;> omega
    · exact .inl (finish_decreases hh hr p (.inr rfl))

theorem measure_count {L : Launch} {g lo hi : Nat} {d d' : D} {e : Event}
    (hh : hi < 2 ^ 31) (hr : Ref lo hi d) (hn : next L g d e = some (some d')) :
    measure d' + (if e.counts then 1 else 0) ≤ measure d := by
  rcases measure_next hh hr hn with h | ⟨rfl, _, m, q, ac, sc, hk⟩
  · split <;> omega
  · cases e with
    | mk pc kind => cases hk; exact le_rfl

theorem measure_bound (d : D) : measure d ≤ 22 * 2 ^ 32 + 6 := by
  obtain ⟨s,i,n,a,b⟩ := d
  have hi : iterationsLeft i n < 2 ^ 32 := Nat.mod_lt _ (by decide)
  cases s <;> simp only [measure] <;> omega

end PTX.Kernels.InklingRelDecode.Proof.Loader
