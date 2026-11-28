-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.RefNext
public import Lemmas.Flow.PollRounds
import Lemmas.Flow.Arith32Word

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof

/-- Successful empty polls preceding the next event. A packet is issued after its poll. -/
noncomputable def polls (lo hi : Nat) (d : D) : Nat :=
  match d.site with
  | .dec | .first | .second | .beginBar => 0
  | .endBar | .inc | .dispatch => hi - lo
  | .poll => (bits d.counter).toNat - lo
  | _ => (bits d.counter).toNat - lo + 1

private theorem inc_bits {j : Nat} (hj : j + 1 < 2 ^ 32) :
    (bits (.bits 32 (truncBits 32 (bits (b32 j) + 1)))).toNat = j + 1 := by
  rw [bits_b32 (by omega)]
  change (Arith32.r32 (Arith32.r32 (BitVec.ofNat 64 j + BitVec.ofNat 64 1))).toNat = _
  rw [← BitVec.ofNat_add, Arith32.r32_W hj, Arith32.r32_W hj]
  simp only [BitVec.toNat_ofNat]
  omega

private theorem finish_polls {lo hi j : Nat} (hj : lo ≤ j) (hl : j < hi) (hh : hi < 2 ^ 31)
    (s : Site) (p : Fin 4) (a b : Value) :
    polls lo hi (finishPair ⟨s,b32 j,b32 hi,a,b⟩ p) = j - lo + 1 := by
  have hw : (bits (b32 j)).toNat = j := by
    rw [bits_b32 (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  fin_cases p <;> simp only [finishPair, polls, hw]
  split_ifs
  · rename_i he
    have hinc := inc_bits (j := j) (by omega)
    rw [he, bits_b32 (by omega : hi < 2^32)] at hinc
    change (bits (b32 hi)).toNat = j + 1 at hinc
    rw [bits_b32 (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hinc
    change hi - lo = j - lo + 1
    omega
  · change (bits (.bits 32 (truncBits 32 (bits (b32 j) + 1)))).toNat - lo = _
    rw [inc_bits (by omega)]
    omega

theorem polls_next {L : Launch} {g lo hi : Nat} {d d' : D} {e : Event}
    (hh : hi < 2 ^ 31) (hlo : lo ≤ hi) (hr : Ref lo hi d)
    (hn : next L g d e = some (some d')) (hc : e.pc = d.site.pc) :
    polls lo hi d' = polls lo hi d + (if okPollAt 2374 e then 1 else 0) := by
  have outside {s : Site} (h : e.pc = s.pc) (hn : s ≠ .poll) : okPollAt 2374 e = false := by
    have hp : s.pc ≠ 2374 := by
      cases s <;> try contradiction
      all_goals first | decide | (rename_i p; fin_cases p <;> decide) |
        (rename_i p b; fin_cases p <;> cases b <;> decide)
    cases e with
    | mk pc ek =>
      cases ek <;> try rfl
      rename_i ok _ _
      cases ok <;> simp_all [okPollAt]
  obtain ⟨s,i,n,a,b⟩ := d
  by_cases hs : s = .poll
  · subst s
    obtain ⟨j,hle,hlt,rfl,rfl⟩ := hr
    simp only [next] at hn
    split at hn <;> try contradiction
    rename_i ok _ _ he
    cases e with
    | mk pc ek =>
      subst hc
      change ek = _ at he
      subst ek
      cases ok <;> cases hn <;> simp [polls, okPollAt, Site.pc]
  simp only [outside hc hs, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  cases s with
  | dec | first | second | beginBar | endBar | inc =>
    first | (obtain ⟨_,_,_,_,_,rfl⟩ := read_next hn; rfl) | (cases hn; rfl) |
      (obtain ⟨rfl,rfl⟩ := hr
       simp only [next, Option.some.injEq] at hn
       subst d'
       rw [bits_b32 (by omega : hi < 2^32), bits_b32 (by omega : lo < 2^32),
         Arith32.toSigned_W hh, Arith32.toSigned_W (by omega)]
       split <;> simp [polls, bits_b32 (by omega : lo < 2^32), BitVec.toNat_ofNat] <;> omega)
  | poll => contradiction
  | dispatch => cases hn
  | page b => cases b <;> obtain ⟨_,_,_,_,_,rfl⟩ := read_next hn <;> rfl
  | readyBar => simp only [next] at hn; split at hn <;> cases hn <;> rfl
  | arrive | warpBar => cases hn; rfl
  | copy p u =>
    cases u
    · cases hn; rfl
    · cases hn
      obtain ⟨j,hj,hl,rfl,rfl⟩ := hr
      rw [finish_polls hj hl hh]
      change _ = (bits (b32 j)).toNat - lo + 1
      rw [bits_b32 (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  | elect p =>
    simp only [next] at hn
    split at hn <;> try contradiction
    split at hn <;> cases hn
    · rfl
    · obtain ⟨j,hj,hl,rfl,rfl⟩ := hr
      rw [finish_polls hj hl hh]
      change _ = (bits (b32 j)).toNat - lo + 1
      rw [bits_b32 (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

end PTX.Kernels.InklingRelDecode.Proof.Loader
