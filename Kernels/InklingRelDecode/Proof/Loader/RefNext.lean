-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Ref
import Lemmas.Flow.AllocTmpl
import Lemmas.Flow.Arith32Word

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Proof PTX.Flow Arith32

/-- The two observed load responses that introduce reference words. No page data
enters the counter reference. -/
def PairResponse (lo hi : Nat) (s : Site) (e : Event) : Prop :=
  match s, e.kind with
  | .first, .rd _ bs => bs = (b32 lo).toBytes.map some
  | .second, .rd _ bs => bs = (b32 hi).toBytes.map some
  | _, _ => True

private theorem pair_succ {lo hi j : Nat} (hlo : lo ≤ j) (hj : j < hi) (hh : hi < 2 ^ 31)
    (s : Site) (p : Fin 4) (a b : Value) :
    Ref lo hi (finishPair ⟨s,b32 j,b32 hi,a,b⟩ p) := by
  have H : ∃ m, lo ≤ m ∧ m < hi ∧ b32 j = b32 m ∧ b32 hi = b32 hi :=
    ⟨j, hlo, hj, rfl, rfl⟩
  fin_cases p
  · exact H
  · exact H
  · exact H
  · change Ref lo hi ⟨if _ then .endBar else .poll, _, _, _, _⟩
    rw [bits_b32 (by omega : j < 2 ^ 32), bits_b32 (by omega : hi < 2 ^ 32)]
    have inc : truncBits 32 (BitVec.ofNat 64 j + 1) = BitVec.ofNat 64 (j+1) := by
      change r32 (BitVec.ofNat 64 j + BitVec.ofNat 64 1) = _
      rw [← BitVec.ofNat_add]
      exact r32_W (by omega)
    rw [inc]
    split
    · rfl
    · rename_i h
      exact ⟨j+1, by omega, by
        by_contra! hle
        exact h (congrArg (BitVec.ofNat 64) (by omega)), rfl, rfl⟩

theorem read_next {f : Value → D} {e : Event} {d : D}
    (hn : readResult e f = some (some d)) :
    ∃ ac bs v, e.kind = .rd ac bs ∧ rebuild 3 bs = .ok v ∧ d = f v := by
  cases e with
  | mk pc ek =>
    cases ek <;> simp only [readResult] at hn
    all_goals try contradiction
    rename_i ac bs
    cases hv : rebuild 3 bs with
    | error f => rw [hv] at hn; contradiction
    | ok v =>
      rw [hv] at hn
      obtain rfl := Option.some.inj (Option.some.inj hn)
      exact ⟨ac, bs, v, rfl, hv, rfl⟩

theorem ref_next {L : Launch} {g lo hi : Nat} {d d' : D} {e : Event}
    (hh : hi < 2 ^ 31) (hlo : lo ≤ hi) (hr : Ref lo hi d)
    (hpair : PairResponse lo hi d.site e) (hn : next L g d e = some (some d')) :
    Ref lo hi d' := by
  obtain ⟨s,i,n,a,b⟩ := d
  cases s with
  | dec | endBar | inc =>
    simp only [next, Option.some.injEq] at hn
    subst d'
    exact hr
  | dispatch => cases hn
  | first | second =>
    obtain ⟨ac, bs, v, he, hv, rfl⟩ := read_next hn
    simp only [PairResponse, he] at hpair
    rw [hpair, rebuild_b32] at hv
    cases hv
    first | rfl | exact ⟨hr, rfl⟩
  | beginBar =>
    obtain ⟨rfl, rfl⟩ := hr
    simp only [next, Option.some.injEq] at hn
    subst d'
    rw [bits_b32 (by omega : hi < 2 ^ 32), bits_b32 (by omega : lo < 2 ^ 32),
      toSigned_W hh, toSigned_W (by omega)]
    split
    · rfl
    · exact ⟨lo, le_rfl, by omega, rfl, rfl⟩
  | poll =>
    simp only [next] at hn
    split at hn
    · split at hn <;> cases hn <;> exact hr
    · contradiction
  | readyBar =>
    simp only [next] at hn
    split at hn <;> cases hn <;> exact hr
  | arrive | warpBar =>
    cases hn
    exact hr
  | page upper =>
    cases upper <;> obtain ⟨_, _, _, _, _, rfl⟩ := read_next hn <;> exact hr
  | elect p =>
    obtain ⟨j,hj,hlt,rfl,rfl⟩ := hr
    simp only [next] at hn
    split at hn
    · split at hn
      · cases hn
        exact ⟨j,hj,hlt,rfl,rfl⟩
      · cases hn
        exact pair_succ hj hlt hh _ p a b
    · contradiction
  | copy p upper =>
    cases upper with
    | false => cases hn; exact hr
    | true =>
      obtain ⟨j,hj,hlt,rfl,rfl⟩ := hr
      cases hn
      exact pair_succ hj hlt hh _ p a b

end PTX.Kernels.InklingRelDecode.Proof.Loader
