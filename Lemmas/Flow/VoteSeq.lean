-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NthEv
public import Core.Sync.Vote

@[expose] public section

/-! # The ballots of a thread, by ordinal

A proof tool. `voteNz X g k` says whether the ballot of thread `g`'s ballot event with `k`
earlier ones is nonzero. The nonzero ballots among a prefix of the trace are those of its first
`n` ballot events, `n` the prefix's ballot count (`countP_nz_take`). The `k`-th full-mask ballots
of two lanes of a warp are equal when no lane of the warp exited before its `k`-th such ballot
and they share the instance's inputs (`ballot_eq`, from `VoteOk`): each bit is the lane's
predicate. -/

namespace PTX.Flow
open PTX

noncomputable section

variable {L : Launch} {X : Execution}

/-- A ballot event (`vote.sync.ballot.b32`). -/
def isBallot (e : Event) : Bool :=
  match e.kind with
  | .vote .. => true
  | _ => false

/-- A ballot event with a nonzero ballot. -/
def isNzVote (e : Event) : Bool :=
  match e.kind with
  | .vote _ _ b => b != 0
  | _ => false

/-- Whether thread `g`'s ballot event with `k` earlier ones has a nonzero ballot. -/
def voteNz (X : Execution) (g k : Nat) : Bool :=
  match X.get (g, nthEv X isBallot g k) with
  | some e => isNzVote e
  | none => false

/-- **The nonzero ballots of a prefix are those of its ballot events by ordinal.** -/
theorem countP_nz_take (g j : Nat) :
    ((X.tr g).take j).countP isNzVote =
      (List.range (((X.tr g).take j).countP isBallot)).countP (voteNz X g) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rcases Nat.lt_or_ge j (X.tr g).length with hj | hj
    · have he : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hj
      rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
        List.countP_append, List.countP_append, ih]
      by_cases hv : isBallot (X.tr g)[j] = true
      · simp only [List.countP_singleton, hv, ↓reduceIte, List.range_succ, List.countP_append]
        have hn := nthEv_eq he hv
        have hz : voteNz X g (((X.tr g).take j).countP isBallot) =
            isNzVote (X.tr g)[j] := by
          rw [voteNz, hn, he]
        rw [hz]
      · have hnz : isNzVote (X.tr g)[j] = false := by
          revert hv
          rcases (X.tr g)[j] with ⟨pc, k⟩
          cases k <;> simp [isNzVote, isBallot]
        simp [hv, hnz]
    · rw [List.take_of_length_le hj, List.take_of_length_le (by omega)] at *
      exact ih

/-- Threads of one warp start at one thread of the launch: their lane numbers count from the
same position. -/
theorem sameWarp_warpStart {g h : Nat} (hs : SameWarp L g h) :
    h - laneOf L h = g - laneOf L g := by
  obtain ⟨⟨-, -, hc⟩, hw⟩ := hs
  have h1 := Nat.div_add_mod g L.block
  have h2 := Nat.div_add_mod h L.block
  have h3 := Nat.div_add_mod (g % L.block) 32
  have h4 := Nat.div_add_mod (h % L.block) 32
  simp only [laneOf]
  rw [← hc] at h2
  omega

/-- **The `k`-th full-mask ballots of two lanes of a warp are equal** when the instance they
belong to takes part with one input function and no lane of the warp exited before its `k`-th
such ballot event. -/
theorem ballot_eq (hv : VoteOk L X) (hblk : L.block % 32 = 0) {g h j j' k pc pc' : Nat}
    {a a' : Bool} {b b' : BitVec 32} {part : Nat → Option Bool} (hs : SameWarp L g h)
    (he : X.get (g, j) = some ⟨pc, .vote (2 ^ 32 - 1) a b⟩)
    (hk : X.MaskK voteClass (g, j) (2 ^ 32 - 1) k)
    (he' : X.get (h, j') = some ⟨pc', .vote (2 ^ 32 - 1) a' b'⟩)
    (hk' : X.MaskK voteClass (h, j') (2 ^ 32 - 1) k)
    (hpart : MaskInstance L voteClass X g (2 ^ 32 - 1) k .ballot part)
    (hall : ∀ y, SameWarp L g y → ¬ MaskExited voteClass X y (2 ^ 32 - 1) k) : b = b' := by
  have hsw : SameWarp L g h := hs
  apply BitVec.eq_of_getLsbD_eq
  intro l hl
  obtain ⟨⟨hg, -, -⟩, -⟩ := hs
  -- the lane `l` of the warp
  set y := g - laneOf L g + l with hy
  have hbpos : 0 < L.block := by
    rcases Nat.eq_zero_or_pos L.block with h0 | h0
    · simp [Launch.threads, h0] at hg
    · exact h0
  obtain ⟨q, hq⟩ : ∃ q, L.block = 32 * q := ⟨L.block / 32, by omega⟩
  have hgm := Nat.mod_lt g hbpos
  have hlt : 32 * (g % L.block / 32) + l < L.block := by
    rw [hq] at hgm ⊢
    omega
  have h1 := Nat.div_add_mod g L.block
  have hy' : y = L.block * (g / L.block) + (32 * (g % L.block / 32) + l) := by
    simp only [hy, laneOf]; omega
  have hgy : g / L.block = y / L.block ∧ g % L.block / 32 = y % L.block / 32 ∧
      laneOf L y = l := by
    simp only [laneOf]
    rw [hy', Nat.mul_add_div hbpos, Nat.div_eq_of_lt hlt, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    refine ⟨by simp, by omega, by omega⟩
  have hyt : y < L.threads := by
    have hgc : g / L.block < L.grid := by
      rw [Nat.div_lt_iff_lt_mul hbpos]; exact hg
    have : L.block * (g / L.block) + L.block ≤ L.threads := by
      simp only [Launch.threads]
      calc L.block * (g / L.block) + L.block = (g / L.block + 1) * L.block := by
            rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
        _ ≤ L.grid * L.block := Nat.mul_le_mul_right _ hgc
    omega
  have hsy : SameWarp L g y := ⟨⟨hg, hyt, hgy.1⟩, hgy.2.1⟩
  -- the two lanes share one warp start
  have hbase := sameWarp_warpStart hsw
  have hpart' : MaskInstance L voteClass X h (2 ^ 32 - 1) k .ballot part := by
    intro lane hlane
    exact hbase ▸ hpart lane hlane
  have hfull : (2 ^ 32 - 1 : Nat).testBit l = true := by
    rw [Nat.testBit_two_pow_sub_one]; simpa using hl
  obtain ⟨v, hvpart⟩ : ∃ v, part l = some v := by
    rcases (hpart l hl).1 hfull with ⟨j1, p1, k1, v, -, -, -, hp⟩ | ⟨hx, -⟩
    · exact ⟨v, hp⟩
    · exact absurd hx (hall y hsy)
  have hbg := (hv g j k pc (2 ^ 32 - 1) a b he hk part hpart l hl).1 v hvpart
  have hbh := (hv h j' k pc' (2 ^ 32 - 1) a' b' he' hk' part hpart' l hl).1 v hvpart
  rw [hbg, hbh]

end
end PTX.Flow
