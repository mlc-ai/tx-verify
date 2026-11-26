-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.RowMaxCarry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Vote
public import Lemmas.Kernel.VotePair
public import Lemmas.Kernel.FullVote
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.VoteExist
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Bar
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.VoteBlock

@[expose] public section

/-! # The two lanes of a pair vote alike

The rescale vote at pc 578 sees, in lane `y` of one warp and in its partner `tid ^ 64` of another
warp, the same input: the exchange word of the one is the other's own maximum
(`rmax_block_pair`), so the larger of the two maxima is the same, and the carried maxima agree
by induction on the blocks. Equal inputs lane by lane give equal ORs (`voteMode_pair`) and equal
results, hence equal carried maxima after the block (`vote_in_pair`, `vote_agree`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- `x ^^^ 64` below 128 flips the half. -/
theorem xor64_of_lt : ∀ x < 128, x ^^^ 64 = if x < 64 then x + 64 else x - 64 := by decide

/-- **The lanes of a warp and of its partner's** (warpgroup 0): lane `l` of the warp of `g` is
in the warpgroup, in the CTA of `g`, and its partner is lane `l` of the partner's warp. -/
theorem lane_pair (hp : Pre P L m) {g l : Nat} (hw : warp L g < 4) (hg : g < L.threads)
    (hl : l < 32) :
    g - PTX.laneOf L g + l < L.threads ∧ warp L (g - PTX.laneOf L g + l) < 4 ∧
      (g - PTX.laneOf L g + l) / L.block = g / L.block ∧
      w0Partner L (g - PTX.laneOf L g + l) = w0Partner L g - PTX.laneOf L (w0Partner L g) + l := by
  obtain ⟨-, hwh, hdiv, hmod⟩ := w0Partner_facts hp hw hg
  have hb : L.block = 384 := by have := hp.block; omega
  have hlt : g % 384 < 128 := by
    simp only [warp, tidOf_x_eq hp] at hw
    omega
  have hth : L.threads = L.grid * 384 := by simp only [Launch.threads, hb]
  have hlg : PTX.laneOf L g = g % 384 % 32 := by unfold PTX.laneOf; rw [hb]
  have hy : g - PTX.laneOf L g + l < L.threads := by rw [hth] at hg ⊢; omega
  have hyd : (g - PTX.laneOf L g + l) / 384 = g / 384 := by omega
  have hym : (g - PTX.laneOf L g + l) % 384 < 128 := by omega
  refine ⟨hy, ?_, by rw [hb]; exact hyd, ?_⟩
  · simp only [warp, tidOf_x_eq hp]
    omega
  · rw [hb] at hdiv hmod
    have hx1 := xor64_of_lt (g % 384) hlt
    have hx2 := xor64_of_lt ((g - PTX.laneOf L g + l) % 384) hym
    have hlh : PTX.laneOf L (w0Partner L g) = (w0Partner L g) % 384 % 32 := by
      unfold PTX.laneOf; rw [hb]
    have hp1 : w0Partner L (g - PTX.laneOf L g + l) =
        (g - PTX.laneOf L g + l) - (g - PTX.laneOf L g + l) % 384 +
          (((g - PTX.laneOf L g + l) % 384) ^^^ 64) := by
      unfold w0Partner; rw [hb]
    rw [hp1, hlh, hmod, hx2, hx1]
    rw [hx1] at hmod
    by_cases hc : g % 384 < 64
    · have hc2 : (g - PTX.laneOf L g + l) % 384 < 64 := by omega
      simp only [hc, hc2, ↓reduceIte] at hmod ⊢
      omega
    · have hc2 : ¬ (g - PTX.laneOf L g + l) % 384 < 64 := by omega
      simp only [hc, hc2, ↓reduceIte] at hmod ⊢
      omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hnu : ¬ HasUb X) (hR : BarRows P L X) (hC : Complete L X)
  (hV : ∀ y, warp L y < 4 → W0Trace P X y)
include hp hX hFw hnu hR hC hV

/-- **The votes of a lane and its partner at block `t`** (complete): both have their `t`-th vote,
at pc 578, with equal inputs when the two carried maxima agree, and the finished block `t` of
each has the vote's result as its vote word; the larger of the two maxima of the block is the
same in both. -/
theorem vote_in_pair {y t : Nat} (hw : warp L y < 4) (hy : y < L.threads)
    (ht : t < blocksOf P L (y / L.block))
    (hcar : (w0Carry P.scale ((w0Fin (X.tr y)).1.take t)).1 =
      (w0Carry P.scale ((w0Fin (X.tr (w0Partner L y))).1.take t)).1) :
    ∃ j a r j' a' r' s s',
      X.get (y, j) = some ⟨578, .voteMode .any (2 ^ 32 - 1) a r⟩ ∧
      ((X.tr y).take j).countP (voteWith (2 ^ 32 - 1)) = t ∧
      X.get (w0Partner L y, j') = some ⟨578, .voteMode .any (2 ^ 32 - 1) a' r'⟩ ∧
      ((X.tr (w0Partner L y)).take j').countP (voteWith (2 ^ 32 - 1)) = t ∧ a = a' ∧
      (w0Fin (X.tr y)).1[t]? = some s ∧ (w0Fin (X.tr (w0Partner L y))).1[t]? = some s' ∧
      (w0Words s).vt = r ∧ (w0Words s').vt = r' ∧
      max (w0Loc P.scale (w0Words s)) (w0FE (w0Words s).pm) =
        max (w0Loc P.scale (w0Words s')) (w0FE (w0Words s').pm) := by
  obtain ⟨⟨hpt, -, -⟩, hwh, hdiv, -⟩ := w0Partner_facts hp hw hy
  have hpp := w0Partner_partner hp hw hy
  have ht' : t < blocksOf P L (w0Partner L y / L.block) := by rw [hdiv]; exact ht
  obtain ⟨j, a, r, hj, hcj, hlj, ha, hbl⟩ := w0_vote_exists hp hX hFw hnu hw hy (hV y hw) hC
    (fun _ _ h => startup_exit hp hX hFw h) ht
  obtain ⟨j', a', r', hj', hcj', hlj', ha', hbl'⟩ :=
    w0_vote_exists hp hX hFw hnu hwh hpt (hV _ hwh) hC
    (fun _ _ h => startup_exit hp hX hFw h) ht'
  obtain ⟨s, hs1, hs2, hvt, hloc, hpm⟩ := w0_vote_block hp hX hFw hnu hw (hV y hw) hj rfl
    (k := (X.tr y).length) (by rw [List.take_length, hlj]; omega)
  obtain ⟨s', hs1', hs2', hvt', hloc', hpm'⟩ := w0_vote_block hp hX hFw hnu hwh (hV _ hwh) hj' rfl
    (k := (X.tr (w0Partner L y)).length) (by rw [List.take_length, hlj']; omega)
  rw [List.take_length, hlj] at hs1 hs2
  rw [List.take_length, hlj'] at hs1' hs2'
  obtain ⟨sx, sy, hx1, hy1, hxy⟩ := rmax_block_pair hp hX hFw hnu hR hw hy (hV y hw) (hV _ hwh) hC
    (kx := (X.tr y).length) (ky := (X.tr (w0Partner L y)).length)
    (by rw [List.take_length]; omega) (by rw [List.take_length]; omega) ht
  obtain ⟨sy', sx', hy2, hx2, hyx⟩ := rmax_block_pair hp hX hFw hnu hR hwh hpt (hV _ hwh)
    (by rw [hpp]; exact hV y hw) hC (kx := (X.tr (w0Partner L y)).length)
    (ky := (X.tr y).length) (by rw [List.take_length]; omega)
    (by rw [hpp, List.take_length]; omega) ht'
  rw [hpp] at hx2
  rw [List.take_length] at hx1 hy1 hy2 hx2
  rw [hs1] at hx1 hx2
  rw [hs1'] at hy1 hy2
  cases hx1
  cases hy1
  cases hx2
  cases hy2
  have hmax : max (w0Loc P.scale (w0Words s)) (w0FE (w0Words s).pm) =
      max (w0Loc P.scale (w0Words s')) (w0FE (w0Words s').pm) := by
    rw [hxy, hyx, max_comm]
  have hA : ∀ {u l : Nat} {b : Bool} {blk : List Event}
      (hb : b = w0VoteIn P.scale ((X.tr u).take l))
      (h2 : (w0Fin ((X.tr u).take l)).1 = (w0Fin (X.tr u)).1.take t)
      (hl : w0Loc P.scale (w0Words blk) = w0Loc P.scale (w0Words (w0Fin ((X.tr u).take l)).2))
      (hq : (w0Words blk).pm = (w0Words (w0Fin ((X.tr u).take l)).2).pm),
      b = w0VoteArg P.scale (w0Words blk) (w0Carry P.scale ((w0Fin (X.tr u)).1.take t)).1 :=
    fun hb h2 hl hq => by
      rw [hb, w0VoteIn, h2]
      exact (w0VoteArg_of_max (by rw [← hl, ← hq])).symm
  refine ⟨j, a, r, j', a', r', s, s', hj, hcj, hj', hcj', ?_, hs1, hs1', hvt .any _ a r rfl,
    hvt' .any _ a' r' rfl, hmax⟩
  rw [hA ha hs2 hloc hpm, hA ha' hs2' hloc' hpm', hcar]
  exact w0VoteArg_of_max hmax

/-- **One block on** (complete): if every lane of warpgroup 0 carries, after `t` blocks, the same
maximum as its partner, the lane `y` and its partner carry the same one after block `t`. -/
theorem carry_succ {y t : Nat} (hw : warp L y < 4) (hy : y < L.threads)
    (ht : t < blocksOf P L (y / L.block))
    (hIH : ∀ y', y' < L.threads → warp L y' < 4 → t ≤ blocksOf P L (y' / L.block) →
      (w0Carry P.scale ((w0Fin (X.tr y')).1.take t)).1 =
        (w0Carry P.scale ((w0Fin (X.tr (w0Partner L y'))).1.take t)).1) :
    (w0Carry P.scale ((w0Fin (X.tr y)).1.take (t + 1))).1 =
      (w0Carry P.scale ((w0Fin (X.tr (w0Partner L y))).1.take (t + 1))).1 := by
  have hcar := hIH y hy hw ht.le
  obtain ⟨j, a, r, j', a', r', s, s', hj, hcj, hj', hcj', -, hs1, hs1', hvt, hvt', hmax⟩ :=
    vote_in_pair hp hX hFw hnu hR hC hV hw hy ht hcar
  have hrr : r = r' := by
    refine Step.voteMode_pair hX (n := t) (m := 2 ^ 32 - 1) (fun l hl => by
      rw [Nat.testBit_two_pow_sub_one]; simp [hl]) hj hj'
      ⟨⟨_, ⟨2 ^ 32 - 1, .any, a⟩, hj, rfl, rfl⟩, hcj⟩
      ⟨⟨_, ⟨2 ^ 32 - 1, .any, a'⟩, hj', rfl, rfl⟩, hcj'⟩ ?_
    intro l hl
    obtain ⟨hy1, hw1, hd1, hpr⟩ := lane_pair hp hw hy hl
    obtain ⟨j1, a1, r1, j2, a2, r2, -, -, hj1, hc1, hj2, hc2, haa, -⟩ :=
      vote_in_pair hp hX hFw hnu hR hC hV hw1 hy1 (by rw [hd1]; exact ht)
        (hIH _ hy1 hw1 (by rw [hd1]; exact ht.le))
    rw [hpr] at hj2 hc2
    exact ⟨a1, ⟨j1, 578, r1, hj1, ⟨⟨_, ⟨2 ^ 32 - 1, .any, a1⟩, hj1, rfl, rfl⟩, hc1⟩⟩,
      ⟨j2, 578, r2, haa ▸ hj2, ⟨⟨_, ⟨2 ^ 32 - 1, .any, a2⟩, hj2, rfl, rfl⟩, hc2⟩⟩⟩
  have hm1 : ∀ {u : Nat} {s : List Event}, (w0Fin (X.tr u)).1[t]? = some s →
      (w0Carry P.scale ((w0Fin (X.tr u)).1.take (t + 1))).1 =
        w0Max P.scale (w0Carry P.scale ((w0Fin (X.tr u)).1.take t)).1 (w0Words s) :=
    fun hs => by
      rw [List.take_add_one, hs, Option.toList_some, w0Carry_snoc]
      rfl
  have hvv : (w0Words s).vt = (w0Words s').vt := by rw [hvt, hvt', hrr]
  rw [hm1 hs1, hm1 hs1', hcar]
  simp only [w0Max, hvv, hmax]

/-- **Every lane of warpgroup 0 carries the maximum of its partner, block by block.** -/
theorem carry_agree {y : Nat} (t : Nat) (hy : y < L.threads) (hw : warp L y < 4)
    (ht : t ≤ blocksOf P L (y / L.block)) :
    (w0Carry P.scale ((w0Fin (X.tr y)).1.take t)).1 =
      (w0Carry P.scale ((w0Fin (X.tr (w0Partner L y))).1.take t)).1 := by
  induction t generalizing y with
  | zero => rfl
  | succ t ih =>
    exact carry_succ hp hX hFw hnu hR hC hV hw hy ht
      (fun y' hy' hw' ht' => ih hy' hw' ht')

omit hR hC hV in
/-- The finished blocks of a prefix are the leading ones of the whole trace's. -/
theorem fin_take_eq {y k : Nat} (hw : warp L y < 4) :
    (w0Fin ((X.tr y).take k)).1 =
      (w0Fin (X.tr y)).1.take (w0Fin ((X.tr y).take k)).1.length := by
  by_cases hk : k ≤ (X.tr y).length
  · have := w0Fin_take_prefix hp hX hFw hnu hw hk
    rw [List.take_length] at this
    exact List.prefix_iff_eq_take.mp this
  · rw [List.take_of_length_le (by omega)]
    simp

/-- **The two lanes of a pair carry the same maximum** (complete execution): at prefixes of lane
`g` and of its partner with all the block count's blocks finished, the carried maxima are
equal. -/
theorem vote_agree {g k k' : Nat} (hw : warp L g < 4) (hg : g < L.threads)
    (hk : (w0Fin ((X.tr g).take k)).1.length = blocksOf P L (g / L.block))
    (hk' : (w0Fin ((X.tr (w0Partner L g)).take k')).1.length = blocksOf P L (g / L.block)) :
    (w0Carry P.scale (w0Fin ((X.tr g).take k)).1).1 =
      (w0Carry P.scale (w0Fin ((X.tr (w0Partner L g)).take k')).1).1 := by
  obtain ⟨-, hwh, -, -⟩ := w0Partner_facts hp hw hg
  rw [fin_take_eq hp hX hFw hnu hw, fin_take_eq hp hX hFw hnu hwh (k := k'), hk, hk']
  exact carry_agree hp hX hFw hnu hR hC hV _ hg hw le_rfl

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
