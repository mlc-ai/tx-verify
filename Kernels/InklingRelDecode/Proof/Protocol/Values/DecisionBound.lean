-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.ScratchWord
public import Kernels.InklingRelDecode.Proof.Lib.ScoreEv
public import Kernels.InklingRelDecode.Proof.Lib.PvFold
public import Kernels.InklingRelDecode.Proof.Lib.FoldPw
public import Kernels.InklingRelDecode.Proof.Lib.BiasEv
public import Kernels.InklingRelDecode.Proof.Softmax.Export.StageCover
import Kernels.InklingRelDecode.Proof.Protocol.Alpha.RoundNi
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchButterfly
import Kernels.InklingRelDecode.Proof.Softmax.Export.StageAlpha
import Kernels.InklingRelDecode.Proof.Softmax.Export.DecisionFour
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleData
import Kernels.InklingRelDecode.Proof.Softmax.Export.ReadRound
import Kernels.InklingRelDecode.Proof.Softmax.Export.PollKeep
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mem

@[expose] public section

/-! # A rescale decision of a round does not skip when a row's factor is below one

The decision's four scratch words are the minima of the four warps' butterflies in the decision's
round; the warp of the row holds a word at most the row's factor, the first-stage word of the
row's lane in either half. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Flow Shared Softmax.Export Lib

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A factor that is not one is below one. -/
theorem fold_al_lt (Q : Params) (L : Launch) (c b row : Nat) (ne : foldAl Q L c b row ≠ 1) :
    foldAl Q L c b row < 1 := by
  unfold foldAl SoftRow.stepAlpha at ne ⊢
  split_ifs at ne ⊢ with h
  · exact absurd rfl ne
  · have lt : SoftFold.alphaLog2 (Q.scale * log2eF32) (SoftRow.kSt Q ((L.ctaidOf c).get .z)
        ((L.ctaidOf c).get .x) (row / 6) ((L.ctaidOf c).get .y * 6 + row % 6) 0 b).m
        (max (SoftRow.kSt Q ((L.ctaidOf c).get .z) ((L.ctaidOf c).get .x) (row / 6)
          ((L.ctaidOf c).get .y * 6 + row % 6) 0 b).m (SoftFold.blockMax (SoftRow.kBlk Q
            ((L.ctaidOf c).get .z) ((L.ctaidOf c).get .x) (row / 6)
            ((L.ctaidOf c).get .y * 6 + row % 6) 0 b))) < ((-8 : ℝ) : EReal) :=
      not_le.mp h
    generalize SoftFold.alphaLog2 _ _ _ = a at lt ⊢
    induction a using EReal.rec with
    | bot => simp [SoftFold.pow2]
    | coe r =>
      have : r < -8 := EReal.coe_lt_coe_iff.mp lt
      simp only [SoftFold.pow2, EReal.coe_ne_bot, ite_false, EReal.toReal_coe]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    | top => exact absurd lt (by simp)

/-- **The first-stage word of a lane at the shuffle count of the round is the row's factor.** -/
theorem leaf_bound (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hB : ∀ g, BiasEv Q L g X) (hS : ∀ g, ScoreEv Q L g X) {y b row : Nat}
    (lane : y % L.block < 128) (hrow : softRow (y % L.block) = row)
    (valid : QRowValid Q L (y / L.block) row) {j : Nat} {a r : Value} (st : Stage X 0 y j a r)
    (cnt : ((X.tr y).take j).countP Execution.isShfl =
      1 + Iface.preloadCount Q L (y / L.block) + shflBase b + 3) :
    ∀ x : ℝ, Rd a x → (x : EReal) ≤ ((foldAl Q L (y / L.block) b row : ℝ) : EReal) := by
  intro x hx
  obtain ⟨R, -, c, hr⟩ := stage0_ev hp hX hf hB hS lane st
  have e : R = b := by
    have h1 : shflBase R = shflBase b := by omega
    rcases lt_trichotomy R b with h | h | h
    · have := shflBase_lt h; omega
    · exact h
    · have := shflBase_lt h; omega
  subst e
  subst hrow
  have h2 := hr valid
  have : x = foldAl Q L (y / L.block) R (softRow (y % L.block)) := by
    have := hx.symm.trans h2
    exact (Option.some.inj this |> Except.ok.inj |> EReal.coe_eq_coe_iff.1)
  rw [this]

/-- **A scratch read of round `b` rebuilds to the minimum of the last stage's words of a lane of the
warp its index modulo four names**, whose stage events are at the round's shuffle counts. -/
theorem slot_facts (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (agree : ∀ n, StoreAgree L X n) (equal : WarpStoresEqual L X)
    (hR : ∀ g j, g % L.block < 128 → ∀ p ∈ Softmax.Data.roundWords X g j,
      SK.ni.Has p.1 ∧ SK.ni.Has p.2)
    (hB : ∀ g, BiasEv Q L g X) (hS : ∀ g, ScoreEv Q L g X) {gi ji b : Nat} {ac : Acc}
    {bs : List (Option Byte)} (read : X.get (gi, ji) = some ⟨2252, .rd ac bs⟩)
    (hb : pollRound 1257 ((X.tr gi).take ji) = b + 1) :
    ∃ h j' a' r', loadWord bs = minWord a' r' ∧ Stage X 3 h j' a' r' ∧ h % L.block < 128 ∧
      h / L.block = gi / L.block ∧ h % L.block / 32 % 4 = gi % L.block % 4 ∧
      ((X.tr h).take j').countP Execution.isShfl =
        1 + Iface.preloadCount Q L (gi / L.block) + shflBase b + 3 + 3 := by
  obtain ⟨v, h, j', a', r', hv, -, e, st, cta, warp, round⟩ :=
    scratch_min hp hX hf agree equal hR read
  have lane : h % L.block < 128 := by
    obtain ⟨ok, get⟩ := st
    exact data_site hp hX get (fun _ => nofun) (by show 574 < 2242 + 2 * 3; omega)
      (by show 2242 + 2 * 3 < 2331; omega)
  obtain ⟨j0, a0, r0, s0, e1, c1, p1⟩ := stage_origin hp hX 3 le_rfl h j' a' r' st
  obtain ⟨R, pr, cn, -⟩ := stage0_ev hp hX hf hB hS lane s0
  have eR : R = b := by omega
  refine ⟨h, j', a', r', ?_, st, lane, cta, warp, ?_⟩
  · unfold loadWord
    rw [hv]
    exact e
  · rw [c1, cn, eR, cta]

private theorem xor_half : ∀ a < 32, ∀ t < 16, (a ^^^ (a / 16 * 16 + t)) < 16 := by
  decide +kernel

/-- The lane of the row in the half of `h`: the same warp and half, and the row's position. -/
private theorem leaf_lane (hb : L.block = 256) {h row : Nat} (lane : h % L.block < 128)
    (hw : h % L.block / 32 % 4 = row / 16) (_hr : row < 64) :
    ∃ y, y % L.block < 128 ∧ y / L.block = h / L.block ∧ softRow (y % L.block) = row ∧
      Cover 4 h y := by
  refine ⟨h - h % 32 + h % 32 / 16 * 16 + row % 16, ?_, ?_, ?_, ?_⟩
  · rw [hb] at lane ⊢
    omega
  · rw [hb]
    omega
  · unfold softRow
    rw [hb] at hw ⊢
    omega
  · have e : (h - h % 32 + h % 32 / 16 * 16 + row % 16) % 32 = h % 32 / 16 * 16 + row % 16 := by
      omega
    refine ⟨by omega, ?_, ?_⟩
    · rw [e]
      exact xor_half _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide))
    · simp

/-- **A decision of a round in which a row's factor is below one does not skip.** -/
theorem decision_false (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X)
    (hS : ∀ g k a vals sh, X.get (g, k) = some ⟨1265, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (hB : ∀ g, BiasEv Q L g X) (hSe : ∀ g, ScoreEv Q L g X) {g k b row : Nat} {a b' c' : _}
    {recv : Value} {ok : Bool} (get : X.get (g, k) = some ⟨2255, .shfl .bfly a b' c' recv ok⟩)
    (lane : g % L.block < 128) (hb : pollRound 1257 ((X.tr g).take k) = b + 1) (hrow : row < 64)
    (valid : QRowValid Q L (g / L.block) row) (ne : foldAl Q L (g / L.block) b row ≠ 1) :
    rescaleSkip L a recv = false := by
  have blk : L.block = 256 := hp.block
  have hR : ∀ g j, g % L.block < 128 → ∀ p ∈ Softmax.Data.roundWords X g j,
      SK.ni.Has p.1 ∧ SK.ni.Has p.2 := fun _ _ lane => roundWords_ni hp hX hf hS lane
  have agree : ∀ n, StoreAgree L X n := fun _ => StoreAgree.of_safe hX safe
  have equal : WarpStoresEqual L X := warp_stores_equal hp hX hf (alpha_agree hp hX hf)
  obtain ⟨bsOf, reads, hskip⟩ := decision_four hp hX hf get lane
  obtain ⟨j0, ac0, bs0, p0, ok0, hk0, rd0, sh0, -, -, -⟩ := rescale_data hp hX get
  subst hk0
  have lt1 := fold_al_lt Q L (g / L.block) b row ne
  have rg : pollRound 1257 ((X.tr g).take j0) = b + 1 := by
    rw [← hb, poll_keep sh0 (by show 2253 ≠ 1257; omega),
      poll_keep rd0 (by show 2252 ≠ 1257; omega)]
  have claim : ∀ i < 4, ∃ x : ℝ, Rd (loadWord (bsOf i)) x ∧
      (i = row / 16 → (x : EReal) ≤ ((foldAl Q L (g / L.block) b row : ℝ) : EReal)) := by
    intro i hi
    obtain ⟨ji, aci, hrd, hcnt⟩ := reads i hi
    have cg : (g - g % 4 + i) / L.block = g / L.block := by rw [blk]; omega
    have rnd : pollRound 1257 ((X.tr (g - g % 4 + i)).take ji) = b + 1 := by
      rw [← rg]
      exact (read_round hp hX hf rd0 hrd cg.symm (by simpa using hcnt.symm)).symm
    obtain ⟨h, j', a', r', hw, st, lane_h, cta, warp, cnt⟩ :=
      slot_facts hp hX hf agree equal hR hB hSe hrd rnd
    rw [hw]
    by_cases hiW : i = row / 16
    · obtain ⟨y, ly, cy, sy, cov⟩ := leaf_lane blk lane_h (by rw [warp, blk]; omega) hrow
      have cyg : y / L.block = g / L.block := by rw [cy, cta, cg]
      have H0 : ∀ j a r, Stage X 0 y j a r → ((X.tr y).take j).countP Execution.isShfl =
          1 + Iface.preloadCount Q L (g / L.block) + shflBase b + 3 →
          ∀ x : ℝ, Rd a x → (x : EReal) ≤ ((foldAl Q L (g / L.block) b row : ℝ) : EReal) := by
        intro j a r st0 cnt0 x hx
        have := leaf_bound hp hX hf hB hSe ly sy (by rw [cyg]; exact valid) st0
          (by rw [cyg]; exact cnt0) x hx
        rwa [cyg] at this
      obtain ⟨⟨x, hx⟩, f⟩ := store_cover hp hX hf hR H0 lane_h st (by rw [cnt, cg])
      exact ⟨x, hx, fun _ => f cov x hx⟩
    · obtain ⟨⟨x, hx⟩, -⟩ := store_cover hp hX hf hR (y := 0) (v0 := ⊤) (C := 1 +
        Iface.preloadCount Q L (g / L.block) + shflBase b + 3) (fun _ _ _ _ _ _ _ => le_top)
        lane_h st (by rw [cnt, cg])
      exact ⟨x, hx, fun h => absurd h hiW⟩
  choose! xs hxs using claim
  have hW : row / 16 < 4 := by omega
  have xW : xs (row / 16) < 1 := lt_of_le_of_lt
    (EReal.coe_le_coe_iff.mp ((hxs _ hW).2 rfl)) lt1
  have bound : ∀ i < 4, min (min (xs 0) (xs 2)) (min (xs 1) (xs 3)) ≤ xs i := by
    intro i hi
    interval_cases i <;> simp [min_le_iff]
  rw [hskip]
  exact skip_false (rd_min (hxs 0 (by omega)).1 (hxs 2 (by omega)).1)
    (rd_min (hxs 1 (by omega)).1 (hxs 3 (by omega)).1) (lt_of_le_of_lt (bound _ hW) xW)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
