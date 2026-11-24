-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.CollPos
public import Kernels.TmlFa4Fwd.Proof.Progress.Time
import Kernels.TmlFa4Fwd.Proof.Lib.RoundsBound
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A state of the rescale rounds among its warp's collectives -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Progress (clk slotOf bandC primeBase endBase scanBase bmax
  passTime)
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (RefQ ptsOf passed before inRound preR tailR
  allSites mem_allSites)
open PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp (rvN refV)

namespace CorrColl
noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

def cN (st : Fin 2) (s : Correction.Site) : Nat := (ptsOf (.nb st)).countP (before s)

/-- The ballots of the round before a site. -/
def bN (s : Correction.Site) : Nat := if inRound s.pc then CorrWarp.sv s else 0

/-- The round site check: the ballots of the round before a site, its slot and its time. -/
def rsChk (s : Correction.Site) : Bool :=
  match Progress.Cr.part s with
  | none => !s.isRvote && (s.late || preR s) && !tailR s && !inRound s.pc &&
      (Progress.Cr.late s == s.late)
  | some (st, past) =>
    let pb := if past then 1 else 0
    (CorrWarp.epi s == .ready 0) && s.hasUk && !s.late && decide (bN s ≤ 2) &&
    decide (pb ≤ cN st s) && (s.wcoll == s.isRvote) &&
    (preR s && !inRound s.pc && !tailR s || inRound s.pc && !tailR s ||
      tailR s && !inRound s.pc) &&
    (tailR s && !s.isRvote || (if s.isRvote then
        inRound s.pc && cN st s - pb == 1 && past && bN s == st.val && s == .rvote st
      else decide (cN st s - pb < 1 + bN s / 2) || (cN st s - pb == 1 + bN s / 2 &&
        decide (bandC st.val + (Progress.Cr.tailOff s).getD (Progress.Cr.roundOff s) <
          bandC (bN s % 2) + 4))))

theorem rs_chk : allSites.all rsChk = true := by decide +kernel

theorem rs_ok (s : Correction.Site) : rsChk s = true :=
  List.all_eq_true.mp rs_chk s (mem_allSites s)

theorem nb_rnd (st : Fin 2) : (ptsOf (.nb st)).countP inRound = 1 := by
  revert st; decide

theorem trip_inj {a b B : Int} (ha : 0 ≤ a ∧ a < B) (hb : 0 ≤ b ∧ b < B)
    (hB : B < 2 ^ 31) (h : Epilogue.i32 (a - B) = Epilogue.i32 (b - B)) : a = b := by
  have h' := congrArg BitVec.toNat h
  simp only [Epilogue.i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt] at h'
  omega

theorem Bs_lt (v : Correction.V) : Correction.Bs p L g v < 2 ^ 31 := by
  unfold Correction.Bs
  generalize Epilogue.r32 (Correction.blocks p L g v) = x
  have := Nat.mod_lt x.toNat (show 0 < 2 ^ 32 by decide)
  simp only [toSigned]
  split <;> omega

section
variable (hp : Pre p L m)
include hp

omit hp in
/-- **A state of the rounds.** -/
theorem corr_round {d : Correction.D} {n : Cls → Nat} {r ℓ rv : Nat} {a : CorrTile}
    (hQ : RefQ p L g d (fun c => n (.corr c)) r ℓ) (hrv : CorrWarp.RvAt p L g d rv)
    (haV : a.V = rvN (Correction.Bs p L g d.v)) (hb : a.V / 2 + 1 ≤ bmax p)
    {x : Fin 2 × Bool} (hpl : Progress.Cr.part d.site = some x) :
    CorrM p a (a.ch + rv) (Progress.Cr.time p d n)
      (if d.site.isRvote then some d.site else none) := by
  obtain ⟨st, past⟩ := x
  have hck := rs_ok d.site
  simp only [rsChk, hpl, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Bool.not_eq_true'] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hlate⟩, hb2⟩, hpb⟩, hwc⟩, hreg⟩, hck⟩ := hck
  have hnb := hQ.cnt (.nb st) (by simp)
  simp only [passed, nb_rnd, Nat.mul_one] at hnb
  change n (.corr (.nb st)) = cN st d.site + r at hnb
  have hoff := Progress.Cr.off_lt st d.site
  have ht : Progress.Cr.time p d n = clk p (slotOf p (n (.corr (.nb st)) -
      if past then 1 else 0)) (bandC st.val +
        (Progress.Cr.tailOff d.site).getD (Progress.Cr.roundOff d.site)) := by
    simp only [Progress.Cr.time, hpl, Progress.Cr.slot]
  rw [hnb] at ht
  have htE : Progress.Cr.time p d n < endBase p := by
    have hend : Progress.tailBase p + 4096 = endBase p := rfl
    rw [ht]
    exact (Progress.clk_lt_tail hoff).trans_le (by omega)
  have hBl := Bs_lt (p := p) (L := L) (g := g) d.v
  -- the ballots
  have hrv' : (tailR d.site = true ∧ rv = a.V) ∨
      (tailR d.site = false ∧ rv = 2 * r + bN d.site ∧ 2 * r + bN d.site ≤ a.V ∧
        (inRound d.site.pc = true → 2 * r + 2 ≤ a.V)) := by
    simp only [CorrWarp.RvAt, hlate, Bool.false_eq_true, ite_false] at hrv
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hreg
    rcases hreg with (⟨⟨h1, h2⟩, h3⟩ | ⟨h2, h3⟩) | ⟨h3, h2⟩
    · simp only [h2, h3, Bool.false_eq_true, ite_false] at hrv
      have h0 := hQ.pre h1
      have hbz : bN d.site = 0 := by simp [bN, h2]
      refine .inr ⟨h3, by omega, by omega, fun h => by rw [h2] at h; cases h⟩
    · simp only [h2, ite_true] at hrv
      obtain ⟨r', hr1, hr2, hr3⟩ := hrv
      obtain ⟨hl1, hl2⟩ := hQ.loop h2
      have hrr : (r' : Int) = r := trip_inj ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hBl
        (hr2.symm.trans hl2)
      obtain rfl : r' = r := by exact_mod_cast hrr
      have hbz : bN d.site = CorrWarp.sv d.site := by simp [bN, h2]
      have hV : 2 * r' + 2 ≤ a.V := by
        rw [haV]; unfold rvN; split <;> omega
      exact .inr ⟨h3, by omega, by omega, fun _ => hV⟩
    · simp only [h2, h3, Bool.false_eq_true, ite_false, ite_true] at hrv
      exact .inl ⟨h3, by rw [hrv, haV]⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hck
  rcases hrv' with ⟨htl, hj⟩ | ⟨htl, hj, hjV, hjR⟩
  · -- the final stage
    have hnr : d.site.isRvote = false := by
      rcases hck with ⟨-, h⟩ | h
      · exact h
      · split at h
        · simp only [Bool.and_eq_true] at h
          rw [Bool.or_eq_true] at hreg
          rename_i hrvt
          simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hreg
          rcases hreg with (⟨-, h3⟩ | ⟨-, h3⟩) | ⟨-, h3⟩
          · rw [htl] at h3; cases h3
          · rw [htl] at h3; cases h3
          · rw [h.1.1.1.1] at h3; cases h3
        · rename_i hrvt; simpa using hrvt
    rw [hnr]
    exact .inr (.inl ⟨rfl, rv, by omega, rfl, htE, fun h => by omega⟩)
  · have hck := hck.resolve_left (fun h => by rw [htl] at h; cases h.1)
    cases hr : d.site.isRvote with
    | true =>
      simp only [hr, ite_true, Bool.and_eq_true, beq_iff_eq] at hck
      obtain ⟨⟨⟨⟨hin, hc1⟩, hps⟩, hbs⟩, hs⟩ := hck
      have hst := st.isLt
      have hV := hjR hin
      refine .inr (.inr ⟨r, st, by omega, by omega, by omega, ?_, ?_⟩)
      · rw [ht, Progress.slotOf_eq (by omega)]
        have e1 : cN st d.site + r - (if past then 1 else 0) = 1 + r := by omega
        rw [e1, hs]
        rfl
      · simp only [ite_true, hs]
    | false =>
      simp only [hr, Bool.false_eq_true, ite_false, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq] at hck
      refine .inr (.inl ⟨rfl, rv, by omega, rfl, htE, fun hlt => ?_⟩)
      rw [ht]
      have hd : rv / 2 = r + bN d.site / 2 := by omega
      have hm : rv % 2 = bN d.site % 2 := by omega
      rw [hd, hm]
      rcases hck with h | ⟨h, h2⟩
      · refine Progress.clk_lt_of_slot ?_ hoff
        have : slotOf p (cN st d.site + r - if past then 1 else 0) ≤
            cN st d.site + r - if past then 1 else 0 := by unfold slotOf; omega
        omega
      · have : slotOf p (cN st d.site + r - if past then 1 else 0) ≤
            cN st d.site + r - if past then 1 else 0 := by unfold slotOf; omega
        rcases Nat.lt_or_ge (slotOf p (cN st d.site + r - if past then 1 else 0))
          (1 + (r + bN d.site / 2)) with h3 | h3
        · exact Progress.clk_lt_of_slot h3 hoff
        · have e1 : slotOf p (cN st d.site + r - if past then 1 else 0) =
              1 + (r + bN d.site / 2) := by omega
          rw [e1]
          exact Progress.clk_lt_of_off h2

/-- A state's tile, from the picked tile. -/
theorem corr_tile {w : Nat} (hg : g < L.threads) (hw : Prologue.warpIndex L g = w)
    {R : Nat} {bal : BitVec 64} (hP : Epilogue.Picked p L g R bal) :
    ∃ a : CorrTile, IsCorrTile p L w (g / L.block) g a ∧
      a.ch = 4 + 7 * (R + 1) + Epilogue.selN bal ∧
      a.V = rvN (Correction.Bs p L g (refV p L g R bal)) := by
  have hCR : CorrRounds p L g ((Correction.Bs p L g (corrRef p L g R bal)).toNat - 1) :=
    ⟨R, bal, hP, rfl⟩
  have hle := mma_rounds_bmax hp hg (hCR.mma hp hg)
  obtain ⟨V, hV⟩ : ∃ V, V = rvN (Correction.Bs p L g (refV p L g R bal)) := ⟨_, rfl⟩
  refine ⟨⟨_, V⟩, ⟨hg, hw, rfl, ?_, R, bal, hP, rfl, hV⟩, rfl, hV⟩
  have h2 : V / 2 = (Correction.Bs p L g (corrRef p L g R bal)).toNat - 1 := by
    rw [hV, show Correction.Bs p L g (corrRef p L g R bal) =
      Correction.Bs p L g (refV p L g R bal) from rfl]
    unfold rvN
    split <;> omega
  show V / 2 + 1 ≤ _
  omega

end

end
end CorrColl
end PTX.Kernels.TmlFa4Fwd.Proof
