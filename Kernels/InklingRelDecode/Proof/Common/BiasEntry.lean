-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Data
public import Kernels.InklingRelDecode.Proof.Common.DataRef
import Kernels.InklingRelDecode.Proof.Prologue.PreloadCount
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Kernels.InklingRelDecode.Proof.Lib.Geometry
import Lemmas.Flow.Arith32Norm
import Lemmas.Flow.Arith32WordWide

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof Arith32

private theorem addi_neg {a k : Nat} (ha : a < 2 ^ 32) (hk : k < 2 ^ 31) :
    addi (W a) (-(k : Int)) = W ((a + 2 ^ 32 - k) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [addi, i32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt]
  omega

private theorem positive_W (n : Nat) (h : n < 2 ^ 31) :
    Prologue.Control.positive (W n) = W n := by
  have test : scmpi .gt .s (W n) 0 = decide (n > 0) := scmp_gt_W h (by decide)
  simp only [Prologue.Control.positive, test, decide_eq_true_eq, r32_W (show n < 2 ^ 32 by omega)]
  split
  · rfl
  · have hn : n = 0 := by omega
    rw [hn]; rfl

private theorem scmp_neg_W {a : Nat} (h : 2 ^ 31 ≤ a) (h2 : a < 2 ^ 32) :
    scmpi .gt .s (W a) 0 = false := by
  simp only [scmpi, PTX.compare, r32_W h2]
  have hn : ¬ a < 2 ^ (32 - 1) := by norm_num; omega
  have s1 : toSigned 32 (W a) = (a : Int) - 2 ^ 32 := by
    simp only [toSigned, W, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt h2]
    simp only [hn, ↓reduceIte]
  have s2 : toSigned 32 (i32 0) = 0 := by decide
  rw [s1, s2]
  simp only [decide_eq_false_iff_not]
  omega

private theorem sub_word (a b : Nat) (hab : b ≤ a) (ha : a < 2 ^ 32) :
    Prologue.Control.subValue (b32 a) (b32 b) = b32 (a - b) := by
  change Value.bits 32 (sub32 (Lib.word (b32 a)) (Lib.word (b32 b))) = _
  have w1 : Lib.word (b32 a) = W a := r32_W ha
  have w2 : Lib.word (b32 b) = W b := r32_W (by omega)
  rw [w1, w2, sub32_W hab ha]
  rfl

/-- The bias block threshold of the entry: the first block with relative logits. -/
theorem entry_nbias {Q L m g w d} (hp : Pre Q L m) (hg : g < L.threads)
    (first : d.first = b32 (Q.qStart ((L.ctaidOf (g/L.block)).get .z)))
    (last : d.last = b32 (Q.qStart (((L.ctaidOf (g/L.block)).get .z) + 1)))
    (seq : d.seq = b32 (Q.seqK ((L.ctaidOf (g/L.block)).get .z))) :
    (dataEntry Q L g w d).nbias = Q.nBias ((L.ctaidOf (g/L.block)).get .z) ∧
    (dataEntry Q L g w d).biasOffset = Q.blocks ((L.ctaidOf (g/L.block)).get .z) * 128 := by
  obtain ⟨_, _, hr⟩ := Lib.coordinate_bounds hp hg
  generalize (L.ctaidOf (g/L.block)).get .z = r at *
  have bound := (Lib.qStart_mono hp (r := r + 1) (r' := Q.b) (by omega) le_rfl).trans hp.cuEnd
  have tok := hp.nTokRange
  have len := hp.qLenSeq r hr
  have seqBound := hp.seqRange r hr
  have mono := hp.cuMono r hr
  have prior : Prologue.Control.past d = W (Q.past r) := by
    unfold Prologue.Control.past
    rw [first, last, seq, sub_word _ _ mono (by omega)]
    change Lib.word (Prologue.Control.subValue (b32 (Q.seqK r)) (b32 (Q.qLen r))) = _
    rw [sub_word _ _ len (by omega)]
    exact r32_W (by omega)
  have pastLe : Q.past r ≤ Q.seqK r := Nat.sub_le _ _
  constructor
  · change (shru (Prologue.Control.positive (addi (Prologue.Control.past d) (-1023))) 7).toNat = _
    rw [prior]
    have h1 : addi (W (Q.past r)) (-1023) = W ((Q.past r + 2 ^ 32 - 1023) % 2 ^ 32) := by
      have := addi_neg (a := Q.past r) (k := 1023) (by omega) (by norm_num)
      simpa using this
    rw [h1]
    by_cases hc : 1023 ≤ Q.past r
    · rw [show (Q.past r + 2 ^ 32 - 1023) % 2 ^ 32 = Q.past r - 1023 by omega,
        positive_W _ (by omega), shru_int (by omega) (by norm_num) (by norm_num)]
      have e7 : Int.toNat 7 = 7 := rfl
      rw [e7, toNat_W (by have := Nat.div_le_self (Q.past r - 1023) (2 ^ 7); omega)]
      rfl
    · rw [show (Q.past r + 2 ^ 32 - 1023) % 2 ^ 32 = Q.past r + 2 ^ 32 - 1023 by omega]
      have neg : scmpi .gt .s (W (Q.past r + 2 ^ 32 - 1023)) 0 = false :=
        scmp_neg_W (by omega) (by omega)
      simp only [Prologue.Control.positive, neg]
      have s0 : (shru 0 7).toNat = 0 := by decide
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [s0]
      have z : Q.nBias r = 0 := by
        have : Q.past r < 1023 := by omega
        unfold Params.nBias
        omega
      exact z.symm
  · change (andi (add32 (addi (Lib.word d.seq) 127)
      (shru (shrs (addi (Lib.word d.seq) 127) 31) 25)) (-128)).toNat = _
    have word : Lib.word (b32 (Q.seqK r)) = W (Q.seqK r) := r32_W (by omega)
    have a127 : addi (W (Q.seqK r)) 127 = W (Q.seqK r + 127) :=
      addi_W (n := 127) (by norm_num) (by omega)
    rw [seq, word, a127]
    have sh : shrs (W (Q.seqK r + 127)) 31 = W ((Q.seqK r + 127) / 2 ^ 31) :=
      toNat_shrs_W (by omega) (k := 31) (by norm_num)
    have q0 : (Q.seqK r + 127) / 2 ^ 31 = 0 := by omega
    rw [sh, q0]
    have sh2 : shru (W 0) 25 = W 0 := by
      have := shru_int (a := 0) (n := 25) (by norm_num) (by norm_num) (by norm_num)
      simpa using this
    rw [sh2, add32_W (by omega), Nat.add_zero]
    have m : (-128 : Int) = -((2 ^ 7 : Nat) : Int) := by norm_num
    rw [m, andi_W_negpow (by omega) (by norm_num), toNat_W (by omega)]
    unfold Params.blocks
    omega

private theorem block_late (s : Prologue.Site) (b : Fin 3) (h : s.block = some b) :
    41 < s.pc := by
  have h1 : ∀ b j, 41 < Prologue.pbPc b j := by decide
  have h2 : ∀ b, 41 < Prologue.arrPc b := by decide
  have h3 : ∀ b h, 41 < Prologue.lbPc b h := by decide
  have h4 : ∀ b, 41 < Prologue.pshPc b := by decide
  have h5 : ∀ b j, 41 < Prologue.pelPc b j := by decide
  have h6 : ∀ b j, 41 < Prologue.ptcPc b j := by decide
  cases s <;> simp only [Prologue.Site.block, reduceCtorEq] at h <;>
    simp only [Prologue.Site.pc] <;>
    first | exact h1 _ _ | exact h2 _ | exact h3 _ _ | exact h4 _ | exact h5 _ _ | exact h6 _ _

/-- **A prologue state at a site of a preload block is in a block the CTA preloads.** -/
theorem pro_gate {Q L m X g k w d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads) (hk : k ≤ (X.tr g).length)
    (hs : Frame.stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.prologue w), .inl d⟩, n)))
    (nu : Frame.NoUbBefore X g k) :
    ∀ b : Fin 3, d.site.block = some b → b.val < Iface.preloadCount Q L (g / L.block) := by
  intro b hb
  have late := block_late d.site b hb
  have hist := (data_reference hp hX hk hs (prefix_ub_zero hs nu)).1
  have cap := Prologue.preload_count hp hg (hist.known.first (by omega))
    (hist.known.last (by omega)) (hist.known.seq (by omega))
  rw [← cap]
  exact lt_min b.isLt (hist.block b hb)

end PTX.Kernels.InklingRelDecode.Proof
