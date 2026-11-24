-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxMaskWord
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.TauFrame
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Flow.Code.Part060
import Kernels.TmlFa4Fwd.Flow.Code.Part062
import Kernels.TmlFa4Fwd.Flow.Code.Part064
import Kernels.TmlFa4Fwd.Flow.Code.Part065

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

/-- The raw 32-bit representation of a signed PTX operand. -/
def maskSigned (v : Int) : Value := .bits 32 ((BitVec.ofInt 32 v).setWidth 64)

private def trunc32 (v : Int) : BitVec 64 := (BitVec.ofInt 32 v).setWidth 64

private theorem trunc32_as_word (v : Int) :
    truncBits 32 (BitVec.ofInt 64 v) = trunc32 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, trunc32, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  omega

private theorem trunc32_twice (v : Int) : truncBits 32 (trunc32 v) = trunc32 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, trunc32, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  omega

private theorem trunc32_term (v : Int) : (BitVec.ofInt 32 v).setWidth 64 = trunc32 v := rfl

private theorem trunc32_nat {v : Nat} (hv : v < 2^32) :
    trunc32 (v : Int) = BitVec.ofNat 64 v := by
  rw [← trunc32_as_word, BitVec.ofInt_natCast, truncBits_ofNat hv (by decide)]

private theorem trunc32_bits (h : Nat) :
    truncBits 32 (BitVec.ofNat 64 h) = trunc32 (h : Int) := by
  rw [← trunc32_as_word, BitVec.ofInt_natCast]

private theorem trunc32_add (a b : Int) :
    truncBits 32 (trunc32 a + trunc32 b) = trunc32 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, trunc32, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_add,
    BitVec.toNat_ofInt]
  omega

private theorem trunc32_sub (a b : Int) :
    truncBits 32 (trunc32 a - trunc32 b) = trunc32 (a - b) := by
  simp only [sub_eq_add_neg]
  rw [← trunc32_add]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, trunc32, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_add,
    BitVec.toNat_ofInt, BitVec.toNat_neg]
  omega

private theorem trunc32_signed {v : Int} (hLo : -2^31 ≤ v) (hHi : v < 2^31) :
    toSigned 32 (trunc32 v) = v := by
  have hEq : toSigned 32 (trunc32 v) = (BitVec.ofInt 32 v).toInt := by
    rw [BitVec.toInt_eq_toNat_cond]
    simp only [toSigned, trunc32, BitVec.toNat_setWidth, BitVec.toNat_ofInt]
    have hMod : (v % (2^32 : Int)).toNat < 2^32 := by omega
    split <;> split <;> omega
  rw [hEq]
  exact BitVec.toInt_ofInt_eq_self (by decide) hLo hHi

private theorem maskShift {active : Int} (group : Nat)
    (hs : max (32 * (group + 1 : Nat) - active : Int) 0 < 2 ^ 32) :
    (if (trunc32 (max (32 * (group + 1 : Nat) - active : Int) 0)).toNat ≥ 32 then 0
      else trunc32 (-1) >>> (trunc32 (max (32 * (group + 1 : Nat) - active : Int) 0)).toNat) =
      BitVec.ofNat 64 (maskWord group active.toNat) := by
  have hn : 0 ≤ max (32 * (group + 1 : Nat) - active : Int) 0 := le_max_right _ _
  let n := (max (32 * (group + 1 : Nat) - active : Int) 0).toNat
  have h : (n : Int) = max (32 * (group + 1 : Nat) - active : Int) 0 :=
    Int.toNat_of_nonneg hn
  have hlt : n < 2^32 := by omega
  rw [← h, trunc32_nat hlt, toNat_ofNat_lt (by omega), show trunc32 (-1) =
    BitVec.ofNat 64 (2^32-1) from rfl]
  unfold maskWord
  -- Negative active rows have zero bits set regardless of the exact oversized shift.
  by_cases hx : active < 0
  · have h0 : active.toNat = 0 := by omega
    have hN : n ≥ 32 := by dsimp [n]; omega
    have hR : (32 : Nat) ≤ 32 * (group + 1) - active.toNat := by rw [h0]; omega
    rw [ite_eq_left hN, Nat.shiftRight_eq_zero _ _ (by
      have := Nat.pow_le_pow_right (n := 2) (by decide) hR; omega)]
    rfl
  · have he : n = 32 * (group + 1) - active.toNat := by dsimp [n]; omega
    rw [he]
    split
    · rw [Nat.shiftRight_eq_zero _ _ (by
        rename_i he
        have := Nat.pow_le_pow_right (n := 2) (by decide) he
        omega)]
      rfl
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by decide : 2^32-1 < 2^64)]
      rw [Nat.mod_eq_of_lt ((Nat.shiftRight_le _ _).trans_lt (by decide))]

private theorem truncateMaskCount (group : Nat) {active : Int}
    (hLo : -2^31 ≤ 32 * (group + 1 : Nat) - active)
    (hHi : 32 * (group + 1 : Nat) - active < 2^31) :
    (if compare .gt .s 32 (trunc32 (32 * (group + 1 : Nat) - active)) (trunc32 0)
      then trunc32 (32 * (group + 1 : Nat) - active) else trunc32 0) =
      trunc32 (max (32 * (group + 1 : Nat) - active : Int) 0) := by
  unfold compare
  rw [trunc32_signed hLo hHi, trunc32_signed (by decide : (-2^31 : Int) ≤ 0) (by decide)]
  change (if decide (0 < 32 * (group + 1 : Nat) - active) then _ else _) = _
  by_cases h : 0 < 32 * (group + 1 : Nat) - active
  · simp only [decide_eq_true h, max_eq_left h.le]
    rfl
  · simp only [decide_eq_false h, max_eq_right (le_of_not_gt h)]
    rfl

private theorem maskShiftMax {active : Int} (group : Nat)
    (hLo : -2^31 ≤ 32 * (group + 1 : Nat) - active)
    (hHi : 32 * (group + 1 : Nat) - active < 2^31) :
    let x := trunc32 (32 * (group + 1 : Nat) - active)
    let s := truncBits 32 (if compare .gt .s 32 x (trunc32 0) then x else trunc32 0)
    (if s.toNat ≥ 32 then 0 else trunc32 (-1) >>> s.toNat) =
      BitVec.ofNat 64 (maskWord group active.toNat) := by
  dsimp only
  rw [truncateMaskCount group hLo hHi, trunc32_twice]
  exact maskShift group (by omega)

private theorem maskSigned_word (v : Int) : maskSigned v = .bits 32 (trunc32 v) := rfl

private theorem maxOp_true : (IntOp.max false == IntOp.max false) = true := rfl

private theorem signedKind_true : ((some IType.s : Option IType) == some IType.s) = true := rfl

/-- The first mask acquires its shift count and the common all-ones literal. -/
theorem firstMaskInitialWord (l : Launch) (g : Nat) {active : Int}
    (hLo : -2^31 + 128 < active) (hHi : active < 2^31) :
    Seg kernel Assumptions.all l g 4 3872 [(3235, maskSigned active)] 3876
      [(3079, b32 (maskWord 0 active.toNat)), (3235, maskSigned active),
        (3080, maskSigned (-1))] := by
  have hWord := maskShiftMax 0 (active := active) (by omega) (by omega)
  intro t ht
  seg_fp ht using
    simp only [maskSigned_word, b32, trunc32_as_word, trunc32_term, trunc32_twice,
        trunc32_sub,
        maxOp_true, signedKind_true, ite_true]
    all_goals exact congrArg (Value.bits 32) hWord

def maskGap : Fin 3 → Nat
  | 0 => 3987
  | 1 => 4101
  | 2 => 4215

def maskGapWord : Fin 3 → Nat
  | 0 => 3082
  | 1 => 3084
  | 2 => 3086

/-- Between mask groups the actual three instructions recompute their common predicate word. -/
theorem nextMaskWord (site : Fin 3) (l : Launch) (g : Nat) {active : Int}
    (hLo : -2^31 + 128 < active) (hHi : active < 2^31) :
    Seg kernel Assumptions.all l g 3 (maskGap site)
      [(3235, maskSigned active), (3080, maskSigned (-1))] (maskGap site + 3)
      [(maskGapWord site, b32 (maskWord (site.val + 1) active.toNat)),
        (3235, maskSigned active), (3080, maskSigned (-1))] := by
  have hSite := site.isLt
  have hWord := maskShiftMax (site.val + 1) (active := active) (by omega) (by omega)
  fin_cases site <;> intro t ht <;>
    seg_fp ht using
      simp only [b32, trunc32_as_word, trunc32_term, trunc32_twice, trunc32_sub,
        maxOp_true, signedKind_true, ite_true]
      exact congrArg (Value.bits 32) hWord

private theorem minOp_false : (IntOp.min false == IntOp.max false) = false := rfl

private theorem trunc32_min {a b : Int} (ha : -2^31 ≤ a ∧ a < 2^31)
    (hb : -2^31 ≤ b ∧ b < 2^31) :
    (if compare .lt .s 32 (trunc32 a) (trunc32 b) then trunc32 a else trunc32 b) =
      trunc32 (min a b) := by
  unfold compare
  rw [trunc32_signed ha.1 ha.2, trunc32_signed hb.1 hb.2]
  change (if decide (a < b) then _ else _) = _
  by_cases h : a < b
  · simp only [decide_eq_true h, min_eq_left h.le]
    rfl
  · simp only [decide_eq_false h, min_eq_right (le_of_not_gt h)]
    rfl

/-- The two instructions derive the lane's query row from the stage's 128-aligned base. -/
private theorem maskRowSegment (l : Launch) (g tid base : Nat) (q keyLeft : Int)
    (htid : tid < 2^32) (hb : 128 * base + tid % 128 < 2^31) :
    Seg kernel Assumptions.all l g 2 3866
      [(3229, maskSigned keyLeft), (3219, b32 tid), (2868, b32 (128 * base)),
        (1223, maskSigned (-q))] 3868
      [(3231, maskSigned (128 * base + (tid % 128 : Nat))), (1223, maskSigned (-q)),
        (3229, maskSigned keyLeft)] := by
  have hAnd : (BitVec.ofNat 64 tid &&& BitVec.ofNat 64 127) = BitVec.ofNat 64 (tid % 128) := by
    rw [← BitVec.ofNat_and, show 127 = 2^7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hLane : tid % 128 < 128 := Nat.mod_lt _ (by decide)
  have hOr : tid % 128 ||| 128 * base = 128 * base + tid % 128 := by
    rw [Nat.or_comm]
    exact (Nat.two_pow_add_eq_or_of_lt (i := 7) hLane base).symm.trans (by simp [Nat.mul_comm])
  have he : ((128 * base + (tid % 128 : Nat)) : Int) = ((128 * base + tid % 128 : Nat) : Int) :=
    by simp
  intro t ht
  seg_fp ht using
    simp only [maskSigned_word, he, trunc32_nat (show 128 * base + tid % 128 < 2^32 by omega),
      truncBits_ofNat htid (by decide),
      truncBits_ofNat (show 128 * base < 2^32 by omega) (by decide),
      truncBits_ofNat (show tid % 128 < 2^32 by omega) (by decide),
      show truncBits 32 (BitVec.ofInt 64 127) = BitVec.ofNat 64 127 from rfl,
      hAnd, ← BitVec.ofNat_or, hOr]

private theorem maskKSegment (l : Launch) (g last key tid base : Nat) (q : Int)
    (hBlock : 128 * last ≤ key) (hKey : key < 2^31) :
    Seg kernel Assumptions.all l g 3 3863
      [(1229, b32 last), (1224, b32 key), (3219, b32 tid), (2868, b32 (128 * base)),
        (1223, maskSigned (-q))] 3866
      [(3229, maskSigned ((key : Int) - 128 * last)), (3219, b32 tid), (2868, b32 (128 * base)),
        (1223, maskSigned (-q))] := by
  have hLast : last < 2^32 := by omega
  have hShift : truncBits 32 (BitVec.ofNat 64 last <<< 7) = BitVec.ofNat 64 (128 * last) := by
    apply BitVec.eq_of_toNat_eq
    simp only [truncBits, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show last < 2^64 by omega)]
    rw [Nat.mod_eq_of_lt (show last * 2^7 < 2^64 by omega)]
    rw [Nat.mod_eq_of_lt (show last * 2^7 < 2^32 by omega)]
    rw [Nat.mod_eq_of_lt (show last * 2^7 < 2^64 by omega)]
    rw [Nat.mod_eq_of_lt (show 128 * last < 2^64 by omega)]
    omega
  have hselect : (if compare .gt .s 32 (BitVec.ofNat 64 last) (trunc32 0)
      then BitVec.ofNat 64 last else trunc32 0) = BitVec.ofNat 64 last := by
    by_cases hz : last = 0
    · subst last
      rfl
    · have hPos : (0 : Int) < last := by omega
      unfold compare
      rw [← trunc32_nat hLast, trunc32_signed (show -2^31 ≤ (last : Int) by omega)
        (by omega), trunc32_signed (by decide : (-2^31 : Int) ≤ 0) (by decide)]
      change (if decide (0 < (last : Int)) then _ else _) = _
      rw [decide_eq_true hPos]
      rfl
  intro t ht
  seg_fp ht using
    simp only [maskSigned_word, truncBits_ofNat hLast (by decide), trunc32_as_word,
      maxOp_true, signedKind_true, ite_true, hselect, hShift,
      show (trunc32 7).toNat = 7 from rfl, show ¬(7:Nat) ≥ 32 from by decide]
    simp only [ite_false, trunc32_bits key, trunc32_bits (128*last), trunc32_sub]
    push_cast
    rfl

private theorem maskActiveSegment (l : Launch) (g : Nat) (row q keyLeft : Int)
    (hLeft : -2^31 ≤ keyLeft ∧ keyLeft < 2^31)
    (hCausal : -2^31 ≤ row + (-q) + keyLeft + 1 ∧ row + (-q) + keyLeft + 1 < 2^31) :
    Seg kernel Assumptions.all l g 4 3868
      [(3231, maskSigned row), (1223, maskSigned (-q)), (3229, maskSigned keyLeft)] 3872
      [(3235, maskSigned (min (row + (-q) + keyLeft + 1) keyLeft))] := by
  intro t ht
  seg_fp ht using
    simp only [maskSigned_word, trunc32_term, trunc32_as_word, trunc32_twice, trunc32_add,
      minOp_false, signedKind_true, Bool.false_eq_true, ite_false, ite_true,
      trunc32_min hCausal hLeft]

/-- The local arithmetic derives the number of unmasked keys from the fetched lengths,
the block count, and the lane's row. The stage row base is in units of 128 rows. -/
theorem firstActiveSegment (p : Params) (l : Launch) (g batch tid base blocks : Nat)
    (htid : tid < 2^32) (hLengths : p.qLength batch ≤ p.kLength batch)
    (hK : p.kLength batch + 256 < 2^31)
    (hQ : 128 * base + tid % 128 < p.qLength batch + 256)
    (hBlocks : 128 * (blocks - 1) ≤ p.kLength batch) :
    Seg kernel Assumptions.all l g 9 3863
      [(1229, b32 (blocks-1)), (1224, b32 (p.kLength batch)),
        (3219, b32 tid), (2868, b32 (128 * base)), (1223, maskSigned (-(p.qLength batch : Int)))]
      3872 [(3235, maskSigned (firstActive p batch (128 * base + tid % 128) blocks))] := by
  have hLeft : (0 : Int) ≤ (p.kLength batch : Int) - 128 * (blocks - 1 : Nat) := by omega
  have hRow : 128 * base + tid % 128 < 2^31 := by omega
  have h1 := maskKSegment l g (blocks-1) (p.kLength batch) tid base (p.qLength batch)
    hBlocks (by omega)
  have h2 := maskRowSegment l g tid base (p.qLength batch)
    ((p.kLength batch : Int) - 128 * (blocks - 1 : Nat)) htid hRow
  have h3 := maskActiveSegment l g (128 * base + (tid % 128 : Nat)) (p.qLength batch)
    ((p.kLength batch : Int) - 128 * (blocks - 1 : Nat)) (by omega) (by omega)
  have hResult :
      min (128 * (base : Int) + (tid % 128 : Nat) + -(p.qLength batch : Int) +
        ((p.kLength batch : Int) - 128 * (blocks - 1 : Nat)) + 1)
        ((p.kLength batch : Int) - 128 * (blocks - 1 : Nat)) =
        firstActive p batch (128 * base + tid % 128) blocks := by
    rw [firstActive_min]
    omega
  rw [hResult] at h3
  exact (h1.comp h2).comp h3

/-- The integer temporaries written outside the instruction groups that mask the score pairs. -/
def firstMaskSetupWrites : List Nat :=
  (List.range 10).map (3227 + ·) ++
    [3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087, 3332, 3428, 3524]

private def maskSetupStart : Fin 4 → Nat
  | 0 => 3863
  | 1 => 3987
  | 2 => 4101
  | 3 => 4215

private def maskSetupLen : Fin 4 → Nat
  | 0 => 13
  | _ => 3

private theorem maskSetupCode (site : Fin 4) (i : Fin (maskSetupLen site)) :
    ∃ ins, kernel.code[maskSetupStart site + i.val]? = some ins ∧
      Assumptions.coreOp ins.op = true ∧
      nextPc ins.op (maskSetupStart site + i.val) = maskSetupStart site + i.val + 1 ∧
      (∀ target, ¬ BrxTarget ins.op target) ∧
      (writesRegs ins.op).all (· ∈ firstMaskSetupWrites) = true := by
  fin_cases site
  · fin_cases i
    · exact ⟨_, Flow.code_3863, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_3864, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_3865, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_3866, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_3867, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_3868, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_3869, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_3870, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_3871, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_3872, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_3873, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_3874, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_3875, rfl, rfl, fun _ => nofun, by decide⟩
  · fin_cases i
    · exact ⟨_, Flow.code_3987, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_3988, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_3989, rfl, rfl, fun _ => nofun, by decide⟩
  · fin_cases i
    · exact ⟨_, Flow.code_4101, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_4102, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_4103, rfl, rfl, fun _ => nofun, by decide⟩
  · fin_cases i
    · exact ⟨_, Flow.code_4215, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_4216, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_4217, rfl, rfl, fun _ => nofun, by decide⟩

private theorem maskCoreFrame {l : Launch} {g n : Nat} {t u : TState}
    (site : Fin 4) (hStart : maskSetupStart site ≤ t.pc)
    (hEnd : t.pc + n ≤ maskSetupStart site + maskSetupLen site)
    (hRun : run kernel Assumptions.all l g n t = some u) :
    ∀ r ∉ firstMaskSetupWrites, u.regs r = t.regs r := by
  induction n generalizing t with
  | zero =>
    have hu : t = u := Option.some.inj hRun
    subst u
    exact fun _ _ => rfl
  | succ n ih =>
    let i : Fin (maskSetupLen site) := ⟨t.pc - maskSetupStart site, by omega⟩
    have hPc : maskSetupStart site + i.val = t.pc := by dsimp [i]; omega
    obtain ⟨ins, hCode, hCore, hNext, hNoBrx, hWrites⟩ := maskSetupCode site i
    rw [hPc] at hCode hNext
    have hSite : maskSetupStart site + maskSetupLen site ≤ 4218 ∧
        3863 ≤ maskSetupStart site := by fin_cases site <;> decide
    have hOff : t.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    have hModel := Assumptions.tauStep_all_eq_nil (L := l) (g := g) hOff hCode hCore
    cases hStep : tauStep kernel [] l g t with
    | none => simp [run, hModel, hStep] at hRun
    | some v =>
      have hTail : run kernel Assumptions.all l g n v = some u := by
        simpa only [run, hModel, hStep, Option.bind_some] using hRun
      have hTau := tauStep_iff.mp hStep
      have hv : v.pc = t.pc + 1 := by
        rcases tau_core_frame hCode hTau with rfl | h
        · rfl
        · exact h.pc.elim (·.trans hNext) (fun h => (hNoBrx _ h).elim)
      intro r hr
      have hWrite : r ∉ writesRegs ins.op := fun hm =>
        hr (of_decide_eq_true (List.all_eq_true.mp hWrites r hm))
      exact (ih (by omega) (by omega) hTail r hr).trans (tau_core_regs hCode hTau hWrite)

/-- The initial geometry and word setup leaves the scores and publication arguments live. -/
theorem firstMaskSetupFrame {l : Launch} {g n : Nat} {t u : TState}
    (hStart : 3863 ≤ t.pc) (hEnd : t.pc + n ≤ 3876)
    (hRun : run kernel Assumptions.all l g n t = some u) :
    ∀ r ∉ firstMaskSetupWrites, u.regs r = t.regs r :=
  maskCoreFrame 0 hStart hEnd hRun

/-- A subsequent word setup keeps every loaded score and already masked scalar. -/
theorem nextMaskSetupFrame {l : Launch} {g : Nat} {t u : TState}
    (site : Fin 3) (hPc : t.pc = maskGap site)
    (hRun : run kernel Assumptions.all l g 3 t = some u) :
    ∀ r ∉ firstMaskSetupWrites, u.regs r = t.regs r := by
  apply maskCoreFrame ⟨site.val + 1, by have := site.isLt; omega⟩ _ _ hRun
  · fin_cases site <;> rw [hPc] <;> exact Nat.le_refl _
  · fin_cases site <;> rw [hPc] <;> exact Nat.le_refl _

end PTX.Kernels.TmlFa4Fwd.Softmax
