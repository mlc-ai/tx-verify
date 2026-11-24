-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxMaskLayout

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Assumption PTX.Proof

noncomputable section

def firstMaskWordReg (group : Nat) : Nat :=
  if group = 0 then 3079 else 3080 + 2 * group

def maskScratch (group pair : Nat) : Nat := 3237 + 96 * group + 6 * pair

def maskPred (group pair : Nat) : Nat := 494 + 32 * group + 2 * pair

def firstMaskPairRegs (group pair : Nat) : MaskPairRegs :=
  ⟨7897 + 32 * group + 2 * pair, maskScratch group pair + 3,
    maskScratch group pair + (if pair = 15 then 4 else 5)⟩

private def maskInf : Opnd := .f32imm 0xFF800000

private def maskPairItems (group pair : Nat) : List RItem :=
  let src := firstMaskWordReg group
  let a := maskScratch group pair
  let p := maskPred group pair
  let d := firstMaskPairRegs group pair
  let low := RItem.selp d.low (if pair = 0 then .reg (a + 1) else maskInf)
    (if pair = 0 then maskInf else .reg (a + 1)) p
  let high := RItem.selp d.high maskInf (.reg (a + 2)) (p + 1)
  .andImm a src (2 ^ (2 * pair)) :: .setpImm (if pair = 0 then .ne else .eq) .b p a 0 ::
    .unpack (a + 1) (a + 2) d.packed :: low ::
    if pair = 15 then [.setpImm .gt .s (p + 1) src (-1), high] else
      [.andImm (a + 4) src (2 ^ (2 * pair + 1)), .setpImm .eq .b (p + 1) (a + 4) 0, high]

private theorem maskPairLength (g j : Nat) :
    (maskPairItems g j).length = if j = 15 then 6 else 7 := by
  by_cases hj : j = 15 <;> simp [maskPairItems, hj]

private theorem rCode_slice (K K' : Kernel) (pc pc' : Nat) (items : List RItem)
    (h : ∀ n < items.length, K.code[pc+n]? = K'.code[pc'+n]?) :
    rCodeB K pc items = rCodeB K' pc' items := by
  induction items generalizing pc pc' with
  | nil => rfl
  | cons it is ih =>
    have hc : K.code[pc]? = K'.code[pc']? := by simpa using h 0 (by simp)
    have hIt : it.codeB K pc = it.codeB K' pc' := by
      cases it <;> simp only [RItem.codeB, hc]
    simp only [rCodeB, hIt]
    rw [ih]
    intro n hn
    simpa only [Nat.add_assoc, Nat.add_comm 1 n] using h (n+1) (by simp; omega)

private def maskSlice : List Instr :=
  Decoded.code121 ++ Decoded.code122 ++ Decoded.code123 ++ Decoded.code124 ++
    Decoded.code125 ++ Decoded.code126 ++ Decoded.code127 ++ Decoded.code128 ++
    Decoded.code129 ++ Decoded.code130 ++ Decoded.code131 ++ Decoded.code132 ++
    Decoded.code133 ++ Decoded.code134 ++ Decoded.code135

private theorem maskSlice_eq : maskSlice = (Decoded.kernel.code.drop 3872).take 480 := by
  kernel_rfl

private def maskGroupKernel (group : Nat) : Kernel :=
  { kernel with code := firstMaskGroupCode group }

private theorem maskPairGroupCode (group : Fin 4) :
    ∀ j : Fin 16, rCodeB (maskGroupKernel group) (7 * j) (maskPairItems group j) = true := by
  fin_cases group <;> decide +kernel

private theorem maskPairCode (group : Fin 4) (j : Fin 16) :
    rCodeB kernel (firstMaskGroupStart group + 7 * j) (maskPairItems group j) = true := by
  rw [rCode_slice kernel (maskGroupKernel group) _ (7 * j) (maskPairItems group j)]
  · exact maskPairGroupCode group j
  · intro n hn
    rw [maskPairLength] at hn
    have hg := group.isLt
    have hj := j.isLt
    have h0 : 3872 ≤ firstMaskGroupStart group := by unfold firstMaskGroupStart; omega
    have h1 : 7 * (j : Nat) + n < 111 := by split at hn <;> omega
    have h2 : 7 * (j : Nat) + n + (firstMaskGroupStart group - 3872) < 480 := by
      unfold firstMaskGroupStart
      omega
    set_option maxRecDepth 100000 in
    change Decoded.kernel.code[firstMaskGroupStart group + 7 * j + n]? =
      (((maskSlice.drop (firstMaskGroupStart group - 3872)).take 111)[7 * j+n]?)
    set_option maxRecDepth 100000 in
    rw [List.getElem?_take, ite_eq_left h1, List.getElem?_drop, maskSlice_eq,
      List.getElem?_take, ite_eq_left (by omega), List.getElem?_drop]
    congr 1
    omega

private theorem maskShape (group : Fin 4) :
    ∀ j : Fin 16, let items := maskPairItems group j
      let d := firstMaskPairRegs group j
      rVaryingB items = true ∧ rReadsB [firstMaskWordReg group, d.packed] items = true := by
  fin_cases group <;> decide +kernel

private theorem maskWord_bound (group active : Nat) : maskWord group active < 2^32 :=
  (Nat.shiftRight_le _ _).trans_lt (by omega)

private theorem mask_trunc {x : Nat} (h : x < 2^32) :
    truncBits 32 (BitVec.ofNat 64 x) = BitVec.ofNat 64 x := by
  rw [truncBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x < 2^64 by omega),
    Nat.mod_eq_of_lt h]

private theorem andBit {x bit : Nat} (hx : x < 2^32) (hb : bit < 32) :
    truncBits 32 (BitVec.ofNat 64 x) &&& truncBits 32 (BitVec.ofInt 64 (2 ^ bit)) =
      BitVec.ofNat 64 (if x.testBit bit then 2 ^ bit else 0) := by
  have hp := Nat.pow_lt_pow_right (by decide : 1 < 2) hb
  rw [mask_trunc hx]
  have he : (BitVec.ofInt 64 (2 ^ bit)) = BitVec.ofNat 64 (2 ^ bit) := by
    rw [← BitVec.ofInt_natCast, Int.natCast_pow]
    rfl
  rw [he, mask_trunc hp]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show x < 2^64 by omega), Nat.mod_eq_of_lt (show 2^bit < 2^64 by omega),
    Nat.mod_eq_of_lt (show (if x.testBit bit then 2^bit else 0) < 2^64 by split <;> omega)]
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases h : b = bit
  · subst b
    cases x.testBit bit <;> simp
  · cases x.testBit bit <;> simp [Ne.symm h]

private theorem maskBitPred {x bit : Nat} (hx : x < 2^32) (hb : bit < 32) (direct : Bool) :
    compare (if direct then .ne else .eq) .b 32
      (truncBits 32 (truncBits 32 (BitVec.ofNat 64 x) &&&
        truncBits 32 (BitVec.ofInt 64 (2 ^ bit)))) (truncBits 32 (BitVec.ofInt 64 0)) =
      if direct then x.testBit bit else !(x.testBit bit) := by
  rw [andBit hx hb]
  have hp := Nat.pow_lt_pow_right (by decide : 1 < 2) hb
  have hzero : truncBits 32 (BitVec.ofInt 64 0) = 0 := by decide
  have hnat : (BitVec.ofNat 64 (2^bit)).toNat = 2^bit :=
    Nat.mod_eq_of_lt (show 2^bit < 2^64 by omega)
  rw [hzero]
  cases x.testBit bit <;> cases direct <;> simp [compare, mask_trunc hp, hnat] <;> decide

private theorem maskSignPred {x : Nat} (hx : x < 2^32) :
    compare .gt .s 32 (truncBits 32 (BitVec.ofNat 64 x))
      (truncBits 32 (BitVec.ofInt 64 (-1))) = !(x.testBit 31) := by
  have hneg : toSigned 32 (truncBits 32 (BitVec.ofInt 64 (-1))) = -1 := by decide
  rw [mask_trunc hx]
  change decide (toSigned 32 (BitVec.ofNat 64 x) > _) = _
  rw [hneg]
  simp only [toSigned, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show x < 2^64 by omega), Nat.mod_eq_of_lt hx]
  have hBit : x.testBit 31 = decide (2^31 ≤ x) := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rw [decide_eq_decide]
    omega
  rw [hBit, ← decide_not, decide_eq_decide]
  split <;> omega

private theorem maskBitAbsent {x bit : Nat} (hx : x < 2^32) (hb : bit < 32) :
    compare .eq .b 32
      (truncBits 32 (truncBits 32 (BitVec.ofNat 64 x) &&&
        truncBits 32 (BitVec.ofInt 64 (2 ^ bit)))) (truncBits 32 (BitVec.ofInt 64 0)) =
      !(x.testBit bit) := maskBitPred hx hb false

private theorem maskBitPresent {x bit : Nat} (hx : x < 2^32) (hb : bit < 32) :
    compare .ne .b 32
      (truncBits 32 (truncBits 32 (BitVec.ofNat 64 x) &&&
        truncBits 32 (BitVec.ofInt 64 (2 ^ bit)))) (truncBits 32 (BitVec.ofInt 64 0)) =
      x.testBit bit := maskBitPred hx hb true

private theorem maskSplit (a b : Option ℝ) :
    splitValue 64 (Value.pair (scoreValue a) (scoreValue b)) = (scoreValue a, scoreValue b) := by
  cases a <;> cases b <;> rfl

private theorem maskPackedBytes (a b : Option ℝ) :
    (Value.pair (scoreValue a) (scoreValue b)).bytes = 8 := by
  cases a <;> cases b <;> rfl

private def maskValues (group x : Nat) (a b : Option ℝ) (r : Nat) : Value :=
  if r = firstMaskWordReg group then b32 x else Value.pair (scoreValue a) (scoreValue b)

private theorem maskOpnd (v : Bool) (r : Nat) :
    isRegOrF32 (if v then maskInf else .reg r) = true ∧
    isRegOrF32 (if v then .reg r else maskInf) = true := by
  cases v <;> exact ⟨rfl, rfl⟩

private theorem maskSel (V : Nat → Value) (v : Bool) (r : Nat) :
    opndVal V (if v then maskInf else .reg r) = (if v then scoreValue none else V r) ∧
    opndVal V (if v then .reg r else maskInf) = (if v then V r else scoreValue none) := by
  cases v <;> exact ⟨rfl, rfl⟩

private theorem selectMaskedValue (v : Bool) (s : Option ℝ) :
    (if !v then scoreValue none else scoreValue s) = scoreValue (if v then s else none) ∧
    (if v then scoreValue s else scoreValue none) = scoreValue (if v then s else none) := by
  cases v <;> exact ⟨rfl, rfl⟩

private theorem maskSetpEq (p r : Nat) :
    IntInstr.rule ⟨.setp .eq none, .int .b 32, false, [some p], [.reg r, .imm 0]⟩ =
      some .threadInt := rfl

private theorem maskSetpNe (p r : Nat) :
    IntInstr.rule ⟨.setp .ne none, .int .b 32, false, [some p], [.reg r, .imm 0]⟩ =
      some .threadInt := rfl

private theorem maskSetpSign (p r : Nat) :
    IntInstr.rule ⟨.setp .gt none, .int .s 32, false, [some p], [.reg r, .imm (-1)]⟩ =
      some .threadInt := rfl

private theorem maskPairEval (group pair x : Nat) (hg : group < 4) (hj : pair < 16)
    (hx : x < 2^32) (a b : Option ℝ) :
    let V := maskValues group x a b
    let items := maskPairItems group pair
    let dst := firstMaskPairRegs group pair
    rReq V items = true ∧ rCond V items ∧
      rFinal V items dst.low = scoreValue (if x.testBit (2 * pair) then a else none) ∧
      rFinal V items dst.high = scoreValue (if x.testBit (2 * pair + 1) then b else none) := by
  have hreg : 3000 < firstMaskWordReg group ∧ firstMaskWordReg group < 3100 := by
    unfold firstMaskWordReg
    split <;> omega
  have hlo := @maskBitAbsent x (2*pair) hx (by omega)
  have hhi := @maskBitAbsent x (2*pair+1) hx (by omega)
  have hpos := @maskBitPresent x (2*pair) hx (by omega)
  have hsgn := maskSignPred hx
  by_cases hLast : pair = 15 <;> by_cases hFirst : pair = 0
  all_goals try omega
  all_goals
    simp only [maskPairItems, hFirst, hLast, ite_true, ite_false,
      firstMaskPairRegs, maskScratch, maskPred]
    try subst pair
    repeat' first
      | simp only [rReq, rCond, rFinal, RItem.req, RItem.cond, RItem.upd, RItem.vals,
          List.foldl_cons, List.foldl_nil]
      | simp (disch := omega) only [Function.update_self, Function.update_of_ne,
          maskValues, ite_eq_right, ite_true, b32, bitsOf, maskSplit, maskPackedBytes,
          hlo, hhi, hpos, hsgn, isBits, isPred, predOf, maskSetpEq, maskSetpNe, maskSetpSign,
          maskOpnd, maskSel, scoreValue_bytes, Bool.and_true, true_and, beq_self_eq_true,
          and_true, selectMaskedValue]

private theorem maskPairLocal (group pair : Nat) : NoItemRule Assumptions.all
    (maskPairItems group pair) := by
  intro it hi _ l g t a ha
  rw [Assumptions.all, List.mem_append, List.mem_append, List.mem_singleton] at ha
  rcases ha with (ha | ha) | rfl
  · simp only [Assumptions.numeric, List.mem_cons, List.not_mem_nil, or_false] at ha
    by_cases hj : pair = 15
    · simp only [maskPairItems, hj, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases ha with rfl | rfl | rfl | rfl | rfl <;> rfl
    · simp only [maskPairItems, hj, ite_false, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases ha with rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [Assumptions.synchronization, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> rfl
  · rfl

private theorem maskWrites (g j r : Nat) (hr : r ∈ rWrites (maskPairItems g j)) :
    (maskPred g j ≤ r ∧ r < maskPred g j + 2) ∨
      (maskScratch g j ≤ r ∧ r < maskScratch g j + 6) := by
  by_cases hj : j = 15 <;> simp [maskPairItems, hj, rWrites, RItem.writes,
    firstMaskPairRegs] at hr
  all_goals simp only [maskScratch, maskPred] at hr ⊢
  all_goals omega

section
variable {l : Launch} {g : Nat}

private theorem maskPairTrace {t : TState} (group : Fin 4) (j : Fin 16) (x : Nat) (hx : x < 2^32)
    (a b : Option ℝ) (ht : At t (firstMaskGroupStart group + 7 * j) [])
    (hword : t.regs (firstMaskWordReg group) = some (b32 x))
    (hscore : t.regs (firstMaskPairRegs group j).packed =
      some (Value.pair (scoreValue a) (scoreValue b))) :
    ∃ u, At u ((firstMaskGroupStart group + 7 * j) + (if (j : Nat) = 15 then 6 else 7)) [] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      u.regs (firstMaskPairRegs group j).low =
        some (scoreValue (if x.testBit (2*j) then a else none)) ∧
      u.regs (firstMaskPairRegs group j).high =
        some (scoreValue (if x.testBit (2*j+1) then b else none)) ∧
      ∀ r, r ∉ rWrites (maskPairItems group j) → u.regs r = t.regs r := by
  let ops := maskPairItems group j
  let dom := [firstMaskWordReg group, (firstMaskPairRegs group j).packed]
  let V := maskValues group x a b
  have hk (n : Nat) (hn : n < ops.length) : t.pc + n ∉ Assumptions.swExp2Sites := by
    have hgroup := group.isLt
    have hj := j.isLt
    change n < (maskPairItems group j).length at hn
    rw [maskPairLength] at hn
    rw [ht.1]
    simp only [firstMaskGroupStart, Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil,
      or_false]
    split at hn <;> omega
  obtain ⟨hReq, hCond, hLow, hHigh⟩ := maskPairEval group j x group.isLt j.isLt hx a b
  have hDom : ∀ r ∈ dom, t.regs r = some (V r) := by
    intro r hm
    simp only [dom, List.mem_cons, List.not_mem_nil, or_false] at hm
    have hg := group.isLt
    have hmask : firstMaskWordReg group < 3100 := by unfold firstMaskWordReg; split <;> omega
    rcases hm with rfl | rfl
    · simpa [V, maskValues] using hword
    · have hne : (firstMaskPairRegs group j).packed ≠ firstMaskWordReg group := by
        change 7897 + 32 * (group : Nat) + 2 * (j : Nat) ≠ _
        omega
      simpa [V, maskValues, hne] using hscore
  obtain ⟨u, hRun, hPc, hSub, hAcc, hFault, hFrame, hRegs⟩ :=
    (rRun (K := kernel) (A := Assumptions.all) (L := l) (g := g) ops V dom t
      (ht.1 ▸ maskPairCode group j) ht.2.2.2.1 hDom (maskShape group j).2 hReq
      (maskShape group j).1 (maskPairLocal group j)
      (fun n hn => maxSeg (hk n hn)) (fun n hn s hs => (maxModel (hs ▸ hk n hn)).1)
      (fun n hn s hs => (maxModel (hs ▸ hk n hn)).2)).1 hCond
  have hOut :
      (firstMaskPairRegs group j).low ∈ rWrites ops ∧
        (firstMaskPairRegs group j).high ∈ rWrites ops := by
    by_cases h : (j : Nat) = 15 <;> simp [ops, maskPairItems, rWrites, RItem.writes, h]
  have hLen : ops.length = _ := maskPairLength group j
  exact ⟨u, ⟨by rw [hPc, ht.1, hLen], hSub.trans ht.2.1, hAcc.trans ht.2.2.1,
    hFault.trans ht.2.2.2.1, trivial⟩, run_rtg hRun,
    (hRegs _ (List.mem_append_left _ hOut.1)).trans (congrArg some hLow),
    (hRegs _ (List.mem_append_left _ hOut.2)).trans (congrArg some hHigh), hFrame⟩

/-- The group writes its predicates and scalar scratch, preserving other live registers. -/
def firstMaskGroupWrites (group r : Nat) : Prop :=
  (maskPred group 0 ≤ r ∧ r < maskPred group 0 + 32) ∨
    (maskScratch group 0 ≤ r ∧ r < maskScratch group 0 + 96)

private theorem maskPrefix {t : TState} (group : Fin 4) (x : Nat) (hx : x < 2^32)
    (score : Nat → Option ℝ) (ht : At t (firstMaskGroupStart group) [])
    (hword : t.regs (firstMaskWordReg group) = some (b32 x))
    (hscores : ∀ j < 16, t.regs (firstMaskPairRegs group j).packed =
      some (Value.pair (scoreValue (score (32 * group + 2 * j)))
        (scoreValue (score (32 * group + 2 * j + 1))))) (n : Nat) (hn : n ≤ 16) :
    ∃ u, At u (firstMaskGroupStart group + min (7 * n) 111) [] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (∀ j < n, u.regs (firstMaskPairRegs group j).low =
          some (scoreValue (if x.testBit (2*j) then score (32 * group + 2*j) else none)) ∧
        u.regs (firstMaskPairRegs group j).high =
          some (scoreValue (if x.testBit (2*j+1) then score (32 * group + 2*j+1) else none))) ∧
      ∀ r, ¬ ((maskPred group 0 ≤ r ∧ r < maskPred group 0 + 2 * n) ∨
        (maskScratch group 0 ≤ r ∧ r < maskScratch group 0 + 6 * n)) → u.regs r = t.regs r := by
  induction n with
  | zero =>
    exact ⟨t, by simpa using ht, .refl, fun _ hj => (Nat.not_lt_zero _ hj).elim, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨v, hv, hvr, hSaved, hFrame⟩ := ih (by omega)
    have hgroup := group.isLt
    have hmask : firstMaskWordReg group < 3100 := by unfold firstMaskWordReg; split <;> omega
    have hmaskLo : 3000 < firstMaskWordReg group := by unfold firstMaskWordReg; split <;> omega
    have hv' : At v (firstMaskGroupStart group + 7 * n) [] := by
      simpa only [min_eq_left (show 7 * n ≤ 111 by omega)] using hv
    have hw' : v.regs (firstMaskWordReg group) = some (b32 x) := by
      rw [hFrame _ (by unfold maskPred maskScratch; omega), hword]
    have hs' : v.regs (firstMaskPairRegs group n).packed =
        some (Value.pair (scoreValue (score (32 * group + 2*n)))
          (scoreValue (score (32 * group + 2*n+1)))) := by
      rw [hFrame _ (by unfold firstMaskPairRegs maskPred maskScratch; dsimp; omega)]
      exact hscores n (by omega)
    obtain ⟨u, hu, hur, hLo, hHi, hStep⟩ :=
      maskPairTrace group ⟨n, by omega⟩ x hx _ _ hv' hw' hs'
    have hpc : firstMaskGroupStart group + 7 * n + (if n = 15 then 6 else 7) =
        firstMaskGroupStart group + min (7 * (n+1)) 111 := by
      split <;> omega
    change At u (firstMaskGroupStart group + 7 * n + (if n = 15 then 6 else 7)) [] at hu
    refine ⟨u, hpc ▸ hu, hvr.trans hur, fun j hj => ?_, fun r hNo => ?_⟩
    · by_cases hjn : j = n
      · subst j
        exact ⟨hLo, hHi⟩
      · have he : ∀ r, maskScratch group j ≤ r → r < maskScratch group j + 6 →
              r ∉ rWrites (maskPairItems group n) := by
          intro r hL hH hm
          have hRange := maskWrites _ _ _ hm
          unfold maskPred maskScratch at hRange hL hH
          omega
        obtain ⟨hl, hh⟩ := hSaved j (by omega)
        refine ⟨?_, ?_⟩
        · rw [hStep _ (he _ (by simp [firstMaskPairRegs]) (by simp [firstMaskPairRegs]))]
          exact hl
        · rw [hStep _ (he _ (by unfold firstMaskPairRegs; dsimp; split <;> omega)
            (by unfold firstMaskPairRegs; dsimp; split <;> omega))]
          exact hh
    · rw [hStep _ (fun hm => ?_), hFrame _ (by omega)]
      exact hNo (by
        have hRange := maskWrites _ _ _ hm
        simp only [maskPred, maskScratch] at hRange ⊢
        omega)

/-- An actual 111-instruction mask group preserves visible columns and writes negative
infinity to all columns at or beyond the suffix-causal key limit. -/
theorem firstMaskGroupLocal {t : TState} (p : Params) (batch row blocks : Nat) (group : Fin 4)
    (score : Nat → Option ℝ) (ht : At t (firstMaskGroupStart group) [])
    (hword : t.regs (firstMaskWordReg group) =
      some (b32 (maskWord group (firstActive p batch row blocks).toNat)))
    (hscores : ∀ j < 16, t.regs (firstMaskPairRegs group j).packed =
      some (Value.pair (scoreValue (score (32 * group + 2*j)))
        (scoreValue (score (32 * group + 2*j+1))))) :
    ∃ u, At u (firstMaskGroupStart group + 111) [] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (∀ j < 16, u.regs (firstMaskPairRegs group j).low =
        some (scoreValue (if visitKey blocks 0 (32 * group + 2*j) < p.keyCount batch row
          then score (32 * group + 2*j) else none)) ∧
        u.regs (firstMaskPairRegs group j).high =
        some (scoreValue (if visitKey blocks 0 (32 * group + 2*j+1) < p.keyCount batch row
          then score (32 * group + 2*j+1) else none))) ∧
      ∀ r, ¬ firstMaskGroupWrites group r → u.regs r = t.regs r := by
  obtain ⟨u, hu, hur, hout, hFrame⟩ := maskPrefix group _
    (maskWord_bound _ _) score ht hword hscores 16 (by decide)
  refine ⟨u, hu, hur, fun j hj => ?_, hFrame⟩
  obtain ⟨hlo, hhi⟩ := hout j hj
  rw [firstActive_select p batch row blocks group (2*j) (by omega)] at hlo
  rw [firstActive_select p batch row blocks group (2*j+1) (by omega), ← Nat.add_assoc] at hhi
  exact ⟨by simpa only [decide_eq_true_eq] using hlo, by simpa only [decide_eq_true_eq] using hhi⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Softmax
