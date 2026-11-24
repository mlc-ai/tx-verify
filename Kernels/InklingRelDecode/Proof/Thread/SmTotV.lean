-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmTab
public import Lemmas.Flow.EmuStep

@[expose] public section

/-! # The score stage's second half on any words: the values

The values the registers of pcs 1839 to 2233 hold for any state at the shuffle of the row
maximum and any received word, as Core's outcomes (the definitions of `SmTotD`, `SmTotE` and
`SmTotF`, which prove that the registers hold them), the condition that none of the
instructions faults (`D.s2Ok`) and the words live at the shuffle of the half sums (`D.mnT`,
`D.kpT`, `D.alT`, `D.pvT`, `D.swT`). They are defined before the machine (`Sm.lean`) because
its successor at the shuffle of the row maximum records them. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption
open Classical

noncomputable section
set_option maxRecDepth 100000

set_option linter.unusedVariables false

variable {L : Launch} {g : Nat}

/-- The value of a comparison outcome, `false` where it faults. -/
def okB : Exec Bool → Bool
  | .ok b => b
  | .error _ => false

/-- The overlays after the first `k` instructions (written registers in front). -/
abbrev xa0 (recv : Value) : List (Nat × Value) := [(1521, recv)]

/-! ### The abstract instructions -/

/-- A probability register: `%r47 … %r62` (the selected columns) or `%r(826 + 2 j)`. -/
def isSingle (r : Nat) : Bool :=
  decide ((508 ≤ r ∧ r < 524) ∨ (1287 ≤ r ∧ r < 1415 ∧ (r - 1287) % 2 = 0))

/-- The column a probability register holds. -/
def colOfReg (r : Nat) : Nat := if 508 ≤ r ∧ r < 524 then colR (r - 508) else (r - 1287) / 2

/-- The instruction kinds of the segment: pack two probabilities into a pair; add two pairs. -/
inductive PI where
  | pk (d a b : Nat)
  | ad (d a b : Nat)

/-- The lookup of a pair register's two masks. -/
def lkp (st : List (Nat × (Nat × Nat))) (r : Nat) : Nat × Nat := (st.lookup r).getD (0, 0)

/-- The effect of an instruction on the register-mask list (written registers in front). -/
def PI.upd : PI → List (Nat × (Nat × Nat)) → List (Nat × (Nat × Nat))
  | .pk d a b, st => (d, (2 ^ colOfReg a, 2 ^ colOfReg b)) :: st
  | .ad d a b, st => (d, ((lkp st a).1 ||| (lkp st b).1, (lkp st a).2 ||| (lkp st b).2)) :: st

/-- `mov.b64 %rd d, {%r a, %r b}`. -/
abbrev pkI (d a b : Nat) : PI := .pk (1948 + d) (461 + a) (461 + b)

/-- `add.f32x2 %rd d, %rd a, %rd b`. -/
abbrev adI (d a b : Nat) : PI := .ad (1948 + d) (1948 + a) (1948 + b)

/-- The 63 instructions of pcs 2169 to 2231. -/
def psCode : List PI :=
  [ pkI 46 826 828, pkI 47 830 832, pkI 48 834 836, pkI 49 838 840, pkI 50 842 844,
    pkI 51 846 848, pkI 359 47 48, pkI 360 49 50, pkI 52 858 860, pkI 53 862 864,
    pkI 54 866 868, pkI 55 870 872, pkI 56 874 876, pkI 57 878 880, pkI 361 51 52,
    pkI 362 53 54, pkI 58 890 892, pkI 59 894 896, pkI 60 898 900, pkI 61 902 904,
    pkI 62 906 908, pkI 63 910 912, pkI 363 55 56, pkI 364 57 58, pkI 64 922 924,
    pkI 65 926 928, pkI 66 930 932, pkI 67 934 936, pkI 68 938 940, pkI 69 942 944,
    pkI 365 59 60, pkI 366 61 62,
    adI 367 46 47, adI 368 48 49, adI 369 50 51, adI 370 359 360, adI 371 52 53,
    adI 372 54 55, adI 373 56 57, adI 374 361 362, adI 375 58 59, adI 376 60 61,
    adI 377 62 63, adI 378 363 364, adI 379 64 65, adI 380 66 67, adI 381 68 69,
    adI 382 365 366, adI 383 367 368, adI 384 369 370, adI 385 371 372, adI 386 373 374,
    adI 387 375 376, adI 388 377 378, adI 389 379 380, adI 390 381 382, adI 391 383 384,
    adI 392 385 386, adI 393 387 388, adI 394 389 390, adI 395 391 392, adI 396 393 394,
    adI 397 395 396 ]

/-- A `0f` constant as the value the instruction reads. -/
abbrev imm32 (b : Nat) : Value := .bits 32 (BitVec.ofNat 64 b)

section
variable (d : D) (recv : Value)

/-- `%r1061 = max(m, own maximum, received maximum)`. -/
def D.t1E : Exec Value := maxE [d.m, ownV (fun k => (d.stg.fsv k).1), recv]
def D.t1 : Value := okVal (b32 0) (d.t1E recv)
/-- `%p167 = (%r1061 == -inf)`. -/
def D.t2E : Exec Bool := setpE (.ord .eq) false (d.t1 recv) (imm32 4286578688)
def D.t2 : Bool := okB (d.t2E recv)
/-- `%r1062 = %p167 ? 0 : %r1061`. -/
def D.t3E : Exec Value := movE (if d.t2 recv then imm32 0 else d.t1 recv)
def D.t3 : Value := okVal (b32 0) (d.t3E recv)
/-- `%r1063 = m - %r1062`. -/
def D.t4E : Exec Value := subE false d.m (d.t3 recv)
def D.t4 : Value := okVal (b32 0) (d.t4E recv)
/-- `%r809 = scale_log2 * %r1063`. -/
def D.t5E : Exec Value := mulE false (.float .f32 (slOf d.e)) (d.t4 recv)
def D.t5 : Value := okVal (b32 0) (d.t5E recv)
/-- `%p168 = (%r809 >= -8)`. -/
def D.t6E : Exec Bool := setpE (.ord .ge) false (d.t5 recv) (imm32 3238002688)
def D.t6 : Bool := okB (d.t6E recv)
/-- `%r808 = ex2(%r809)`. -/
def D.t7E : Exec Value := ex2E true (d.t5 recv)
def D.t7 : Value := okVal (b32 0) (d.t7E recv)
/-- `%r46 = %p168 ? 1.0 : %r808` (`alpha`). -/
def D.t8E : Exec Value := movE (if d.t6 recv then imm32 1065353216 else d.t7 recv)
def D.t8 : Value := okVal (b32 0) (d.t8E recv)
/-- `%r1064 = %p168 ? m : %r1062` (`m_use`). -/
def D.t9E : Exec Value := movE (if d.t6 recv then d.m else d.t3 recv)
def D.t9 : Value := okVal (b32 0) (d.t9E recv)
/-- `%r1065 = %r1064 * (-scale_log2)`. -/
def D.t10E : Exec Value := mulE false (d.t9 recv) (.float .f32 (-(slOf d.e)))
def D.t10 : Value := okVal (b32 0) (d.t10E recv)

/-- The overlays after the first `k` instructions. -/
abbrev xb1 : List (Nat × Value) := (1522, d.t1 recv) :: xa0 recv
abbrev xb2 : List (Nat × Value) := (167, .pred (d.t2 recv)) :: xb1 d recv
abbrev xb3 : List (Nat × Value) := (1523, d.t3 recv) :: xb2 d recv
abbrev xb4 : List (Nat × Value) := (1524, d.t4 recv) :: xb3 d recv
abbrev xb5 : List (Nat × Value) := (1270, d.t5 recv) :: xb4 d recv
abbrev xb6 : List (Nat × Value) := (168, .pred (d.t6 recv)) :: xb5 d recv
abbrev xb7 : List (Nat × Value) := (1269, d.t7 recv) :: xb6 d recv
abbrev xb8 : List (Nat × Value) := (507, d.t8 recv) :: xb7 d recv
abbrev xb9 : List (Nat × Value) := (1525, d.t9 recv) :: xb8 d recv
abbrev xb10 : List (Nat × Value) := (1526, d.t10 recv) :: xb9 d recv

/-- None of the ten instructions faults (in the order `SegD.comp` composes them). -/
def D.okA : Prop :=
  ((((((((((d.t1E recv).toBool = true ∧ (d.t2E recv).toBool = true) ∧
    (d.t3E recv).toBool = true) ∧ (d.t4E recv).toBool = true) ∧ (d.t5E recv).toBool = true) ∧
    (d.t6E recv).toBool = true) ∧ (d.t7E recv).toBool = true) ∧ (d.t8E recv).toBool = true) ∧
    (d.t9E recv).toBool = true) ∧ (d.t10E recv).toBool = true)

end

/-- The outcome of `%r(827 + 2 j) = fma(word j, scale_log2, %r1065)`. -/
def D.xTE (d : D) (recv : Value) (j : Nat) : Exec Value :=
  floatE (fmaI .rn false) [(d.stg.fsv j).1, .float .f32 (slOf d.e), d.t10 recv]

/-- The exponent register of column `j` (`b32 0` where its `fma` faults). -/
def D.xT (d : D) (recv : Value) (j : Nat) : Value := okVal (b32 0) (d.xTE recv j)

/-- The overlay after `j` fused multiply-adds. -/
def fxT (d : D) (recv : Value) : Nat → List (Nat × Value)
  | 0 => []
  | j + 1 => (1288 + 2 * j, d.xT recv j) :: fxT d recv j

section
variable (v : Value)

/-- `c = max.ftz(x, -127)`. -/
def nCE : Exec Value := maxFE v (imm32 3271426048)
def nC : Value := okVal (b32 0) (nCE v)
/-- `r = add.rm.ftz(c, 1.5 · 2 ^ 23)`. -/
def nRE : Exec Value := floatE addRmI [nC v, imm32 1262485504]
def nR : Value := okVal (b32 0) (nRE v)
/-- `rb = sub.rn.ftz(r, 1.5 · 2 ^ 23)`. -/
def nRbE : Exec Value := subRnE (nR v) (imm32 1262485504)
def nRb : Value := okVal (b32 0) (nRbE v)
/-- `f = sub.rn.ftz(c, rb)`. -/
def nFE : Exec Value := subRnE (nC v) (nRb v)
def nF : Value := okVal (b32 0) (nFE v)
/-- The three `fma.rn.ftz` of the polynomial. -/
def nP1E : Exec Value := floatE (fmaI .rn true) [nF v, imm32 1033760925, imm32 1047070372]
def nP1 : Value := okVal (b32 0) (nP1E v)
def nP2E : Exec Value := floatE (fmaI .rn true) [nP1 v, nF v, imm32 1060238617]
def nP2 : Value := okVal (b32 0) (nP2E v)
def nP3E : Exec Value := floatE (fmaI .rn true) [nP2 v, nF v, imm32 1065353216]
def nP3 : Value := okVal (b32 0) (nP3E v)
/-- `e = mov.b32 r`, then `shl.b32 e, e, 23`. -/
def nE1E : Exec Value := movE (nR v)
def nE1 : Value := okVal (b32 0) (nE1E v)
def nE2E : Exec Value := shlE (nE1 v) 23
def nE2 : Value := okVal (b32 0) (nE2E v)
/-- `y = mov.b32 p`, then `add.s32 y, y, e`. -/
def nY1E : Exec Value := movE (nP3 v)
def nY1 : Value := okVal (b32 0) (nY1E v)
def nY2E : Exec Value := addIE (nY1 v) (nE2 v)
/-- The word the path leaves in the output register. -/
def nanY : Value := okVal (b32 0) (nY2E v)

/-- None of the 11 instructions faults (in the order `SegD.comp` composes them). -/
def nanOk : Prop :=
  (((((((((((nCE v).toBool = true ∧ (nRE v).toBool = true) ∧ (nRbE v).toBool = true) ∧
    (nFE v).toBool = true) ∧ (nP1E v).toBool = true) ∧ (nP2E v).toBool = true) ∧
    (nP3E v).toBool = true) ∧ (nE1E v).toBool = true) ∧ (nE2E v).toBool = true) ∧
    (nY1E v).toBool = true) ∧ (nY2E v).toBool = true)

/-- **The output of an instance** on the input `v`: the exact power of two of a number or of
`-inf`, the word of the NaN path for a NaN (the value of a faulting input is not used). -/
def emuYE : Value :=
  match readEReal .f32 v with
  | some (.ok x) => .float .f32 (Softmax.pow2 x)
  | some (.error _) => b32 0
  | none => nanY v

/-- **The instance does not fault** on the input `v`. -/
def emuOkE : Prop :=
  match readEReal .f32 v with
  | some (.ok x) => x ≠ ⊤
  | some (.error _) => False
  | none => nanOk v

end

/-- The output of instance `i` on the stage's words. -/
def D.yT (d : D) (recv : Value) (i : Nat) : Value := emuYE (d.xT recv (colR i))

/-- The overlay after `i` software exponentials. -/
def emT (d : D) (recv : Value) : Nat → List (Nat × Value)
  | 0 => []
  | i + 1 => (1271 + i, d.yT recv i) :: emT d recv i

/-- `%r(826 + 2 j) = ex2(%r(827 + 2 j))`. -/
def D.zTE (d : D) (recv : Value) (j : Nat) : Exec Value := ex2E true (d.xT recv j)
def D.zT (d : D) (recv : Value) (j : Nat) : Value := okVal (b32 0) (d.zTE recv j)

/-- The overlay after `j` exponentials. -/
def e2T (d : D) (recv : Value) : Nat → List (Nat × Value)
  | 0 => []
  | j + 1 => (1287 + 2 * j, d.zT recv j) :: e2T d recv j

/-- The overlay of the facts after the fused multiply-adds and the software exponentials. -/
abbrev base2T (d : D) (recv : Value) : List (Nat × Value) :=
  emT d recv 16 ++ (fxT d recv 64 ++ xb10 d recv)

/-- The predicate of selection `i` (`%p179` for the first eight, `%p180` for the others). -/
def D.pickT (L : Launch) (g : Nat) (d : D) (i : Nat) : Bool :=
  if i / 8 = 0 then pe0 d.e (g % L.block) d.n else pe1 d.e (g % L.block) d.n

/-- `%r(47 + i) = selp(%r(810 + i), %r(826 + 2 colR i), p)`. -/
def D.sTE (L : Launch) (g : Nat) (d : D) (recv : Value) (i : Nat) : Exec Value :=
  movE (if d.pickT L g i then d.yT recv i else d.zT recv (colR i))
def D.sT (L : Launch) (g : Nat) (d : D) (recv : Value) (i : Nat) : Value :=
  okVal (b32 0) (d.sTE L g recv i)

/-- The overlay after `i` selections. -/
def sl16T (L : Launch) (g : Nat) (d : D) (recv : Value) : Nat → List (Nat × Value)
  | 0 => []
  | i + 1 => (508 + i, d.sT L g recv i) :: sl16T L g d recv i

/-- The overlay of the facts after the exponentials. -/
abbrev base3T (d : D) (recv : Value) : List (Nat × Value) := e2T d recv 64 ++ base2T d recv

/-- The overlay of the facts after the selections. -/
abbrev base4T (L : Launch) (g : Nat) (d : D) (recv : Value) : List (Nat × Value) :=
  sl16T L g d recv 16 ++ base3T d recv

/-- The destination of an instruction of the tree. -/
def PI.dst : PI → Nat
  | .pk d _ _ => d
  | .ad d _ _ => d

/-- The effect of an instruction of the tree on the register-value list, the single registers
read from `sg` (written registers in front). -/
def PI.updV (sg : Nat → Value) : PI → List (Nat × Value) → List (Nat × Value)
  | .pk d a b, st => (d, okVal (b32 0) (packE (sg a) (sg b))) :: st
  | .ad d a b, st => (d, okVal (b32 0) (add2NE (lkV st a) (lkV st b))) :: st

/-- The instruction has an outcome. -/
def PI.okV (sg : Nat → Value) (st : List (Nat × Value)) : PI → Bool
  | .pk _ a b => (packE (sg a) (sg b)).toBool
  | .ad _ a b => (add2NE (lkV st a) (lkV st b)).toBool

/-- The register-value list after the first `c` instructions. -/
def psV (sg : Nat → Value) (c : Nat) : List (Nat × Value) :=
  (psCode.take c).foldl (fun st i => i.updV sg st) []

/-- The value of a single register in the facts after the selections. -/
abbrev sgT (L : Launch) (g : Nat) (d : D) (recv : Value) (r : Nat) : Value :=
  valueEx (valueOf L g d) (base4T L g d recv) r

/-- The tree's instructions have outcomes, the first `m` of them. -/
def PsOk (sg : Nat → Value) (m : Nat) : Prop :=
  ∀ c < m, ∀ i, psCode[c]? = some i → i.okV sg (psV sg c) = true

/-- The root pair `%rd397` on any words. -/
def D.rootT (L : Launch) (g : Nat) (d : D) (recv : Value) : Value :=
  lkV (psV (sgT L g d recv) 63) (1948 + 397)

/-- The unpack of the root pair. -/
def D.uTE (L : Launch) (g : Nat) (d : D) (recv : Value) : Exec (Value × Value) :=
  unpackE 64 (d.rootT L g recv)
def D.uT (L : Launch) (g : Nat) (d : D) (recv : Value) : Value × Value :=
  match d.uTE L g recv with
  | .ok x => x
  | .error _ => (b32 0, b32 0)

/-- `%r1068 = %r1066 + %r1067`, the thread's sum of probabilities. -/
def D.swTE (L : Launch) (g : Nat) (d : D) (recv : Value) : Exec Value :=
  floatE (addI false) [(d.uT L g recv).1, (d.uT L g recv).2]
def D.swT (L : Launch) (g : Nat) (d : D) (recv : Value) : Value :=
  okVal (b32 0) (d.swTE L g recv)

/-- **No instruction of the stage's second half faults** (pcs 1839 to 2233): the ten scalars,
the 64 exponents, the 16 software exponentials, the 64 exponentials, the 16 selections, the packs
and the sum tree, the unpack and the last sum. -/
def D.s2Ok (L : Launch) (g : Nat) (d : D) (recv : Value) : Prop :=
  d.okA recv ∧ (∀ j < 64, (d.xTE recv j).toBool = true) ∧
    (∀ i < 16, emuOkE (d.xT recv (colR i))) ∧ (∀ j < 64, (d.zTE recv j).toBool = true) ∧
    (∀ i < 16, (d.sTE L g recv i).toBool = true) ∧ PsOk (sgT L g d recv) 63 ∧
    (d.uTE L g recv).toBool = true ∧ (d.swTE L g recv).toBool = true

/-- The new maximum `%r1061`. -/
abbrev D.mnT (d : D) (recv : Value) : Value := d.t1 recv
/-- The lazy-rescale decision `%p168`. -/
abbrev D.kpT (d : D) (recv : Value) : Bool := d.t6 recv
/-- `alpha` (`%r46`). -/
abbrev D.alT (d : D) (recv : Value) : Value := d.t8 recv

/-- The selection that holds column `k`, if one does. -/
def selIdx (k : Nat) : Option Nat := (List.range 16).find? fun i => colR i == k

/-- **The probability word of column `k`** as the registers hold it: the selection's register
for the columns `colR i`, the exponential's for the others. -/
def D.pvT (L : Launch) (g : Nat) (d : D) (recv : Value) (k : Nat) : Value :=
  match selIdx k with
  | some i => d.sT L g recv i
  | none => d.zT recv k

/-- The real number a word reads as (`0` where it does not read as one). -/
def alrOf (v : Value) : ℝ :=
  match readEReal .f32 v with
  | some (.ok x) => x.toReal
  | _ => 0

/-- **The state after the shuffle of the row maximum on any words**: the registers the stage's
second half writes are Core's outcomes (the new maximum, the decision, `alpha` and the real number
it reads as, the 64 probability words and their sum), and the flag of the real numbers is
cleared. -/
def D.afterMaxT (L : Launch) (g : Nat) (d : D) (recv : Value) : D :=
  { d with
    site := .shfl6
    stg := { d.stg with
      mn := d.mnT recv, kp := d.kpT recv, al := d.alT recv, alr := alrOf (d.alT recv),
      pv := d.pvT L g recv, sw := d.swT L g recv, re := false } }

/-- The inputs of the stage's second half are score words: the running maximum, the received
maximum and the 64 words of the columns. -/
def D.RealIn (d : D) (recv : Value) : Prop :=
  ScoreWord d.m ∧ ScoreWord recv ∧ ∀ k < 64, ScoreWord (d.stg.fsv k).1

/-- **The successor of the shuffle of the row maximum** where the thread lives: the state of the
real numbers on score words, the state of Core's outcomes otherwise. -/
def D.afterS (L : Launch) (g : Nat) (d : D) (recv : Value) : D :=
  if d.RealIn recv then d.afterMax recv else d.afterMaxT L g recv

/-! The fields both successors keep (simp lemmas for the proofs that follow `Sm.next`). -/

section
variable (L : Launch) (g : Nat) (d : D) (r : Value)
@[simp] theorem D.afterMax_site : (d.afterMax r).site = .shfl6 := rfl
@[simp] theorem D.afterMax_e : (d.afterMax r).e = d.e := rfl
@[simp] theorem D.afterMax_i : (d.afterMax r).i = d.i := rfl
@[simp] theorem D.afterMax_m : (d.afterMax r).m = d.m := rfl
@[simp] theorem D.afterMax_l : (d.afterMax r).l = d.l := rfl
@[simp] theorem D.afterMax_cw : (d.afterMax r).cw = d.cw := rfl
@[simp] theorem D.afterMax_cv : (d.afterMax r).cv = d.cv := rfl
@[simp] theorem D.afterMaxT_site : (d.afterMaxT L g r).site = .shfl6 := rfl
@[simp] theorem D.afterMaxT_e : (d.afterMaxT L g r).e = d.e := rfl
@[simp] theorem D.afterMaxT_i : (d.afterMaxT L g r).i = d.i := rfl
@[simp] theorem D.afterMaxT_m : (d.afterMaxT L g r).m = d.m := rfl
@[simp] theorem D.afterMaxT_l : (d.afterMaxT L g r).l = d.l := rfl
@[simp] theorem D.afterMaxT_cw : (d.afterMaxT L g r).cw = d.cw := rfl
@[simp] theorem D.afterMaxT_cv : (d.afterMaxT L g r).cv = d.cv := rfl
@[simp] theorem D.afterMaxT_pf : (d.afterMaxT L g r).pf = d.pf := rfl
end

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
