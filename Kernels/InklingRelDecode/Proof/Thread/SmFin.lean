-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmBase
public import Kernels.InklingRelDecode.Proof.Result.Softmax

@[expose] public section

/-! # The numbers of the score stage as functions of the state

The score stage (pcs 1299 to 2233) turns the S words, the bias words and the running maximum into
the final score words (`D.fin`: the S tile plus the bias, masked), the new running maximum
(`m_new`), the lazy-rescale decision, `alpha`, the 64 probabilities and their sum. This file
defines these numbers on the machine's state, so that the successor function (`Sm.next`) can
record them where the stage's events occur, and the register table (`Sm.lean`) can give them to
the registers. The facts that the registers really hold them are the segment lemmas of the
`SmSc*`, `SmMax` and `SmExp*` files.

A **score word** is a `.f32` number or the bit pattern of `-inf` (`ScoreWord`); `eOf` reads it as
an extended real. The registers of the row maximum are the extended reals' maxima over sets of
columns (`cmaxW`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption
open Classical

noncomputable section
set_option maxRecDepth 100000

/-! ### The visibility, the bias and the mask -/

/-- The block's last column is at or before the first query position (`%p97`). -/
def pr97 (e : Ent) (n : Nat) : Bool := decide (n * 128 + 127 ≤ e.past)

/-- The column `k` of the thread is visible: its key is at or before the query's position. -/
def visK (e : Ent) (T n k : Nat) : Bool :=
  decide (n * 128 + half T * 64 + k ≤ e.past + tokOf T)

/-- `%p96 = (n < n_bias)`: the block has no bias. -/
def pr96 (e : Ent) (n : Nat) : Bool := decide (n < e.nbias)

/-- `%p164 = %p166 = (n < r23)`. -/
def pr166 (e : Ent) (n : Nat) : Bool := decide (n < e.r23)

/-- `%p179`, `%p180`: the columns of the thread's half use the software `exp2` (the half's bit,
and where the block is not before `n_bias` also `n < past / 128`). -/
def pe0 (e : Ent) (T n : Nat) : Bool :=
  if pr96 e n then decide (half T ≠ 0) else decide (half T ≠ 0) && pr166 e n
def pe1 (e : Ent) (T n : Nat) : Bool :=
  if pr96 e n then decide (half T = 0) else decide (half T = 0) && pr166 e n

/-- The number of a bias word: the loaded number, zero for the zero half-word. -/
def bfR (v : Value) : ℝ :=
  match v with
  | .float _ x => x
  | _ => 0

/-- A bias word is a `bf16` number or the zero half-word. -/
def BfOk (v : Value) : Prop := (∃ x, v = .float .bf16 x) ∨ v = z16

/-- The bias number of the word `k` of the block in the registers. -/
def D.bR (d : D) (k : Nat) : ℝ := bfR (d.wd k)

/-- The score of the column `k`: `fma(bias, inv_scale, s)` as an exact number. -/
def D.scd (d : D) (k : Nat) : ℝ := d.bR k * (1 / d.e.sc) + bfR (d.sv k).1

/-- The S words with the pairs `q < m` replaced by their scores. -/
def scSv (d : D) (m : Nat) (k : Nat) : { v : Value // v.bytes = 4 } :=
  if k / 2 < m then ⟨.float .f32 (d.scd k), rfl⟩ else d.sv k

/-- The state in which the pairs `q < m` are scored. -/
def D.scored (d : D) (m : Nat) : D := { d with sv := scSv d m }

/-- The masked word of the column `k`: its score where it is visible, `-inf` (`0xFF800000`). -/
def mw (e : Ent) (T n : Nat) (sc : Nat → ℝ) (k : Nat) : Value :=
  if visK e T n k then .float .f32 (sc k) else b32 4286578688

theorem mw_bytes (e : Ent) (T n : Nat) (sc : Nat → ℝ) (k : Nat) : (mw e T n sc k).bytes = 4 := by
  unfold mw
  split_ifs <;> rfl

/-- The pair `q` is masked after `m` groups: the groups take the pairs in the order `1, 0, 2, 3,
…, 31` (the code unpacks `%rd500` first). -/
def msk (m q : Nat) : Bool := if m = 1 then decide (q = 1) else decide (q < m)

/-- The S words with the pairs of the first `m` groups masked (the scored words elsewhere). -/
def mSv (L : Launch) (g : Nat) (d : D) (m : Nat) (k : Nat) : { v : Value // v.bytes = 4 } :=
  if msk m (k / 2) then ⟨mw d.e (g % L.block) d.n d.scd k, mw_bytes _ _ _ _ _⟩ else scSv d 32 k

/-- The state in which the pairs `q < m` are masked (and all are scored). -/
def D.masked (L : Launch) (g : Nat) (d : D) (m : Nat) : D := { d with sv := mSv L g d m }

/-- The state after the score stage: the block has no bias (`%p96`) and the scores are the S
words, or the biased scores (`%p97`: all visible), or the masked scores. -/
def D.fin (L : Launch) (g : Nat) (d : D) : D :=
  if pr96 d.e d.n then d else if pr97 d.e d.n then d.scored 32 else D.masked L g d 32

/-! ### Score words -/

/-- The bit pattern of `-inf` (`0xFF800000`) as a register value. -/
abbrev infB : Value := b32 4286578688

/-- The extended real of a score word: a `.float` payload is its number, any other word is `-inf`
(the masked words). -/
def eOf : Value → EReal
  | .float _ x => (x : EReal)
  | _ => ⊥

/-- A score word the stage produces: a `.f32` number or the pattern of `-inf`. -/
def ScoreWord (v : Value) : Prop := (∃ x, v = .float .f32 x) ∨ v = infB

/-- The register number (decoder id) of the unpacked score word of column `k` at pc 1838:
`%r954, %r955, %r956, %r957, %r959, …` (the registers in between hold partial maxima). -/
def colRegL : List Nat :=
  [954, 955, 956, 957, 959, 960, 961, 962, 964, 965, 967, 968, 970, 971, 972, 973, 975, 976, 977,
    978, 980, 981, 982, 983, 985, 986, 988, 989, 991, 992, 993, 994, 996, 997, 999, 1000, 1002,
    1003, 1004, 1005, 1007, 1008, 1010, 1011, 1013, 1014, 1015, 1016, 1018, 1019, 1020, 1021,
    1023, 1024, 1025, 1026, 1028, 1029, 1031, 1032, 1034, 1035, 1036, 1037]

/-- The decoder id of the unpacked word of column `k`. -/
def colReg (k : Nat) : Nat := 461 + colRegL.getD k 0

theorem colReg_range : ∀ k < 64, 1415 ≤ colReg k ∧ colReg k < 1499 := by decide +kernel

/-- The extended-real maximum of the columns whose bit is set in the mask `m` (`-inf` for none),
over the words `w`. -/
def cmaxW (w : Nat → Value) (m : Nat) : EReal :=
  ((Finset.range 64).filter fun k => m.testBit k).sup fun k => eOf (w k)

/-- The mask of all 64 columns. -/
abbrev fullMask : Nat := 2 ^ 64 - 1

/-! ### The numbers after the row maximum

`rE` is the maximum the lane `^ 16` sent (the shuffle at pc 1838). -/

/-- `scale_log2 = softmax_scale * 1.4426950408889634` (`%r37`). -/
def slOf (e : Ent) : ℝ := e.sc * log2eF32

/-- The running maximum as an extended real. -/
def D.mE (d : D) : EReal := eOf d.m

/-- The maximum of the thread's own 64 score words. -/
def D.ownE (d : D) : EReal := cmaxW (fun k => (d.stg.fsv k).1) fullMask

/-- `m_new = max(m, own maximum, received maximum)` (`max.f32 %r1061, %r1453, %r1059, %r1060`). -/
def D.mnE (d : D) (rE : EReal) : EReal := max (max d.mE d.ownE) rE

/-- `alpha_log2 = (m - m_safe) * scale_log2`. -/
def D.aLog (d : D) (rE : EReal) : EReal :=
  Softmax.alphaLog2 (slOf d.e) d.mE (d.mnE rE)

/-- The lazy-rescale decision (`%p168`). -/
def D.keepB (d : D) (rE : EReal) : Bool := decide (Softmax.Keep (d.aLog rE))

/-- `m_use` as a real. -/
def D.mUse (d : D) (rE : EReal) : ℝ :=
  if Softmax.Keep (d.aLog rE) then d.mE.toReal else Softmax.mSafe (d.mnE rE)

/-- `alpha` as the register holds it (`%r46`): the pattern `1.0` where the rescale is lazy, else
the exact `2 ^ alpha_log2` (`0` for `-inf`). -/
def D.alV (d : D) (rE : EReal) : Value :=
  if Softmax.Keep (d.aLog rE) then b32 1065353216 else .float .f32 (Softmax.pow2 (d.aLog rE))

/-- `alpha` as a real. -/
def D.alR (d : D) (rE : EReal) : ℝ :=
  if Softmax.Keep (d.aLog rE) then 1 else Softmax.pow2 (d.aLog rE)

/-- The probability of a score word: `2 ^ (s * scale_log2 + m_use * (-scale_log2))`, `0` for a
masked (`-inf`) word. -/
def pOfV (sl mu : ℝ) (v : Value) : ℝ :=
  match v with
  | .float _ x => (2 : ℝ) ^ (x * sl + mu * (-sl))
  | _ => 0

/-- The 64 probabilities after the shuffle of the row maximum that returned `rv`. -/
abbrev D.pfM (d : D) (rv : Value) (k : Nat) : ℝ :=
  pOfV (slOf d.e) (d.mUse (eOf rv)) (d.stg.fsv k).1

/-- The state after the shuffle of the row maximum: the new maximum, the decision, `alpha` and the
64 probabilities are recorded, the probability words and their sum's word as the numbers'
`.f32` values. -/
def D.afterMax (d : D) (rv : Value) : D :=
  { d with
    site := .shfl6
    stg := { d.stg with
      mn := erealValue .f32 (d.mnE (eOf rv)), kp := d.keepB (eOf rv), al := d.alV (eOf rv),
      alr := d.alR (eOf rv), pv := fun k => .float .f32 (d.pfM rv k),
      sw := .float .f32 ((List.range 64).map (d.pfM rv)).sum }
    pf := d.pfM rv }

/-- The sum of the thread's 64 probabilities (`%r1068`). -/
def D.sumP (d : D) : ℝ := ((List.range 64).map d.pf).sum

/-- The state after the shuffle of the half sums: the row sum `v` is the outcome of
`add.f32 %r1070, %r1068, %r1069` on the thread's sum and the received word (`Sm.D.rsOut`); the
site is the wait on `o_done`, which the first iteration (`i = 0`) skips (`toBar20`). -/
def D.afterSum (d : D) (v : Value) : D :=
  { d with site := .waitO, stg := { d.stg with rs := v } }

/-- The state after the shuffle of the half sums where the received word is the `.f32` number
`y`: the row sum is the number `sumP + y` (`floatE_add_fin`). -/
def D.afterSumR (d : D) (y : ℝ) : D := d.afterSum (.float .f32 (d.sumP + y))

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
