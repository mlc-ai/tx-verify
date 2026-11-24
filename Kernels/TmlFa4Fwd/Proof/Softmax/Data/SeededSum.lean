-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.FirstSum
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1Kinds
import Tactics.KernelRfl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow PTX.Assumption
noncomputable section
set_option maxRecDepth 100000

def PairReads (v : Value) (r : ℝ × ℝ) :=
  pairRead v = some (.ok ((r.1 : EReal), (r.2 : EReal)))

private theorem plus_reads {v w a b} (hv : PairReads v a) (hw : PairReads w b) :
    plusV v w = pairV (plusR a b) := by
  rw [plusV, add2E_reads hv hw (addEReal_coe _ _) (addEReal_coe _ _), erealValue_coe,
    erealValue_coe]
  rfl

private theorem reads_pair (r : ℝ × ℝ) : PairReads (pairV r) r :=
  pairRead_of_reads (readEReal_float _) (readEReal_float _)

private theorem stripe_reads (W : Nat → Value) (w : Nat → ℝ × ℝ)
    (h : ∀ j < 64, PairReads (W j) (w j)) (a n : Nat) (hn : a+4*n < 64) :
    PairReads (stripe plusV W a n) (stripe plusR w a n) := by
  induction n with
  | zero => exact h a (by omega)
  | succ n ih =>
    rw [stripe, stripe, plus_reads (ih (by omega)) (h _ (by omega))]
    exact reads_pair _

private theorem total (W : Nat → Value) (w : Nat → ℝ × ℝ) (h : ∀ j < 64, PairReads (W j) (w j)) :
    reduce plusV W = pairV (reduce plusR w) := by
  have s (a : Nat) (ha : a < 4) := stripe_reads W w h a 15 (by omega)
  dsimp only [reduce]
  rw [plus_reads (s 0 (by decide)) (s 1 (by decide)), plus_reads (s 2 (by decide))
      (s 3 (by decide)),
    plus_reads (reads_pair _) (reads_pair _)]

def seeded (z : Value) (W : Nat → Value) :=
  horizontal (reduce plusV (fun j => if j = 0 then plusV z (W j) else W j))

private def seededR (seed : ℝ) (w : Nat → ℝ) (j : Nat) :=
  let x := (w (2*j), w (2*j+1))
  if j = 0 then plusR (seed,0) x else x

private theorem seeded_total (seed : ℝ) (w : Nat → ℝ) :
    let r := reduce plusR (seededR seed w)
    r.1+r.2 = rowSumT seed w := by
  kernel_rfl

theorem seeded_value (seed : ℝ) (w : Nat → ℝ) (z : Value) (W : Nat → Value)
    (hz : PairReads z (seed,0)) (hw : ∀ j < 64, PairReads (W j) (w (2*j), w (2*j+1))) :
    seeded z W = .float .f32 (rowSumT seed w) := by
  have h (j : Nat) (hj : j < 64) : PairReads (if j = 0 then plusV z (W j) else W j)
      (seededR seed w j) := by
    unfold seededR
    split
    · rw [plus_reads hz (hw j hj)]
      exact reads_pair _
    · exact hw j hj
  rw [seeded, total _ _ h, horizontal_eq, seeded_total]

theorem seed_mul {x y : ℝ} {a b : Value} (ha : Reads a x) (hb : Reads b y) :
    PairReads (joinValue (offset a b) (.bits 32 0)) (x*y,0) := by
  rw [offset_val ha hb]
  exact pairRead_of_reads (readEReal_float _) readEReal_zero32

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
