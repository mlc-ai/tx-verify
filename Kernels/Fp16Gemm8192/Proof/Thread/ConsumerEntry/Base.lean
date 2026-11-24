-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Consumer
public import Kernels.Fp16Gemm8192.Proof.Thread.Cluster
public import Kernels.Fp16Gemm8192.Proof.Thread.Claims
public import Lemmas.Flow.Local
public import Lemmas.Flow.Async
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Definitions and helper facts of `ConsumerEntry`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000

/-- The continuation of a step of this role: the thread leaves the role, or steps to `d'` at
`t'` by a run of `Tau` (the conclusion of each step lemma). -/
syntax "entry_cont " term:max term:max term:max term:max term:max : term
macro_rules
  | `(entry_cont $L $g $d $e $u) => `(next $L $g $d $e = some none ∨ ∃ d' t', next $L $g $d $e =
    some (some d') ∧
      Relation.ReflTransGen (Tau kernel [Assumptions.idealArith,
        Assumptions.clusterMbar, Assumptions.pollAgree] $L $g) $u t' ∧
      At t' d'.site.pc (facts $L $g d') ∧ Inv d')


/-- The response register holds the state's response. -/
theorem resp_of {L : Launch} {g : Nat} {d : D} {t : TState} {r : ClcResponse}
    (h : At t d.site.pc (facts L g d)) (hlive : 969 ∈ Flow.live d.site.pc)
    (hr : readValue L g t 128 (.reg 969) = .ok (.clc r)) : d.resp = .clc r := by
  have hreg : t.regs 969 = some (valueOf L g d 969) :=
    holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d) hlive)
  have hv : valueOf L g d 969 = d.resp := by cons_values
  rw [hv] at hreg
  simp only [readValue, readReg, hreg, pure, Except.pure] at hr
  exact Except.ok.inj hr

/-- A register's value from the facts of its state. -/
theorem reg_val {L : Launch} {g pc : Nat} {d : D} {t : TState} {r : Nat}
    (h : At t pc (factsAt L g pc d)) (hl : r ∈ Flow.live pc) : t.regs r = some (valueOf L g d r) :=
  holds_mem h.2.2.2.2 (Flow.mem_factsFrom hl)

/-- The next tile is a tile. -/
theorem nextTile_lt {d : D} (hi : Inv d) : (nextTile d).1 < 16 ∧ (nextTile d).2 < 32 := by
  unfold nextTile
  split_ifs with hx
  · exact ⟨hi.m, hi.n⟩
  · exact Loader.claim_lt d.x

/-- The claimed row's bits in the shifted-and-masked form the code computes. -/
theorem claimN_bits : ∀ x < 1024, (truncBits 32
    (truncBits 32
        (if (truncBits 32 (BitVec.ofInt 64 4)).toNat ≥ 32 then 0
        else truncBits 32 (BitVec.ofNat 64 x) >>> (truncBits 32 (BitVec.ofInt 64 4)).toNat) &&&
      truncBits 32 (BitVec.ofInt 64 31))) = BitVec.ofNat 64 (x / 16 % 32) := by
  table_decide

/-- The predicate a 32-bit comparison with zero writes, for the group's lead value. -/
theorem cmp_ne_zero (X : Nat) (hX : X < 2 ^ 32) :
    PTX.compare Cmp.ne IType.b 32 (truncBits 32 (BitVec.ofNat 64 X))
      (truncBits 32 (BitVec.ofInt 64 0)) = decide (X ≠ 0) := by
  rw [truncBits_ofNat hX (by decide)]
  have h0 : truncBits 32 (BitVec.ofInt 64 0) = BitVec.ofNat 64 0 := by
    simp [truncBits]
  rw [h0]
  simp only [PTX.compare, toNat_ofNat_lt (show X < 2 ^ 64 by omega),
    toNat_ofNat_lt (show 0 < 2 ^ 64 by omega)]
  simp

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
