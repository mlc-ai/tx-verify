-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Ref
public import Lemmas.Flow.TensorIssueCopy
public import Lemmas.Tensor.TensorMulticast
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefArith
import Lemmas.Flow.Step.SiteShape
import Lemmas.Flow.Step.SegSym

@[expose] public section

/-! # The TMA warp's gathers move 2304 bytes

A gather4 load reads its map from `%rd3049`, the main cache's descriptor slot of `param_1`
(`+ 768`) while the block is a main one (`isMain`), else the extra cache's (`+ 896`). Both are
`encodeKv` maps (`Pre.mapKVBind`, `Pre.mapExtraKvBind` when the extra cache is on), whose four-row
box moves `4 * 144` words of 4 bytes (`gather_bytes_of`, `gather_bytes`). A block with an extra
length word of zero is a main one (`isMain_of`): the block count is the main blocks'. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **A gather4 load on a cache map moves 2304 bytes.** -/
theorem gather_bytes_of (hp : Pre P L m) {t : TState} {dst : Nat} {cs : List Opnd}
    {pol : Option Opnd} {pc : Nat} {e : Event} {o : Option TState} {x : Nat}
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.cpTensor false false dst 0 (.reg 3049) cs 696 0 none .fourRows pol)) e o)
    (hm : t.regs 3049 = some (.bits 64 (BitVec.ofNat 64 (P.param1Base + x))))
    (hx : x = 768 ∨ (x = 896 ∧ P.extra_topk ≠ 0)) {a : Nat} {s : TensorCopy.Spec}
    (hk : e.kind = .tensorIssue a s) : TensorTransfer.bytes s.descriptor = 2304 := by
  obtain ⟨hma, -, d, hd, -, hdesc, -⟩ := tensorLoadCopy_ok (fires_cpTensor_copy hf hk)
  rw [tensorMapAddress_bits hm] at hma
  obtain rfl := (Except.ok.inj hma).symm
  have h64 : (BitVec.ofNat 64 (P.param1Base + x)).toNat = P.param1Base + x := by
    have := hp.param1Range
    simp only [BitVec.toNat_ofNat]
    omega
  rw [h64] at hd
  rw [hdesc]
  rcases hx with rfl | ⟨rfl, hx⟩
  · rw [hp.mapKVBind] at hd
    have hb' := congrArg (fun y : (n : Nat) × TensorDescriptor.Descriptor n =>
      TensorTransfer.bytes (TensorMode.fourRows.transfer y.2)) (Option.some.inj hd)
    simp only at hb'
    refine hb'.symm.trans ?_
    simp [mapKv, encodeKv, TensorTransfer.bytes, TensorDescriptor.Descriptor.fourRows,
      TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step,
      TensorDescriptor.Format.bytes]
  · rcases hp.mapExtraKvBind with h0 | hb
    · exact absurd h0 hx
    rw [hb] at hd
    have hb' := congrArg (fun y : (n : Nat) × TensorDescriptor.Descriptor n =>
      TensorTransfer.bytes (TensorMode.fourRows.transfer y.2)) (Option.some.inj hd)
    simp only at hb'
    refine hb'.symm.trans ?_
    simp [mapExtraKv, encodeKv, TensorTransfer.bytes, TensorDescriptor.Descriptor.fourRows,
      TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step,
      TensorDescriptor.Format.bytes]

/-- The padded extra length of zero. -/
theorem padB0 : padB 0 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [padB, andi, add32, addi, shru, shrs, r32, i32, truncBits, toSigned]
/-- With an extra length of zero the padded total is the main one. -/
theorem tot0_of (x : Nat) (hM : x < 2 ^ 32) :
    add32 (add32 (addi 0 63) (W x)) (sub32 (padB 0) (addi 0 63)) = W x := by
  rw [padB0, show (0 : BitVec 64) = W 0 from rfl, addi_Wm (by decide) (by decide), sub32_Wm,
    add32_Wm, add32_Wm]
  refine congrArg W ?_
  simp only [Int.reduceToNat]
  omega
/-- The main padded length is a 32-bit word. -/
theorem maxA_lt (a : BitVec 64) : (maxA a).toNat < 2 ^ 32 := by
  unfold maxA max32; split <;> simp [r32, truncBits]; omega
/-- **A block with an extra length word of zero is a main one.** -/
theorem isMain_of {d : D} (h : LoopOk d) (h1 : d.l1 = 0) : isMain d = true := by
  obtain ⟨hlt, -, hR, hr, hc, -⟩ := h
  have hA := maxA_lt d.l0
  have ht : tot d.l0 d.l1 = maxA d.l0 := by
    rw [h1]
    have h := tot0_of _ hA
    rwa [← eq_W] at h
  have hx : (tot d.l0 d.l1).toNat < 2 ^ 32 := by rw [ht]; exact hA
  have hb := word_ge64 hx hlt
  have hq := div64_word _ hb.1 hb.2
  rw [← eq_W] at hq
  have hRe : rounds d.l0 d.l1 = (tot d.l0 d.l1).toNat / 64 := by
    simp only [rounds, hlt, Bool.false_eq_true, ↓reduceIte]
    rw [show nblk d.l0 d.l1 = _ from hq]
    exact toNat_W (by omega)
  have hn : nmain d.l0 = W ((maxA d.l0).toNat / 64) := by
    have h := shru_int (n := 6) hA (by decide) (by decide)
    rw [← eq_W] at h
    exact h
  rw [ht] at hRe
  have hcn : d.cnt.toNat < 2 ^ 32 := by rw [hc]; simp [W]; omega
  simp only [isMain, hn, scmp]
  rw [eq_W d.cnt, r32_W hcn, r32_W (by omega)]
  simp only [PTX.compare, toNat_W (show d.cnt.toNat < 2 ^ 64 by omega),
    toNat_W (show (maxA d.l0).toNat / 64 < 2 ^ 64 by omega)]
  simp only [decide_eq_true_eq]
  omega

set_option linter.unusedSimpArgs false in
/-- **A gather moves 2304 bytes** when its block is a main one or the extra cache is on. -/
theorem gather_bytes (hp : Pre P L m) {d : D} {k : Fin 16} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hat : (code P L g).AtD d t) (hs : d.site = .gather k)
    (hc : kernel.code[(code P L g).pc d]? = some ins)
    (hf : Fires ((code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hmain : isMain d = true ∨ P.extra_topk ≠ 0) {a : Nat} {s : TensorCopy.Spec}
    (hk : e.kind = .tensorIssue a s) : TensorTransfer.bytes s.descriptor = 2304 := by
  have hx : (sel (isMain d) 768 896).toNat = 768 ∨
      ((sel (isMain d) 768 896).toNat = 896 ∧ P.extra_topk ≠ 0) := by
    cases hm : isMain d
    · rw [hm] at hmain
      exact .inr ⟨by simp [sel], hmain.resolve_left (by decide)⟩
    · exact .inl (by simp [sel])
  tma_state d
  obtain ⟨hpc, -, -, -, hF⟩ := hat
  simp only at hs
  subst hs
  fin_cases k <;>
  · try dsimp only [code, facts, Site.pc, coordPc, Fin.isValue, Fin.val_zero, Fin.val_one,
      Fin.val_two] at hpc hc hf hF ⊢
    try simp only [Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.reduceEqDiff,
      Fin.val_ofNat, Nat.reduceMod] at hpc hc hf hF ⊢
    have hreg := regs_of_factsFrom hF (r := 3049) (by decide)
    simp only [valueOf, values, dstVals, valuesLoop, valuesPre,
      List.lookup, List.cons_append, List.nil_append, Option.getD_some] at hreg
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact gather_bytes_of hp hf hreg hx hk

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
