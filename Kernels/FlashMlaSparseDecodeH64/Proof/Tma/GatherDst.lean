-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Gather
public import Lemmas.Tensor.LoadBox
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.KvMapAt
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Objs
import Lemmas.Flow.Step.SiteShape

@[expose] public section

/-! # The TMA warp's gathers land in the raw tile

Gather `k` of a block whose raw tile is `b` writes to the shared base `131072 + 36864 b + 2304 k`
of its CTA's workspace (the destination register `%r690`, `%r697`, ... is the raw tile's base
plus `2304 k`, `dstVals`), and its box, the four-row transfer of a cache map (`encodeKv`: 144
words of 4 bytes per row, no swizzle), covers 2304 bytes from the base (`gather_dst`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A 32-bit destination register as a shared address of the thread's CTA. -/
theorem dst_loc {t : TState} {r : Nat} {x : BitVec 64} (hr : t.regs r = some (.bits 32 x)) :
    sharedEffAddr L g t false r 0 = .ok ⟨.shared, g / L.block, (truncBits 32 x).toNat⟩ := by
  simp [sharedEffAddr, readReg, hr, readBits, bind, Except.bind, pure, Except.pure, truncBits]

/-- The raw tile `b`'s byte `n` as a 32-bit word. -/
theorem rawDst (hp : Pre P L m) {d : D} {b : Nat} (hb : b < 2) (hbuf : d.buf = W b)
    {n : Nat} (hn : n ≤ 165632) :
    (truncBits 32 (addi (rawB L d) (n : Int))).toNat = L.sharedBase + (36864 * b + n) := by
  have h3 := sharedBase_lt hp
  simp only [rawB, tileB, hbuf]
  rw [slotB_W hp (by omega), show (36856 : Int) = ((36856 : Nat) : Int) from rfl,
    i32_W (n := 36856) (by decide), mad32_W (by omega) (by decide) (by omega),
    addi_W (by omega) (by omega)]
  simp only [W, truncBits, BitVec.toNat_ofNat]
  omega

/-- **A gather4 load of a cache map** to the shared word `y` lands at `y` and covers 2304
unswizzled bytes. -/
theorem gather_of (hp : Pre P L m) {t : TState} {dst : Nat} {cs : List Opnd}
    {pol : Option Opnd} {pc : Nat} {e : Event} {o : Option TState} {x : Nat} {y : BitVec 64}
    {c : Nat}
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.cpTensor false false dst 0 (.reg 3049) cs 696 0 none .fourRows pol)) e o)
    (hm : t.regs 3049 = some (.bits 64 (BitVec.ofNat 64 (P.param1Base + x))))
    (hx : x = 768 ∨ (x = 896 ∧ P.extra_topk ≠ 0))
    (hdr : t.regs dst = some (.bits 32 y)) (hy : (truncBits 32 y).toNat = L.sharedBase + c)
    {a : Nat} {s : TensorCopy.Spec} (hk : e.kind = .tensorIssue a s) :
    s.sharedBase = ⟨.shared, g / L.block, L.sharedBase + c⟩ ∧ s.descriptor.swizzle = .none ∧
      TensorTile.rows s.descriptor.box *
        (TensorTile.count s.descriptor.box 0 * s.descriptor.format.bytes) = 2304 ∧
      ∃ d0, s.descriptor = TensorMode.fourRows.transfer d0 ∧ KvMapAt P x ⟨s.outer, d0⟩ := by
  have hcp := fires_cpTensor_copy hf hk
  obtain ⟨hma, -, d, hd, -, hdesc, -⟩ := tensorLoadCopy_ok hcp
  have hsb := TensorCopy.tensorLoadCopy_dst hcp
  rw [dst_loc hdr, hy] at hsb
  rw [tensorMapAddress_bits hm] at hma
  obtain rfl := (Except.ok.inj hma).symm
  have h64 : (BitVec.ofNat 64 (P.param1Base + x)).toNat = P.param1Base + x := by
    have := hp.param1Range
    simp only [BitVec.toNat_ofNat]
    omega
  rw [h64] at hd
  have hmap : KvMapAt P x ⟨s.outer, d⟩ := by
    rcases hx with rfl | ⟨rfl, hx⟩
    · rw [hp.mapKVBind] at hd
      exact .inl ⟨rfl, (Option.some.inj hd).symm⟩
    · rcases hp.mapExtraKvBind with h0 | hb
      · exact absurd h0 hx
      rw [hb] at hd
      exact .inr ⟨rfl, hx, (Option.some.inj hd).symm⟩
  refine ⟨(Except.ok.inj hsb).symm, ?_⟩
  suffices H : s.descriptor.swizzle = .none ∧ TensorTile.rows s.descriptor.box *
      (TensorTile.count s.descriptor.box 0 * s.descriptor.format.bytes) = 2304 from
    ⟨H.1, H.2, d, hdesc, hmap⟩
  rw [hdesc]
  have hgeo : ∀ y : (n : Nat) × TensorDescriptor.Descriptor n,
      y = ⟨1, mapKv P.kvBase P.numBlocks P.blockStride P.kvClass⟩ ∨
        y = ⟨1, mapExtraKv P.extraKvBase P.extraNumBlocks P.extraBlockStride P.extraKvClass⟩ →
      (TensorMode.fourRows.transfer y.2).swizzle = .none ∧
        TensorTile.rows (TensorMode.fourRows.transfer y.2).box *
          (TensorTile.count (TensorMode.fourRows.transfer y.2).box 0 *
            (TensorMode.fourRows.transfer y.2).format.bytes) = 2304 := by
    rintro y (rfl | rfl) <;>
      simp [mapKv, mapExtraKv, encodeKv, TensorMode.transfer, TensorDescriptor.Descriptor.fourRows,
        TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step,
        TensorDescriptor.Format.bytes]
  rcases hmap with ⟨-, h⟩ | ⟨-, -, h⟩
  · exact hgeo ⟨s.outer, d⟩ (.inl h)
  · exact hgeo ⟨s.outer, d⟩ (.inr h)

set_option linter.unusedSimpArgs false in
/-- **Gather `k` lands in raw tile `b`**: its shared base is the workspace byte
`131072 + 36864 b + 2304 k` of the CTA, its box 2304 unswizzled bytes, when its block is a main
one or the extra cache is on. -/
theorem gather_dst (hp : Pre P L m) {d : D} {k : Fin 16} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hat : (code P L g).AtD d t) (hs : d.site = .gather k)
    (hc : kernel.code[(code P L g).pc d]? = some ins)
    (hf : Fires ((code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hmain : isMain d = true ∨ P.extra_topk ≠ 0) {b : Nat} (hb : b < 2) (hbuf : d.buf = W b)
    {a : Nat} {s : TensorCopy.Spec} (hk : e.kind = .tensorIssue a s) :
    s.sharedBase = ⟨.shared, g / L.block, L.sharedBase + (36864 * b + (131072 + 2304 * k.val))⟩ ∧
      s.descriptor.swizzle = .none ∧ TensorTile.rows s.descriptor.box *
        (TensorTile.count s.descriptor.box 0 * s.descriptor.format.bytes) = 2304 ∧
      ∃ d0, s.descriptor = TensorMode.fourRows.transfer d0 ∧
        KvMapAt P (sel (isMain d) 768 896).toNat ⟨s.outer, d0⟩ := by
  have hx : (sel (isMain d) 768 896).toNat = 768 ∨
      ((sel (isMain d) 768 896).toNat = 896 ∧ P.extra_topk ≠ 0) := by
    cases hm : isMain d
    · rw [hm] at hmain
      exact .inr ⟨by simp [sel], hmain.resolve_left (by decide)⟩
    · exact .inl (by simp [sel])
  have hR := rawDst (d := d) (n := 131072 + 2304 * k.val) hp hb hbuf
    (by have := k.isLt; omega)
  tma_state d
  obtain ⟨hpc, -, -, -, hF⟩ := hat
  simp only at hs
  subst hs
  fin_cases k <;>
  · try dsimp only [code, facts, Site.pc, coordPc, Fin.isValue, Fin.val_zero, Fin.val_one,
      Fin.val_two] at hpc hc hf hF hR ⊢
    try simp only [Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.reduceEqDiff,
      Fin.val_ofNat, Nat.reduceMod, Nat.cast_ofNat] at hpc hc hf hF hR ⊢
    have hreg := regs_of_factsFrom hF (r := 3049) (by decide)
    simp only [valueOf, values, dstVals, valuesLoop, valuesPre,
      List.lookup, List.cons_append, List.nil_append, Option.getD_some] at hreg
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact gather_of hp hf hreg hx (regs_of_factsFrom hF (by decide)) hR hk

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
