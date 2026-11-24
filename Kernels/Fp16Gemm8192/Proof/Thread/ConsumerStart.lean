-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Consumer
public import Kernels.Fp16Gemm8192.Proof.Thread.Cluster
public import Kernels.Fp16Gemm8192.Proof.Thread.Claims
public import Lemmas.Flow.Local
public import Lemmas.Flow.Async
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The consumer warps' start: the tile and the address registers

Warps 0 to 7 leave the prologue's dispatch and lower their register count. The CTA index gives the
tile the thread starts with; the swizzled staging addresses come from the thread index before the
CLC
poll. The bit arithmetic on the thread index is closed by bounded lemmas, checked on every thread
index below 256. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

/-- The lead value of a thread: the code's bit arithmetic on its warp index and lane. -/
theorem setup_lead : ∀ tid < 256, truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid / 32)) &&&
    truncBits 32 (BitVec.ofInt 64 3)) ||| truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid)) &&&
    truncBits 32 (BitVec.ofInt 64 31)) = BitVec.ofNat 64 (tid / 32 % 4 ||| tid % 32) := by
  table_decide

/-- The predicate of the lead value being nonzero (the `setp` of the code). -/
theorem setup_leadNe : ∀ tid < 256,
    PTX.compare Cmp.ne IType.b 32 (truncBits 32 (BitVec.ofNat 64 (tid / 32 % 4 ||| tid %
    32))) (truncBits 32 (BitVec.ofInt 64 0)) = decide (tid / 32 % 4 ||| tid % 32 ≠ 0) := by
  table_decide

/-- The swizzle offset of the warp group, shifted by 5 and masked by 128. -/
theorem setup_p8 : ∀ tid < 256, truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 5)).toNat ≥ 32 then
    0 else truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid / 32)) <<<
    (truncBits 32 (BitVec.ofInt 64 5)).toNat)) &&& truncBits 32 (BitVec.ofInt 64 128) =
    BitVec.ofNat 64 (128 * (tid / 32 / 4)) := by
  table_decide

/-- The accumulator column offset of the warp group, shifted by 6 and masked by 256. -/
theorem setup_p113 : ∀ tid < 256, truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 6)).toNat ≥
    32 then 0 else truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid / 32)) <<<
    (truncBits 32 (BitVec.ofInt 64 6)).toNat)) &&& truncBits 32 (BitVec.ofInt 64 256) =
    BitVec.ofNat 64 (256 * (tid / 32 / 4)) := by
  table_decide

/-- The column offsets added to the warp group offset: an offset `c` below 256 sets bits that the
group offset does not have, so the `|||` is the sum. -/
theorem setup_or : ∀ tid < 256, ∀ c : Int, 0 ≤ c → c < 256 →
    truncBits 32 (BitVec.ofNat 64 (256 * (tid / 32 / 4))) ||| truncBits 32 (BitVec.ofInt 64 c) =
      BitVec.ofNat 64 (256 * (tid / 32 / 4) + c.toNat) := by
  have key : ∀ k < 2, ∀ n : ℕ, n < 256 → truncBits 32 (BitVec.ofNat 64 (256 * k)) |||
      truncBits 32 (BitVec.ofInt 64 (n : Int)) = BitVec.ofNat 64 (256 * k + n) := by
    table_decide
  intro tid htid c h0 h1
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  simpa using key (tid / 32 / 4) (by omega) n (by omega)

/-- The staging offset of chunk 0, doubled (the code shifts it left by one) -/
theorem setup_sh0 : ∀ tid < 256, truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 1)).toNat ≥ 32 then
    0 else truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 (if
    (truncBits 32 (BitVec.ofInt 64 10)).toNat ≥ 32 then 0 else truncBits 32
    (truncBits 32 (BitVec.ofNat 64 (tid / 32)) <<< (truncBits 32 (BitVec.ofInt 64 10)).toNat)) &&&
    truncBits 32 (BitVec.ofInt 64 3072)) |||
    truncBits 32 (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 5)).toNat ≥ 32 then 0 else
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid)) <<<
    (truncBits 32 (BitVec.ofInt 64 5)).toNat)) &&& truncBits 32 (BitVec.ofInt 64 960))) |||
    truncBits 32 (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 11)).toNat ≥ 32 then 0 else
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid / 32)) <<<
    (truncBits 32 (BitVec.ofInt 64 11)).toNat)) &&& truncBits 32 (BitVec.ofInt 64 8192))) |||
    truncBits 32 (truncBits 32 (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 5)).toNat ≥ 32 then
    0 else truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid)) <<<
    (truncBits 32 (BitVec.ofInt 64 5)).toNat)) &&& truncBits 32 (BitVec.ofInt 64 32)) |||
    truncBits 32 (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 2)).toNat ≥ 32 then 0 else
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid)) <<<
    (truncBits 32 (BitVec.ofInt 64 2)).toNat)) &&& truncBits 32 (BitVec.ofInt 64 24)))) <<<
    (truncBits 32 (BitVec.ofInt 64 1)).toNat)) = BitVec.ofNat 64 (2 * stage tid 0) := by
  table_decide

/-- The staging offset of chunk 1, doubled (the code shifts it left by one) -/
theorem setup_sh1 : ∀ tid < 256, truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 1)).toNat ≥ 32 then
    0 else truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 (if
    (truncBits 32 (BitVec.ofInt 64 10)).toNat ≥ 32 then 0 else truncBits 32
    (truncBits 32 (BitVec.ofNat 64 (tid / 32)) <<< (truncBits 32 (BitVec.ofInt 64 10)).toNat)) &&&
    truncBits 32 (BitVec.ofInt 64 3072)) |||
    truncBits 32 (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 5)).toNat ≥ 32 then 0 else
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid)) <<<
    (truncBits 32 (BitVec.ofInt 64 5)).toNat)) &&& truncBits 32 (BitVec.ofInt 64 960))) |||
    truncBits 32 (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 11)).toNat ≥ 32 then 0 else
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid / 32)) <<<
    (truncBits 32 (BitVec.ofInt 64 11)).toNat)) &&& truncBits 32 (BitVec.ofInt 64 8192))) |||
    truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64
    5)).toNat ≥ 32 then 0 else truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid)) <<<
    (truncBits 32 (BitVec.ofInt 64 5)).toNat)) &&& truncBits 32 (BitVec.ofInt 64 32)) |||
    truncBits 32 (BitVec.ofInt 64 8)) ^^^ truncBits 32
    (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 2)).toNat ≥ 32 then 0 else
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid)) <<<
    (truncBits 32 (BitVec.ofInt 64 2)).toNat)) &&& truncBits 32 (BitVec.ofInt 64 24)))) <<<
    (truncBits 32 (BitVec.ofInt 64 1)).toNat)) = BitVec.ofNat 64 (2 * stage tid 1) := by
  table_decide

/-- The staging offset of chunk 2, doubled (the code shifts it left by one) -/
theorem setup_sh2 : ∀ tid < 256, truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 1)).toNat ≥ 32 then
    0 else truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 (if
    (truncBits 32 (BitVec.ofInt 64 10)).toNat ≥ 32 then 0 else truncBits 32
    (truncBits 32 (BitVec.ofNat 64 (tid / 32)) <<< (truncBits 32 (BitVec.ofInt 64 10)).toNat)) &&&
    truncBits 32 (BitVec.ofInt 64 3072)) |||
    truncBits 32 (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 5)).toNat ≥ 32 then 0 else
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid)) <<<
    (truncBits 32 (BitVec.ofInt 64 5)).toNat)) &&& truncBits 32 (BitVec.ofInt 64 960))) |||
    truncBits 32 (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 11)).toNat ≥ 32 then 0 else
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid / 32)) <<<
    (truncBits 32 (BitVec.ofInt 64 11)).toNat)) &&& truncBits 32 (BitVec.ofInt 64 8192))) |||
    truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64
    5)).toNat ≥ 32 then 0 else truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid)) <<<
    (truncBits 32 (BitVec.ofInt 64 5)).toNat)) &&& truncBits 32 (BitVec.ofInt 64 32)) |||
    truncBits 32 (BitVec.ofInt 64 16)) ^^^ truncBits 32
    (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 2)).toNat ≥ 32 then 0 else
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid)) <<<
    (truncBits 32 (BitVec.ofInt 64 2)).toNat)) &&& truncBits 32 (BitVec.ofInt 64 24)))) <<<
    (truncBits 32 (BitVec.ofInt 64 1)).toNat)) = BitVec.ofNat 64 (2 * stage tid 2) := by
  table_decide

/-- The staging offset of chunk 3, doubled (the code shifts it left by one) -/
theorem setup_sh3 : ∀ tid < 256, truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 1)).toNat ≥ 32 then
    0 else truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 (if
    (truncBits 32 (BitVec.ofInt 64 10)).toNat ≥ 32 then 0 else truncBits 32
    (truncBits 32 (BitVec.ofNat 64 (tid / 32)) <<< (truncBits 32 (BitVec.ofInt 64 10)).toNat)) &&&
    truncBits 32 (BitVec.ofInt 64 3072)) |||
    truncBits 32 (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 5)).toNat ≥ 32 then 0 else
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid)) <<<
    (truncBits 32 (BitVec.ofInt 64 5)).toNat)) &&& truncBits 32 (BitVec.ofInt 64 960))) |||
    truncBits 32 (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 11)).toNat ≥ 32 then 0 else
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid / 32)) <<<
    (truncBits 32 (BitVec.ofInt 64 11)).toNat)) &&& truncBits 32 (BitVec.ofInt 64 8192))) |||
    truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64
    5)).toNat ≥ 32 then 0 else truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid)) <<<
    (truncBits 32 (BitVec.ofInt 64 5)).toNat)) &&& truncBits 32 (BitVec.ofInt 64 32)) |||
    truncBits 32 (BitVec.ofInt 64 24)) ^^^ truncBits 32
    (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 2)).toNat ≥ 32 then 0 else
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid)) <<<
    (truncBits 32 (BitVec.ofInt 64 2)).toNat)) &&& truncBits 32 (BitVec.ofInt 64 24)))) <<<
    (truncBits 32 (BitVec.ofInt 64 1)).toNat)) = BitVec.ofNat 64 (2 * stage tid 3) := by
  table_decide

/-- The warp group offset of the second staging buffer, masked by 16384. -/
theorem setup_sel : ∀ tid < 256,
    truncBits 32 (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 12)).toNat ≥ 32 then 0 else
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 (tid / 32)) <<<
    (truncBits 32 (BitVec.ofInt 64 12)).toNat)) &&& truncBits 32 (BitVec.ofInt 64 16384)) =
    BitVec.ofNat 64 (16384 * (tid / 32 / 4)) := by
  table_decide

/-- The starting tile row of a CTA, from its index. -/
theorem setup_m : ∀ c < 1024,
    truncBits 32 (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 6)).toNat ≥ 32 then 0 else
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 (c))) >>>
    (truncBits 32 (BitVec.ofInt 64 6)).toNat) &&& truncBits 32 (BitVec.ofInt 64 33554424)) |||
    truncBits 32 (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 1)).toNat ≥ 32 then 0 else
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 (c))) >>>
    (truncBits 32 (BitVec.ofInt 64 1)).toNat) &&& truncBits 32 (BitVec.ofInt 64 7)) =
    BitVec.ofNat 64 (c / 512 % 2 * 8 + c / 2 % 8) := by
  table_decide

/-- The starting tile column of a CTA, from its index. -/
theorem setup_n : ∀ c < 1024, truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 4)).toNat ≥ 32 then
    0 else truncBits 32 (truncBits 32 (BitVec.ofNat 64 (c))) >>>
    (truncBits 32 (BitVec.ofInt 64 4)).toNat) &&& truncBits 32 (BitVec.ofInt 64 31) =
    BitVec.ofNat 64 (c / 16 % 32) := by
  table_decide

/-- The stage index is below 16384 for every thread of the warp groups. -/
theorem setup_stageLt : ∀ tid < 256, ∀ k < 4, stage tid k < 16384 := by
  table_decide

/-- The group's warps lower their register count: the tile of the CTA is set from the CTA index
and the CLC poll is reached, with the address registers computed. -/
theorem step_setMaxReg {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads) (hw : tidOf L g < 256)
    (hs : d.site = .setMaxReg) (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    next L g d e = some none ∨
      ∃ d' t', next L g d e = some (some d') ∧
        Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
          Inv d' := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_1)
  obtain rfl := fires_next (show AdvancesOp (.setMaxReg true 224) from trivial) hf
  have h1 := At.next h
  have hc1024 : g / L.block < 1024 := hpre.grid ▸ cta_lt hpre hg
  have hs0 := setup_stageLt (tidOf L g) hw 0 (by decide)
  have hs1 := setup_stageLt (tidOf L g) hw 1 (by decide)
  have hs2 := setup_stageLt (tidOf L g) hw 2 (by decide)
  have hs3 := setup_stageLt (tidOf L g) hw 3 (by decide)
  obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 87 (PTX.next t) = some t' ∧
      At t' Site.clcWait.pc (facts L g ⟨.clcWait, Loader.claimM (g / L.block),
        Loader.claimN (g / L.block), m', n', 0, 0, resp, x, acc, base⟩) := by
    cons_seg h1 hpre [  -- the bounds of `setup_or` are closed by the two Int simprocs
      sregValue, Prologue.claimM_of hc1024, Prologue.claimN_of hc1024,
      setup_lead (tidOf L g) hw, setup_leadNe (tidOf L g) hw, setup_p8 (tidOf L g) hw,
      setup_p113 (tidOf L g) hw, setup_or (tidOf L g) hw, Int.reduceLE, Int.reduceLT,
      setup_sh0 (tidOf L g) hw, setup_sh1 (tidOf L g) hw, setup_sh2 (tidOf L g) hw,
      setup_sh3 (tidOf L g) hw, setup_sel (tidOf L g) hw, setup_m (g / L.block) hc1024,
      setup_n (g / L.block) hc1024, Launch.oneDim_ctaidOf hpre.oneDimLaunch.1 (g / L.block),
      Dim3.get]
  right
  refine ⟨⟨.clcWait, Loader.claimM (g / L.block), Loader.claimN (g / L.block), m', n', 0, 0,
    resp, x, acc, base⟩, t', ?_, run_rtg hr, ht', ⟨(Loader.claim_lt _).1, (Loader.claim_lt _).2,
    hi.3, hi.4, (by show (0 : Nat) < 2; omega), (by show (0 : Nat) < 2; omega), hi.7⟩⟩
  simp [next]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
