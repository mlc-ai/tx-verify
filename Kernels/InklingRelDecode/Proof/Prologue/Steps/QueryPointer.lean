-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Frame
import Kernels.InklingRelDecode.Gen.StepPrologue
import Kernels.InklingRelDecode.Gen.StepPrologue01
import Kernels.InklingRelDecode.Gen.StepPrologue02
import Lemmas.Flow.SegChain
import Lemmas.Flow.SignedBits

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

set_option maxRecDepth 100000
variable {Q : Params} {L : Launch} {g : Nat} {w : Value} {d : D}
local notation "F" => facts Q L g w d

private theorem tok_lt (tid gp : Nat) (h : gp < 4) : qTok tid gp < 2 ^ 31 := by
  unfold qTok qRow; omega

private theorem plain_add (bit : d.first.regBits.isSome) (δ : Nat) :
    Lib.addBase d.first δ = b32 (((Lib.word d.first).toNat + δ) % 2 ^ 32) := by
  unfold Lib.addBase
  cases h : d.first <;> simp_all [Value.regBits]

private theorem add_tok (bit : d.first.regBits.isSome) {pc dst src : Nat} (gp : Nat)
    (hgp : gp < 4)
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.add, .int .s 32, false, [some dst],
      [.reg 610, .reg src]⟩⟩) (hs : Assumptions.emuSites.contains pc = false)
    (hdst : valueOf Q L g w d dst =
      b32 (((Lib.word d.first).toNat + qTok (g % L.block) gp) % 2 ^ 32))
    (hsrc : valueOf Q L g w d src = b32 (qTok (g % L.block) gp))
    (k610 : 610 ∈ ctlLive pc) (ksrc : src ∈ ctlLive pc)
    (live : ∀ x ∈ ctlLive (pc + 1), x = dst ∨ x ∈ ctlLive pc) :
    SegU kernel Assumptions.all L g pc (factsFrom (ctlLive pc) (valueOf Q L g w d)) (pc + 1)
      (factsFrom (ctlLive (pc + 1)) (valueOf Q L g w d)) := by
  refine Lib.sum_span (V := valueOf Q L g w d) (r := 610) (δ := qTok (g % L.block) gp)
    (op := .reg src) false (tok_lt _ gp hgp) hc hs k610 ?_ ?_ live
  · have h610 : valueOf Q L g w d 610 = d.first := rfl
    rw [hdst, h610, plain_add bit]
  · intro t h
    exact Lib.delta_reg h ksrc hsrc (by have := tok_lt (g % L.block) gp hgp; omega)

private theorem query_tokens (bit : d.first.regBits.isSome) :
    SegU kernel Assumptions.all L g 84 (F 84) 88 (F 88) := by
  have step (pc dst src gp : Nat) (hgp : gp < 4)
      (hc : kernel.code[pc]? = some ⟨none, .int ⟨.add, .int .s 32, false, [some dst],
        [.reg 610, .reg src]⟩⟩) (hs : Assumptions.emuSites.contains pc = false)
      (hdst : valueOf Q L g w d dst =
        b32 (((Lib.word d.first).toNat + qTok (g % L.block) gp) % 2 ^ 32))
      (hsrc : valueOf Q L g w d src = b32 (qTok (g % L.block) gp))
      (k : 610 ∈ ctlLive pc ∧ src ∈ ctlLive pc ∧
        ∀ x ∈ ctlLive (pc + 1), x = dst ∨ x ∈ ctlLive pc) :
      SegU kernel Assumptions.all L g pc (F pc) (pc + 1) (F (pc + 1)) :=
    add_tok bit gp hgp hc hs hdst hsrc k.1 k.2.1 k.2.2
  exact (step 84 645 644 0 (by decide) Flow.code_84 (by decide) rfl rfl (by decide +kernel)).comp
    ((step 85 646 643 1 (by decide) Flow.code_85 (by decide) rfl rfl (by decide +kernel)).comp
    ((step 86 647 642 2 (by decide) Flow.code_86 (by decide) rfl rfl (by decide +kernel)).comp
    (step 87 648 641 3 (by decide) Flow.code_87 (by decide) rfl rfl (by decide +kernel))))

private theorem mulwide_s32 (a b : Nat) :
    truncBits (2 * 32) (BitVec.ofInt 64 (toSigned 32 (truncBits 32 (BitVec.ofNat 64 a)) *
      toSigned 32 (truncBits 32 (BitVec.ofNat 64 b)))) =
      BitVec.ofNat 64 ((Lib.sx a * Lib.sx b) % 2 ^ 64) := by
  have h := Lib.madwide_s32 a b 0
  have z : intOf IType.s 64 (truncBits 64 (BitVec.ofNat 64 0)) = 0 := by
    simp [intOf, toSigned, truncBits]
  rw [z] at h
  simpa [intBits, intOf] using h

private theorem sx_mod (n : Nat) : Lib.sx (n % 2 ^ 32) = Lib.sx n := by
  unfold Lib.sx
  simp

theorem seg_query_origins :
    Seg kernel Assumptions.all L g 12 88 (F 88) 100 (F 100) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    seg_close [queryValue, qProd, queryOrigin, u64, b64, mulwide_s32, sx_mod])

private theorem and7 (x : Nat) : x &&& 7 = x % 8 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 3
  simpa using this

/-- Close a value of the pointer chain: the stated value unfolded, the machine integer
normal form, the small remainders removed, then linear arithmetic. -/
local macro "qclose" : tactic => `(tactic| first
  | seg_close [queryValue, qSum, qTok, qRow, qHoff, u16, u32, and7]
  | (show Value.bits _ _ = _
     simp only [queryValue, qSum, qTok, qRow, qHoff, u16, u32, and7]
     nf_simp [and7]
     try simp (disch := omega) only [Nat.mod_eq_of_lt]
     all_goals omega))

theorem seg_sums : Seg kernel Assumptions.all L g 8 101 (F 101) 109 (F 109) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    qclose)

theorem seg_rems : Seg kernel Assumptions.all L g 8 109 (F 109) 117 (F 117) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    qclose)

theorem seg_heads : Seg kernel Assumptions.all L g 4 117 (F 117) 121 (F 121) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    qclose)

theorem seg_hoffs : Seg kernel Assumptions.all L g 4 121 (F 121) 125 (F 125) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    qclose)

private theorem hoff_m32 (y tid gp : Nat) : qHoff y tid gp % 4294967296 = qHoff y tid gp := by
  unfold qHoff; omega

private theorem hoff_m64 (y tid gp : Nat) :
    qHoff y tid gp % 18446744073709551616 = qHoff y tid gp := by
  unfold qHoff; omega

private theorem origin_m64 (Q : Params) (first : Value) (tid gp : Nat) :
    queryOrigin Q first tid gp % 18446744073709551616 = queryOrigin Q first tid gp := by
  unfold queryOrigin; omega

theorem seg_query_pointers : Seg kernel Assumptions.all L g 4 125 (F 125) 129 (F 129) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    show Value.bits _ _ = _
    simp only [queryValue, queryPointer, u64, b64]
    nf_simp
    simp only [intBits, intOf, truncBits, BitVec.toNat_ofInt, BitVec.toNat_ofNat, reduceCtorEq,
      ↓reduceIte, Nat.reducePow, Nat.reduceMod, Nat.mod_mod]
    simp only [hoff_m32, hoff_m64, origin_m64]
    apply congrArg
    omega)

private theorem head_mul (x : Nat) :
    Value.bits 32 (mul32 (W (x % 2 ^ 32)) (i32 6)) = u32 (x * 6) := by
  apply congrArg (Value.bits 32)
  apply BitVec.eq_of_toNat_eq
  simp only [mul32, r32, i32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_mul,
    BitVec.toNat_ofInt]
  norm_num

theorem seg_head : Seg kernel Assumptions.all L g 1 100 (F 100) 101 (F 101) := by
  intro t ht
  seg_fp ht using exact head_mul _

/-- The query row pointers of pcs 84 to 128: the sums of the first word with the tokens, the
row origins, the head offsets and the four pointers. -/
theorem query_chain (bit : d.first.regBits.isSome) :
    SegU kernel Assumptions.all L g 84 (F 84) 129 (F 129) :=
  (query_tokens bit).comp ((SegU.of_seg seg_query_origins).comp ((SegU.of_seg seg_head).comp
    ((SegU.of_seg (((seg_sums.comp seg_rems).comp seg_heads).comp seg_hoffs)).comp
      (SegU.of_seg seg_query_pointers))))

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
