-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Ld
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Div
public import Lemmas.Flow.SegQChain
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Geometry
import Kernels.InklingRelDecode.Proof.Prologue.Steps.QuerySetup
import Kernels.InklingRelDecode.Proof.Prologue.Steps.QueryPointer
import Kernels.InklingRelDecode.Proof.Prologue.Steps.SequenceMath

@[expose] public section

/-! # The strict step of the third request load and the sequence span -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

variable (a y p : Nat) (won : Bool) (bcast : Value) (v : Data.Vals)

/-- The words of the sequence span: the request words are read, the site is the first election. -/
abbrev dSeq : Data.D := ⟨⟨.el 0, .bits 32 (BitVec.ofNat 64 a), .bits 32 (BitVec.ofNat 64 y),
  .bits 32 (BitVec.ofNat 64 p), won, bcast⟩, v⟩

seg_chain seqA (fun a F b G => SegQ kernel Assumptions.all L g (QT proQt) a F b G)
  (fun pc => dFactsAt Q L g w (dSeq a y p won bcast v) pc) from 42 to 59 step 4
  by simp only [dSeq]; pro_seg

variable (hb : g % L.block < 256)
include hb

local notation "DD" => Data.dF Q L g (dSeq a y p won bcast v)
local notation "VV" => valueOf Q L g w (Data.D.c (dSeq a y p won bcast v))
local notation "FA" pc => dFactsAt Q L g w (dSeq a y p won bcast v) pc

omit hb in
/-- The four token sums of the query rows (pcs 84 to 88). -/
theorem seqT : SegQ kernel Assumptions.all L g (QT proQt) 84 (FA 84) 88 (FA 88) := by
  simp only [dSeq]; pro_seg

/-- The sequence span from the division to the first election, by the exact stretches of the
control machine. -/
theorem seqC : SegQ kernel Assumptions.all L g (QT proQt) 60 (FA 60) 130 (FA 130) := by
  refine
    SegQ.comp (b := 61) (G := FA 61) ?_ (
    SegQ.comp (b := 64) (G := FA 64) ?_ (
    SegQ.comp (b := 66) (G := FA 66) ?_ (
    SegQ.comp (b := 71) (G := FA 71) ?_ (
    SegQ.comp (b := 75) (G := FA 75) ?_ (
    SegQ.comp (b := 79) (G := FA 79) ?_ (
    SegQ.comp (b := 84) (G := FA 84) ?_ (
    SegQ.comp (b := 88) (G := FA 88) (seqT a y p won bcast v) (
    SegQ.comp (b := 100) (G := FA 100) ?_ (
    SegQ.comp (b := 101) (G := FA 101) ?_ (
    SegQ.comp (b := 109) (G := FA 109) ?_ (
    SegQ.comp (b := 117) (G := FA 117) ?_ (
    SegQ.comp (b := 121) (G := FA 121) ?_ (
    SegQ.comp (b := 125) (G := FA 125) ?_ (
    SegQ.comp (b := 129) (G := FA 129) ?_ ?_))))))))))))))
  · pro_br seg_clip
  · pro_br (seg_lane_row hb)
  · pro_br (seg_lane_col hb)
  · pro_br (seg_groups hb)
  · pro_br (seg_token_hi hb)
  · pro_br (seg_token_lo hb)
  · pro_br (seg_masks _ rfl)
  · pro_br seg_query_origins
  · pro_br seg_head
  · pro_br seg_sums
  · pro_br seg_rems
  · pro_br seg_heads
  · pro_br seg_hoffs
  · pro_br seg_query_pointers
  · pro_br (seg_eligible hb)

omit hb in
theorem r32_mod32 (n : Nat) : r32 (BitVec.ofNat 64 (n % 2 ^ 32)) = r32 (BitVec.ofNat 64 n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [r32, truncBits, BitVec.toNat_ofNat]
  omega

omit hb in
/-- **The division of the iteration count** (pc 59): non-negative numerator, positive divisor. -/
theorem seqD (hs0 : 0 < Q.splits) (hs1 : (L.ctaidOf (g / L.block)).get .x < Q.splits)
    (hs2 : Q.splits + 2 ^ 24 < 2 ^ 31) (hp : p + 511 < 2 ^ 31) :
    SegQ kernel Assumptions.all L g (QT proQt) 59 (FA 59) 60 (FA 60) := by
  refine div_s_piece (dst := 486) (x := 637) (y := 532) Flow.code_59 (by decide +kernel)
    (holds_tab (D := DD) (V := VV) (rs := ctlLive 59) (r := 637) (by decide +kernel))
    (holds_tab (D := DD) (V := VV) (rs := ctlLive 59) (r := 532) (by decide +kernel))
    (fun R h => ?_) ?_ ?_ (by decide +kernel) (by decide +kernel)
  · have h1 := holds_tab_write (D := DD) (V := VV) (rs := ctlLive 59) (rs' := ctlLive 60)
      (dst := 486) (fun q hq => ?_) (by decide +kernel) R h
    · convert h1 using 4
      · simp only [valueOf_plain (by decide +kernel : copyReg 486 = false), registerValue, iters]
        rw [r32_mod32]
      · rfl
    · have := dF_keys_early (L := L) (g := g) (d := dSeq a y p won bcast v) rfl q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      omega
  · have e : addi (W p) 127 = W (p + 127) := by
      simpa using addi_W (a := p) (n := 127) (by omega) (by omega)
    have e2 : Lib.word (Value.bits 32 (BitVec.ofNat 64 p)) = W p := r32_W (by omega)
    simp only [e2, e]
    exact dividend_nonneg hs1 hs2 (by omega)
  · exact divisor_pos hs0 (by omega)

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
