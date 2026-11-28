-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StepArrS
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Arr
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.Epi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.EpiFacts
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part017

@[expose] public section

/-! # The strict window of the loop's exit (pcs 1147 to 1153)

The epilogue's first run (`Gen.e1_run`) with the control constants it writes kept: the barrier's
operands (registers 1725 and 1726) and the ring parity's low byte (register 2954). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The first run of the epilogue, with the control constants it writes among its facts. -/
theorem e1S (L : Launch) (g : Nat) (V : Nat → Value) :
    SegD kernel Assumptions.all L g 7 1147 (Gen.e1_facts0 V) 1154
      ((1725, Gen.e1_v1152 V) :: (1726, Gen.e1_v1153 V) :: (2954, Gen.e1_v1149 V) ::
        Gen.e1_facts1 V) (Gen.e1_cond V) :=
  SegD.outs_lit (items := Gen.e1_items0)
    ⟨⟨XItem.codeB_of Flow.code_1147 rfl,
          PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 1147,
          PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.rule_w0 1147 rfl⟩,
     ⟨XItem.codeB_of Flow.code_1148 rfl,
         PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 1148, XItem.core_cvtInt
         (PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 1148)
         (PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.noRuleW0 (op := Gen.e1_op1148) 1148 rfl)
         rfl rfl rfl rfl⟩,
     ⟨XItem.codeB_of Flow.code_1149 rfl,
         PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 1149, XItem.core_and
         (PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 1149)
         (PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.noRuleW0 (op := Gen.e1_op1149) 1149 rfl)
         rfl⟩,
     ⟨XItem.codeB_of Flow.code_1150 rfl,
         PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 1150,
         PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.rule_move 1150 rfl⟩,
     ⟨XItem.codeB_of Flow.code_1151 rfl,
         PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 1151,
         PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.rule_move 1151 rfl⟩,
     ⟨XItem.codeB_of Flow.code_1152 rfl,
         PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 1152, XItem.core_mov
         (PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 1152)
         (PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.noRuleW0 (op := Gen.e1_op1152) 1152 rfl)
         rfl⟩,
     ⟨XItem.codeB_of Flow.code_1153 rfl,
         PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 1153, XItem.core_mov
         (PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 1153)
         (PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.noRuleW0 (op := Gen.e1_op1153) 1153 rfl)
         rfl⟩,
     trivial⟩
    rfl (by kernel_rfl) rfl (by kernel_rfl) (by kernel_rfl)

/-- The ring parity register's value is the table's field. -/
theorem arrS_v452 (d : Control.D) :
    Control.valueOf P L g w d 452 = .bits 16 d.ps := by
  simp only [Control.valueOf, Control.values, List.append_assoc]
  rw [arrL_lookup_off (a := Control.valuesLen d) (by simp [Control.valuesLen])]
  rfl

/-- The barrier's operands and the parity's low byte, in the control table. -/
theorem arrS_vconst (d : Control.D) :
    Control.valueOf P L g w d 1725 = w32 9 ∧ Control.valueOf P L g w d 1726 = w32 128 ∧
      Control.valueOf P L g w d 2954 = w32 (Control.parW d.ps) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [Control.valueOf, Control.values, List.append_assoc]
    rw [arrL_lookup_off (a := Control.valuesLen d) (by simp [Control.valuesLen])]
    rfl

/-- The facts the first run of the epilogue reads: the ring parity and the carried words. -/
def exitFacts (L : Launch) (c : Control.D) (b : Blk) : List (Nat × Value) :=
  (452, .bits 16 c.ps) :: wF (scX L) .bar0 (arrNext L b)

/-- The condition of the exit's window. -/
def exitCond (L : Launch) (c : Control.D) (b : Blk) : Prop :=
  Gen.e1_cond (lookupD (exitFacts L c b))

/-- The registers of the control table that are live at the epilogue's first barrier and
untouched by the run. -/
def exitKeep : List Nat :=
  [459, 460, 463, 465, 469, 471, 472, 2953, 2991, 2992, 2993, 2994, 2995, 2996, 2997, 2998,
    2999, 3001]

theorem arrS_exit (d : D) (hs : d.c.site = .arrS)
    (h0 : scmpi .eq .b d.c.cnt 0 = true) (h117 : scmpi .ne .b (addi d.c.cnt 1) 1 = false)
    (hc : exitCond L d.c d.b) :
    ∃ n, Seg kernel Assumptions.all L g n 1123
      (Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b) 1154
      (Control.facts P L g w { Control.advance d.c with site := .ebar0 } ++
        wF (scX L) .ebar0 (arrNext L d.b)) := by
  have hp : d.c.site.pc = 1122 := by rw [hs]; rfl
  obtain ⟨n1, h1⟩ := arrSWinE (P := P) (L := L) (g := g) (w := w) d.c h0 h117
  have hf := Seg.frameSet (H := wF (scX L) .bar0 (arrNext L d.b)) rulesFrame (S := arrSS)
    (by kernel_rfl) (fun _ _ => PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree _)
    (by kernel_rfl) h1
  have h2 := (SegD.frame (H := factsFrom exitKeep (Control.valueOf P L g w
      { Control.advance d.c with site := .ebar0 }) ++ wF (scX L) .bar0 (arrNext L d.b))
    rulesFrame (e1S L g (lookupD (exitFacts L d.c d.b))) rfl (by kernel_rfl)
    (by rw [List.map_append, factsFrom_keys]; kernel_rfl)
    fun _ _ => PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree _).seg hc
  simp only [Control.advance, h0, ↓reduceIte] at hf h2 ⊢
  refine ⟨n1 + _, (hf.weaken_start fun R hR => ?_).comp
    ((h2.weaken_start fun R hR => ?_).weaken_end fun R hR => ?_)⟩
  · obtain ⟨hc', hd⟩ := (holds_append _ _ _).mp hR
    rw [hs] at hd
    unfold Control.facts at hc'
    rw [hp] at hc'
    exact (holds_append _ _ _).mpr ⟨holds_factsFrom_mono hc' (by decide +kernel),
      arrS_carry hd⟩
  · obtain ⟨hc', hd⟩ := (holds_append _ _ _).mp hR
    have h452 := holds_mem hc' (mem_factsFrom (show 452 ∈ Control.ctlLive 1147 by decide +kernel))
    rw [arrS_ring_eq d.c _ _ _ 452 (by simp), arrS_v452] at h452
    have hX : Holds R (exitFacts L d.c d.b) := ⟨h452, hd⟩
    exact (holds_append _ _ _).mpr
      ⟨holds_lookupD (live := [452, 2885, 2950, 2955]) hX (by kernel_rfl),
        (holds_append _ _ _).mpr ⟨holds_factsFrom_mono hc' (by decide +kernel), hd⟩⟩
  · obtain ⟨hl, hH⟩ := (holds_append _ _ _).mp hR
    obtain ⟨h1725, h1726, h2954, he1⟩ := hl
    obtain ⟨hK, hC⟩ := (holds_append _ _ _).mp hH
    obtain ⟨c1725, c1726, c2954⟩ := arrS_vconst (P := P) (L := L) (g := g) (w := w) d.c
    have hn : Holds R (factsFrom [1725, 1726, 2954] (Control.valueOf P L g w
        { site := .ebar0, el := d.c.el, a0 := d.c.a0, l0 := d.c.l0, l1 := d.c.l1,
          cnt := addi d.c.cnt 1, bi := addi d.c.bi 1, vs := d.c.vs, pv := d.c.pv, sl := d.c.sl,
          ps := d.c.ps, vt := d.c.vt })) := by
      refine ⟨?_, ?_, ?_, trivial⟩
      · show R 1725 = some (Control.valueOf P L g w _ 1725)
        rw [(arrS_vconst (P := P) (L := L) (g := g) (w := w) _).1]; exact h1725
      · show R 1726 = some (Control.valueOf P L g w _ 1726)
        rw [(arrS_vconst (P := P) (L := L) (g := g) (w := w) _).2.1]; exact h1726
      · show R 2954 = some (Control.valueOf P L g w _ 2954)
        rw [(arrS_vconst (P := P) (L := L) (g := g) (w := w) _).2.2]
        exact h2954
    have hall : Holds R (factsFrom (exitKeep ++ [1725, 1726, 2954]) (Control.valueOf P L g w
        { site := .ebar0, el := d.c.el, a0 := d.c.a0, l0 := d.c.l0, l1 := d.c.l1,
          cnt := addi d.c.cnt 1, bi := addi d.c.bi 1, vs := d.c.vs, pv := d.c.pv, sl := d.c.sl,
          ps := d.c.ps, vt := d.c.vt })) := by
      unfold factsFrom
      rw [List.map_append]
      exact (holds_append _ _ _).mpr ⟨hK, hn⟩
    have hmono : ∀ r ∈ Control.ctlLive 1154, r ∈ exitKeep ++ [1725, 1726, 2954] := by
      decide +kernel
    have h2880 := holds_lookupD (live := [2880]) hC (by kernel_rfl)
    exact (holds_append _ _ _).mpr ⟨holds_factsFrom_mono hall hmono,
      (holds_append _ _ _).mpr ⟨he1, h2880⟩⟩

/-- **The strict step at pc 1122**: the arrival ends the block; at the last block the epilogue's
first run is under its condition. -/
theorem sk_1122 (d : D) (hs : d.c.site = .arrS) (hok : d.ok = true)
    (hc : scmpi .ne .b (Control.advance d.c).cnt 1 = false → exitCond L d.c d.b) (e : Event) :
    (code P L g w).StepFor d e := by
  by_cases h117 : scmpi .ne .b (Control.advance d.c).cnt 1 = true
  · exact sk_1122b d hs hok h117 e
  · have h117' : scmpi .ne .b (Control.advance d.c).cnt 1 = false := by simpa using h117
    have hsucc : ∀ e, Control.succ P L g w d.c e =
        some (some { Control.advance d.c with site := .ebar0 }) := by
      intro e; simp [Control.succ, hs, h117']
    obtain ⟨hz, hnz⟩ := exit_cnt (P := P) (L := L) (g := g) (w := w) (e := e) hs
      (hsucc e) rfl
    have key : ∀ e, (code P L g w).StepFor d e := by
      refine skW_arr (pc := 1122) (pc' := 1154)
        (c' := { Control.advance d.c with site := .ebar0 })
        hs (by rw [hs]; rfl) rfl (by rw [hs]; exact Flow.code_1122)
        (fun {t e u} hf => by rw [hs] at hf; exact Code.fires_arrive_next hf)
        (by rw [hs]; rfl) hok hsucc (fun h => by simpa [advance_el] using h)
        (fun h => by simp [advance_el, h, Control.elems]) ?_
      exact arrS_exit (P := P) (L := L) (g := g) (w := w) d hs hz hnz (hc h117')
    exact fun ins => key e ins

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
