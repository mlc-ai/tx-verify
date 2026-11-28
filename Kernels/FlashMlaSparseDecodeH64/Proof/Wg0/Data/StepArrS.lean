-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictF
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.ArrLWin
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StepKinds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.GenRules
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part009
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part010
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part017

@[expose] public section

/-! # The strict step of the softmax-ready arrival (pc 1122)

The block ends: the block's end values become the carried statistics of the next block
(`dataNext` at `arrS`), and the stretch to the next head is exact (`arrSWinA`, `arrSWinB`). -/

/-! # The control stretch after the softmax-ready arrival (pcs 1123 to 255), exactly

The counter test (pc 1123), the rings' advance (pcs 1125-1142, three `selp`s on the parity tests),
the counters (pcs 1143-1144), and the test of the last block (pcs 1145-1146); then the loop's
head (pcs 253-255) or the epilogue's masked moves (pc 1147). The pieces with a `selp` end in
explicit lists, which the symbolic walk needs to restate the conditional values. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64
open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The registers the stretch reads. -/
def arrSIn : List Nat := [2884, 2883, 2953, 452, 451, 2952, 465]

/-- The ring registers' values after the advance (pcs 1125-1142) with the counters (1143-1146). -/
def arrSLitB (d : Control.D) : List (Nat × Value) :=
  [(452, .bits 16 (sel (psc d.sl d.ps) (i16 1) (i16 0))),
   (451, .bits 16 (sel (pvc d.vs d.pv) (i16 1) (i16 0))),
   (2953, w32 (andi (not32 d.sl) 1)), (2952, w32 (nvs d.vs)),
   (2884, w32 (addi d.cnt 1)), (2883, w32 (addi d.bi 1)),
   (117, .pred (scmpi .ne .b (addi d.cnt 1) 1)), (465, w32 w)]

theorem arrSSegB (d : Control.D) :
    ∃ n, Seg kernel Assumptions.all L g n 1125
      ((113, .pred false) :: factsFrom arrSIn (valueOf P L g w d)) 1146 (arrSLitB (w := w) d) := by
  unfold arrSLitB
  seg_sym using w0_segS

/-- The counter test (pc 1123). -/
theorem arrSSeg0 (d : Control.D) :
    ∃ n, Seg kernel Assumptions.all L g n 1123 (factsFrom arrSIn (valueOf P L g w d)) 1124
      ((113, .pred (scmpi .eq .b d.cnt 0)) :: factsFrom arrSIn (valueOf P L g w d)) := by
  seg_sym using w0_segS

/-- The loop's head set-up (pcs 253-255), the facts of the stretch kept. -/
theorem arrSSegT (d : Control.D) :
    ∃ n, Seg kernel Assumptions.all L g n 253 (arrSLitB (w := w) d) 256
      ((76, .pred (scmpi .gt .s w 1)) :: (972, w32 9) :: (973, w32 128) ::
        arrSLitB (w := w) d) := by
  unfold arrSLitB
  seg_sym using w0_segS

/-- **The stretch with the rings' advance, to the loop's head** (pcs 1123 to 255). -/
theorem arrSCoreB (d : Control.D) (h0 : scmpi .eq .b d.cnt 0 = false)
    (h117 : scmpi .ne .b (addi d.cnt 1) 1 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 1123 (factsFrom arrSIn (valueOf P L g w d)) 256
      ((76, .pred (scmpi .gt .s w 1)) :: (972, w32 9) :: (973, w32 128) ::
        arrSLitB (w := w) d) := by
  obtain ⟨n1, h1⟩ := arrSSeg0 (P := P) (L := L) (g := g) (w := w) d
  rw [h0] at h1
  have hb := Seg.bra (K := kernel) (A := Assumptions.all) (L := L) (g := g) (target := 1143)
    (p := 113) (uni := false) (pick := false) Flow.code_1124
    (F := (113, .pred false) :: factsFrom arrSIn (valueOf P L g w d)) (List.mem_cons_self ..)
    (fun t _ a ha => bra_rule t a ha)
    (PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 1124)
  obtain ⟨n2, h2⟩ := arrSSegB (P := P) (L := L) (g := g) (w := w) d
  have hb2 := Seg.bra (K := kernel) (A := Assumptions.all) (L := L) (g := g) (target := 253)
    (p := 117) (uni := false) (pick := true) Flow.code_1146 (F := arrSLitB (w := w) d)
    (by simp only [arrSLitB, h117]; simp) (fun t _ a ha => bra_rule t a ha)
    (PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 1146)
  obtain ⟨n3, h3⟩ := arrSSegT (L := L) (g := g) (w := w) d
  exact ⟨_, h1.comp (hb.comp (h2.comp (hb2.comp h3)))⟩

/-- The facts after the counters when the block is the last (no ring advance). -/
def arrSLitA (d : Control.D) : List (Nat × Value) :=
  (2884, w32 (addi d.cnt 1)) :: (2883, w32 (addi d.bi 1)) ::
    (117, .pred (scmpi .ne .b (addi d.cnt 1) 1)) ::
    factsFrom [2953, 452, 451, 2952, 465] (valueOf P L g w d)

theorem arrSSegA (d : Control.D) :
    ∃ n, Seg kernel Assumptions.all L g n 1143
      ((113, .pred true) :: factsFrom arrSIn (valueOf P L g w d)) 1146
      (arrSLitA (P := P) (L := L) (g := g) (w := w) d) := by
  unfold arrSLitA
  seg_sym using w0_segS

theorem arrSSegTA (d : Control.D) :
    ∃ n, Seg kernel Assumptions.all L g n 253 (arrSLitA (P := P) (L := L) (g := g) (w := w) d) 256
      ((76, .pred (scmpi .gt .s w 1)) :: (972, w32 9) :: (973, w32 128) ::
        arrSLitA (P := P) (L := L) (g := g) (w := w) d) := by
  unfold arrSLitA
  seg_sym using w0_segS

/-- The head of the stretch when the block is the last (the counter is zero). -/
theorem arrSHeadA (d : Control.D) (h0 : scmpi .eq .b d.cnt 0 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 1123 (factsFrom arrSIn (valueOf P L g w d)) 1146
      (arrSLitA (P := P) (L := L) (g := g) (w := w) d) := by
  obtain ⟨n1, h1⟩ := arrSSeg0 (P := P) (L := L) (g := g) (w := w) d
  rw [h0] at h1
  have hb := Seg.bra (K := kernel) (A := Assumptions.all) (L := L) (g := g) (target := 1143)
    (p := 113) (uni := false) (pick := true) Flow.code_1124
    (F := (113, .pred true) :: factsFrom arrSIn (valueOf P L g w d)) (List.mem_cons_self ..)
    (fun t _ a ha => bra_rule t a ha)
    (PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 1124)
  obtain ⟨n2, h2⟩ := arrSSegA (P := P) (L := L) (g := g) (w := w) d
  exact ⟨_, h1.comp (hb.comp h2)⟩

theorem arrSCoreA (d : Control.D) (h0 : scmpi .eq .b d.cnt 0 = true)
    (h117 : scmpi .ne .b (addi d.cnt 1) 1 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 1123 (factsFrom arrSIn (valueOf P L g w d)) 256
      ((76, .pred (scmpi .gt .s w 1)) :: (972, w32 9) :: (973, w32 128) ::
        arrSLitA (P := P) (L := L) (g := g) (w := w) d) := by
  obtain ⟨n1, h1⟩ := arrSHeadA (P := P) (L := L) (g := g) (w := w) d h0
  have hb2 := Seg.bra (K := kernel) (A := Assumptions.all) (L := L) (g := g) (target := 253)
    (p := 117) (uni := false) (pick := true) Flow.code_1146
    (F := arrSLitA (P := P) (L := L) (g := g) (w := w) d)
    (by simp only [arrSLitA, h117]; simp) (fun t _ a ha => bra_rule t a ha)
    (PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 1146)
  obtain ⟨n3, h3⟩ := arrSSegTA (P := P) (L := L) (g := g) (w := w) d
  exact ⟨_, h1.comp (hb2.comp h3)⟩

/-- The exit: the stretch of the last block to the epilogue's masked moves (pc 1147). -/
theorem arrSCoreE (d : Control.D) (h0 : scmpi .eq .b d.cnt 0 = true)
    (h117 : scmpi .ne .b (addi d.cnt 1) 1 = false) :
    ∃ n, Seg kernel Assumptions.all L g n 1123 (factsFrom arrSIn (valueOf P L g w d)) 1147
      (arrSLitA (P := P) (L := L) (g := g) (w := w) d) := by
  obtain ⟨n1, h1⟩ := arrSHeadA (P := P) (L := L) (g := g) (w := w) d h0
  have hb2 := Seg.bra (K := kernel) (A := Assumptions.all) (L := L) (g := g) (target := 253)
    (p := 117) (uni := false) (pick := false) Flow.code_1146
    (F := arrSLitA (P := P) (L := L) (g := g) (w := w) d)
    (by simp only [arrSLitA, h117]; simp) (fun t _ a ha => bra_rule t a ha)
    (PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 1146)
  exact ⟨_, h1.comp hb2⟩

/-- The registers the stretch leaves alone, of the control table. -/
def arrSKeep : List Nat :=
  [459, 460, 463, 465, 469, 471, 472, 474, 475, 476, 988, 989, 990, 991, 992, 993, 994, 995, 996,
    2991, 2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3001]

/-- The positions of the stretch (the epilogue's masked moves included). -/
def arrSS : List Nat := [253, 254, 255] ++ List.range' 1123 31

theorem arrS_keep_eq (d d' : Control.D) : ∀ r ∈ arrSKeep,
    Control.valueOf P L g w d r = Control.valueOf P L g w d' r := by
  intro r hr
  simp only [arrSKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;>
  exact arrL_valueOf_off (by simp [Control.valuesLen]) (by simp [Control.valuesLoop])
    (by simp [Control.valuesLen]) (by simp [Control.valuesLoop])

/-- A window over the kept registers framed. -/
theorem arrS_frame {E : List (Nat × Value)} {pc : Nat} (d : Control.D)
    (h : ∃ n, Seg kernel Assumptions.all L g n 1123 (factsFrom arrSIn (valueOf P L g w d)) pc E) :
    ∃ n, Seg kernel Assumptions.all L g n 1123 (factsFrom (ctlLive 1123) (valueOf P L g w d)) pc
      (E ++ factsFrom arrSKeep (valueOf P L g w d)) := by
  obtain ⟨n, h⟩ := h
  have hf := Seg.frameSet (H := factsFrom arrSKeep (valueOf P L g w d)) rulesFrame (S := arrSS)
    (by rw [factsFrom_keys]; kernel_rfl)
    (fun _ _ => PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree _) (by kernel_rfl) h
  exact ⟨n, hf.weaken_start fun R hR =>
    (holds_append _ _ _).mpr ⟨holds_factsFrom_mono hR (by decide +kernel),
      holds_factsFrom_mono hR (by decide +kernel)⟩⟩

/-- Facts that hold register by register hold as a table. -/
theorem arrS_cover {R : Nat → Option Value} {F : List (Nat × Value)} {T : List Nat}
    {V : Nat → Value} (h : Holds R F) (hm : ∀ r ∈ T, ∃ v, (r, v) ∈ F ∧ v = V r) :
    Holds R (factsFrom T V) :=
  holds_of_pointwise fun r hr => by
    obtain ⟨v, hv, rfl⟩ := hm r hr
    exact holds_mem h hv

/-- **The stretch to the loop's head, with the rings' advance** on the control table. -/
theorem arrSWinB (d : Control.D) (h0 : scmpi .eq .b d.cnt 0 = false)
    (h117 : scmpi .ne .b (addi d.cnt 1) 1 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 1123
      (factsFrom (ctlLive 1123) (valueOf P L g w d)) 256
      (factsFrom (ctlLive 256) (valueOf P L g w { advance d with site := .bar0 })) := by
  obtain ⟨n, h⟩ := arrS_frame (P := P) (L := L) (g := g) (w := w) d
    (arrSCoreB (P := P) (L := L) (g := g) (w := w) d h0 h117)
  refine ⟨n, h.weaken_end fun R hR => ?_⟩
  have hs : ∀ r ∈ ctlLive 256, r ∉ arrSKeep →
      r ∈ [76, 451, 452, 972, 973, 2883, 2884, 2952, 2953] := by decide +kernel
  refine arrS_cover hR fun r hr => ?_
  by_cases hk : r ∈ arrSKeep
  · exact ⟨_, List.mem_append_right _ (mem_factsFrom hk), arrS_keep_eq d _ r hk⟩
  · have hr' := hs r hr hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    simp only [advance, h0, Bool.false_eq_true, ↓reduceIte]
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨.pred (scmpi .gt .s w 1), by simp, rfl⟩
    · exact ⟨.bits 16 (sel (pvc d.vs d.pv) (i16 1) (i16 0)), by simp [arrSLitB], rfl⟩
    · exact ⟨.bits 16 (sel (psc d.sl d.ps) (i16 1) (i16 0)), by simp [arrSLitB], rfl⟩
    · exact ⟨w32 9, by simp, rfl⟩
    · exact ⟨w32 128, by simp, rfl⟩
    · exact ⟨w32 (addi d.bi 1), by simp [arrSLitB], rfl⟩
    · exact ⟨w32 (addi d.cnt 1), by simp [arrSLitB], rfl⟩
    · exact ⟨w32 (nvs d.vs), by simp [arrSLitB], rfl⟩
    · exact ⟨w32 (andi (not32 d.sl) 1), by simp [arrSLitB], rfl⟩

/-- The counters' advance leaves the ring registers' values alone. -/
theorem arrS_ring_eq (d : Control.D) (s : Site) (c b : BitVec 64) :
    ∀ r ∈ [451, 452, 2952, 2953, 465],
      Control.valueOf P L g w { d with site := s, cnt := c, bi := b } r =
        Control.valueOf P L g w d r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [Control.valueOf, Control.values, List.append_assoc]
    rw [arrL_lookup_off (a := Control.valuesLen d) (by simp [Control.valuesLen]),
      arrL_lookup_off (a := Control.valuesLen { d with site := s, cnt := c, bi := b })
        (by simp [Control.valuesLen])]
    rfl

/-- **The stretch of the last block** (no ring advance), to the loop's head: the facts. -/
theorem arrSWinA (d : Control.D) (h0 : scmpi .eq .b d.cnt 0 = true)
    (h117 : scmpi .ne .b (addi d.cnt 1) 1 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 1123
      (factsFrom (ctlLive 1123) (valueOf P L g w d)) 256
      (factsFrom (ctlLive 256) (valueOf P L g w { advance d with site := .bar0 })) := by
  obtain ⟨n, h⟩ := arrS_frame (P := P) (L := L) (g := g) (w := w) d
    (arrSCoreA (P := P) (L := L) (g := g) (w := w) d h0 h117)
  refine ⟨n, h.weaken_end fun R hR => ?_⟩
  have hs : ∀ r ∈ ctlLive 256, r ∉ arrSKeep →
      r ∈ [76, 451, 452, 972, 973, 2883, 2884, 2952, 2953] := by decide +kernel
  refine arrS_cover hR fun r hr => ?_
  by_cases hk : r ∈ arrSKeep
  · exact ⟨_, List.mem_append_right _ (mem_factsFrom hk), arrS_keep_eq d _ r hk⟩
  · have hr' := hs r hr hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    simp only [advance, h0, ↓reduceIte]
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨.pred (scmpi .gt .s w 1), by simp, rfl⟩
    · exact ⟨valueOf P L g w d 451, by simp [arrSLitA, factsFrom],
        (arrS_ring_eq d _ _ _ 451 (by simp)).symm⟩
    · exact ⟨valueOf P L g w d 452, by simp [arrSLitA, factsFrom],
        (arrS_ring_eq d _ _ _ 452 (by simp)).symm⟩
    · exact ⟨w32 9, by simp, rfl⟩
    · exact ⟨w32 128, by simp, rfl⟩
    · exact ⟨w32 (addi d.bi 1), by simp [arrSLitA], rfl⟩
    · exact ⟨w32 (addi d.cnt 1), by simp [arrSLitA], rfl⟩
    · exact ⟨valueOf P L g w d 2952, by simp [arrSLitA, factsFrom],
        (arrS_ring_eq d _ _ _ 2952 (by simp)).symm⟩
    · exact ⟨valueOf P L g w d 2953, by simp [arrSLitA, factsFrom],
        (arrS_ring_eq d _ _ _ 2953 (by simp)).symm⟩

/-- **The stretch of the last block to the epilogue's masked moves** (pc 1147). -/
theorem arrSWinE (d : Control.D) (h0 : scmpi .eq .b d.cnt 0 = true)
    (h117 : scmpi .ne .b (addi d.cnt 1) 1 = false) :
    ∃ n, Seg kernel Assumptions.all L g n 1123
      (factsFrom (ctlLive 1123) (valueOf P L g w d)) 1147
      (factsFrom (ctlLive 1147) (valueOf P L g w { advance d with site := .ebar0 })) := by
  obtain ⟨n, h⟩ := arrS_frame (P := P) (L := L) (g := g) (w := w) d
    (arrSCoreE (P := P) (L := L) (g := g) (w := w) d h0 h117)
  refine ⟨n, h.weaken_end fun R hR => ?_⟩
  have hs : ∀ r ∈ ctlLive 1147, r ∉ arrSKeep → r ∈ [452, 2953] := by decide +kernel
  refine arrS_cover hR fun r hr => ?_
  by_cases hk : r ∈ arrSKeep
  · exact ⟨_, List.mem_append_right _ (mem_factsFrom hk), arrS_keep_eq d _ r hk⟩
  · have hr' := hs r hr hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    simp only [advance, h0, ↓reduceIte]
    rcases hr' with rfl | rfl
    · exact ⟨valueOf P L g w d 452, by simp [arrSLitA, factsFrom],
        (arrS_ring_eq d _ _ _ 452 (by simp)).symm⟩
    · exact ⟨valueOf P L g w d 2953, by simp [arrSLitA, factsFrom],
        (arrS_ring_eq d _ _ _ 2953 (by simp)).symm⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m : Mem0}

/-- The carried statistics after the block: its end values. -/
def arrNext (L : Launch) (b : Blk) : Blk :=
  { m := lookupD (wF (scX L) .arrS b) 2950, l := lookupD (wF (scX L) .arrS b) 2955,
    mx := lookupD (wF (scX L) .arrS b) 2885, sk := lookupD (wF (scX L) .arrS b) 2880 }

/-- **An event at the arrival** that continues at the next instruction, to the successor `c'`. -/
theorem skW_arr {d : D} {c' : Control.D} {ins0 : Instr} {pc pc' : Nat}
    (hs : d.c.site = .arrS) (hp : d.c.site.pc = pc) (hp' : c'.site.pc = pc')
    (hc : kernel.code[d.c.site.pc]? = some ins0)
    (hadv : ∀ {t e u}, Fires d.c.site.pc (eventTmpl Assumptions.all L g t ins0.op) e (some u) →
      u = PTX.next t)
    (hel1 : Control.elems d.c.site = 1) (hok : d.ok = true)
    (hsucc : ∀ e, Control.succ P L g w d.c e = some (some c'))
    (he1 : d.c.el = 0 → c'.el = 0)
    (hel : d.c.el = 0 → c'.el < Control.elems c'.site)
    (hseg : ∃ n, Seg kernel Assumptions.all L g n (pc + 1)
      (Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b) pc'
      (Control.facts P L g w c' ++ wF (scX L) c'.site (arrNext L d.b))) (e : Event) :
    (code P L g w).StepFor d e := by
  have hn : ∀ e, (code P L g w).next d e =
      some (some ⟨c', arrNext L d.b, d.hist ++ [d.b], true⟩) := by
    intro e
    show (Control.succ P L g w d.c e).map _ = _
    rw [hsucc e]
    show some (some (dataNext L d c' e)) = _
    simp only [dataNext, hs, hok, arrNext]
  refine fun {t u} ins hat hi hc' hf => ?_
  have he0 := el0_of_one hel1 hi
  refine (Code.step_issue (C := code P L g w)
    (dn := ⟨c', arrNext L d.b, d.hist ++ [d.b], true⟩) hc hadv (fun e => hn e) (by exact he0)
    (by simp [Control.D.acc, he0]) ?_).step ins hat hi hc' hf
  refine ⟨fun _ => ?_, he1 he0, by simp [Control.D.acc, he1 he0], fun _ => hel he0⟩
  show ∃ n, Seg _ _ _ _ _ (d.c.site.pc + 1) _ c'.site.pc _
  rw [hp, hp']
  have hf0 : (code P L g w).facts d =
      Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b := facts_ok hok
  have hf1 : (code P L g w).facts ⟨c', arrNext L d.b, d.hist ++ [d.b], true⟩ =
      Control.facts P L g w c' ++ wF (scX L) c'.site (arrNext L d.b) := facts_ok rfl
  rw [hf0, hf1]
  exact hseg

/-- The carried facts of the next block, from the block's end facts. -/
theorem arrS_carry {R : Nat → Option Value} {d : D}
    (h : Holds R (wF (scX L) .arrS d.b)) :
    Holds R (wF (scX L) .bar0 (arrNext L d.b)) :=
  holds_lookupD (live := [467, 3243, 2950, 2955, 2885, 2880]) h (by kernel_rfl)

/-- **The window of the arrival to the next block's head**, over the control table and the
carried facts. -/
theorem arrS_bar (d : D) (hs : d.c.site = .arrS)
    (h117 : scmpi .ne .b (addi d.c.cnt 1) 1 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 1123
      (Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b) 256
      (Control.facts P L g w { Control.advance d.c with site := .bar0 } ++
        wF (scX L) .bar0 (arrNext L d.b)) := by
  have hp : d.c.site.pc = 1122 := by rw [hs]; rfl
  obtain ⟨n, h⟩ : ∃ n, Seg kernel Assumptions.all L g n 1123
      (factsFrom (Control.ctlLive 1123) (Control.valueOf P L g w d.c)) 256
      (factsFrom (Control.ctlLive 256) (Control.valueOf P L g w
        { Control.advance d.c with site := .bar0 })) := by
    cases h0 : scmpi .eq .b d.c.cnt 0
    · exact arrSWinB d.c h0 h117
    · exact arrSWinA d.c h0 h117
  have hf := Seg.frameSet (H := wF (scX L) .bar0 (arrNext L d.b)) rulesFrame (S := arrSS)
    (by kernel_rfl) (fun _ _ => PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree _)
    (by kernel_rfl) h
  refine ⟨n, (hf.weaken_start fun R hR => ?_).weaken_end fun R hR => ?_⟩
  · obtain ⟨hc, hd⟩ := (holds_append _ _ _).mp hR
    rw [hs] at hd
    unfold Control.facts at hc
    rw [hp] at hc
    exact (holds_append _ _ _).mpr ⟨holds_factsFrom_mono hc (by decide +kernel),
      arrS_carry hd⟩
  · exact hR

theorem advance_el (c : Control.D) : (Control.advance c).el = c.el := by
  unfold Control.advance; split <;> rfl

/-- **The strict step at pc 1122**, when the block is not the last. -/
theorem sk_1122b (d : D) (hs : d.c.site = .arrS) (hok : d.ok = true)
    (h117 : scmpi .ne .b (Control.advance d.c).cnt 1 = true) (e : Event) :
    (code P L g w).StepFor d e := by
  have h117' : scmpi .ne .b (addi d.c.cnt 1) 1 = true := by
    have : (Control.advance d.c).cnt = addi d.c.cnt 1 := by
      unfold Control.advance; split <;> rfl
    rwa [this] at h117
  have key : ∀ e, (code P L g w).StepFor d e := by
    refine skW_arr (pc := 1122) (pc' := 256) (c' := { Control.advance d.c with site := .bar0 })
      hs (by rw [hs]; rfl) rfl (by rw [hs]; exact Flow.code_1122)
      (fun {t e u} hf => by rw [hs] at hf; exact Code.fires_arrive_next hf) (by rw [hs]; rfl) hok
      (fun e => by simp [Control.succ, hs, h117]) (fun h => by simpa [advance_el] using h)
      (fun h => by simp [advance_el, h, Control.elems]) ?_
    have := arrS_bar (P := P) (L := L) (g := g) (w := w) d hs h117'
    exact this
  exact fun {t u} => key e

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
