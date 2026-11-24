-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LoaderRaw

@[expose] public section

/-! # The loader's named barrier and the head of its iteration loop

The step of the named barrier after the vector load of `(num_pre, num_iters)` (each loaded value
is kept in its register as it is): the compare that skips the loop (a segment cut at its branch:
`p19 = num_pre >= num_iters`, signed, on the numbers the two words read as; a word without bits
faults there), then the slot computation of the loop's head (`seg_head`, also the end of
`loopEnd`) to the poll of the ring slot's `kv_empty` barrier. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-- **The slot computation at the loop's head** (pcs 2365 to 2373): the `mul.hi.s32` of the
counter word (the counter modulo `2 ^ 32`), then the slot's offsets and barriers, to the poll of
the iteration. -/
theorem seg_head (P : Pro) (vi vn : Value) (i n p0 p1 : Nat) (ln : Bool) {pc0 : Nat}
    (hw : Raw.word32Of vi = some (i % 2 ^ 32))
    (hl : ∀ r ∈ Flow.live 2366, r = 597 ∨ r ∈ Flow.live pc0)
    (hl0 : 1905 ∈ Flow.live pc0) (s : Site) :
    SegTo L g 2365 (factsAt L g pc0 ⟨s, Pro.valW L g P vi vn, i, n, p0, p1, ln⟩)
      ⟨.wait, Pro.valW L g P vi vn, i, n, p0, p1, ln⟩ := by
  have h1 : Seg kernel asms L g 1 2365
      (factsAt L g pc0 ⟨s, Pro.valW L g P vi vn, i, n, p0, p1, ln⟩) 2366
      (factsAt L g 2366 ⟨s, Pro.valW L g P vi vn, i, n, p0, p1, ln⟩) :=
    seg_mulhi (tbl_mem hl0 (by simp [valueOf, table, PTX.Flow.lookupLit, Pro.valW])) hw
      (fun R hR => Raw.holds_set_live hR (by
        simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]
        rw [mulHiW_mod]) hl)
  exact ⟨1 + 8, Seg.comp h1 (fun t h => by lw_seg h)⟩

theorem step_bar0 (hs : d.site = .bar0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_28)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSync _ _) from trivial) hf
  obtain ⟨P, vi, vn, hP⟩ := hi.proW
  simp only at hP
  subst hP
  have hln : ln = decide (laneOf L g = 0) := hi.ln
  have hwi : (Raw.word32Of vi).getD 0 = i := by
    simpa [wordI, Pro.valW] using hi.wi (.inr rfl)
  have hwn : (Raw.word32Of vn).getD 0 = n := by simpa [wordN, Pro.valW] using hi.wn rfl
  have hm1905 : (1905, vi) ∈ factsAt L g 2346 ⟨.bar0, Pro.valW L g P vi vn, i, n, p0, p1, ln⟩ :=
    tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit, Pro.valW])
  have hm467 : (467, vn) ∈ factsAt L g 2346 ⟨.bar0, Pro.valW L g P vi vn, i, n, p0, p1, ln⟩ :=
    tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit, Pro.valW])
  have hu := At.next h
  cases hvi : Raw.word32Of vi with
  | none =>
    refine .inl (.inr ⟨by simp [next, wordI, Pro.valW, hvi], ?_⟩)
    refine Raw.dead_int1 Flow.code_2347 rfl rfl (Raw.asms_segFree (by decide +kernel))
      (fun t' h' => ?_) hu
    obtain ⟨f, hf⟩ := Raw.readBits_word32_none (L := L) (g := g)
      (holds_mem h'.2.2.2.2 hm1905) hvi
    exact ⟨f, by simp only [execInt, hf, DType.width]; rfl⟩
  | some x =>
    cases hvn : Raw.word32Of vn with
    | none =>
      refine .inl (.inr ⟨by simp [next, wordI, wordN, Pro.valW, hvi, hvn], ?_⟩)
      refine Raw.dead_int1 Flow.code_2347 rfl rfl (Raw.asms_segFree (by decide +kernel))
        (fun t' h' => ?_) hu
      obtain ⟨f, hf⟩ := Raw.readBits_word32_none (L := L) (g := g)
        (holds_mem h'.2.2.2.2 hm467) hvn
      exact ⟨f, by simp only [execInt, rd_word h' hm1905 hvi, hf, DType.width, bind,
        Except.bind]⟩
    | some y =>
      simp only [hvi, hvn, Option.getD_some] at hwi hwn
      subst hwi hwn
      have hA : Seg kernel asms L g 1 2347
          (factsAt L g 2346 ⟨.bar0, Pro.valW L g P vi vn, x, y, p0, p1, ln⟩) 2348
          (factsAt L g 2348 ⟨.bar0, Pro.valW L g P vi vn, x, y, p0, p1, ln⟩) :=
        seg_p19 hm1905 hm467 hvi hvn (fun R hR => Raw.holds_set_live hR
          (by simp [valueOf, table]) (by live_dec))
      have hB1 : Seg kernel asms L g 11 2349
          (factsAt L g 2348 ⟨.bar0, Pro.valW L g P vi vn, x, y, p0, p1, ln⟩) 2360
          (factsAt L g 2360 ⟨.bar0, Pro.valW L g P vi vn, x, y, p0, p1, ln⟩) :=
        fun t h => by lw_seg h
      have hB2 : Seg kernel asms L g 1 2360
          (factsAt L g 2360 ⟨.bar0, Pro.valW L g P vi vn, x, y, p0, p1, ln⟩) 2361
          (factsAt L g 2361 ⟨.bar0, Pro.valW L g P vi vn, x, y, p0, p1, ln⟩) :=
        seg_shl (s := 3) Flow.code_2360 (by norm_num) (Raw.asms_segFree (by decide +kernel))
          (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit, Pro.valW])) hvi
          (fun R hR => Raw.holds_set_live hR
            (by simp [valueOf, table, PTX.Flow.lookupLit]) (by live_dec))
      have hB3 : Seg kernel asms L g 1 2361
          (factsAt L g 2361 ⟨.bar0, Pro.valW L g P vi vn, x, y, p0, p1, ln⟩) 2362
          (factsAt L g 2362 ⟨.bar0, Pro.valW L g P vi vn, x, y, p0, p1, ln⟩) :=
        seg_shl (s := 15) Flow.code_2361 (by norm_num) (Raw.asms_segFree (by decide +kernel))
          (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit, Pro.valW])) hvi
          (fun R hR => Raw.holds_set_live hR
            (by simp [valueOf, table, PTX.Flow.lookupLit]) (by live_dec))
      have hB4 : Seg kernel asms L g 1 2362
          (factsAt L g 2362 ⟨.bar0, Pro.valW L g P vi vn, x, y, p0, p1, ln⟩) 2363
          (factsAt L g 2363 ⟨.bar0, Pro.valW L g P vi vn, x, y, p0, p1, ln⟩) :=
        seg_mad577 (w := P.w71) (x := ctaX L g)
          (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit, Pro.valW,
            Pro.val, Pro.table]))
          (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit, Pro.valW]))
          (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit])) hvi
          (fun R hR => Raw.holds_set_live hR
            (by
              have hxm4 : x % 4294967296 = x := by have := Raw.word32Of_lt hvi; omega
              simp [valueOf, table, PTX.Flow.lookupLit, Pro.valW, Pro.val, Pro.table,
                natOf_b32, hxm4]) (by live_dec))
      have hB5 : Seg kernel asms L g 2 2363
          (factsAt L g 2363 ⟨.bar0, Pro.valW L g P vi vn, x, y, p0, p1, ln⟩) 2365
          (factsAt L g 2365 ⟨.bar0, Pro.valW L g P vi vn, x, y, p0, p1, ln⟩) :=
        fun t h => by lw_seg h [hln]
      obtain ⟨k5, hB6⟩ := seg_head (L := L) (g := g) P vi vn x y p0 p1 ln (pc0 := 2365)
        (by rw [hvi, Nat.mod_eq_of_lt (Raw.word32Of_lt hvi)]) (by live_dec) (by live_dec) .bar0
      have hmem : (19, Value.pred (decide (sxI y ≤ sxI x))) ∈
          factsAt L g 2348 ⟨.bar0, Pro.valW L g P vi vn, x, y, p0, p1, ln⟩ :=
        tbl_mem (by live_dec) (by simp [valueOf, table])
      obtain ⟨k, hB⟩ := segTo_bra (L := L) (g := g) (pc := 2348) (p := 19)
        (c := decide (sxI y ≤ sxI x))
        (d1 := ⟨.bar1, Pro.valW L g P vi vn, x, y, p0, p1, ln⟩)
        (d2 := ⟨.wait, Pro.valW L g P vi vn, x, y, p0, p1, ln⟩)
        Flow.code_2348 hmem (fun _ => segTo_here rfl rfl (by live_dec))
        (fun _ => ⟨11 + (1 + (1 + (1 + (2 + k5)))), Seg.comp hB1 (Seg.comp hB2 (Seg.comp hB3
          (Seg.comp hB4 (Seg.comp hB5 hB6))))⟩)
      have hxl := Raw.word32Of_lt hvi
      have hyl := Raw.word32Of_lt hvn
      by_cases hni : sxI y ≤ sxI x
      · simp only [hni, decide_true, ↓reduceIte] at hB
        exact step_of_seg (d' := ⟨.bar1, Pro.valW L g P vi vn, x, y, p0, p1, ln⟩)
          (by simp [next, wordI, wordN, Pro.valW, hvi, hvn, hni]) (by inv_to hi) rfl rfl hu
          ⟨1 + k, Seg.comp hA hB⟩
      · simp only [hni, decide_false, Bool.false_eq_true, ↓reduceIte] at hB
        have hxy : x ≠ y := by
          intro hxy
          subst hxy
          exact hni le_rfl
        refine step_of_seg (d' := ⟨.wait, Pro.valW L g P vi vn, x, y, p0, p1, ln⟩)
          (by simp [next, wordI, wordN, Pro.valW, hvi, hvn, hni]) ?_ rfl rfl hu
          ⟨1 + k, Seg.comp hA hB⟩
        have hxm : x % 2 ^ 32 = x := Nat.mod_eq_of_lt hxl
        have hxm4 : x % 4294967296 = x := by omega
        refine Inv.move hi .wait (fun h => by rcases h with h | h <;> cases h)
          (fun _ => by simp [wordN, Pro.valW, hvn])
          (fun _ => ⟨by simp [wordI, Pro.valW, hvi, hxm4], by simp [wordN, Pro.valW, hvn]⟩)
          (fun _ => ⟨by simp only; rw [hxm]; exact hxy, by simp only; omega⟩)
          (fun h => by cases h)

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
