-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LoaderBase

@[expose] public section

/-! # The loader's block-table loads

The two loads of a block-table word (`ldb0`, `ldb1`): the instruction after each reads the loaded
value as bits (`mad.lo.s32`, `seg_madWord`), and a word without bits faults there. The other
sites of the loop body are proved by `site_cases` (`LoaderSteps`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-- `mad.lo.s32 dst, src, %r68, %r9` on a register `src` that holds a loaded block-table value
`v`, which the code reads as the 32-bit number `x`: one step, with `val` the result. -/
theorem seg_madWord {pc dst src a c x : Nat} {F G : List (Nat × Value)} {v val : Value}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.mad .lo, .int .s 32, false, [some dst],
      [.reg src, .reg 529, .reg 470]⟩⟩)
    (hsf : Assumption.SegFreePc asms pc) (hsrc : (src, v) ∈ F) (hw : Raw.word32Of v = some x)
    (ha : (529, b32 a) ∈ F) (hcc : (470, b32 c) ∈ F)
    (hval : Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 x) *
      truncBits 32 (BitVec.ofNat 64 a) + truncBits 32 (BitVec.ofNat 64 c))) = val)
    (hG : ∀ R, Holds R F → Holds (Function.update R dst (some val)) G) :
    Seg kernel asms L g 1 pc F (pc + 1) G := by
  refine Raw.seg_int1 hc rfl rfl hsf (fun t h => ?_) hG
  have hb := Raw.readBits_word32 (L := L) (g := g) (holds_mem h.2.2.2.2 hsrc) hw
  have h1 := holds_mem h.2.2.2.2 ha
  have h2 := holds_mem h.2.2.2.2 hcc
  have hb1 : readBits L g t 32 (.reg 529) = .ok (truncBits 32 (BitVec.ofNat 64 a)) := by
    simp [readBits, readReg, h1, b32]; rfl
  have hb2 : readBits L g t 32 (.reg 470) = .ok (truncBits 32 (BitVec.ofNat 64 c)) := by
    simp [readBits, readReg, h2, b32]; rfl
  simp only [execInt, hb, hb1, hb2, DType.width, bind, Except.bind, pure, Except.pure, ← hval]

theorem step_ldb0 (hs : d.site = .ldb0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
  simp only at hs
  subst hs
  obtain ⟨a, ha1, ha2, ha3, ha4, ha5⟩ : ∃ a : MemAccess, kernel.code[2382]? = some ⟨none, .mem a⟩ ∧
      a.kind = .load ∧ a.nc = false ∧ a.ext = .same ∧ a.regs = [581] :=
    ⟨_, Flow.code_2382, rfl, rfl, rfl, rfl⟩
  obtain rfl := Option.some.inj (hc.symm.trans ha1)
  obtain ⟨r, bs, rfl, rfl⟩ := fires_load ha2 ha3 hf ha4
  obtain ⟨P, vi, vn, hP⟩ := hi.proW
  simp only at hP
  subst hP
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inl (.inr ⟨by simp [next, hv], Machine.dead_of_fault (f := f) (by
      simp [afterLoad, hv])⟩)
  | ok v =>
    have hF := at_afterLoad (d := 581) h hv (facts_ne (by live_dec))
    rw [ha5]
    cases hw : Raw.word32Of v with
    | none =>
      refine .inl (.inr ⟨by simp [next, hv, hw], ?_⟩)
      refine Raw.dead_int1 Flow.code_2383 rfl rfl (Raw.asms_segFree (by decide +kernel))
        (fun t' h' => ?_) hF
      obtain ⟨f, hf⟩ := Raw.readBits_word32_none (L := L) (g := g)
        (holds_mem h'.2.2.2.2 List.mem_cons_self) hw
      exact ⟨f, by simp only [execInt, hf, DType.width]; rfl⟩
    | some x =>
      have hxl := Raw.word32Of_lt hw
      have hm : x % 4294967296 = x := Nat.mod_eq_of_lt hxl
      have hi' : Inv L g ⟨.ldb0, Pro.valW L g P vi vn, i, n, x, p1, ln⟩ :=
        Inv.data hi rfl rfl rfl rfl rfl
      have h1 : Seg kernel asms L g 1 2383 ((581, v) :: factsAt L g 2382
          ⟨.ldb0, Pro.valW L g P vi vn, i, n, p0, p1, ln⟩) 2384
          ((584, valueOf L g ⟨.wb1, Pro.valW L g P vi vn, i, n, x, p1, ln⟩ 584) ::
            (581, v) :: factsAt L g 2382 ⟨.ldb0, Pro.valW L g P vi vn, i, n, p0, p1, ln⟩) := by
        refine seg_madWord (a := P.w68) (c := natOf (Pro.valW L g P vi vn 530) * ctaY L g % 2 ^ 32)
          Flow.code_2383 (Raw.asms_segFree (by decide +kernel))
          List.mem_cons_self hw (List.mem_cons_of_mem _ (tbl_mem (by live_dec) (by lw_values)))
          (List.mem_cons_of_mem _ (tbl_mem (by live_dec) (by lw_values))) ?_
          (fun R hR => ⟨Function.update_self .., holds_update hR ?_⟩)
        · lw_values
          lw_close [hm]
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · simp
          · exact facts_ne (by live_dec) p hp
      refine step_of_seg (d' := ⟨.wb1, Pro.valW L g P vi vn, i, n, x, p1, ln⟩)
        (by simp [next, hv, hw]) (by inv_to hi') rfl rfl hF
        ⟨1 + 3, Seg.comp h1 (fun t h => by lw_seg h [hm])⟩

theorem step_ldb1 (hs : d.site = .ldb1) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
  simp only at hs
  subst hs
  obtain ⟨a, ha1, ha2, ha3, ha4, ha5⟩ : ∃ a : MemAccess, kernel.code[2399]? = some ⟨none, .mem a⟩ ∧
      a.kind = .load ∧ a.nc = false ∧ a.ext = .same ∧ a.regs = [591] :=
    ⟨_, Flow.code_2399, rfl, rfl, rfl, rfl⟩
  obtain rfl := Option.some.inj (hc.symm.trans ha1)
  obtain ⟨r, bs, rfl, rfl⟩ := fires_load ha2 ha3 hf ha4
  obtain ⟨P, vi, vn, hP⟩ := hi.proW
  simp only at hP
  subst hP
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inl (.inr ⟨by simp [next, hv], Machine.dead_of_fault (f := f) (by
      simp [afterLoad, hv])⟩)
  | ok v =>
    have hF := at_afterLoad (d := 591) h hv (facts_ne (by live_dec))
    rw [ha5]
    cases hw : Raw.word32Of v with
    | none =>
      refine .inl (.inr ⟨by simp [next, hv, hw], ?_⟩)
      refine Raw.dead_int1 Flow.code_2400 rfl rfl (Raw.asms_segFree (by decide +kernel))
        (fun t' h' => ?_) hF
      obtain ⟨f, hf⟩ := Raw.readBits_word32_none (L := L) (g := g)
        (holds_mem h'.2.2.2.2 List.mem_cons_self) hw
      exact ⟨f, by simp only [execInt, hf, DType.width]; rfl⟩
    | some x =>
      have hxl := Raw.word32Of_lt hw
      have hm : x % 4294967296 = x := Nat.mod_eq_of_lt hxl
      have hi' : Inv L g ⟨.ldb1, Pro.valW L g P vi vn, i, n, p0, x, ln⟩ :=
        Inv.data hi rfl rfl rfl rfl rfl
      have h1 : Seg kernel asms L g 1 2400 ((591, v) :: factsAt L g 2399
          ⟨.ldb1, Pro.valW L g P vi vn, i, n, p0, p1, ln⟩) 2401
          ((593, valueOf L g ⟨.wb3, Pro.valW L g P vi vn, i, n, p0, x, ln⟩ 593) ::
            (591, v) :: factsAt L g 2399 ⟨.ldb1, Pro.valW L g P vi vn, i, n, p0, p1, ln⟩) := by
        refine seg_madWord (a := P.w68) (c := natOf (Pro.valW L g P vi vn 530) * ctaY L g % 2 ^ 32)
          Flow.code_2400 (Raw.asms_segFree (by decide +kernel))
          List.mem_cons_self hw (List.mem_cons_of_mem _ (tbl_mem (by live_dec) (by lw_values)))
          (List.mem_cons_of_mem _ (tbl_mem (by live_dec) (by lw_values))) ?_
          (fun R hR => ⟨Function.update_self .., holds_update hR ?_⟩)
        · lw_values
          lw_close [hm]
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · simp
          · exact facts_ne (by live_dec) p hp
      refine step_of_seg (d' := ⟨.wb3, Pro.valW L g P vi vn, i, n, p0, x, ln⟩)
        (by simp [next, hv, hw]) (by inv_to hi') rfl rfl hF
        ⟨1 + 0, Seg.comp h1 (fun t h => by lw_seg h [hm])⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
