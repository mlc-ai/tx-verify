-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0
import Kernels.FlashMlaSparseDecodeH64.Audit.DeadPack
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputNumeric
import Lemmas.Flow.EventCont
import Lemmas.Flow.Join
import Lemmas.Flow.FmaRun

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}

private def rescaleStoreSrcs (j : Fin 4) : List Opnd := (rescaleStoreRegs j).map Opnd.reg

private theorem rescaleLoad_code (j : Fin 4) :
    kernel.code[(Site.rescaleLoad j).pc]? =
      some ⟨none, .tcLd (rescaleLoadRegs j) (rescaleAddressReg j) .s32x32b none⟩ := by
  fin_cases j <;>
    first | exact Flow.code_716 | exact Flow.code_817 | exact Flow.code_918 | exact Flow.code_1019

private theorem rescaleWait_code (j : Fin 4) :
    kernel.code[(Site.rescaleWait j).pc]? = some ⟨none, .tcWaitLd⟩ := by
  fin_cases j <;> kernel_rfl

private theorem rescaleStore_code (j : Fin 4) :
    kernel.code[(Site.rescaleStore j).pc]? =
      some ⟨none, .tcSt (rescaleAddressReg j) (rescaleStoreSrcs j) .s32x32b⟩ := by
  fin_cases j <;>
    first | exact Flow.code_814 | exact Flow.code_915 | exact Flow.code_1016 | exact Flow.code_1117

private theorem rescaleWaitSt_code (j : Fin 4) :
    kernel.code[(Site.rescaleWaitSt j).pc]? = some ⟨none, .tcWaitSt⟩ := by
  fin_cases j <;> kernel_rfl

private theorem rescale_sub_zero {d : D} (hi : Inv P L g d) (hs : d.site.inRescale = true) :
    d.sub = 0 := by
  have h := hi.subLt
  have he : d.site.elems = 1 := by
    cases hcase : d.site <;> simp [hcase, Site.inRescale, Site.elems] at hs ⊢
  omega

private theorem rescale_load_template (hpre : Pre P L mem0) {j : Fin 4} {t : TState}
    (hr : t.regs (rescaleAddressReg j) = some (b32 (64 * j.val))) :
    eventTmpl asms L g t (.tcLd (rescaleLoadRegs j) (rescaleAddressReg j) .s32x32b none) =
      .tcLd (64 * j.val) 64 .s32x32b (fun vs => setRegs (PTX.next t) (rescaleLoadRegs j) vs) := by
  have hj := j.isLt
  have hreg := readBits_b32 (L := L) (g := g) hr (by omega)
  have hbound : 64 * j.val < 2 ^ 64 := by omega
  have hnat : (BitVec.ofNat 64 (64 * j.val)).toNat = 64 * j.val := toNat_ofNat_lt hbound
  have hsize : TcShape.s32x32b.countOk 64 = true := rfl
  have haddr : tcDataAddressOk L g .s32x32b (64 * j.val) = true := by
    have hh : 64 * j.val / 2 ^ 16 = 0 := by omega
    simp only [tcDataAddressOk, hh]
    rfl
  have hplain : ∀ s, TcShape.s32x32b ≠ .packed16 s := by intro s hs; cases hs
  have hwait : asms.any (·.tcLdWait t.pc) = false := rfl
  simp only [eventTmpl, tcLdTmpl, hwait, ↓reduceIte, tcTmpl_tcLd_none hplain, hpre.block,
    hsize, hreg, hnat, haddr, bind, Except.bind, pure, Except.pure,
    Bool.false_eq_true, ofExec, Nat.reduceMod, rescaleLoadRegs, List.length_range']

/-- A rescale store is followed by the actual Tensor Memory completion wait. -/
theorem fires_rescaleWaitSt {d : D} {j : Fin 4} {t u : TState} {e : Event} {ins : Instr}
    (hd : d.site = .rescaleWaitSt j) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    e.kind = .tc .waitSt ∧ u = PTX.next t := by
  rw [hd] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans (rescaleWaitSt_code j))
  obtain ⟨hu, he⟩ := fires_tcWaitSt hf
  exact ⟨congrArg Event.kind he, hu⟩

/-- The pack, multiply and unpack for input pair `i` of rescale chunk `j`. -/
private def rescalePairPc (j : Fin 4) (i : Nat) : Nat := 718 + 101 * j.val + 3 * i

private def rescalePackReg (j : Fin 4) (i : Nat) : Nat :=
  if j.val = 0 ∧ i < 2 then 3309 + 2 * i else 3310 + 64 * j.val + 2 * i

private def rescaleInputReg (j : Fin 4) (i : Nat) : Nat := 1199 + 129 * j.val + i

private def rescaleOutputReg (j : Fin 4) (i : Nat) : Nat := 1264 + 129 * j.val + i

private def rescale_pack_op (j : Fin 4) (i : Nat) : Op :=
  .move ⟨.pack, .int .b 64, [some (rescalePackReg j i)],
    [.reg (rescaleInputReg j (2 * i)), .reg (rescaleInputReg j (2 * i + 1))]⟩

private def rescale_mul_op (j : Fin 4) (i : Nat) : Op :=
  .float {
    op := .mul, ty := ⟨.f32, 2⟩, dsts := [some (rescalePackReg j i - 1)],
    srcs := [.reg (rescalePackReg j i), .reg 3312] }

private def rescale_unpack_op (j : Fin 4) (i : Nat) : Op :=
  .move ⟨.unpack, .int .b 64,
    [some (rescaleOutputReg j (2 * i)), some (rescaleOutputReg j (2 * i + 1))],
    [.reg (rescalePackReg j i - 1)]⟩

private theorem rescalePack_code (j : Fin 4) (i : Fin 32) :
    kernel.code[rescalePairPc j i.val]? = some ⟨none, rescale_pack_op j i.val⟩ := by
  fin_cases j <;> fin_cases i <;> output_code

private theorem rescaleMul_code (j : Fin 4) (i : Fin 32) :
    kernel.code[rescalePairPc j i.val + 1]? = some ⟨none, rescale_mul_op j i.val⟩ := by
  fin_cases j <;> fin_cases i <;> output_code

private theorem rescaleUnpack_code (j : Fin 4) (i : Fin 32) :
    kernel.code[rescalePairPc j i.val + 2]? = some ⟨none, rescale_unpack_op j i.val⟩ := by
  fin_cases j <;> fin_cases i <;> output_code

private theorem rescalePack_ne_gain (j : Fin 4) (i : Fin 32) : 3312 ≠ rescalePackReg j i.val := by
  fin_cases j <;> simp [rescalePackReg] <;> (try split_ifs) <;> omega

private theorem rescalePair_finite (j : Fin 4) (i : Fin 32) {F : List (Nat × Value)} {t : TState}
    {lo hi gainWord : Value} {x y gain : ℝ}
    (hat : At t (rescalePairPc j i.val) F)
    (hlo : t.regs (rescaleInputReg j (2 * i.val)) = some lo)
    (hhi : t.regs (rescaleInputReg j (2 * i.val + 1)) = some hi)
    (hg : t.regs 3312 = some (joinValue gainWord gainWord))
    (hlShape : Assumptions.scoreHalf lo) (hhShape : Assumptions.scoreHalf hi)
    (hgShape : Assumptions.scoreHalf gainWord)
    (hx : valFloat .f32 lo = .ok x) (hy : valFloat .f32 hi = .ok y)
    (hr : valFloat .f32 gainWord = .ok gain)
    (hpack : ∀ q ∈ F, q.1 ≠ rescalePackReg j i.val)
    (hmul : ∀ q ∈ F, q.1 ≠ rescalePackReg j i.val - 1)
    (hlOut : ∀ q ∈ F, q.1 ≠ rescaleOutputReg j (2 * i.val))
    (hhOut : ∀ q ∈ F, q.1 ≠ rescaleOutputReg j (2 * i.val + 1)) :
    ∃ u, run kernel asms L g 3 t = some u ∧ At u (rescalePairPc j (i.val + 1))
      ((rescaleOutputReg j (2 * i.val + 1), fl (y * gain)) ::
        (rescaleOutputReg j (2 * i.val), fl (x * gain)) :: F) := by
  let pack := rescalePackReg j i.val
  let mul := pack - 1
  let outLo := rescaleOutputReg j (2 * i.val)
  let outHi := rescaleOutputReg j (2 * i.val + 1)
  let t₁ := PTX.next (setReg t pack (joinValue lo hi))
  have hr₁ : run kernel asms L g 1 t = some t₁ := by
    apply run_local (rescalePack_code j i) rfl hat
    have hpc : 713 ≤ t.pc := by rw [hat.1, rescalePairPc]; omega
    exact exec_outputPack hpc hlo hhi (Assumptions.scoreHalf_bytes hlShape)
      (Assumptions.scoreHalf_bytes hhShape)
  have hat₁ : At t₁ (rescalePairPc j i.val + 1) F := at_set_keep hat hpack
  have hp : t₁.regs pack = some (joinValue lo hi) := Function.update_self ..
  have hgg : t₁.regs 3312 = some (joinValue gainWord gainWord) := by
    change Function.update t.regs pack (some (joinValue lo hi)) 3312 = _
    rw [Function.update_of_ne (rescalePack_ne_gain j i), hg]
  let v := Value.pair (fl (x * gain)) (fl (y * gain))
  let t₂ := PTX.next (setReg t₁ mul v)
  have hr₂ : run kernel asms L g 1 t₁ = some t₂ := by
    apply run_local (rescaleMul_code j i) rfl hat₁
    have hs := split_join_words hlShape hhShape
    have ht := split_join_words hgShape hgShape
    exact exec_fmul2 outputMul_ideal.at hp hgg (hs ▸ hx) (hs ▸ hy) (ht ▸ hr) (ht ▸ hr)
  have hat₂ : At t₂ (rescalePairPc j i.val + 2) F := at_set_keep hat₁ hmul
  let t₃ := PTX.next (setReg (setReg t₂ outLo (fl (x * gain))) outHi (fl (y * gain)))
  have hr₃ : run kernel asms L g 1 t₂ = some t₃ := by
    apply run_local (rescaleUnpack_code j i) rfl hat₂
    have hsf : Assumption.SegFreePc asms t₂.pc :=
      fun a ha l ix state _ => asms_segment_free (L := l) (g := ix) state a ha
    exact exec_unpack64 (Function.update_self ..) rfl rfl hsf outputNoUnpack
  have hLoNe : outLo ≠ outHi := by dsimp [outLo, outHi, rescaleOutputReg]; omega
  have hmem : Holds t₃.regs F := holds_update (holds_update hat₂.2.2.2.2 hlOut) hhOut
  have hLo : t₃.regs outLo = some (fl (x * gain)) := by
    change Function.update (Function.update t₂.regs outLo (some (fl (x * gain))))
      outHi (some (fl (y * gain))) outLo = _
    rw [Function.update_of_ne hLoNe, Function.update_self]
  refine ⟨t₃, run_comp (run_comp hr₁ hr₂) hr₃, ?_, hat₂.2.1, hat₂.2.2.1,
    hat₂.2.2.2.1, Function.update_self .., hLo, hmem⟩
  change t₂.pc + 1 = rescalePairPc j (i.val + 1)
  rw [hat₂.1, rescalePairPc, rescalePairPc]
  omega

private def rescaleLive (s : Site) : List Nat := (Flow.live s.pc).filter tracked.contains

private theorem rescale_inv {d : D} (h : Inv P L g d) (hin : d.site.inRescale = true)
    {s : Site} (hs : s.inRescale = true) :
    Inv P L g {d with site := s, sub := 0} := by
  refine inv_setSite h s ?_ (fun _ => h.rescaleArm hin) ?_ ?_ ?_ ?_ ?_
  · cases s <;> simp_all [Site.inEpilogue, Site.inRescale]
  · cases s <;> simp_all [Site.inRescale]
  · cases s <;> simp_all [Site.inRescale]
  · cases s <;> simp_all [Site.inRescale]
  · cases s <;> simp_all [Site.inRescale, Site.needsRowTotal]
  · cases s <;> simp_all [Site.inRescale, Site.needsExchangeReady]

private theorem rescale_address_value (d : D) (j : Fin 4) :
    valueOf P L g d (rescaleAddressReg j) = b32 (64 * j.val) := by
  fin_cases j <;> rfl

private theorem rescale_input_value (d : D) (j : Fin 4) (i : Fin 64) :
    valueOf P L g d (rescaleInputReg j i.val) = d.rescaleWords.getD i.val (b32 0) := by
  fin_cases j <;> fin_cases i <;> rfl

private theorem rescale_output_value (d : D) (j : Fin 4) (i : Fin 64) :
    valueOf P L g d (rescaleOutputReg j i.val) = rescaleValue d i.val := by
  fin_cases j <;> fin_cases i <;> rfl

private theorem rescale_input_mem (j : Fin 4) (i : Fin 64) :
    rescaleInputReg j i.val ∈ rescaleLoadRegs j := by
  simp [rescaleInputReg, rescaleLoadRegs, List.mem_range']

private theorem rescale_reads_after_load (j : Fin 4) :
    ∀ r ∈ rescaleLive (.rescaleWait j), r ∈ rescaleLoadRegs j ∨
      (r ∈ rescaleLive (.rescaleLoad j) ∧ (r < 1199 ∨ 1714 < r ∨ r = rescaleAddressReg j)) := by
  fin_cases j <;> decide +kernel

/-- The rescale input uses a defined 64-word Tensor Memory read template. -/
theorem rescaleLoad_template (hpre : Pre P L mem0) {d : D} {j : Fin 4}
    {t : TState} {ins : Instr}
    (hd : d.site = .rescaleLoad j) (ha : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins) :
    eventTmpl asms L g t ins.op =
      .tcLd (64 * j.val) 64 .s32x32b (fun vs => setRegs (PTX.next t) (rescaleLoadRegs j) vs) := by
  have hr : t.regs (rescaleAddressReg j) = some (b32 (64 * j.val)) := by
    rw [← rescale_address_value (P := P) (L := L) (g := g) d j]
    exact reg_value ha (by rw [hd]; fin_cases j <;> decide +kernel)
  rw [hd] at hc
  obtain rfl := Option.some.inj (hc.symm.trans (rescaleLoad_code j))
  exact rescale_load_template (g := g) hpre hr

/-- The TC load reads the 64 words of its chunk at the same column for every lane. -/
theorem fires_rescaleLoad (hpre : Pre P L mem0) {d : D} {j : Fin 4}
    {t u : TState} {e : Event} {ins : Instr}
    (hd : d.site = .rescaleLoad j) (ha : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ vs, vs.length = 64 ∧ e.kind = .tc (.ld (64 * j.val) vs .s32x32b) ∧
      u = setRegs (PTX.next t) (rescaleLoadRegs j) vs := by
  rw [rescaleLoad_template hpre hd ha hc] at hf
  obtain ⟨values, hlength, he, hu⟩ := hf
  exact ⟨values, hlength, congrArg Event.kind he, Option.some.inj hu⟩

private theorem store_rescaleLoad_regs (d : D) (j : Fin 4) (words : List Value)
    (hw : words.length = 64)
    {t : TState} (hd : d.site = .rescaleLoad j) (ha : (code P L g).AtD d t) :
    Holds (setRegs (PTX.next t) (rescaleLoadRegs j) words).regs
      (facts P L g {d with site := .rescaleWait j, rescaleWords := words}) := by
  change Holds _ (factsFrom (rescaleLive (.rescaleWait j))
    (valueOf P L g {d with site := .rescaleWait j, rescaleWords := words}))
  refine holds_of_pointwise fun r hr => ?_
  rcases rescale_reads_after_load j r hr with hdst | ⟨hframe, hscope⟩
  · have hloc := (List.mem_range'.mp hdst : ∃ ix < 64, r = 1199 + 129 * j.val + 1 * ix)
    obtain ⟨ix, hix, hreg⟩ := hloc
    have he : r = rescaleInputReg j ix := by simp [rescaleInputReg, hreg]
    rw [he, rescale_input_value _ j ⟨ix, hix⟩]
    have hw' : ix < words.length := by omega
    exact setRegs_get _ _ _ ix _ _ List.nodup_range'
      (by simp [rescaleLoadRegs, rescaleInputReg, hix])
      (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw'])
  · have hn : r ∉ rescaleLoadRegs j := by
      rw [rescaleLoadRegs, List.mem_range']
      rintro ⟨ix, hix, rfl⟩
      rcases hscope with h | h | h <;> simp [rescaleAddressReg] at h <;>
        have hj := j.isLt <;> omega
    rw [setRegs_other _ _ _ _ hn]
    have hbefore : Holds t.regs (factsFrom (rescaleLive (.rescaleLoad j)) (valueOf P L g d)) := by
      simpa only [code, facts, hd, rescaleLive] using ha.2.2.2.2
    change t.regs r = _
    rw [holds_mem hbefore (mem_factsFrom hframe)]
    congr 1
    rcases hscope with hl | hh | he
    · simp only [valueOf, show ¬ (1199 ≤ r ∧ r ≤ 1714) by omega, ite_false]
      rfl
    · simp only [valueOf, show ¬ (1199 ≤ r ∧ r ≤ 1714) by omega, ite_false]
      rfl
    · rw [he, rescale_address_value, rescale_address_value]

/-- The TC load records its concrete input tile before the wait. -/
theorem step_rescaleLoad (hpre : Pre P L mem0) (d : D) (j : Fin 4) (hd : d.site = .rescaleLoad j) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins ha hi hc hf => by
    obtain ⟨words, hlen, he, rfl⟩ := fires_rescaleLoad hpre hd ha hc hf
    let d' : D := {d with site := .rescaleWait j, rescaleWords := words}
    have hn : next P L g d e = some (some d') := by simp [next, nextSite, hd, he, d']
    have hsub := rescale_sub_zero hi (by rw [hd]; rfl)
    have hpc : d.site.pc = 716 + 101 * j.val := by rw [hd]; rfl
    have hat := at_next_of ha hpc hsub
    have hs := setRegs_skel (PTX.next t) (rescaleLoadRegs j) words
    refine Or.inl (Or.inr ⟨d', _, hn, .refl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    · refine hs.1.trans (hat.1.trans ?_)
      change 716 + 101 * j.val + 1 = 717 + 101 * j.val
      omega
    · exact hs.2.1.trans (hat.2.1.trans hsub.symm)
    · exact hs.2.2.1.trans hat.2.2.1
    · exact hs.2.2.2.trans hat.2.2.2.1
    · exact store_rescaleLoad_regs d j words hlen hd ha
    · have hi' : Inv P L g {d with rescaleWords := words} := {hi with blockLt := hi.blockLt}
      have hr := rescale_inv hi' (by change d.site.inRescale = true; rw [hd]; rfl)
        (s := .rescaleWait j) rfl
      simpa [code, d', hsub] using hr

private def rescaleAfterWaitSt (j : Fin 4) : Site :=
  if h : j.val + 1 < 4 then .rescaleLoad ⟨j.val + 1, h⟩ else .rescaleFenceB

private theorem rescale_afterWaitSt_isRescale (j : Fin 4) :
    (rescaleAfterWaitSt j).inRescale = true := by
  unfold rescaleAfterWaitSt
  split <;> rfl

private theorem run_rescale_waitSt (d : D) (j : Fin 4) {t : TState}
    (ha : At t ((Site.rescaleWaitSt j).pc + 1)
      (factsFrom (rescaleLive (.rescaleWaitSt j)) (valueOf P L g d))) :
    ∃ u, run kernel asms L g (if j.val + 1 < 4 then 1 else 0) t = some u ∧
      At u (rescaleAfterWaitSt j).pc
        (factsFrom (rescaleLive (rescaleAfterWaitSt j)) (valueOf P L g d)) := by
  simp only [rescaleLive] at ha ⊢
  fin_cases j
  · seg_fp ha using rfl
  · seg_fp ha using rfl
  · seg_fp ha using rfl
  · exact ⟨t, rfl, ha.mono (holds_factsFrom_mono ha.2.2.2.2 (by decide +kernel))⟩

/-- Wait for a rescale store, then form the next tile address or enter the final fence. -/
theorem step_rescaleWaitSt (d : D) (j : Fin 4) (hd : d.site = .rescaleWaitSt j) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins ha hi hc hf => by
    obtain ⟨he, rfl⟩ := fires_rescaleWaitSt hd hc hf
    have hin : d.site.inRescale = true := by rw [hd]; rfl
    have hsub := rescale_sub_zero hi hin
    have hsite : d.site.pc = (Site.rescaleWaitSt j).pc := by rw [hd]
    have hat := at_next_of ha hsite hsub
    obtain ⟨v, hr, hv⟩ := run_rescale_waitSt d j hat
    let d' : D := {d with site := rescaleAfterWaitSt j, sub := 0}
    have hn : next P L g d e = some (some d') := by
      simp [next, nextSite, hd, he, d', rescaleAfterWaitSt, hsub]
    refine Or.inl (Or.inr ⟨d', v, hn, run_rtg hr,
      ⟨hv.1, hv.2.1, ?_, hv.2.2.2.1, ?_⟩, ?_⟩)
    · exact hv.2.2.1.trans (siteAcc_nil d' rfl).symm
    · exact hv.2.2.2.2
    · exact rescale_inv hi hin (rescale_afterWaitSt_isRescale j)

def rescaleStoreValues (d : D) : List Value := (List.range 64).map (rescaleValue d)

private theorem rescale_reads_store (d : D) (j : Fin 4) {t : TState}
    (h : ∀ i < 64, t.regs (rescaleOutputReg j i) = some (rescaleValue d i)) :
    (rescaleStoreSrcs j).mapM (readValue L g t 32) = .ok (rescaleStoreValues d) := by
  have hs : rescaleStoreSrcs j = (List.range 64).map (fun i => .reg (rescaleOutputReg j i)) := by
    rw [rescaleStoreSrcs, rescaleStoreRegs, List.range'_eq_map_range, List.map_map]
    rfl
  rw [hs, rescaleStoreValues]
  generalize hl : List.range 64 = is
  have hw : ∀ i ∈ is, t.regs (rescaleOutputReg j i) = some (rescaleValue d i) := by
    intro i hi
    rw [← hl] at hi
    exact h i (List.mem_range.mp hi)
  clear h hl
  induction is with
  | nil => rfl
  | cons i is ih =>
    have hi := hw i (List.mem_cons_self)
    have hs := ih (fun r hr => hw r (List.mem_cons_of_mem _ hr))
    simp [List.mapM_cons, hi, hs, readValue, readReg, pure, Except.pure, bind, Except.bind]

/-- The converted rescale registers give a defined Tensor Memory store template. -/
theorem rescaleStore_template (hpre : Pre P L mem0) {d : D} {j : Fin 4}
    {t : TState} {ins : Instr}
    (hd : d.site = .rescaleStore j) (ha : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins) :
    eventTmpl asms L g t ins.op =
      .tc (.st (64 * j.val) (rescaleStoreValues d) .s32x32b) (PTX.next t) := by
  have hreg : t.regs (rescaleAddressReg j) = some (b32 (64 * j.val)) := by
    rw [← rescale_address_value (P := P) (L := L) (g := g) d j]
    exact reg_value ha (by rw [hd]; fin_cases j <;> decide +kernel)
  have hvals : ∀ i < 64, t.regs (rescaleOutputReg j i) = some (rescaleValue d i) := by
    intro i hi
    let ix : Fin 64 := ⟨i, hi⟩
    rw [← rescale_output_value (P := P) (L := L) (g := g) d j ix]
    exact reg_value ha (by
      rw [hd]
      change rescaleOutputReg j i ∈ rescaleLive (.rescaleStore j)
      have hsub : rescaleStoreRegs j ⊆ rescaleLive (.rescaleStore j) := by
        fin_cases j <;> decide +kernel
      exact hsub (List.mem_range'.mpr ⟨i, hi, by simp [rescaleOutputReg]⟩))
  rw [hd] at hc
  obtain rfl := Option.some.inj (hc.symm.trans (rescaleStore_code j))
  have hm := rescale_reads_store (L := L) (g := g) d j hvals
  have hj := j.isLt
  have hread := readBits_b32 (L := L) (g := g) hreg (by omega)
  have hnat : (BitVec.ofNat 64 (64 * j.val)).toNat = 64 * j.val := toNat_ofNat_lt (by omega)
  have hsize : TcShape.s32x32b.countOk 64 = true := rfl
  have haddr : tcDataAddressOk L g .s32x32b (64 * j.val) = true := by
    have hh : 64 * j.val / 2 ^ 16 = 0 := by omega
    simp only [tcDataAddressOk, hh]
    rfl
  have hbytes : (rescaleStoreValues d).all (fun v => decide (v.bytes = 4)) = true := by
    simp only [rescaleStoreValues, List.all_eq_true, List.mem_map, decide_eq_true_eq]
    rintro _ ⟨i, _, rfl⟩
    rfl
  have hplain : ∀ s, TcShape.s32x32b ≠ .packed16 s := by intro s hs; cases hs
  have hlen : (rescaleStoreSrcs j).length = 64 := by
    simp [rescaleStoreSrcs, rescaleStoreRegs]
  rw [eventTmpl_tcSt_noWait (by rfl)]
  simp only [tcTmpl_tcSt_plain hplain, hpre.block, Nat.reduceMod, hlen, hsize, hread,
    hnat, haddr, hm, hbytes, ↓reduceIte, ofExec,
    pure, Except.pure, bind, Except.bind]

/-- The store writes the 64 products of the loaded words and the observed gain. -/
theorem fires_rescaleStore (hpre : Pre P L mem0) {d : D} {j : Fin 4}
    {t u : TState} {e : Event} {ins : Instr}
    (hd : d.site = .rescaleStore j) (ha : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    e.kind = .tc (.st (64 * j.val) (rescaleStoreValues d) .s32x32b) ∧
      u = PTX.next t := by
  rw [rescaleStore_template hpre hd ha hc] at hf
  exact ⟨congrArg Event.kind hf.1, Option.some.inj hf.2⟩

/-- The rescale store updates the abstract output columns with its observed words. -/
theorem step_rescaleStore (hpre : Pre P L mem0)
    (d : D) (j : Fin 4) (hd : d.site = .rescaleStore j) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins ha hi hc hf => by
    obtain ⟨he, rfl⟩ := fires_rescaleStore hpre hd ha hc hf
    have hin : d.site.inRescale = true := by rw [hd]; rfl
    have hsub := rescale_sub_zero hi hin
    let row : D := {d with o := tileOutput L g d j (rescaleStoreValues d)}
    let d' : D := {row with site := .rescaleWaitSt j}
    have hn : next P L g d e = some (some d') := by
      simp [next, nextSite, hd, he, d', row]
    have hpc : d.site.pc = (Site.rescaleStore j).pc := by rw [hd]
    have ht := at_next_of ha hpc hsub
    have hv : valueOf P L g d' = valueOf P L g d := by rfl
    have hkeep : rescaleLive (.rescaleWaitSt j) ⊆ rescaleLive (.rescaleStore j) := by
      fin_cases j <;> decide +kernel
    refine Or.inl (Or.inr ⟨d', PTX.next t, hn, .refl,
      ⟨?_, ht.2.1.trans hsub.symm, ht.2.2.1, ht.2.2.2.1, ?_⟩, ?_⟩)
    · refine ht.1.trans ?_
      change 814 + 101 * j.val + 1 = 815 + 101 * j.val
      omega
    · change Holds (PTX.next t).regs (factsFrom (rescaleLive (.rescaleWaitSt j)) (valueOf P L g d'))
      rw [hv]
      exact holds_factsFrom_mono ht.2.2.2.2 hkeep
    · have hi' : Inv P L g row := {hi with blockLt := hi.blockLt}
      have hr := rescale_inv hi' hin (s := .rescaleWaitSt j) rfl
      simpa [code, d', row, hsub] using hr

private def rescaleWritten (d : D) (j : Fin 4) (i : Nat) : List (Nat × Value) :=
  ((List.range (2 * i)).reverse).map fun r => (rescaleOutputReg j r, rescaleValue d r)

private theorem rescale_written_succ (d : D) (j : Fin 4) (i : Nat) :
    rescaleWritten d j (i + 1) =
      (rescaleOutputReg j (2 * i + 1), rescaleValue d (2 * i + 1)) ::
        (rescaleOutputReg j (2 * i), rescaleValue d (2 * i)) :: rescaleWritten d j i := by
  rw [rescaleWritten, show 2 * (i + 1) = (2 * i + 1) + 1 by omega,
    List.range_succ, List.range_succ]
  simp [rescaleWritten]

private theorem rescale_output_mul (d : D) {gain : ℝ}
    (h : valFloat .f32 d.gainWord = .ok gain) (i : Nat) :
    rescaleValue d i = fl (outputReal d.rescaleWords i * gain) := by
  simp [rescaleValue, h, Except.toOption]

private theorem rescale_pair_regs_bounds (j : Fin 4) (i : Fin 32) :
    3308 ≤ rescalePackReg j i.val - 1 ∧ rescalePackReg j i.val ≤ 3564 ∧
      rescalePackReg j i.val ≠ 3312 ∧ rescalePackReg j i.val - 1 ≠ 3312 := by
  have hi := i.isLt
  fin_cases j <;> simp [rescalePackReg] <;> (try split_ifs) <;> omega

private theorem rescale_wait_footprint (j : Fin 4) :
    ∀ r ∈ rescaleLive (.rescaleWait j),
      (r < 3308 ∨ 3564 < r ∨ r = 3312) ∧
        (r < rescaleOutputReg j 0 ∨ rescaleOutputReg j 64 ≤ r) := by
  fin_cases j <;> decide +kernel

private theorem rescale_fresh_pair (d : D) (j : Fin 4) (i : Fin 32) {r : Nat} {v : Value}
    (hm : (r, v) ∈ rescaleWritten d j i.val ++
      factsFrom (rescaleLive (.rescaleWait j)) (valueOf P L g d)) :
    r ≠ rescalePackReg j i.val ∧ r ≠ rescalePackReg j i.val - 1 ∧
      r ≠ rescaleOutputReg j (2 * i.val) ∧ r ≠ rescaleOutputReg j (2 * i.val + 1) := by
  have hi := i.isLt
  have hj := j.isLt
  obtain ⟨hmin, hmax, hpk, hml⟩ := rescale_pair_regs_bounds j i
  rcases List.mem_append.mp hm with hp | hh
  · obtain ⟨ix, hix, hv⟩ := List.mem_map.mp hp
    have hloc : r = rescaleOutputReg j ix := congrArg Prod.fst hv.symm
    rw [List.mem_reverse, List.mem_range] at hix
    unfold rescaleOutputReg at hloc ⊢
    omega
  · obtain ⟨w, hw, hv⟩ := List.mem_map.mp hh
    have heq : w = r := congrArg Prod.fst hv
    subst w
    obtain ⟨hreg, hout⟩ := rescale_wait_footprint j r hw
    unfold rescaleOutputReg at hout ⊢
    omega

private theorem rescale_wait_input_live (j : Fin 4) :
    rescaleLoadRegs j ⊆ rescaleLive (.rescaleWait j) := by fin_cases j <;> decide +kernel

private theorem rescale_wait_gain_live (j : Fin 4) : 3312 ∈ rescaleLive (.rescaleWait j) :=
  by fin_cases j <;> decide +kernel

private theorem rescale_store_cover (j : Fin 4) :
    ∀ r ∈ rescaleLive (.rescaleStore j),
      r ∈ rescaleStoreRegs j ∨ r ∈ rescaleLive (.rescaleWait j) := by
  fin_cases j <;> decide +kernel

private theorem rescale_pair_loop (d : D) (j : Fin 4)
    (hw : goodOutputWords d.rescaleWords = true) {gain : ℝ}
    (hgSh : Assumptions.scoreHalf d.gainWord) (hg : valFloat .f32 d.gainWord = .ok gain)
    {t : TState} (ha : At t (rescalePairPc j 0)
      (factsFrom (rescaleLive (.rescaleWait j)) (valueOf P L g d))) :
    ∀ i ≤ 32, ∃ u, run kernel asms L g (3 * i) t = some u ∧
      At u (rescalePairPc j i) (rescaleWritten d j i ++
        factsFrom (rescaleLive (.rescaleWait j)) (valueOf P L g d)) := by
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨t, rfl, ha⟩
  | succ n ih =>
    intro hn
    obtain ⟨v, hr, hv⟩ := ih (by omega)
    let i : Fin 32 := ⟨n, by omega⟩
    let F := rescaleWritten d j n ++ factsFrom (rescaleLive (.rescaleWait j)) (valueOf P L g d)
    have hbase : Holds v.regs (factsFrom (rescaleLive (.rescaleWait j)) (valueOf P L g d)) :=
      ((holds_append v.regs _ _).mp hv.2.2.2.2).2
    have hinput (ix : Fin 64) :
        v.regs (rescaleInputReg j ix.val) = some (d.rescaleWords.getD ix.val (b32 0)) := by
      rw [← rescale_input_value (P := P) (L := L) (g := g) d j ix]
      exact holds_mem hbase (mem_factsFrom (rescale_wait_input_live j (rescale_input_mem j ix)))
    have hgain : v.regs 3312 = some (joinValue d.gainWord d.gainWord) :=
      holds_mem hbase (mem_factsFrom (rescale_wait_gain_live j))
    have hLo := hinput ⟨2 * n, by omega⟩
    have hHi := hinput ⟨2 * n + 1, by omega⟩
    obtain ⟨hl, hxl⟩ := outputWords_at hw (show 2 * n < 64 by omega)
    obtain ⟨hh, hxh⟩ := outputWords_at hw (show 2 * n + 1 < 64 by omega)
    have hf (q : Nat × Value) (hq : q ∈ F) := rescale_fresh_pair d j i hq
    obtain ⟨u, hu, hau⟩ := rescalePair_finite j i hv hLo hHi hgain hl hh hgSh hxl hxh hg
      (fun q hq => (hf q hq).1) (fun q hq => (hf q hq).2.1)
      (fun q hq => (hf q hq).2.2.1) (fun q hq => (hf q hq).2.2.2)
    have hrun := run_comp hr hu
    rw [show 3 * n + 3 = 3 * (n + 1) by omega] at hrun
    refine ⟨u, hrun, ?_⟩
    rw [rescale_written_succ, rescale_output_mul d hg, rescale_output_mul d hg]
    exact hau

private theorem run_rescale_tile (d : D) (j : Fin 4)
    (hw : goodOutputWords d.rescaleWords = true) (hgain : outputWord d.gainWord = true)
    {t : TState} (ha : At t (rescalePairPc j 0)
      (factsFrom (rescaleLive (.rescaleWait j)) (valueOf P L g d))) :
    ∃ u, run kernel asms L g 96 t = some u ∧
      At u (Site.rescaleStore j).pc (facts P L g {d with site := .rescaleStore j}) := by
  have ⟨hgSh, hgSome⟩ : Assumptions.scoreHalf d.gainWord ∧
      (valFloat .f32 d.gainWord).toOption.isSome = true := by
    simpa [outputWord] using hgain
  cases hv : valFloat .f32 d.gainWord with
  | error err => simp [hv, Except.toOption] at hgSome
  | ok gain =>
    obtain ⟨u, hr, hau⟩ := rescale_pair_loop d j hw hgSh hv ha 32 (by decide)
    have hpc : rescalePairPc j 32 = (Site.rescaleStore j).pc := by
      simp [rescalePairPc, Site.pc]
      omega
    rw [hpc] at hau
    refine ⟨u, hr, hau.mono ?_⟩
    have hv : valueOf P L g {d with site := .rescaleStore j} = valueOf P L g d := rfl
    change Holds u.regs (factsFrom (rescaleLive (.rescaleStore j))
      (valueOf P L g {d with site := .rescaleStore j}))
    rw [hv]
    obtain ⟨hout, hwait⟩ := (holds_append u.regs _ _).mp hau.2.2.2.2
    refine holds_of_pointwise fun r hr' => ?_
    rcases rescale_store_cover j r hr' with hdst | hframe
    · have hi := (List.mem_range'.mp hdst : ∃ i < 64, r = 1264 + 129 * j.val + 1 * i)
      obtain ⟨i, hi, he⟩ := hi
      have hu : r = rescaleOutputReg j i := by simp [rescaleOutputReg, he]
      rw [hu, rescale_output_value _ j ⟨i, hi⟩]
      exact holds_mem hout (List.mem_map.mpr ⟨i, by simpa using hi, rfl⟩)
    · exact holds_mem hwait (mem_factsFrom hframe)

/-- Wait for the loaded tile and scale all 64 words before the corresponding store. -/
theorem step_rescaleWait (hpre : Pre P L mem0)
    (d : D) (j : Fin 4) (hd : d.site = .rescaleWait j) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins ha hi hc hf => by
    rw [hd] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans (rescaleWait_code j))
    have hev : eventTmpl asms L g t .tcWaitLd = .tc .waitLd (PTX.next t) := by
      simp [eventTmpl, tcTmpl, hpre.block, ofExec, pure, Except.pure]
    rw [hev] at hf
    obtain ⟨he, hu⟩ := hf
    have hu' := Option.some.inj hu
    subst hu'
    by_cases hg : (goodOutputWords d.rescaleWords && outputWord d.gainWord) = true
    · have hpair : goodOutputWords d.rescaleWords = true ∧ outputWord d.gainWord = true := by
        simpa only [Bool.and_eq_true] using hg
      obtain ⟨hw, hgain⟩ := hpair
      have hin : d.site.inRescale = true := by rw [hd]; rfl
      have hsub := rescale_sub_zero hi hin
      have hsite : d.site.pc = (Site.rescaleWait j).pc := by rw [hd]
      have hp : (Site.rescaleWait j).pc + 1 = rescalePairPc j 0 := by
        simp [Site.pc, rescalePairPc]
        omega
      have ht := at_next_of ha hsite hsub
      rw [hp] at ht
      obtain ⟨v, hr, hav⟩ := run_rescale_tile d j hw hgain ht
      let d' : D := {d with site := .rescaleStore j}
      have hn : next P L g d e = some (some d') := by simp [next, nextSite, hd, he, hw, hgain, d']
      refine Or.inl (Or.inr ⟨d', v, hn, run_rtg hr,
        ⟨hav.1, hav.2.1.trans hsub.symm, hav.2.2.1, hav.2.2.2.1, hav.2.2.2.2⟩, ?_⟩)
      have hi' := rescale_inv hi hin (s := .rescaleStore j) rfl
      simpa [code, d', hsub] using hi'
    · exact Or.inl (Or.inl (by
        simp only [next, nextSite, hd, he, hg, Bool.false_eq_true, ite_false]))

private theorem rescale_gain_pack_bytes {v : Value} (hv : Assumptions.scoreHalf v) :
    (joinValue v (b32 0)).bytes = 8 := by
  have hb := Assumptions.scoreHalf_bytes hv
  cases v with
  | bits w x =>
    by_cases hw : w = 32
    · subst w
      rfl
    · simp [b32, joinValue, hw, Value.bytes]
      simpa only [Value.bytes] using hb
  | slice whole offset bytes =>
    cases offset <;> (change _ + 4 = 8; rw [hb])
  | _ =>
    change _ + 4 = 8
    rw [hb]

private theorem run_rescale_open (d : D) (hgain : Assumptions.scoreHalf d.gainWord) {t : TState}
    (ha : At t 712 (factsFrom (rescaleLive .rescaleFence) (valueOf P L g d))) :
    ∃ u, run kernel asms L g 4 t = some u ∧
      At u 716 (facts P L g {d with site := .rescaleLoad 0}) := by
  let F := factsFrom (rescaleLive .rescaleFence) (valueOf P L g d)
  have hr : t.regs 2951 = some d.gainWord :=
    holds_mem ha.2.2.2.2 (mem_factsFrom (r := 2951) (by decide +kernel))
  let t₁ := PTX.next (setReg t 3565 (joinValue d.gainWord (b32 0)))
  have hs : Assumptions.deadPackWords t.pc = some (3565, 2951, 1715) := by rw [ha.1]; rfl
  have hd := Audit.deadPack_uses_low (L := L) (g := g) hs hr (Assumptions.scoreHalf_bytes hgain)
  let m : MoveInstr := ⟨.pack, .int .b 64, [some 3565], [.reg 2951, .reg 1715]⟩
  have hshare : Assumptions.sharedBits.localRule L g t (.move m) = some (.ok t₁) := by
    have hscope : Assumptions.sharedBitsSites.contains t.pc = false := by rw [ha.1]; decide
    have hd' : Assumptions.deadPackRule L g t (.move m) = some (.ok t₁) := hd
    simp only [Assumptions.sharedBits, hscope, Bool.false_eq_true, ite_false, hd', Option.orElse]
  have hparam : Assumptions.paramPointers.localRule L g t (.move m) = none :=
    Thread.paramPointers_localRule_none (by rw [ha.1]; decide) (by rw [ha.1]; decide)
  have hfind : asms.findSome? (fun a => a.localRule L g t (.move m)) = some (.ok t₁) := by
    simp only [Assumptions.all, List.findSome?_cons, hparam, hshare]
    rfl
  have hcode : kernel.code[712]? = some ⟨none, .move m⟩ := Flow.code_712
  have hrun : run kernel asms L g 1 t = some t₁ := run_paramRule hcode ha rfl hfind
  have ha₁ : At t₁ 713 ((3565, joinValue d.gainWord (b32 0)) :: F) :=
    ha.set (not_mem_factsFrom (by decide +kernel))
  let unpack : MoveInstr := ⟨.unpack, .int .b 64, [some 1716, none], [.reg 3565]⟩
  let t₂ := PTX.next (setReg t₁ 1716 d.gainWord)
  have hunpack : execLocalA asms L g t₁ (.move unpack) = .ok t₂ := by
    have hnone := Thread.asms_localRule_move (t := t₁) (m := unpack) (L := L) (g := g)
      (by rw [ha₁.1]; decide) (by rw [ha₁.1]; decide) (by rw [ha₁.1]; decide)
    rw [execLocalA_noSegment (asms_segment_free t₁), execLocalRule_of_none hnone]
    change execMove L g t₁ (.move unpack) = _
    have hp : t₁.regs 3565 = some (joinValue d.gainWord (b32 0)) := ha₁.2.2.2.2.1
    have hp8 := rescale_gain_pack_bytes hgain
    have hg4 := Assumptions.scoreHalf_bytes hgain
    have hzero : Assumptions.scoreHalf (b32 0) := by
      change (BitVec.ofNat 64 0).toNat < 2 ^ 32
      decide
    have hsplit := split_join_words hgain hzero
    simp [unpack, execMove, DType.width, readValue, readReg, hp, hp8, hsplit, hg4,
      bind, Except.bind, pure, Except.pure, setDst, t₂]
    rfl
  have hrun₂ : run kernel asms L g 1 t₁ = some t₂ := by
    exact run_local Flow.code_713 rfl ha₁ hunpack
  have ha₁' := ha₁.mono ha₁.2.2.2.2.2
  have ha₂ : At t₂ 714 ((1716, d.gainWord) :: F) :=
    ha₁'.set (not_mem_factsFrom (by decide +kernel))
  let t₃ := PTX.next (setReg t₂ 3312 (joinValue d.gainWord d.gainWord))
  have hrun₃ : run kernel asms L g 1 t₂ = some t₃ := by
    apply run_local Flow.code_714 rfl ha₂
    have hp : t₂.regs 1716 = some d.gainWord := ha₂.2.2.2.2.1
    have hw := Assumptions.scoreHalf_bytes hgain
    exact exec_outputPack (by rw [ha₂.1]; decide) hp hp hw hw
  have ha₂' := ha₂.mono ha₂.2.2.2.2.2
  have ha₃ : At t₃ 715 ((3312, joinValue d.gainWord d.gainWord) :: F) :=
    ha₂'.set (not_mem_factsFrom (by decide +kernel))
  obtain ⟨v, hv, hav⟩ : ∃ u, run kernel asms L g 1 t₃ = some u ∧
      At u 716 (factsFrom ((Flow.live 716).filter tracked.contains) (valueOf P L g d)) := by
    change At t₃ 715 ((3312, joinValue d.gainWord d.gainWord) ::
      factsFrom ((Flow.live 711).filter tracked.contains) (valueOf P L g d)) at ha₃
    seg_fp ha₃ using rfl
  exact ⟨v, run_comp (run_comp (run_comp hrun hrun₂) hrun₃) hv, hav⟩

/-- The rescale arm opens with its Tensor Memory fence and broadcasts the gain to both lanes. -/
theorem step_rescaleFence (d : D) (hd : d.site = .rescaleFence) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins ha hi hc hf => by
    have hsite : d.site.pc = 711 := by rw [hd]; rfl
    rw [hsite] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_711)
    change e = ⟨711, .tc .fenceAfter⟩ ∧ some u = some (PTX.next t) at hf
    obtain ⟨he, hu⟩ := hf
    have hu' := Option.some.inj hu
    subst hu'
    by_cases hg : outputWord d.gainWord = true
    · have hshape : Assumptions.scoreHalf d.gainWord := by
        have h := hg
        simp only [outputWord, Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.1
      have hin : d.site.inRescale = true := by rw [hd]; rfl
      have hsub := rescale_sub_zero hi hin
      have ht := at_next_of ha hsite hsub
      obtain ⟨v, hr, hv⟩ := run_rescale_open d hshape ht
      let d' : D := {d with site := .rescaleLoad 0}
      have hn : next P L g d e = some (some d') := by simp [next, nextSite, hd, he, hg, d']
      refine Or.inl (Or.inr ⟨d', v, hn, run_rtg hr,
        ⟨hv.1, hv.2.1.trans hsub.symm, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2⟩, ?_⟩)
      have hi' := rescale_inv hi hin (s := .rescaleLoad 0) rfl
      simpa [code, d', hsub] using hi'
    · exact Or.inl (Or.inl (by simp [next, nextSite, hd, he, hg]))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
