-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0
import Lemmas.Flow.LoadShared
import Lemmas.Flow.ArithCore

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}

/-- The scalar non-coherent read used to acquire a sink or a per-batch length. -/
private def ncInput (ty : DType) (base dst : Nat) : MemAccess :=
  { kind := .load, space := some .global, sem := .weak, elem := ty, nc := true
    addr := ⟨.reg base 64, 0⟩, dsts := [some dst] }

private theorem fires_input {t u : TState} {e : Event} {ty : DType} {base dst off : Nat}
    (hw : ty.width = 32) (hr : (ncInput ty base dst).rule = some .threadAccess)
    (hsub : t.sub = 0) (hreg : t.regs base = some (b64 off))
    (hword : off < 2 ^ 64) (halign : off % 4 = 0) (hnc : asms.any (·.ncLoads t.pc) = true)
    (hf : Fires t.pc (eventTmpl asms L g t (.mem (ncInput ty base dst))) e (some u)) :
    ∃ a bs, e.kind = .nc a bs ∧ u = afterLoad t [dst] bs := by
  have ht := loadTmpl_global_nc (A := asms) (L := L) (g := g) (t := t)
    (d := dst) (base := base) (w := 32) hsub hreg hword (by decide) halign hnc
  rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) (base := base) (w := 64)
    hr rfl rfl rfl rfl] at hf
  change Fires t.pc (loadTmpl asms L g t .global true ty.width [dst] base 0) e (some u) at hf
  rw [hw, ht] at hf
  obtain ⟨bs, _, he, hu⟩ := hf
  exact ⟨_, bs, congrArg Event.kind he, Option.some.inj hu⟩

/-- The exact operand words at the join of the scalar parameter and optional read paths. -/
private def inputValue (P : Params) (L : Launch) (g r : Nat) : Value :=
  if r = 2880 then sinkReg P L g
  else if r = 2881 then b32 (P.topkLen (eOf L g))
  else if r = 470 then b32 (Result.ceilToMultiple (P.topkLen (eOf L g)) 64)
  else if r = 2882 then b32 (P.extraTopkLen (eOf L g))
  else if r = 942 then b32 (P.extraTopkLen (eOf L g) + 63)
  else if r = 946 then b32 (Result.ceilToMultiple (P.extraTopkLen (eOf L g)) 64)
  else if r = 947 then b32 (Result.origPadded (P.topkLen (eOf L g)))
  else valueOf P L g (init P L g) r

private def inputFacts (P : Params) (L : Launch) (g pc : Nat) : List (Nat × Value) :=
  factsFrom (startLive pc) (inputValue P L g)

macro "input_values" : tactic =>
  `(tactic| simp only [inputValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some,
    Option.getD_none, Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceLT, true_and, false_and,
    and_true, and_false, ite_false, ite_true])

private theorem input_reg {pc r : Nat} {t : TState} (ha : At t pc (inputFacts P L g pc))
    (hr : r ∈ startLive pc) : t.regs r = some (inputValue P L g r) :=
  holds_mem ha.2.2.2.2 (mem_factsFrom hr)

private theorem input_bra {t : TState} {pc target p b : Nat} {pick : Bool}
    (hc : kernel.code[pc]? = some ⟨some (p, false), .bra target false⟩)
    (h : At t pc (inputFacts P L g pc)) (hp : p ∈ startLive pc)
    (hv : inputValue P L g p = .pred pick)
    (hb : b = if pick then target else pc + 1)
    (hl : startLive b ⊆ startLive pc)
    (h1 : pc ∉ paramAdds) (h2 : pc ∉ prefetchTensorMapSites)
    (hsf : Assumption.SegFreePc asms pc := by seg_free_pc) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' b (inputFacts P L g b) := by
  have hL : ∀ a ∈ asms, a.localRule L g t (.bra target false) = none := by
    intro a ha
    exact Thread.asms_localRule_bra (t := t) (by rw [h.1]; exact h1) (by rw [h.1]; exact h2) a ha
  obtain ⟨t', hr, ht⟩ := run_bra hc pick h (hv ▸ input_reg h hp) hL hsf
  rw [← hb] at ht
  exact ⟨t', hr, ht.mono (holds_factsFrom_mono ht.2.2.2.2 hl)⟩

private theorem input_param {pc w off dst : Nat} {ty : DType} {t : TState}
    (hpre : Pre P L mem0) (h : At t pc (inputFacts P L g pc))
    (hc : kernel.code[pc]? = some ⟨none, .mem (Thread.paramLoad ty off 2991 dst)⟩)
    (hsup : ParamSupplied L (param "0") off (w / 8))
    (hsize : off + w / 8 ≤ 304)
    (halign : 0 < w / 8 ∧ off % (w / 8) = 0 ∧ (8 : Nat) % (w / 8) = 0)
    (h2991 : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0))
    (hwidth : ty.width = w)
    (hrule : (Thread.paramLoad ty off 2991 dst).rule = some .threadMove)
    (hd : paramElem w w (paramNat L (param "0") off (w / 8)) = inputValue P L g dst)
    (hnew : dst ∉ startLive pc)
    (hkeep : ∀ r ∈ startLive (pc + 1), r = dst ∨ r ∈ startLive pc)
    (hparam : pc ∉ paramAdds) (hmap : pc ∉ prefetchTensorMapSites)
    (hsf : Assumption.SegFreePc asms pc := by seg_free_pc) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u (pc + 1) (inputFacts P L g (pc + 1)) := by
  have hL : ∀ a ∈ asms, a.localRule L g t (.mem (Thread.paramLoad ty off 2991 dst)) = none := by
    intro a ha
    exact Thread.asms_localRule_mem (t := t) (by rw [h.1]; exact hparam)
      (by rw [h.1]; exact hmap) a ha
  refine ⟨PTX.next (setReg t dst (inputValue P L g dst)), ?_, ?_⟩
  · rw [← hd]
    exact run_local hc rfl h (Thread.exec_ldParamReg (A := asms) (L := L) (g := g)
      (w := w) (off := off) (r := 2991) (d := dst) (t := t) (p := param "0") (ty := ty)
      (decl := scalarsParam) (base := P.param0Base) h2991 hpre.param0Object
      ⟨by omega, hsize⟩ halign hsup (Assumption.SegFreePc.of_eq h.1 hsf) hL hwidth hrule)
  · refine (h.set (not_mem_factsFrom hnew)).mono ?_
    apply holds_of_pointwise
    intro r hr
    rcases hkeep r hr with rfl | hr'
    · exact Function.update_self ..
    · have hne : r ≠ dst := fun e => hnew (e ▸ hr')
      simpa [PTX.next, setReg, Function.update_of_ne hne] using input_reg h hr'

/-- A scalar load updates one register and leaves all other live operands intact. -/
private theorem input_afterLoad {t u : TState} {bs : List (Option Byte)} {v : Value} {pc dst : Nat}
    (ha : At t pc (inputFacts P L g pc)) (hu : u = afterLoad t [dst] bs)
    (hv : rebuild 3 bs = .ok v)
    (hval : v = inputValue P L g dst)
    (hkeep : ∀ r ∈ startLive (pc + 1), r = dst ∨ r ∈ startLive pc) :
    At u (pc + 1) (inputFacts P L g (pc + 1)) := by
  rw [hu, afterLoad_ok ha.2.1 ha.2.2.1 hv]
  refine ⟨by rw [ha.1], rfl, rfl, ha.2.2.2.1, holds_of_pointwise fun r hr => ?_⟩
  rcases hkeep r hr with rfl | hr'
  · simpa [setReg] using hval
  · by_cases hne : r = dst
    · subst r
      simpa [setReg] using hval
    · simpa [setReg, Function.update_of_ne hne] using input_reg ha hr'

/-- The unconditional branch after a length read jumps over the fallback parameter load. -/
private theorem input_bra_uncond {pc target : Nat} {t : TState}
    (hc : kernel.code[pc]? = some ⟨none, .bra target true⟩)
    (h : At t pc (inputFacts P L g pc))
    (hkeep : startLive target ⊆ startLive pc)
    (h1 : pc ∉ paramAdds) (h2 : pc ∉ prefetchTensorMapSites)
    (hsf : Assumption.SegFreePc asms pc := by seg_free_pc) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u target (inputFacts P L g target) := by
  have hL : ∀ a ∈ asms, a.localRule L g t (.bra target true) = none := by
    intro a ha
    exact Thread.asms_localRule_bra (t := t) (by rw [h.1]; exact h1) (by rw [h.1]; exact h2) a ha
  have he : execLocalA asms L g t (.bra target true) = .ok {t with pc := target} := by
    rw [(Assumption.SegFreePc.of_eq h.1 hsf).exec, execLocalRule_of_none hL]
    all_goals rfl
  exact ⟨_, run_local hc rfl h he, ⟨rfl, h.2.1, h.2.2.1, h.2.2.2.1,
    holds_factsFrom_mono h.2.2.2.2 hkeep⟩⟩

private theorem input_main_bound (hpre : Pre P L mem0) (hb : eOf L g < P.b) :
    P.topkLen (eOf L g) + 63 < 2 ^ 31 := by
  have h := hpre.paramTopkLen
  cases hp : P.topkLenBase
  · rw [hp] at h
    rw [h.2 _ hb]
    exact hpre.topkAdd63Lt
  · rw [hp] at h
    exact lt_of_le_of_lt (Nat.add_le_add_right ((h.2.2 _ hb 0 (by decide)).2 _ hb) _)
      hpre.topkAdd63Lt

private theorem input_extra_bound (hpre : Pre P L mem0) (hb : eOf L g < P.b) :
    P.extraTopkLen (eOf L g) + 63 < 2 ^ 31 := by
  have h := hpre.paramExtraTopkLen
  cases hp : P.extraTopkLenBase
  · rw [hp] at h
    rw [h.2 _ hb]
    exact hpre.extraTopkAdd63Lt
  · rw [hp] at h
    exact lt_of_le_of_lt (Nat.add_le_add_right ((h.2.2 _ hb 0 (by decide)).2 _ hb) _)
      hpre.extraTopkAdd63Lt

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem input_round_main (hpre : Pre P L mem0) (hb : eOf L g < P.b) {t : TState}
    (ha : At t 171 (inputFacts P L g 171)) :
    ∃ u, run kernel asms L g 5 t = some u ∧ At u 176 (inputFacts P L g 176) := by
  have hn := input_main_bound hpre hb
  dsimp only [inputFacts] at ha ⊢
  seg_fp ha using
    (try input_values)
    (try simp only [truncBits_int_63, truncBits_int_26, truncBits_int_31, truncBits_int_neg64,
      Result.ceilToMultiple, show ∀ n : Nat, n + 64 - 1 = n + 63 from fun _ => by omega])
    (try norm_signed)

private theorem input_from_main_param (hpre : Pre P L mem0) (hb : eOf L g < P.b)
    (hnone : P.topkLenBase = none) {t : TState} (ha : At t 170 (inputFacts P L g 170)) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u 171 (inputFacts P L g 171) := by
  have hlen := hpre.paramTopkLen
  rw [hnone] at hlen
  have hr : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    exact input_reg ha (r := 2991) (by decide +kernel)
  refine input_param hpre ha (w := 32) Flow.code_170
    (supplied_int (off := 40) (x := P.topk) hpre.paramTopk (by decide))
    (by decide) (by decide) hr rfl rfl ?_ (by decide +kernel) (by decide +kernel)
    (by decide) (by decide)
  rw [paramElem_of_ne (by decide)]
  change b32 (paramWord L 40 4) = b32 (P.topkLen (eOf L g))
  rw [paramWord_40 hpre, hlen.2 _ hb]

private theorem input_from_extra_param (hpre : Pre P L mem0) (hb : eOf L g < P.b)
    (hnone : P.extraTopkLenBase = none) {t : TState} (ha : At t 183 (inputFacts P L g 183)) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u 184 (inputFacts P L g 184) := by
  have hlen := hpre.paramExtraTopkLen
  rw [hnone] at hlen
  have hr : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    exact input_reg ha (r := 2991) (by decide +kernel)
  refine input_param hpre ha (w := 32) Flow.code_183
    (supplied_int (off := 120) (x := P.extra_topk) hpre.paramExtraTopk (by decide))
    (by decide) (by decide) hr rfl rfl ?_ (by decide +kernel) (by decide +kernel)
    (by decide) (by decide)
  rw [paramElem_of_ne (by decide)]
  change b32 (paramWord L 120 4) = b32 (P.extraTopkLen (eOf L g))
  rw [paramWord_120 hpre, hlen.2 _ hb]

private theorem input_extra_pointer (hpre : Pre P L mem0) {t : TState}
    (h : At t 176 (inputFacts P L g 176)) :
    ∃ t', run kernel asms L g 2 t = some t' ∧ At t' 178 (inputFacts P L g 178) := by
  have h2991 : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    exact input_reg h (r := 2991) (by decide +kernel)
  obtain ⟨u, hr, hu⟩ := input_param hpre h (w := 64) Flow.code_176
    (supplied_144 hpre) (by decide) (by decide) h2991 rfl rfl (by
      rw [paramElem_of_ne (by decide)]
      rfl) (by decide +kernel) (by decide +kernel) (by decide) (by decide)
  have hv : ∃ v, run kernel asms L g 1 u = some v ∧ At v 178 (inputFacts P L g 178) := by
    dsimp only [inputFacts] at hu ⊢
    seg_fp hu using input_values
  obtain ⟨v, hv, h⟩ := hv
  exact ⟨v, run_comp hr hv, h⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem input_to_extra_address (hpre : Pre P L mem0) (hb : eOf L g < P.b) {t : TState}
    (h : At t 179 (inputFacts P L g 179)) :
    ∃ t', run kernel asms L g 2 t = some t' ∧ At t' 181 (inputFacts P L g 181) := by
  have he : eOf L g < 2 ^ 31 := lt_trans hb hpre.bLt
  dsimp only [inputFacts] at h ⊢
  seg_fp h using
    (try input_values)
    (try nf_simp)
    (try omega)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem input_shared_offsets (hpre : Pre P L mem0) {t : TState}
    (h : At t 184 (inputFacts P L g 184)) :
    ∃ t', run kernel asms L g 5 t = some t' ∧ At t' 189 (inputFacts P L g 189) := by
  have hs := sharedBase_lt hpre
  have htid : tidOf L g < 384 := tid384 hpre
  have h4 : tidOf L g % 128 % 4294967296 * 4 % 4294967296 = 4 * (tidOf L g % 128) := by
    have := Nat.mod_lt (tidOf L g) (by decide : 0 < 128)
    omega
  have hy : 4 * (tidOf L g % 128) ^^^ 256 < 512 :=
    Nat.xor_lt_two_pow (n := 9)
      (by have := Nat.mod_lt (tidOf L g) (by decide : 0 < 128); omega)
      (by norm_num)
  dsimp only [inputFacts] at h ⊢
  seg_fp h using
    (try input_values)
    (try (simp only [truncBits_int_2, truncBits_int_256, sb, Nat.add_zero]))
    (try (nf_simp [nf_xor]))
    (try (rw [h4]))
    (try (norm_bits [nf_xor]))
    (try norm_bits)
    (try (norm_signed [nf_xor]))
    (try omega)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem input_round_extra (hpre : Pre P L mem0) (hb : eOf L g < P.b) {t : TState}
    (h : At t 189 (inputFacts P L g 189)) :
    ∃ t', run kernel asms L g 5 t = some t' ∧ At t' 194 (inputFacts P L g 194) := by
  have hn := input_extra_bound hpre hb
  dsimp only [inputFacts] at h ⊢
  seg_fp h using
    (try input_values)
    (try simp only [truncBits_int_63, truncBits_int_26, truncBits_int_31, truncBits_int_neg64,
      Result.ceilToMultiple, show ∀ n : Nat, n + 64 - 1 = n + 63 from fun _ => by omega])
    (try norm_signed)
    (try (all_goals nf_simp))
    (try (all_goals omega))

private theorem input_total (P : Params) (L : Launch) (g : Nat) :
    64 * blocksOf P L g = Result.origPadded (P.topkLen (eOf L g)) +
      Result.ceilToMultiple (P.extraTopkLen (eOf L g)) 64 := by
  rw [blocksOf, Result.blocks_eq_kernel]
  change 64 * ((Result.origPadded (P.topkLen (eOf L g)) +
    Result.ceilToMultiple (P.extraTopkLen (eOf L g)) 64) / 64) = _
  rw [Nat.mul_comm]
  apply Nat.div_mul_cancel
  apply Nat.dvd_add
  · unfold Result.origPadded Result.topkBlock
    by_cases hp : Result.ceilToMultiple (P.topkLen (eOf L g)) 64 ≤ 64
    · rw [max_eq_right hp]
    · rw [max_eq_left (by omega)]
      unfold Result.ceilToMultiple
      exact dvd_mul_left _ _
  · unfold Result.ceilToMultiple
    exact dvd_mul_left _ _

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem input_count (hpre : Pre P L mem0) (hb : eOf L g < P.b) {t : TState}
    (h : At t 194 (inputFacts P L g 194)) :
    ∃ t', run kernel asms L g 4 t = some t' ∧ At t' 198 (inputFacts P L g 198) := by
  have hpad := hpre.paddedRange (eOf L g) hb
  have hx : Result.ceilToMultiple (P.topkLen (eOf L g)) 64 < 2 ^ 31 := by
    change max (Result.ceilToMultiple (P.topkLen (eOf L g)) 64) 64 +
      Result.ceilToMultiple (P.extraTopkLen (eOf L g)) 64 < 2 ^ 31 at hpad
    have := le_max_left (Result.ceilToMultiple (P.topkLen (eOf L g)) 64) 64
    omega
  have he := input_extra_bound hpre hb
  change Result.origPadded (P.topkLen (eOf L g)) +
    Result.ceilToMultiple (P.extraTopkLen (eOf L g)) 64 < 2 ^ 31 at hpad
  have hy : Result.ceilToMultiple (P.extraTopkLen (eOf L g)) 64 < 2 ^ 31 := by omega
  have hx0 := Nat.mod_eq_of_lt (by omega :
    Result.ceilToMultiple (P.topkLen (eOf L g)) 64 < 4294967296)
  have hy0 := Nat.mod_eq_of_lt (by omega :
    Result.ceilToMultiple (P.extraTopkLen (eOf L g)) 64 < 4294967296)
  have he0 := Nat.mod_eq_of_lt (by omega : P.extraTopkLen (eOf L g) + 63 < 4294967296)
  have he64 := Nat.mod_eq_of_lt (by omega :
    P.extraTopkLen (eOf L g) + 63 < 18446744073709551616)
  have hcmp : PTX.compare .gt .s 32
      (BitVec.ofNat 64 (Result.ceilToMultiple (P.topkLen (eOf L g)) 64))
      (64#64) = decide (64 < Result.ceilToMultiple (P.topkLen (eOf L g)) 64) := by
    norm_signed
  change max (Result.ceilToMultiple (P.topkLen (eOf L g)) 64) 64 +
    Result.ceilToMultiple (P.extraTopkLen (eOf L g)) 64 < 2 ^ 31 at hpad
  dsimp only [inputFacts] at h ⊢
  seg_fp h using
    (try input_values)
    (try (rw [input_total]))
    (try simp only [Result.origPadded, Result.topkBlock,
      show (IntOp.max false == IntOp.max false) = true from rfl, ite_true])
    (all_goals nf_simp [hx0, hy0, he0, he64])
    (all_goals simp only [hcmp, decide_eq_true_eq, max_def])
    (all_goals split_ifs)
    (all_goals norm_bits [hx0, hy0, he0, he64])

private theorem input_finish (hpre : Pre P L mem0) (hb : eOf L g < P.b) {t : TState}
    (ha : At t 184 (inputFacts P L g 184)) :
    ∃ u, run kernel asms L g 14 t = some u ∧ At u 198 (inputFacts P L g 198) := by
  obtain ⟨t₁, hr₁, ha₁⟩ := input_shared_offsets hpre ha
  obtain ⟨t₂, hr₂, ha₂⟩ := input_round_extra hpre hb ha₁
  obtain ⟨u, hr₃, hu⟩ := input_count hpre hb ha₂
  exact ⟨u, run_comp (run_comp hr₁ hr₂) hr₃, hu⟩

private theorem input_restore (hpre : Pre P L mem0) (hwg : wgOf L g = 0)
    {site : Site} {pc : Nat} {read : Bool} {t : TState}
    (hpc : site.pc = pc) (ha : At t pc (inputFacts P L g pc))
    (hkeep : (Flow.live pc).filter tracked.contains ⊆ startLive pc)
    (hval : ∀ r ∈ (Flow.live pc).filter tracked.contains,
      inputValue P L g r = valueOf P L g {init P L g with site, origLenRead := read} r)
    (he : site.inEpilogue = false) (hr : site.inRescale = false)
    (hs : ¬ ∃ a k, site = .scoreLoad a k) (hx : site ≠ .exit)
    (ht : site.needsRowTotal = false) (hw : site.needsExchangeReady = false) :
    (code P L g).Good (some {init P L g with site, origLenRead := read}) t := by
  let initial := {init P L g with origLenRead := read}
  have hi : Inv P L g initial := by
    cases init_inv g hpre hwg
    constructor <;> assumption
  have hf : (code P L g).AtD {initial with site, sub := 0} t := by
    refine ⟨ha.1.trans hpc.symm, ha.2.1, ha.2.2.1.trans (siteAcc_nil _ rfl).symm,
      ha.2.2.2.1, ?_⟩
    change Holds t.regs (facts P L g {initial with site, sub := 0})
    simp only [facts, hpc]
    apply holds_of_pointwise fun r h => ?_
    exact (input_reg ha (hkeep h)).trans (congrArg some (hval r h))
  exact ⟨hf, inv_setSite hi site (by simp [he]) (by simp [hr])
    (by exact fun h => False.elim (hs h)) (by simp [hx])
    (by intro _; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (fun h => False.elim (Bool.false_ne_true (ht.symm.trans h)))
    (fun h => False.elim (Bool.false_ne_true (hw.symm.trans h)))⟩

private theorem input_orig_padded_word (hpre : Pre P L mem0) (hb : eOf L g < P.b) (d : D)
    (hflag : d.origLenRead = P.topkLenBase.isSome) :
    valueOf P L g d 470 = inputValue P L g 470 := by
  input_values
  by_cases hp : P.topkLenBase.isSome
  · simp [hflag, hp]
  · cases hbase : P.topkLenBase
    · have hlen := hpre.paramTopkLen
      rw [hbase] at hlen
      simp only [hflag, hbase, Option.isSome_none, Bool.false_eq_true, ite_false,
        paramWord_40 hpre, hlen.2 _ hb, Result.ceilToMultiple,
        show ∀ n : Nat, n + 64 - 1 = n + 63 from fun _ => by omega]
    · simp [hbase] at hp

private theorem input_at_source (d : D) {t : TState} {pc : Nat}
    (ha : (code P L g).AtD d t) (hi : Inv P L g d) (hpc : d.site.pc = pc)
    (he : d.site.elems = 1)
    (hkeep : startLive pc ⊆ (Flow.live pc).filter tracked.contains)
    (hv : ∀ r ∈ startLive pc, valueOf P L g d r = inputValue P L g r) :
    At t pc (inputFacts P L g pc) := by
  have hsub : d.sub = 0 := by have h := hi.subLt; omega
  refine ⟨ha.1.trans hpc, ha.2.1.trans hsub, ha.2.2.1.trans (siteAcc_nil d hsub),
    ha.2.2.2.1, holds_of_pointwise fun r hr => ?_⟩
  rw [← hv r hr]
  apply reg_value ha
  rw [hpc]
  exact hkeep hr

private theorem input_bulk_values {read : Bool} :
    ∀ r ∈ (Flow.live 198).filter tracked.contains,
      inputValue P L g r =
        valueOf P L g {init P L g with site := .bulkWait, origLenRead := read} r := by
  intro r hr
  change r ∈ [459, 460, 463, 465, 466, 467, 469, 471, 472, 473, 940, 2880, 2991,
    2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3001] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl
  all_goals rfl

private theorem input_to_extra (hpre : Pre P L mem0) (hb : eOf L g < P.b)
    (hwg : wgOf L g = 0) {read : Bool} {t : TState}
    (hcount : valueOf P L g {init P L g with site := .lenExtra, origLenRead := read} 470 =
      inputValue P L g 470)
    (ha : At t 176 (inputFacts P L g 176)) :
    ∃ u, Relation.ReflTransGen (Tau kernel asms L g) t u ∧
      (code P L g).Good (some {init P L g with site := afterLen P, origLenRead := read}) u := by
  obtain ⟨t₁, hr₁, ha₁⟩ := input_extra_pointer hpre ha
  cases hp : P.extraTopkLenBase with
  | some x =>
    have hnull := ptrIsNull_144_some hpre hp
    obtain ⟨t₂, hr₂, ha₂⟩ := input_bra (P := P) (L := L) (g := g) (b := 179)
      Flow.code_178 ha₁ (by decide +kernel) (by input_values; rw [hnull]) rfl
      (by decide +kernel) (by decide) (by decide)
    obtain ⟨u, hr₃, hu⟩ := input_to_extra_address hpre hb ha₂
    refine ⟨u, run_rtg (run_comp (run_comp hr₁ hr₂) hr₃), ?_⟩
    have hs : afterLen P = .lenExtra := by simp [afterLen, hp]
    rw [hs]
    refine input_restore hpre hwg rfl hu (by decide +kernel) ?_ rfl rfl
      (by simp) (by simp) rfl rfl
    intro r hr
    change r ∈ [459, 460, 463, 465, 466, 467, 469, 470, 2880, 2991,
      2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3001, 3142] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | rfl | exact hcount.symm
  | none =>
    have hnull := ptrIsNull_144_none hpre hp
    obtain ⟨t₂, hr₂, ha₂⟩ := input_bra (P := P) (L := L) (g := g) (b := 183)
      Flow.code_178 ha₁ (by decide +kernel) (by input_values; rw [hnull]) rfl
      (by decide +kernel) (by decide) (by decide)
    obtain ⟨t₃, hr₃, ha₃⟩ := input_from_extra_param hpre hb hp ha₂
    obtain ⟨u, hr₄, hu⟩ := input_finish hpre hb ha₃
    refine ⟨u, run_rtg (run_comp (run_comp (run_comp hr₁ hr₂) hr₃) hr₄), ?_⟩
    have hs : afterLen P = .bulkWait := by simp [afterLen, hp]
    rw [hs]
    exact input_restore hpre hwg rfl hu (by decide +kernel) input_bulk_values rfl rfl
      (by simp) (by simp) rfl rfl

/-- A present main-length pointer supplies the updated padded main length. -/
theorem step_lenOrig (hpre : Pre P L mem0) (hb : eOf L g < P.b)
    (d : D) (hd : d.site = .lenOrig) : (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hi hc hf
  have hpc : d.site.pc = 168 := by rw [hd]; rfl
  have ha := input_at_source d hat hi hpc (by rw [hd]; rfl) (by decide +kernel) (by
    intro r hr
    change r ∈ [459, 460, 463, 465, 466, 467, 469, 2880, 2991, 2992, 2993, 2994, 2995,
      2996, 2997, 2998, 2999, 3001, 3140] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals input_values)
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_168)
  rw [← ha.1] at hf
  have hr : t.regs 3140 = some (b64 ((paramWord L 80 8 + 4 * eOf L g) % 2 ^ 64)) := by
    exact input_reg ha (r := 3140) (by decide +kernel)
  obtain ⟨a, bs, he, hu⟩ := fires_input (ty := .int .s 32) rfl rfl ha.2.1 hr
    (Nat.mod_lt _ (by decide)) (Thread.paramAddr_mod4 (Thread.paramWord_80_mod4 hpre) g)
    (by rw [ha.1]; decide +kernel) hf
  rcases hrb : rebuild 3 bs with err | v
  · exact Or.inl (Or.inl (by simp [next, nextSite, hd, he, hrb]))
  by_cases hv : v = b32 (P.topkLen (eOf L g))
  · have h1 : At u 169 (inputFacts P L g 169) :=
      input_afterLoad ha hu hrb (by simpa [inputValue] using hv)
        (by decide +kernel)
    obtain ⟨u₂, hr₂, h₂⟩ := input_bra_uncond Flow.code_169 h1 (by decide +kernel)
      (by decide) (by decide)
    obtain ⟨u₃, hr₃, h₃⟩ := input_round_main hpre hb h₂
    obtain ⟨u₄, hr₄, h₄⟩ := input_to_extra hpre hb hi.wg (read := true) rfl h₃
    exact Or.inl (Or.inr ⟨_, u₄, by simp [next, nextSite, hd, he, hrb, hv],
      (run_rtg (run_comp hr₂ hr₃)).trans hr₄, h₄⟩)
  · exact Or.inl (Or.inl (by simp [next, nextSite, hd, he, hrb, hv]))

/-- A present extra-length pointer supplies the extra padded count and reaches the first wait. -/
theorem step_lenExtra (hpre : Pre P L mem0) (hb : eOf L g < P.b)
    (d : D) (hd : d.site = .lenExtra) : (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hi hc hf
  have hpc : d.site.pc = 181 := by rw [hd]; rfl
  have hs : t.sub = 0 := by
    have h := hi.subLt
    rw [hd] at h
    change d.sub < 1 at h
    have hdsub : d.sub = 0 := by omega
    exact hat.2.1.trans hdsub
  have htp : t.pc = 181 := hat.1.trans hpc
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_181)
  rw [← htp] at hf
  have hr : t.regs 3142 = some (b64 ((paramWord L 144 8 + 4 * eOf L g) % 2 ^ 64)) :=
    reg_value hat (by rw [hpc]; decide +kernel)
  obtain ⟨a, bs, he, hu⟩ := fires_input (ty := .int .s 32) rfl rfl hs hr
    (Nat.mod_lt _ (by decide)) (Thread.paramAddr_mod4 (Thread.paramWord_144_mod4 hpre) g)
    (by rw [htp]; decide +kernel) hf
  rcases hrb : rebuild 3 bs with err | v
  · exact Or.inl (Or.inl (by simp [next, nextSite, hd, he, hrb]))
  by_cases hv : v = b32 (P.extraTopkLen (eOf L g)) ∧ d.origLenRead = P.topkLenBase.isSome
  · have ha := input_at_source d hat hi hpc (by rw [hd]; rfl) (by decide +kernel) (by
      intro r hr
      change r ∈ [459, 460, 463, 465, 466, 467, 469, 470, 2880, 2991, 2992, 2993, 2994,
        2995, 2996, 2997, 2998, 2999, 3001, 3142] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals first | exact input_orig_padded_word hpre hb d hv.2 | input_values)
    have h1 : At u 182 (inputFacts P L g 182) :=
      input_afterLoad ha hu hrb (by simpa [inputValue] using hv.1)
        (by decide +kernel)
    obtain ⟨u₂, hr₂, h₂⟩ := input_bra_uncond Flow.code_182 h1 (by decide +kernel)
      (by decide) (by decide)
    obtain ⟨u₃, hr₃, h₃⟩ := input_finish hpre hb h₂
    refine Or.inl (Or.inr ⟨{init P L g with site := .bulkWait}, u₃,
      by simp [next, nextSite, hd, he, hrb, hv],
      run_rtg (run_comp hr₂ hr₃), ?_⟩)
    exact input_restore hpre hi.wg (read := false) rfl h₃ (by decide +kernel)
      input_bulk_values rfl rfl (by simp) (by simp) rfl rfl
  · exact Or.inl (Or.inl (by simp [next, nextSite, hd, he, hrb, hv]))

private theorem sink_word_aligned (hpre : Pre P L mem0) :
    (paramWord L 88 8 + 4 * head L g) % 2 ^ 64 % 4 = 0 := by
  have hp : paramWord L 88 8 % 4 = 0 := by
    cases hs : P.sinkBase with
    | none => rw [paramWord_88_zero hpre hs, Nat.zero_mod]
    | some x =>
      have hb := hpre.paramSink
      rw [hs] at hb
      exact Thread.paramWord_mod4_of (fun k hk => by simpa using hb.1 k hk) hb.2.1
  rw [Nat.mod_mod_of_dvd _ (show 4 ∣ 2 ^ 64 by decide)]
  omega

private theorem sink_scale {v : Value} {s : ℝ} {t : TState}
    (hs : P.sink (head L g) = some s) (hv : valFloat .f32 v = .ok s)
    (ha : At t 157 ((932, v) :: inputFacts P L g 156)) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u 158 (inputFacts P L g 158) := by
  let op : Op := .float {
    op := .mul, ty := ⟨.f32, 1⟩, ftz := true, dsts := [some 2880],
    srcs := [.reg 932, .f32imm 1069066811] }
  have hc : kernel.code[157]? = some ⟨none, op⟩ := Flow.code_157
  have hval : valFloat .f32 (b32 1069066811) = .ok log2e := by
    have h := valFloat_b32 (by decide : 1069066811 < 2 ^ 64) f32Value_log2e
    convert h using 1
    norm_num [sinkLog2Factor]
  have hi : Assumption.readERealOpnd t .f32 (.f32imm 1069066811) =
      some (.ok (log2e : EReal)) := readEReal_of_valFloat hval
  have hr : Assumption.readERealOpnd t .f32 (.reg 932) = some (.ok (s : EReal)) := by
    rw [readERealOpnd_reg ha.2.2.2.2.1]
    exact readEReal_of_valFloat hv
  have he : execLocalA asms L g t op =
      .ok (PTX.next (setReg t 2880 (sinkReg P L g))) := by
    apply Assumption.execLocalA_idealReal (f := .mul .f32) rfl (by decide)
      (fun a ha l i state _ => asms_segment_free (L := l) (g := i) state a
        (List.mem_cons_of_mem _ ha))
    change Assumption.bindRead (Assumption.readERealOpnd t .f32 (.reg 932)) (fun x =>
      Assumption.bindRead (Assumption.readERealOpnd t .f32 (.f32imm 1069066811)) fun y =>
        (Assumption.mulEReal x y).map (fun z =>
          .ok (PTX.next (setReg t 2880 (Assumption.erealValue .f32 z))))) = _
    rw [hr, hi]
    simp only [Assumption.bindRead, mulEReal_coe, Option.map_some,
      erealValue_coe, sinkReg_some hs]
  have hat := ha.mono ha.2.2.2.2.2
  refine ⟨_, run_local hc rfl ha he, (hat.set (not_mem_factsFrom (by decide +kernel))).mono ?_⟩
  refine holds_of_pointwise fun r h => ?_
  have hproj : ∀ r ∈ startLive 158, r = 2880 ∨ r ∈ startLive 156 := by decide +kernel
  rcases hproj r h with rfl | h'
  · simp [PTX.next, setReg, inputValue]
  · have hne : r ≠ 2880 := fun h => (by decide +kernel : 2880 ∉ startLive 156) (h ▸ h')
    simpa [PTX.next, setReg, Function.update_of_ne hne] using
      (holds_mem hat.2.2.2.2 (mem_factsFrom h') : t.regs r = some (inputValue P L g r))

private theorem input_batch_test (hpre : Pre P L mem0) (hb : eOf L g < P.b) {t : TState}
    (h : At t 158 (inputFacts P L g 158)) :
    ∃ u, run kernel asms L g 3 t = some u ∧ At u 161 (inputFacts P L g 161) := by
  have h2991 : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) :=
    input_reg h (r := 2991) (by decide +kernel)
  obtain ⟨u, hr, hu⟩ := input_param hpre h (w := 32) Flow.code_158
    (supplied_int (off := 0) (x := P.b) hpre.paramB (by decide))
    (by decide) (by decide) h2991 rfl rfl (by rw [paramElem_of_ne (by decide)]; rfl)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide)
  have hv : ∃ v, run kernel asms L g 1 u = some v ∧ At v 160 (inputFacts P L g 160) := by
    dsimp only [inputFacts] at hu ⊢
    seg_fp hu using
      (input_values)
      (simp only [Thread.geBatch, Thread.ctaidY, eOf, ctaidY, Thread.ctaOf, ctaOf])
  obtain ⟨v, hv, h⟩ := hv
  obtain ⟨w, hw, h⟩ := input_bra (P := P) (L := L) (g := g) (b := 161)
    Flow.code_160 h (by decide +kernel) (by input_values; rw [geBatch_false hpre hb]) rfl
    (by decide +kernel) (by decide) (by decide)
  exact ⟨w, run_comp (run_comp hr hv) hw, h⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem input_main_pointer (hpre : Pre P L mem0) {t : TState}
    (ha : At t 161 (inputFacts P L g 161)) :
    ∃ u, run kernel asms L g 4 t = some u ∧ At u 165 (inputFacts P L g 165) := by
  have hw := warpOf_lt (g := g) hpre
  obtain ⟨t₁, hr₁, ha₁⟩ : ∃ v, run kernel asms L g 2 t = some v ∧
      At v 163 (inputFacts P L g 163) := by
    dsimp only [inputFacts] at ha ⊢
    seg_fp ha using
      (try input_values)
      (try (rw [truncBits_int_1]))
      (try norm_bits)
      (try rfl)
  have h2991 : t₁.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) :=
    input_reg ha₁ (r := 2991) (by decide +kernel)
  obtain ⟨t₂, hr₂, ha₂⟩ := input_param hpre ha₁ (w := 64) Flow.code_163 (supplied_80 hpre)
    (by decide) (by decide) h2991 rfl rfl (by rw [paramElem_of_ne (by decide)]; rfl)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide)
  obtain ⟨u, hr₃, hu⟩ : ∃ u, run kernel asms L g 1 t₂ = some u ∧
      At u 165 (inputFacts P L g 165) := by
    dsimp only [inputFacts] at ha₂ ⊢
    seg_fp ha₂ using input_values
  exact ⟨u, run_comp (run_comp hr₁ hr₂) hr₃, hu⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem input_after_sink (hpre : Pre P L mem0) (hb : eOf L g < P.b)
    (hwg : wgOf L g = 0) {t : TState} (ha : At t 158 (inputFacts P L g 158)) :
    ∃ u, Relation.ReflTransGen (Tau kernel asms L g) t u ∧
      (code P L g).Good (some {init P L g with site := afterSink P}) u := by
  obtain ⟨t₁, hr₁, ha₁⟩ := input_batch_test hpre hb ha
  obtain ⟨t₂, hr₂, ha₂⟩ := input_main_pointer hpre ha₁
  cases hp : P.topkLenBase with
  | some x =>
    have hnull := ptrIsNull_80_some hpre hp
    obtain ⟨t₃, hr₃, ha₃⟩ := input_bra (P := P) (L := L) (g := g) (b := 166)
      Flow.code_165 ha₂ (by decide +kernel) (by input_values; rw [hnull]) rfl
      (by decide +kernel) (by decide) (by decide)
    have he : eOf L g < 2 ^ 31 := lt_trans hb hpre.bLt
    obtain ⟨u, hr₄, hu⟩ : ∃ u, run kernel asms L g 2 t₃ = some u ∧
        At u 168 (inputFacts P L g 168) := by
      dsimp only [inputFacts] at ha₃ ⊢
      seg_fp ha₃ using
        (try input_values)
        (try nf_simp)
        (try omega)
    refine ⟨u, run_rtg (run_comp (run_comp (run_comp hr₁ hr₂) hr₃) hr₄), ?_⟩
    have hs : afterSink P = .lenOrig := by simp [afterSink, hp]
    rw [hs]
    refine input_restore hpre hwg (read := false) rfl hu (by decide +kernel) ?_ rfl rfl
      (by simp) (by simp) rfl rfl
    intro r hr
    change r ∈ [459, 460, 463, 465, 466, 467, 469, 2880, 2991, 2992, 2993, 2994, 2995,
      2996, 2997, 2998, 2999, 3001, 3140] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals rfl
  | none =>
    have hnull := ptrIsNull_80_none hpre hp
    obtain ⟨t₃, hr₃, ha₃⟩ := input_bra (P := P) (L := L) (g := g) (b := 170)
      Flow.code_165 ha₂ (by decide +kernel) (by input_values; rw [hnull]) rfl
      (by decide +kernel) (by decide) (by decide)
    obtain ⟨t₄, hr₄, ha₄⟩ := input_from_main_param hpre hb hp ha₃
    obtain ⟨t₅, hr₅, ha₅⟩ := input_round_main hpre hb ha₄
    have hc := input_orig_padded_word hpre hb {init P L g with site := .lenExtra}
      (by simp [init, hp])
    obtain ⟨u, hr₆, hu⟩ := input_to_extra hpre hb hwg hc ha₅
    refine ⟨u, (run_rtg (run_comp (run_comp (run_comp (run_comp hr₁ hr₂) hr₃) hr₄) hr₅)).trans
      hr₆, ?_⟩
    simpa [afterSink, hp] using hu

/-- The optional sink loads a finite value and scales it by the compiled binary32 constant. -/
theorem step_sink (hpre : Pre P L mem0) (hb : eOf L g < P.b)
    (d : D) (hd : d.site = .sink) : (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hi hc hf
  have hpc : d.site.pc = 156 := by rw [hd]; rfl
  have ha := input_at_source d hat hi hpc (by rw [hd]; rfl) (by decide +kernel) (by
    intro r hr
    change r ∈ [459, 460, 463, 465, 466, 467, 2990, 2991, 2992, 2993, 2994, 2995,
      2996, 2997, 2998, 2999, 3138] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals input_values)
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_156)
  rw [← ha.1] at hf
  have hr : t.regs 3138 = some (b64 ((paramWord L 88 8 + 4 * head L g) % 2 ^ 64)) :=
    input_reg ha (r := 3138) (by decide +kernel)
  obtain ⟨a, bs, he, hu⟩ := fires_input (ty := .float .f32) rfl rfl ha.2.1 hr
    (Nat.mod_lt _ (by decide)) (sink_word_aligned hpre)
    (by rw [ha.1]; decide +kernel) hf
  rcases hrb : rebuild 3 bs with err | v
  · exact Or.inl (Or.inl (by simp [next, nextSite, hd, he, hrb]))
  cases hs : P.sink (head L g) with
  | none => exact Or.inl (Or.inl (by simp [next, nextSite, hd, he, hrb, hs]))
  | some s =>
    by_cases hv : (valFloat .f32 v).toOption = some s
    · have hfv : valFloat .f32 v = .ok s := by
        cases h : valFloat .f32 v <;> simp_all [Except.toOption]
      have hu' : At u 157 ((932, v) :: inputFacts P L g 156) := by
        rw [hu, afterLoad_ok ha.2.1 ha.2.2.1 hrb]
        have ha' := ha.set (v := v) (not_mem_factsFrom (by decide +kernel : 932 ∉ startLive 156))
        exact ⟨ha'.1, rfl, rfl, ha'.2.2.2.1, ha'.2.2.2.2⟩
      obtain ⟨u₁, hr₁, ha₁⟩ := sink_scale hs hfv hu'
      obtain ⟨u₂, hr₂, ha₂⟩ := input_after_sink hpre hb hi.wg ha₁
      exact Or.inl (Or.inr ⟨{init P L g with site := afterSink P}, u₂,
        by simp [next, nextSite, hd, he, hrb, hs, hv], (run_rtg hr₁).trans hr₂, ha₂⟩)
    · exact Or.inl (Or.inl (by simp [next, nextSite, hd, he, hrb, hs, hv]))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
