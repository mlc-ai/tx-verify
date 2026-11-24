-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmSteps
public import Lemmas.Flow.EventCont

@[expose] public section

/-! # Generic steps and the table's S-tile and P-store section

The step of an event instruction that continues at the next instruction and takes the machine to
a state with the same registers (`step_adv`: the barriers, `tcgen05.wait::st`, an arrival), the
one-register and two-register instruction pieces between the table's facts (`seg_two`), and the
lookups of the table's last section (`valuesX`): the S tile's words and pairs, the probabilities
as single registers, pairs and `bf16` words, and the registers that address the two Tensor Memory
accesses. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-! ### Facts at a successor pc -/

/-- Registers live at a pc are valued by the table of a state with the same table. -/
theorem holds_live {R : Nat → Option Value} {pc pc' : Nat} {d d' : D}
    (h : Holds R (factsAt L g pc d)) (hv : valueOf L g d' = valueOf L g d)
    (hl : ∀ r ∈ Flow.live pc', r ∈ Flow.live pc) : Holds R (factsAt L g pc' d') := by
  rw [factsAt, hv]
  exact Flow.holds_factsFrom_mono h hl

/-- The thread after an instruction that writes nothing, at the next pc. -/
theorem at_next_live {pc pc' : Nat} {d d' : D} {t : TState}
    (h : At t pc (factsAt L g pc d)) (hpc : pc' = pc + 1)
    (hv : valueOf L g d' = valueOf L g d) (hl : ∀ r ∈ Flow.live pc', r ∈ Flow.live pc) :
    At (PTX.next t) pc' (factsAt L g pc' d') := by
  subst hpc
  exact (At.next h).mono (holds_live h.2.2.2.2 hv hl)

/-- An instruction whose guard `@p` is false is skipped, whatever it is. -/
theorem seg_off {pc p : Nat} {op : Op} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨some (p, false), op⟩) (hp : (p, Value.pred false) ∈ F) :
    Seg kernel asms L g 1 pc F (pc + 1) F := by
  intro t h
  have hp' : t.regs p = some (.pred false) := holds_mem h.2.2.2.2 hp
  refine ⟨skip t, ?_, by simp [skip, h.1], rfl, rfl, h.2.2.2.1, h.2.2.2.2⟩
  simp [run, tauStep, out, h.2.2.2.1, h.1, hc, guardHolds, readReg, hp', bind, Except.bind, pure,
    Except.pure]

/-- The invariant at another late site of the same data. -/
theorem inv_late (hi : Inv L g d) (hl : LateSite d.site) {s : Site} (hs : LateSite s)
    (hlead : s = .arrive → g % L.block = 0) : Inv L g { d with site := s } := by
  obtain ⟨hcw, hcv, hlt⟩ := hi.late hl
  refine ⟨hi.tid, hi.ok, hi.i, fun k hk => ?_, fun k hk => ?_, ⟨fun k hk => ?_, fun hk => ?_⟩,
    hi.wb, hi.vb, fun hk => ?_, fun _ => ⟨hcw, hcv, hlt⟩, hlead, hi.re, hi.lb, hi.four, hi.bw,
    hi.wf, hi.vf⟩
  · have : s = .pre k := hk
    subst this
    exact absurd hs (by simp [LateSite])
  · have : s = .nxt k := hk
    subst this
    exact absurd hs (by simp [LateSite])
  · have : s = .pre k := hk
    subst this
    exact absurd hs (by simp [LateSite])
  · have : s = .bar0 := hk
    subst this
    exact absurd hs (by simp [LateSite])
  · have : s = .setMaxReg := hk
    subst this
    exact absurd hs (by simp [LateSite])

/-- **A step past an instruction that writes nothing, then a local segment** to the next site's
pc, with the facts of its state: the event leaves the thread at the next instruction. -/
theorem step_seg {dn : D} {n : Nat}
    (hu : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u) → u = PTX.next t)
    (hn : next L g d e = some (some dn))
    (hl : ∀ r ∈ Flow.live (d.site.pc + 1), r ∈ Flow.live d.site.pc)
    (hseg : Seg kernel asms L g n (d.site.pc + 1) (factsAt L g (d.site.pc + 1) d) dn.site.pc
      (facts L g dn))
    (hin : Inv L g dn) (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain rfl := hu hf
  have h1 : At (PTX.next t) (d.site.pc + 1) (factsAt L g (d.site.pc + 1) d) :=
    at_next_live h rfl rfl hl
  obtain ⟨t', hr, ht'⟩ := hseg.rtg h1
  exact .inl (.inr ⟨dn, t', hn, hr, ht', hin⟩)

/-- **A step past an instruction that writes nothing**: the event leaves the thread at the next
instruction, and the machine is at `dn`, whose registers are those of `d`. -/
theorem step_adv {dn : D}
    (hu : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u) → u = PTX.next t)
    (hn : next L g d e = some (some dn)) (hpc : dn.site.pc = d.site.pc + 1)
    (hv : valueOf L g dn = valueOf L g d)
    (hl : ∀ r ∈ Flow.live dn.site.pc, r ∈ Flow.live d.site.pc) (hin : Inv L g dn)
    (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain rfl := hu hf
  have h1 := At.next h
  exact .inl (.inr ⟨dn, PTX.next t, hn, .refl, ⟨by rw [hpc]; exact h1.1, h1.2.1, h1.2.2.1,
    h1.2.2.2.1, holds_live h1.2.2.2.2 hv hl⟩, hin⟩)

/-- A register not live at `pc` is no fact of the table's facts there. -/
theorem facts_ne {pc : Nat} {d : D} {r : Nat} (hr : r ∉ Flow.live pc) :
    ∀ p ∈ factsAt L g pc d, p.1 ≠ r := by
  intro p hp he
  simp only [factsAt, Flow.factsFrom, List.mem_map] at hp
  obtain ⟨r', hr', rfl⟩ := hp
  exact hr (he ▸ hr')

instance : DecidablePred IKey := fun r => by unfold IKey; infer_instance

/-- The registers of the bias pointers (`valuesR`). -/
def RKey (r : Nat) : Prop := (2141 ≤ r ∧ r < 2205) ∨ (2211 ≤ r ∧ r < 2275)

instance : DecidablePred RKey := fun r => by unfold RKey; infer_instance

theorem keys_R (d : D) : ∀ r ∈ (valuesR L g d).map Prod.fst, RKey r := by
  intro r hm
  simp only [valuesR, List.map_append, List.map_map, List.mem_append, List.mem_map,
    List.mem_range, Function.comp_apply] at hm
  unfold RKey
  rcases hm with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;> omega

/-- **Two states of different iterations** give a register that changes with neither the iteration
nor the next block's words the same value. -/
theorem valueOf_frameI {d d' : D} (h1 : d'.e = d.e) (h3 : d'.m = d.m) (h4 : d'.l = d.l)
    (hw : d'.wd = d.wd) (h5 : d'.sv = d.sv) (h6 : d'.pf = d.pf) {r : Nat} (hI : ¬ IKey r)
    (hR : ¬ RKey r) (hv : ¬ (332 ≤ r ∧ r < 397)) (hx : d'.stg = d.stg := by rfl) :
    valueOf L g d' r = valueOf L g d r := by
  have eS : valuesS L g d' = valuesS L g d := by simp only [valuesS, h1, h3, h4, hx]
  have eP : valuesP L g d' = valuesP L g d := by simp only [valuesP, h1]
  have eQ : valuesQ L g d' = valuesQ L g d := by simp only [valuesQ, h1]
  have eW : (valuesW d').lookup r = (valuesW d).lookup r := by
    simp only [valuesW, hw]
    exact lookup_valuesWf_off _ _ _ hv
  have eX : valuesX L g d' = valuesX L g d := by
    simp only [valuesX, valuesXt, D.pwV, D.pwE, h5, hx]
  have nR : ∀ x : D, (valuesR L g x).lookup r = none := fun x =>
    lookup_none_of_not_mem _ (fun hm => hR (keys_R x r hm))
  simp only [valueOf, values, lookup_append', lookup_none_of_not_mem _ (notI d' hI),
    lookup_none_of_not_mem _ (notI d hI), nR, eS, eP, eQ, eW, eX, Option.none_or]

/-! ### The table's S-tile and P-store section -/

/-- The registers of the section `valuesX`. -/
def XKey (r : Nat) : Prop :=
  r = 172 ∨ r = 506 ∨ r = 168 ∨ r = 507 ∨ r = 1522 ∨ r = 1531 ∨ r = 1544 ∨ r = 1520 ∨ r = 1529 ∨
    r = 1536 ∨ r = 1538 ∨ r = 1540 ∨ r = 1534 ∨ r = 1542 ∨ (876 ≤ r ∧ r < 940) ∨
    (2447 ≤ r ∧ r < 2479) ∨ (508 ≤ r ∧ r < 524) ∨ (1994 ≤ r ∧ r < 2018) ∨
    (1677 ≤ r ∧ r < 1709) ∨ (1415 ≤ r ∧ r < 1499) ∨ (1547 ≤ r ∧ r < 1611) ∨
    (1612 ≤ r ∧ r < 1676)

/-- The other sections hold no register of `valuesX`. -/
theorem keys_off_nonX (d : D) {r : Nat} (hr : XKey r) :
    r ∉ (valuesI L g d).map Prod.fst ∧ r ∉ (valuesS L g d).map Prod.fst ∧
      r ∉ (valuesP L g d).map Prod.fst ∧
      r ∉ (valuesQ L g d).map Prod.fst ∧ r ∉ (valuesR L g d).map Prod.fst ∧
      r ∉ (valuesW d).map Prod.fst := by
  simp only [XKey] at hr
  refine ⟨notI d (by unfold IKey; omega), fun hm => ?_, fun hm => ?_, fun hm => ?_, fun hm => ?_,
    fun hm => ?_⟩
  · simp only [valuesS, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    omega
  · simp only [valuesP, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    omega
  · simp only [valuesQ, List.map_append, List.map_map, List.mem_append, List.mem_map,
      List.mem_range, Function.comp_apply] at hm
    rcases hm with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;> omega
  · simp only [valuesR, List.map_append, List.map_map, List.mem_append, List.mem_map,
      List.mem_range, Function.comp_apply] at hm
    rcases hm with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;> omega
  · have := keys_words d r hm
    simp only [WordKey] at this
    omega

/-- A register of the section `valuesX` is looked up in it. -/
theorem valueOf_X (d : D) {r : Nat} (hr : XKey r) :
    valueOf L g d r = ((valuesX L g d).lookup r).getD (b32 0) := by
  obtain ⟨hI, hS, hP, hQ, hR, hW⟩ := keys_off_nonX (L := L) (g := g) d hr
  simp only [valueOf, values, lookup_append', lookup_none_of_not_mem _ hI,
    lookup_none_of_not_mem _ hS, lookup_none_of_not_mem _ hP, lookup_none_of_not_mem _ hQ,
    lookup_none_of_not_mem _ hR, lookup_none_of_not_mem _ hW, Option.none_or]

/-- The registers of the tail `valuesXt`. -/
def XtKey (r : Nat) : Prop :=
  (876 ≤ r ∧ r < 940) ∨ (2447 ≤ r ∧ r < 2479) ∨ (508 ≤ r ∧ r < 524) ∨
    (1994 ≤ r ∧ r < 2018) ∨ (1677 ≤ r ∧ r < 1709)

theorem XtKey.xkey {r : Nat} (h : XtKey r) : XKey r := by
  unfold XtKey at h; unfold XKey; omega

/-- A register of the tail is looked up in it. -/
theorem lookup_valuesX_tail (d : D) {r : Nat} (h : XtKey r) :
    (valuesX L g d).lookup r = (valuesXt d).lookup r := by
  have b1 : (r == 172) = false := by unfold XtKey at h; simp; omega
  have b2 : (r == 506) = false := by unfold XtKey at h; simp; omega
  have b3 : (r == 168) = false := by unfold XtKey at h; simp; omega
  have b4 : (r == 507) = false := by unfold XtKey at h; simp; omega
  have b5 : (r == 1522) = false := by unfold XtKey at h; simp; omega
  have b6 : (r == 1531) = false := by unfold XtKey at h; simp; omega
  have b7 : (r == 1544) = false := by unfold XtKey at h; simp; omega
  have b8 : (r == 1520) = false := by unfold XtKey at h; simp; omega
  have b9 : (r == 1529) = false := by unfold XtKey at h; simp; omega
  have b10 : (r == 1536) = false := by unfold XtKey at h; simp; omega
  have b11 : (r == 1538) = false := by unfold XtKey at h; simp; omega
  have b12 : (r == 1540) = false := by unfold XtKey at h; simp; omega
  have b13 : (r == 1534) = false := by unfold XtKey at h; simp; omega
  have b14 : (r == 1542) = false := by unfold XtKey at h; simp; omega
  have hs : (valuesXs d.stg.fsv d.stg.ow d.stg.al).lookup r = none := by
    refine lookup_none_of_not_mem _ (fun hm => ?_)
    have := keys_Xs _ _ _ r hm
    unfold XtKey at h
    omega
  simp only [valuesX, lookup_append', List.lookup, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11,
    b12, b13, b14, hs, Option.or_none, Option.none_or]

/-- A register of the tail has the value of the tail's entry. -/
theorem valueOf_Xt (d : D) {r : Nat} (h : XtKey r) :
    valueOf L g d r = ((valuesXt d).lookup r).getD (b32 0) := by
  rw [valueOf_X d h.xkey, lookup_valuesX_tail d h]

theorem lookup_Xt_sv (d : D) {r : Nat} (h : 876 ≤ r ∧ r < 876 + 64) :
    (valuesXt d).lookup r = some (d.sv (r - 876)).1 := by
  unfold valuesXt
  rw [lookup_append', lookup_range_map, if_pos h]
  simp

theorem lookup_Xt_svp (d : D) {r : Nat} (h : 2447 ≤ r ∧ r < 2447 + 32) :
    (valuesXt d).lookup r =
      some (joinValue (d.sv (2 * (r - 2447))).1 (d.sv (2 * (r - 2447) + 1)).1) := by
  unfold valuesXt
  rw [lookup_append', lookup_range_map, if_neg (by omega), Option.none_or, lookup_append',
    lookup_range_map, if_pos h]
  simp

theorem lookup_Xt_rP (d : D) {r : Nat} (h : 508 ≤ r ∧ r < 508 + 16) :
    (valuesXt d).lookup r = some (d.stg.pv (colR (r - 508))) := by
  unfold valuesXt
  rw [lookup_append', lookup_range_map, if_neg (by omega), Option.none_or, lookup_append',
    lookup_range_map, if_neg (by omega), Option.none_or, lookup_append', lookup_range_map,
    if_pos h]
  simp

theorem lookup_Xt_rd (d : D) {r : Nat} (h : 1994 ≤ r ∧ r < 1994 + 24) :
    (valuesXt d).lookup r = some (joinValue (d.stg.pv (2 * pairW (r - 1994)))
      (d.stg.pv (2 * pairW (r - 1994) + 1))) := by
  unfold valuesXt
  rw [lookup_append', lookup_range_map, if_neg (by omega), Option.none_or, lookup_append',
    lookup_range_map, if_neg (by omega), Option.none_or, lookup_append', lookup_range_map,
    if_neg (by omega), Option.none_or, lookup_append', lookup_range_map, if_pos h]
  simp

theorem lookup_Xt_pw (d : D) {r : Nat} (h : 1677 ≤ r ∧ r < 1677 + 32) :
    (valuesXt d).lookup r = some (d.pwV (r - 1677)) := by
  unfold valuesXt
  rw [lookup_append', lookup_range_map, if_neg (by omega), Option.none_or, lookup_append',
    lookup_range_map, if_neg (by omega), Option.none_or, lookup_append', lookup_range_map,
    if_neg (by omega), Option.none_or, lookup_append', lookup_range_map, if_neg (by omega),
    Option.none_or, lookup_range_map, if_pos h]

/-- `%r(47 + k)`: the probability of column `colR k`. -/
theorem valueOf_rP (d : D) {k : Nat} (hk : k < 16) :
    valueOf L g d (508 + k) = d.stg.pv (colR k) := by
  rw [valueOf_Xt d (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))),
    lookup_Xt_rP d ⟨by omega, by omega⟩]
  simp

/-- `%r(1216 + w)`: the stored word `w`. -/
theorem valueOf_pw (d : D) {w : Nat} (hw : w < 32) : valueOf L g d (1677 + w) = d.pwV w := by
  rw [valueOf_Xt d (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))),
    lookup_Xt_pw d ⟨by omega, by omega⟩]
  simp

/-- `%rd(46 + q)`: the pair of columns `2 (pairW q)` and `2 (pairW q) + 1`. -/
theorem valueOf_rd (d : D) {q : Nat} (hq : q < 24) :
    valueOf L g d (1994 + q) = joinValue (d.stg.pv (2 * pairW q))
      (d.stg.pv (2 * pairW q + 1)) := by
  rw [valueOf_Xt d (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))),
    lookup_Xt_rd d ⟨by omega, by omega⟩]
  simp

/-- `%r(415 + k)`: word `k` of the S tile. -/
theorem valueOf_sv (d : D) {k : Nat} (hk : k < 64) : valueOf L g d (876 + k) = (d.sv k).1 := by
  rw [valueOf_Xt d (Or.inl ⟨by omega, by omega⟩), lookup_Xt_sv d ⟨by omega, by omega⟩]
  simp

/-- `%rd(499 + q)`: the pair of the S words `2 q` and `2 q + 1`. -/
theorem valueOf_svp (d : D) {q : Nat} (hq : q < 32) :
    valueOf L g d (2447 + q) = joinValue (d.sv (2 * q)).1 (d.sv (2 * q + 1)).1 := by
  rw [valueOf_Xt d (Or.inr (Or.inl ⟨by omega, by omega⟩)),
    lookup_Xt_svp d ⟨by omega, by omega⟩]
  simp

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
