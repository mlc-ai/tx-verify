-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.Loader
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.Segment
public import Lemmas.Flow.Hooks
public import Lemmas.Flow.TensorIssue
public import Lemmas.Flow.Events
public import Lemmas.Flow.Vector

@[expose] public section

/-! # Helpers of the loader's step lemmas

The conclusion of a step (`Step`), the concrete state of an abstract one (`AtS`), the segment
pieces the steps are cut into (`SegTo`, `segTo_bra`), the invariant after a move (`inv_to`) and
the segment tactic `lw_seg`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

theorem natOf_b32 (x : Nat) : natOf (b32 x) = x % 2 ^ 32 := by
  simp [natOf, b32, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd]

theorem natOf64_b64 (x : Nat) : natOf64 (b64 x) = x % 2 ^ 64 := by
  simp [natOf64, b64, BitVec.toNat_ofNat]

/-- `mul.hi.s32` by `1431655766` and the correction by its sign bit compute `i / 3` for a loop
counter below `2 ^ 31`; the form is the one the segment evaluator leaves. -/
theorem mulhi3 (i : Nat) (hi : i < 2 ^ 31) :
    (((i % 4294967296 : Nat) : Int) * ((1431655766 : Nat) : Int) / 2 ^ 32 %
      18446744073709551616) = ((i / 3 : Nat) : Int) := by
  have h1 : (((i % 4294967296 : Nat) : Int) * ((1431655766 : Nat) : Int) / 2 ^ 32) =
      ((i / 3 : Nat) : Int) := by omega
  rw [h1]
  exact Int.emod_eq_of_lt (by omega) (by omega)

/-! ### Concrete states of the abstract ones -/

/-- The sub-step and accumulator of a state: nonzero only between the two elements of the
vector load. -/
def sub (d : D) : Nat := match d.site with | .ld1 => 1 | _ => 0
def acc (d : D) : List Value := match d.site with | .ld1 => [wordI d] | _ => []

/-- A concrete state of the abstract state `d`: its program counter, sub-step, accumulator and
register facts (`Code.AtD` of `code`). -/
def AtS (L : Launch) (g : Nat) (d : D) (t : TState) : Prop :=
  t.pc = d.site.pc ∧ t.sub = sub d ∧ t.acc = acc d ∧ t.fault = none ∧ Holds t.regs (facts L g d)

theorem AtS.of_at {L : Launch} {g : Nat} {d : D} {t : TState} (h : At t d.site.pc (facts L g d))
    (hs : sub d = 0) (ha : acc d = []) : AtS L g d t :=
  ⟨h.1, hs ▸ h.2.1, ha ▸ h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- The conclusion of a step of this role: the machine leaves it, or the thread faults (`none`, the
state after the event is dead), or it steps to `d'` at `t'` by a run of `Tau`. -/
def Step (L : Launch) (g : Nat) (d : D) (e : Event) (u : TState) : Prop :=
  (next L g d e = some none ∨
    (next L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u)) ∨
  ∃ d' t', next L g d e = some (some d') ∧
    Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ AtS L g d' t' ∧ Inv L g d'

/-- A segment of the loader's code from `pc` with facts `F` to the site of `d'`. -/
abbrev SegTo (L : Launch) (g pc : Nat) (F : List (Nat × Value)) (d' : D) : Prop :=
  ∃ k, Seg kernel asms L g k pc F d'.site.pc (facts L g d')

theorem facts_ne {L : Launch} {g pc : Nat} {d : D} {r : Nat} (hr : r ∉ Flow.live pc) :
    ∀ p ∈ factsAt L g pc d, p.1 ≠ r := by
  intro p hp he
  simp only [factsAt, Flow.factsFrom, List.mem_map] at hp
  obtain ⟨r', hr', rfl⟩ := hp
  exact hr (he ▸ hr')

/-- Facts at a program counter, restated at another whose live registers are among them. -/
theorem holds_relive {L : Launch} {g pc pc' : Nat} {d d' : D} {R : Nat → Option Value}
    (h : Holds R (factsAt L g pc d)) (hv : valueOf L g d' = valueOf L g d)
    (hl : ∀ r ∈ Flow.live pc', r ∈ Flow.live pc) : Holds R (factsAt L g pc' d') := by
  unfold factsAt at h ⊢
  rw [hv]
  exact holds_factsFrom_mono h hl

/-- A table fact at a checkpoint where the register is live. -/
theorem tbl_mem {L : Launch} {g pc : Nat} {d : D} {r : Nat} {v : Value} (hl : r ∈ Flow.live pc)
    (hv : valueOf L g d r = v) : (r, v) ∈ factsAt L g pc d :=
  hv ▸ Flow.mem_factsFrom hl

/-- No step: the site of `d'` is at the checkpoint itself. -/
theorem segTo_here {L : Launch} {g pc pc0 : Nat} {d d' : D} (hpc : d'.site.pc = pc)
    (hv : valueOf L g d' = valueOf L g d) (hl : ∀ r ∈ Flow.live pc, r ∈ Flow.live pc0) :
    SegTo L g pc (factsAt L g pc0 d) d' :=
  ⟨0, hpc ▸ Seg.weaken_end (Seg.refl _ _) fun _ hR => holds_relive hR hv (hpc ▸ hl)⟩

/-- A segment of the loader as a step. -/
theorem step_of_seg {L : Launch} {g : Nat} {d d' : D} {e : Event} {u : TState}
    {F : List (Nat × Value)} {pc : Nat} (hn : next L g d e = some (some d')) (hi : Inv L g d')
    (hs0 : sub d' = 0) (ha0 : acc d' = []) (hu : At u pc F) (hs : SegTo L g pc F d') :
    Step L g d e u := by
  obtain ⟨k, hs⟩ := hs
  obtain ⟨t', hr, ht'⟩ := hs u hu
  exact .inr ⟨d', t', hn, run_rtg hr, AtS.of_at ht' hs0 ha0, hi⟩

/-! ### The invariant after a move -/

/-- The registers of a state with its invariant: the inherited ones and the two loaded words. -/
theorem Inv.proW {L : Launch} {g : Nat} {d : D} (hi : Inv L g d) :
    ∃ P vi vn, d.pro = Pro.valW L g P vi vn := by
  obtain ⟨P, hP⟩ := hi.pro
  refine ⟨P, d.pro 1905, d.pro 467, funext fun r => ?_⟩
  unfold Pro.valW
  split_ifs with h1 h2
  · rw [h1]
  · rw [h2]
  · exact hP r h1 h2

/-- The registers the table states. -/
def tableKeys : List Nat :=
  [19, 25, 20, 21, 22, 23, 24, 469, 1904, 1903, 1902, 470, 583, 586, 588, 590, 599, 602, 603,
   578, 579, 580, 582, 585, 587, 589, 592, 594, 595, 596, 584, 593, 1950, 2053, 2054, 468, 577,
   597]

theorem tableKeys_eq (L : Launch) (g : Nat) (d : D) : (table L g d).map Prod.fst = tableKeys :=
  rfl

/-- A register the table does not state holds the state's register value. -/
theorem valueOf_pro {L : Launch} {g : Nat} {d : D} {r : Nat} (h : r ∉ tableKeys) :
    valueOf L g d r = d.pro r := by
  unfold valueOf
  have : (table L g d).lookup r = none := by
    rw [List.lookup_eq_none_iff]
    intro p hp
    have : p.1 ∈ tableKeys := by
      rw [← tableKeys_eq L g d]
      exact List.mem_map_of_mem hp
    have hne : r ≠ p.1 := fun he => h (he ▸ this)
    simpa using hne
  rw [this]
  rfl

theorem afterIter_valW {L : Launch} {g : Nat} (s : Site) (P : Pro) (vi vn : Value)
    (i n p0 p1 : Nat) (ln : Bool) :
    afterIter ⟨s, Pro.valW L g P vi vn, i, n, p0, p1, ln⟩ =
      if n = (i + 1) % 2 ^ 32 then
        ⟨.bar1, Pro.valW L g P (b32 ((i + 1) % 2 ^ 32)) vn, i + 1, n, p0, p1, ln⟩
      else
        ⟨.wait, Pro.valW L g P (b32 ((i + 1) % 2 ^ 32)) vn, i + 1, n, p0, p1, ln⟩ := by
  have hp : Function.update (Pro.valW L g P vi vn) 1905 (b32 ((i + 1) % 2 ^ 32)) =
      Pro.valW L g P (b32 ((i + 1) % 2 ^ 32)) vn := by
    funext r
    by_cases h : r = 1905
    · subst h; simp [Pro.valW]
    · simp [Pro.valW, h]
  unfold afterIter
  simp only [hp]

/-- `Inv` of `{ d with site := s }` from `hi : Inv L g d`, each fact of the new site from the old
state's or by evaluating the site's flags. -/
theorem Inv.move {L : Launch} {g : Nat} {d : D} (hi : Inv L g d) (s : Site)
    (hI : s = .ld1 ∨ s = .bar0 → (Raw.word32Of (wordI d)).getD 0 = d.i)
    (hN : s.bounded = true → (Raw.word32Of (wordN d)).getD 0 = d.n)
    (hb : s.inLoop = true → Raw.word32Of (wordI d) = some (d.i % 2 ^ 32) ∧
      Raw.word32Of (wordN d) = some d.n)
    (hl : s.inLoop = true → d.i % 2 ^ 32 ≠ d.n ∧ d.i < 2 ^ 32 + d.n)
    (hln : s = .arrive → d.ln = true) :
    Inv L g { d with site := s } :=
  ⟨hi.pro, hI, hN, hb, hl, hi.ln, hln⟩

/-- `Inv` of a state with the same site, registers, counters and lane as another (the
block-table words are free). -/
theorem Inv.data {L : Launch} {g : Nat} {d d' : D} (hi : Inv L g d) (hs : d'.site = d.site)
    (hp : d'.pro = d.pro) (hi' : d'.i = d.i) (hn : d'.n = d.n) (hl : d'.ln = d.ln) :
    Inv L g d' := by
  obtain ⟨s, p, i, n, p0, p1, l⟩ := d
  obtain ⟨s', p', i', n', p0', p1', l'⟩ := d'
  simp only at hs hp hi' hn hl
  subst hs hp hi' hn hl
  exact ⟨hi.pro, hi.wi, hi.wn, hi.bits, hi.loop, hi.ln, hi.lane⟩

/-- The `num_iters` word reads as `n` in the loop. -/
theorem Inv.getD_of_loop {L : Launch} {g : Nat} {d : D} (hi : Inv L g d)
    (h : d.site.inLoop = true) : (Raw.word32Of (wordN d)).getD 0 = d.n := by
  rw [(hi.bits h).2]
  rfl

/-- `Inv` of `{ d with site := s }` from `hi : Inv L g d`, the new facts being the old ones. -/
macro "inv_to" hi:term:max : tactic => `(tactic| (
  refine Inv.move $hi _ ?_ ?_ ?_ ?_ ?_
  · intro h
    first
      | exact ($hi).wi h
      | (rcases h with h | h <;> cases h; done)
  · intro h
    first
      | exact ($hi).wn rfl
      | exact Inv.getD_of_loop $hi rfl
      | (simp [Site.bounded, Site.inLoop] at h; done)
  · intro h
    first | exact ($hi).bits rfl | (simp [Site.inLoop] at h; done)
  · intro h
    first | exact ($hi).loop rfl | (simp [Site.inLoop] at h; done)
  · intro h
    first | exact ($hi).lane rfl | rfl | assumption | (cases h; done)))

/-! ### Loaded words -/

/-- After a one-register load whose bytes rebuild to `v`. -/
theorem at_afterLoad {t : TState} {F : List (Nat × Value)} {pc d : Nat} {v : Value}
    {bs : List (Option Byte)} (h : At t pc F) (hv : rebuild 3 bs = .ok v)
    (hd : ∀ p ∈ F, p.1 ≠ d) : At (afterLoad t [d] bs) (pc + 1) ((d, v) :: F) := by
  rw [afterLoad_ok h.2.1 h.2.2.1 hv]
  exact ⟨by simp [h.1], rfl, rfl, h.2.2.2.1, Function.update_self .., holds_update h.2.2.2.2 hd⟩

/-- A closed fact about the live registers at a site. `live_dec` unfolds the `Site.pc` of the
namespace where it is used, `live_dec c` unfolds `c`. -/
syntax "live_dec" (ppSpace colGt ident)? : tactic
macro_rules
  | `(tactic| live_dec) => `(tactic| live_dec $(Lean.mkIdent `Site.pc):ident)
  | `(tactic| live_dec $pc:ident) => `(tactic| ((try dsimp only [$pc:ident]); table_decide))

/-! ### Branches -/

/-- No assumption of the kernel has a local rule for a branch. -/
theorem asms_localRule_bra {L : Launch} {g : Nat} {t : TState} {target : Nat} {uni : Bool} :
    ∀ a ∈ asms, a.localRule L g t (.bra target uni) = none := by
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · exact Assumption.idealReal_localRule_none fun f h => by
      simp [Assumption.FloatForm.ofOp] at h
  · exact Assumption.approxExact_localRule_none fun f h => by
      simp [Assumption.ApproxForm.ofOp] at h
  all_goals first | rfl | simp [Assumptions.lg2Exact, Assumptions.divFullExact,
    Assumptions.negExact]

/-- No assumption of the kernel selects a segment at a program counter outside the software
`exp2` instances. -/
theorem asms_segFreePc {pc : Nat} (h : Assumptions.emuSites.contains pc = false) :
    Assumption.SegFreePc asms pc := by
  intro a ha L g t htpc
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · rfl
  · rfl
  · show (if Assumptions.emuSites.contains t.pc ∧ t.sub = 0 ∧ t.acc.isEmpty then _ else none) = none
    rw [htpc, h]
    simp
  all_goals rfl

/-- A conditional branch on a predicate fact `(p, .pred c)`: the segment to `d1` from the
target when `c` holds, to `d2` from the next instruction otherwise. -/
theorem segTo_bra {L : Launch} {g pc target p : Nat} {F : List (Nat × Value)} {c : Bool}
    {d1 d2 : D} (hc : kernel.code[pc]? = some ⟨some (p, false), .bra target false⟩)
    (hp : (p, Value.pred c) ∈ F) (h1 : c = true → SegTo L g target F d1)
    (h2 : c = false → SegTo L g (pc + 1) F d2)
    (hsf : Assumption.SegFreePc asms pc := by exact asms_segFreePc (by decide)) :
    SegTo L g pc F (if c then d1 else d2) := by
  have hb := Seg.bra (K := kernel) (A := asms) (L := L) (g := g) hc hp
    (fun _ _ => asms_localRule_bra) hsf
  cases c
  · obtain ⟨k, hs⟩ := h2 rfl
    exact ⟨1 + k, Seg.comp hb hs⟩
  · obtain ⟨k, hs⟩ := h1 rfl
    exact ⟨1 + k, Seg.comp hb hs⟩

/-! ### Evaluating a segment -/

/-- The table's values at a state, evaluated: the loop's table, the inherited registers of `Pro`. -/
macro "lw_values" : tactic =>
  `(tactic| simp only [valueOf, table, Pro.valW, Pro.val, Pro.table, PTX.Flow.lookupLit,
    Option.getD_some, Option.getD_none, natOf_b32, natOf64_b64, Nat.reduceEqDiff, ↓reduceIte])

/-- Close one equation between a computed and a stated register value: the ring registers are
the code's own terms (`rfl` after unfolding them), the lane predicate by arithmetic (given
`ln = decide (laneOf L g = 0)`), the others by the normal form of integer values, with the
signed rules for `mad.wide`. -/
syntax "lw_close" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| lw_close $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| first
      | (dsimp only [baseW, barW, kvW, slotW, slotKW, quotW, addW, madLoW, mulHiW, shrW,
           notW, andW, sarW, madWideW, add64W]
         all_goals (try simp only [kind_s_beq_s, kind_u_beq_s, kind_b_beq_s, ↓reduceIte, pow32]))
      | (simp only [Value.pred.injEq, $extra,*]
         try unfold laneOf
         nf_simp [PTX.compare, decide_eq_decide, ne_eq]
         omega)
      | seg_close [natOf_b32, natOf64_b64, ctaX, ctaY, ctaZ, $extra,*]
      | (nf_simp [intBits, intOf, toSigned, natOf_b32, natOf64_b64, sx32, ctaX, ctaY, ctaZ,
           $extra,*]
         all_goals (try split_ifs)
         all_goals omega))

/-- Evaluate a segment of the loader from `h` and close the facts of its end state. -/
syntax "lw_seg " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| lw_seg $h $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| seg_fp $h using
        try simp only [valueOf, table, Pro.valW, Pro.val, Pro.table, PTX.Flow.lookupLit,
          Option.getD_some, Option.getD_none, natOf_b32, natOf64_b64, Nat.reduceEqDiff,
          ↓reduceIte, $extra,*]
        all_goals lw_close [$extra,*])

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
