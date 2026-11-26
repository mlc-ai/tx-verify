-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StrictInv2
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StrictWalkD
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Base
public import Lemmas.Flow.StepsQLd
public import Lemmas.Flow.StepsQD
public import Lemmas.Flow.SegQJump

@[expose] public section

/-! # Helpers for the index warp's strict steps

The strict counterparts (`Code.StepForQ (QT ixQt) (IxWf P)`) of the helpers of `Index/Base.lean`:
`one_elQ`/`ixq_site` open a one-element site's state, `pollQ` is a poll (the wait, the branch on
its predicate, the jump back), `pairQ` an element of an index pair's `.nc` load, `stQ` an element
of a coordinate pair's store. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Flow.Havoc PTX.Flow.Tagged

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

/-- A zero-length strict segment between tables of the same state. -/
theorem segq_weaken {a : Nat} {F G : List (Nat × Value)} (h : ∀ R, Holds R F → Holds R G) :
    SegQ kernel Assumptions.all L g (QT ixQt) a F a G := by
  intro t ht hQ
  obtain ⟨h1, h2, h3, h4, h5⟩ := ht
  exact ⟨t, .refl, ⟨h1, h2, h3, h4, h _ h5⟩, hQ⟩

/-- The tags of the facts of a state are untouched by an event of one element at a site: a site of
one element is stepped at element 0. -/
theorem one_elQ {d : D} (h1 : d.site.elems = 1) {e : Event}
    (h : (code P L g).StepForQ (QT ixQt) (IxWf P) { d with el := 0 } e) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  obtain ⟨s, el, ac, c⟩ := d
  intro t u ins hat hinv hc hq hw hf
  have hel : el = 0 := by
    have : el < s.elems := hinv
    have h1' : s.elems = 1 := h1
    omega
  subst hel
  exact h ins hat hinv hc hq hw hf

set_option hygiene false in
/-- Open a one-element site's state `d` (hypothesis `hs` names its site) at element 0. -/
macro "ixq_site" : tactic => `(tactic| (
  obtain ⟨s, el, ac, c⟩ := d
  dsimp only at hs; subst hs
  refine one_elQ rfl ?_))

/-- The tags of an empty environment hold. -/
theorem typed_nil {t : TState} : Typed ([] : Env) t := fun r tg h => by simp at h

/-- **A poll** at `pc` (the branch on its predicate at `pc + 1` to `tgt`, the jump back at
`pc + 2`) at a state of element 0: on success the site `s` by the segment `seg`. -/
theorem pollQ {d : D} {s : IxSite} {pc r base tgt : Nat} {off : Int} {par : Opnd}
    {acq : Bool} {sc : MbarScope} (hp : d.site.pc = pc)
    (hc : kernel.code[pc]? = some ⟨none, .mbarWait r base off par acq sc⟩)
    (hb : kernel.code[pc + 1]? = some ⟨some (r, false), .bra tgt false⟩)
    (hj : kernel.code[pc + 2]? = some ⟨none, .bra pc false⟩)
    (hoff : r ∉ ixLive pc) (he : d.el = 0)
    (hn : ∀ m q ok sc', succ P L g d ⟨d.site.pc, .wait m q ok acq sc'⟩ =
      some (some (if ok then { d with site := s } else d)))
    (hq : Code.afterWrites ixQt pc [(r, .pred)] = true)
    (hq1 : tagsIn (ixQt (pc + 1 + 1)) (ixQt (pc + 1)) = true)
    (hq2 : tagsIn (ixQt tgt) (ixQt (pc + 1)) = true)
    (hq3 : tagsIn (ixQt pc) (ixQt (pc + 2)) = true)
    (seg : SegQ kernel Assumptions.all L g (QT ixQt) tgt (ixFacts P L g d.c d.site) s.pc
      (ixFacts P L g d.c s)) (e : Event) : (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  have ha : ∀ x : D, x.el = 0 → D.acc x = [] := fun x hx => by
    simp only [D.acc, hx]
  have hi : ∀ x : D, x.el = 0 → (code P L g).inv x := fun x hx => by
    change x.el < x.site.elems; rw [hx]; exact IxSite.elems_pos _
  intro t u ins hat hinv hc' hq' hw hf
  refine Code.waitQ (C := code P L g) (qt := ixQt) (ex := []) (Wf := IxWf P)
    (dst := fun ok => if ok then { d with site := s } else d)
    (by show kernel.code[d.site.pc]? = _; rw [hp]; exact hc)
    (by change _ ∉ (factsFrom _ _).map Prod.fst; rw [factsFrom_keys, hp]; exact hoff)
    hn he (ha d he) (fun ok => ?_) (fun ok => ?_) (fun ok => ?_) (fun _ _ => typed_nil)
    (by show Code.afterWrites ixQt d.site.pc _ = _; rw [hp]; exact hq) (fun ok => ?_) e
    ins hat hinv hc' hq' hw hf
  · cases ok <;> exact he
  · cases ok
    · exact ha d he
    · exact ha { d with site := s } he
  · cases ok
    · exact hi d he
    · exact hi { d with site := s } he
  · cases ok
    · change SegQ _ _ _ _ _ (d.site.pc + 1) _ d.site.pc _; rw [hp]
      refine SegQ.comp (b := pc + 1 + 1) (G := ixFacts P L g d.c d.site)
        (SegQ.branch false hb bra_rule noSegments.segFreePc hq1) ?_
      exact SegQ.jmp hj (fun t _ => bra_rule t) noSegments.segFreePc hq3
    · change SegQ _ _ _ _ _ (d.site.pc + 1) _ s.pc _; rw [hp]
      exact SegQ.comp (SegQ.branch true hb bra_rule noSegments.segFreePc hq2) seg

/-- **An element of an index pair** at site `s` (pc `pc`): the payload is a 32-bit word; after the
second element the state `nf` of the pair's two words by the segment `seg`, from the facts with the
words' registers `r0 r1` (the first word is the state's `w0`). -/
theorem pairQ {d : D} {nf : BitVec 64 → BitVec 64 → D} {a : MemAccess}
    {pc base w r0 r1 : Nat} {sp : Space}
    (hp : d.site.pc = pc) (hld : isLd d.site = true) (h2 : d.site.elems = 2)
    (hc : kernel.code[pc]? = some ⟨none, .mem a⟩) (hl : (Op.mem a).isLocal = false)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true) (hregs : a.regs = [r0, r1]) (hr01 : r0 ≠ r1)
    (hoff : ∀ x ∈ ixLive pc, x ∉ a.regs)
    (hn : ∀ x bs, succ P L g d ⟨d.site.pc, .nc x bs⟩ = ncPair ⟨d.site.pc, .nc x bs⟩ d nf)
    (hn0 : ∀ y0 y1, (nf y0 y1).el = 0)
    (hq : Code.afterWrites ixQt pc [(r0, .bits 32), (r1, .bits 32)] = true)
    (seg : ∀ y, SegQ kernel Assumptions.all L g (QT ixQt) (pc + 1)
      ((r0, .bits 32 d.w0) :: (r1, .bits 32 y) :: ixFacts P L g d.c d.site)
      (nf d.w0 y).site.pc (ixFacts P L g (nf d.w0 y).c (nf d.w0 y).site)) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  have hi0 : ∀ y0 y1, (code P L g).inv (nf y0 y1) := fun y0 y1 => by
    change (nf y0 y1).el < (nf y0 y1).site.elems
    rw [hn0]; exact IxSite.elems_pos _
  intro t u ins hat hinv hc' hq' hw hf
  refine Code.ldvNcDQ (C := code P L g) (qt := ixQt) (ex := []) (Wf := IxWf P)
    (dok := fun y => ldNext d y nf) (y0 := d.w0) (live := ixLive d.site.pc)
    (val := ixVal P L g d.c)
    (by show kernel.code[d.site.pc]? = _; rw [hp]; exact hc) hl hru hloc hb hk hsem hnc hregs hr01
    (fun e he => he.nc) (fun hm => ?_) (fun x bs y hy => ?_) (fun hm y => ?_) rfl
    (by rw [hp]; exact hoff) (fun _ _ => typed_nil)
    (by show Code.afterWrites ixQt d.site.pc _ = _; rw [hp]; exact hq) (fun hm y => ?_) e
    ins hat hinv hc' hq' hw hf
  · have h : ¬ d.el + 1 < 2 := hm
    obtain ⟨k, hk⟩ : ∃ k, d.el = k + 1 := ⟨d.el - 1, by omega⟩
    simp only [D.acc, hk, hld, Bool.cond_true]
  · refine (hn x bs).trans ?_
    simp only [ncPair, hy]
  · obtain ⟨he, hacc, hel⟩ := ld_more (y := y) (nf := nf) hld h2 hm
    rw [he]
    exact ⟨rfl, rfl, hacc, rfl, hel⟩
  · rw [ld_last (y := y) (nf := nf) hm]
    refine ⟨hn0 _ _, ?_, hi0 _ _, ?_⟩
    · simp only [D.acc, hn0]
    · change SegQ _ _ _ _ _ (d.site.pc + 1) _ _ _; rw [hp]; exact seg y

/-- **An element of a coordinate pair's store**: after the second, the state `n` by the segment
`seg`. -/
theorem stQ {d n : D} {a : MemAccess} {pc : Nat} (hp : d.site.pc = pc)
    (hld : isLd d.site = false) (h2 : d.site.elems = 2)
    (hc : kernel.code[pc]? = some ⟨none, .mem a⟩) (hst : a.kind = .store)
    (hlen : a.srcs.length = 2)
    (hn : ∀ e, succ P L g d e = some (some (stNext d n))) (hn0 : n.el = 0)
    (hna : isLd n.site = false) (hq : Code.afterWrites ixQt pc [] = true)
    (seg : SegQ kernel Assumptions.all L g (QT ixQt) (pc + 1) (ixFacts P L g d.c d.site)
      n.site.pc (ixFacts P L g n.c n.site)) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  have hacc : ∀ x : D, isLd x.site = false → D.acc x = [] := fun x hx => by
    unfold D.acc; split <;> simp only [hx, Bool.cond_false]
  intro t u ins hat hinv hc' hq' hw hf
  refine Code.vstQ (C := code P L g) (qt := ixQt) (ex := []) (Wf := IxWf P) (dn := stNext d n)
    (by show kernel.code[d.site.pc]? = _; rw [hp]; exact hc) hst hn (hacc d hld)
    (fun hm => ?_) (fun _ _ => typed_nil)
    (by show Code.afterWrites ixQt d.site.pc _ = _; rw [hp]; exact hq) (fun hm => ?_) e
    ins hat hinv hc' hq' hw hf
  · have h : d.el + 1 < 2 := by rw [hlen] at hm; exact hm
    have he : stNext d n = { d with el := d.el + 1, ac := [] } := ite_eq_left h
    rw [he]
    exact ⟨rfl, rfl, hacc { d with el := d.el + 1, ac := [] } hld, rfl,
      by show d.el + 1 < d.site.elems; rw [h2]; exact h⟩
  · have h : ¬ d.el + 1 < 2 := by rw [hlen] at hm; exact hm
    have he : stNext d n = n := ite_eq_right h
    rw [he]
    refine ⟨hn0, hacc n hna, ?_, ?_⟩
    · change n.el < n.site.elems; rw [hn0]; exact IxSite.elems_pos _
    · change SegQ _ _ _ _ _ (d.site.pc + 1) _ _ _; rw [hp]; exact seg

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
