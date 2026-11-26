-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Walk
public import Lemmas.Flow.NcLoadVecU
public import Lemmas.Flow.NcLoadDU
public import Lemmas.Flow.ShflU
public import Lemmas.Flow.WaitU
public import Lemmas.Flow.AdvanceU
public import Lemmas.Flow.StoreU
public import Lemmas.Flow.SegJump
public import Lemmas.Flow.IssueNext
public import Lemmas.Flow.Step.Combinators

@[expose] public section

/-! # Helpers for the index warp's step obligations

* `one_el`: a site of one element is stepped at element 0 (at any other element the invariant
  is false and the obligation is void); `ix_site` opens such a site's state.
* `pollAt`: a poll (the wait, the branch on its predicate, the jump back) going on to a site by a
  segment.
* `pairAt`: an element of an index pair's `.nc` load (any payload), going on by a segment after
  the second.
* `stAt`: an element of a coordinate pair's store, then the validity byte or the arrival by the
  lane's test. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

/-- A site of one element: the obligation at element 0 is the obligation. -/
theorem one_el {d : D} (h1 : d.site.elems = 1)
    (h : (code P L g).StepAtU { d with el := 0 }) : (code P L g).StepAtU d := by
  have key : (code P L g).inv d → d = { d with el := 0 } := by
    intro hi
    change d.el < d.site.elems at hi
    cases d; simp only [D.mk.injEq]; simp_all
  exact ⟨fun hi => key hi ▸ h.site (by rw [← key hi]; exact hi),
    fun ins ht hi => key hi ▸ h.step ins (key hi ▸ ht) (key hi ▸ hi)⟩

/-- A state at a site's first element satisfies the invariant. -/
theorem inv_ofC (p : IxSite × IxCtl) : (code P L g).inv (ofC p) :=
  show 0 < p.1.elems from IxSite.elems_pos _

set_option hygiene false in
/-- Open a one-element site's state `d` (hypothesis `hs` names its site) at element 0. -/
macro "ix_site" : tactic => `(tactic| (
  obtain ⟨s, el, ac, c⟩ := d
  dsimp only at hs; subst hs
  refine one_el rfl ?_))

/-- **A poll** at `pc` (the branch on its predicate at `pc + 1` to `tgt`, the jump back at
`pc + 2`) at a state of element 0: on success the site `s` by the segment `seg`. -/
theorem pollAt {d : D} {s : IxSite} {pc r base tgt : Nat} {off : Int} {par : Opnd}
    {acq : Bool} {sc : MbarScope} (hp : d.site.pc = pc)
    (hc : kernel.code[pc]? = some ⟨none, .mbarWait r base off par acq sc⟩)
    (hb : kernel.code[pc + 1]? = some ⟨some (r, false), .bra tgt false⟩)
    (hj : kernel.code[pc + 2]? = some ⟨none, .bra pc false⟩)
    (hoff : r ∉ ixLive pc) (he : d.el = 0)
    (hn : ∀ m q ok sc', succ P L g d ⟨d.site.pc, .wait m q ok acq sc'⟩ =
      some (some (if ok then { d with site := s } else d)))
    (seg : SegU kernel Assumptions.all L g tgt (ixFacts P L g d.c d.site) s.pc
      (ixFacts P L g d.c s)) : (code P L g).StepAtU d := by
  have ha : ∀ x : D, x.el = 0 → D.acc x = [] := fun x hx => by
    simp only [D.acc, hx]
  have hi : ∀ x : D, x.el = 0 → (code P L g).inv x := fun x hx => by
    change x.el < x.site.elems; rw [hx]; exact IxSite.elems_pos _
  refine Code.waitU (C := code P L g) (dst := fun ok => if ok then { d with site := s } else d)
    (by show kernel.code[d.site.pc]? = _; rw [hp]; exact hc)
    (by change _ ∉ (factsFrom _ _).map Prod.fst; rw [factsFrom_keys, hp]; exact hoff)
    hn he (ha d he) (fun ok => ?_) (fun ok => ?_) (fun ok => ?_) (fun ok => ?_)
  · cases ok <;> exact he
  · cases ok
    · exact ha d he
    · exact ha { d with site := s } he
  · cases ok
    · exact hi d he
    · exact hi { d with site := s } he
  · cases ok
    · change SegU _ _ _ _ (d.site.pc + 1) _ d.site.pc _; rw [hp]
      exact SegU.comp (SegU.branch false hb bra_rule noSegments.segFreePc)
        (SegU.of_seg (seg_jmp hj (fun t _ => bra_rule t) noSegments.segFreePc))
    · change SegU _ _ _ _ (d.site.pc + 1) _ s.pc _; rw [hp]
      exact SegU.comp (SegU.branch true hb bra_rule noSegments.segFreePc) seg

/-- A non-last element of an index pair keeps the first word. -/
theorem ld_more {d : D} {nf : BitVec 64 → BitVec 64 → D} {y : BitVec 64}
    (hld : isLd d.site = true) (h2 : d.site.elems = 2) (hm : d.el + 1 < 2) :
    ldNext d y nf = { d with el := d.el + 1, ac := [.bits 32 y] } ∧
      D.acc { d with el := d.el + 1, ac := [.bits 32 y] } = d.acc ++ [.bits 32 y] ∧
      d.el + 1 < d.site.elems := by
  have h0 : d.el = 0 := by omega
  refine ⟨ite_eq_left hm, ?_, by rw [h2]; exact hm⟩
  simp only [D.acc, D.w0, h0, hld, Bool.cond_true, List.nil_append]

/-- The last element of an index pair ends in the state of its two words. -/
theorem ld_last {d : D} {nf : BitVec 64 → BitVec 64 → D} {y : BitVec 64} (hm : ¬ d.el + 1 < 2) :
    ldNext d y nf = nf d.w0 y := ite_eq_right hm

/-- **An element of an index pair** at site `s` (pc `pc`): a 32-bit word continues; after the
second element the state `nf` of the pair's two words by the segment `seg`, from the facts with
the two words' registers `r0 r1` (the first word is the state's `w0`). -/
theorem pairAt {d : D} {nf : BitVec 64 → BitVec 64 → D} {a : MemAccess}
    {pc base w r0 r1 : Nat} {sp : Space}
    (hp : d.site.pc = pc) (hld : isLd d.site = true) (h2 : d.site.elems = 2)
    (hc : kernel.code[pc]? = some ⟨none, .mem a⟩) (hl : (Op.mem a).isLocal = false)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true) (hregs : a.regs = [r0, r1]) (hr01 : r0 ≠ r1)
    (hoff : ∀ x ∈ ixLive pc, x ∉ a.regs)
    (hn : ∀ x bs, succ P L g d ⟨d.site.pc, .nc x bs⟩ = ncPair ⟨d.site.pc, .nc x bs⟩ d nf)
    (hn0 : ∀ y0 y1, (nf y0 y1).el = 0)
    (seg : ∀ y, SegU kernel Assumptions.all L g (pc + 1)
      ((r0, .bits 32 d.w0) :: (r1, .bits 32 y) :: ixFacts P L g d.c d.site)
      (nf d.w0 y).site.pc (ixFacts P L g (nf d.w0 y).c (nf d.w0 y).site)) :
    (code P L g).StepAtU d := by
  have hi0 : ∀ y0 y1, (code P L g).inv (nf y0 y1) := fun y0 y1 => by
    change (nf y0 y1).el < (nf y0 y1).site.elems
    rw [hn0]; exact IxSite.elems_pos _
  refine Code.ldvNcDU (C := code P L g) (dok := fun y => ldNext d y nf) (y0 := d.w0)
    (by show kernel.code[d.site.pc]? = _; rw [hp]; exact hc)
    hl hru hloc hb hk hsem hnc hregs hr01 (fun hm => ?_) (fun x bs y hy => ?_)
    (fun x bs v hv hn32 => ?_) (fun x bs f hf => ?_) (fun hm y => ?_) rfl
    (by rw [hp]; exact hoff) (fun hm y => ?_)
  · have h : ¬ d.el + 1 < 2 := hm
    obtain ⟨k, hk⟩ : ∃ k, d.el = k + 1 := ⟨d.el - 1, by omega⟩
    simp only [D.acc, hk, hld, Bool.cond_true]
  · refine (hn x bs).trans ?_
    simp only [ncPair, hy]
  · refine (hn x bs).trans ?_
    cases v with
    | bits n y =>
      by_cases h32 : n = 32
      · subst h32; exact absurd rfl (hn32 y)
      · simp [ncPair, hv]
    | _ => simp [ncPair, hv]
  · refine (hn x bs).trans ?_
    simp only [ncPair, hf]
  · obtain ⟨he, hacc, hel⟩ := ld_more (y := y) (nf := nf) hld h2 hm
    rw [he]
    exact ⟨rfl, rfl, hacc, rfl, hel⟩
  · rw [ld_last (y := y) (nf := nf) hm]
    refine ⟨hn0 _ _, ?_, hi0 _ _, ?_⟩
    · simp only [D.acc, hn0]
    · change SegU _ _ _ _ (d.site.pc + 1) _ _ _; rw [hp]; exact seg y

/-- **An element of a coordinate pair's store** at site `s` (pc `pc`): after the second, the
state `n` by the segment `seg`. -/
theorem stAt {d n : D} {a : MemAccess} {pc : Nat} (hp : d.site.pc = pc)
    (hld : isLd d.site = false) (h2 : d.site.elems = 2)
    (hc : kernel.code[pc]? = some ⟨none, .mem a⟩) (hl : (Op.mem a).isLocal = false)
    (hst : a.kind = .store) (hlen : a.srcs.length = 2)
    (hn : ∀ e, succ P L g d e = some (some (stNext d n))) (hn0 : n.el = 0)
    (hna : isLd n.site = false)
    (seg : SegU kernel Assumptions.all L g (pc + 1) (ixFacts P L g d.c d.site) n.site.pc
      (ixFacts P L g n.c n.site)) : (code P L g).StepAtU d := by
  have hacc : ∀ x : D, isLd x.site = false → D.acc x = [] := fun x hx => by
    unfold D.acc; split <;> simp only [hx, Bool.cond_false]
  refine Code.vstU (C := code P L g) (dn := stNext d n)
    (by show kernel.code[d.site.pc]? = _; rw [hp]; exact hc) hl hst hn (hacc d hld)
    (fun hm => ?_) (fun hm => ?_)
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
    · change SegU _ _ _ _ (d.site.pc + 1) _ _ _; rw [hp]; exact seg

set_option hygiene false in
/-- A scalar event that continues at the next instruction, at code lemma `c` (`ev` proves the
continuation from `hf`), to the state `dn`; the segment after it is left. -/
macro "ix_adv " c:term:max " to " dn:term:max " by " ev:tacticSeq : tactic => `(tactic| (
  refine Code.advanceU (C := code P L g) (dn := $dn) $c rfl (fun hf => by $ev) (fun _ => rfl)
    rfl rfl rfl rfl (IxSite.elems_pos _) ?_))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
