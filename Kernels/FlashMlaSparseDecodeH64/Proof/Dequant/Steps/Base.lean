-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CtlSteps
public import Lemmas.Flow.CtlStepsU
public import Lemmas.Flow.LandsU
public import Lemmas.Flow.StoreU
public import Lemmas.Flow.WaitU
public import Lemmas.Flow.BranchU
public import Lemmas.Flow.SegJump

@[expose] public section

/-! # Helpers for the dequantizer's step obligations

* `one_el`: a site of one element is stepped at element 0 (at any other element the invariant
  is false and the obligation is void).
* Tactics: `dq_site` opens a one-element site's state at element 0, `dq_seg` proves a control
  segment between two states' facts, `dq_poll S via cw, cb, cj` steps a poll at code lemma `cw`
  (branch `cb` on success, jump `cj` back) that goes on to the site `S`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- A site of one element: the obligation at element 0 is the obligation. -/
theorem one_el {d : D} (h1 : elems d.site = 1)
    (h : (code P L g w).StepAtU { d with el := 0 }) : (code P L g w).StepAtU d := by
  have key : (code P L g w).inv d → d = { d with el := 0 } := by
    intro hi
    change d.el < elems d.site at hi
    cases d; simp only [D.mk.injEq]; simp_all
  exact ⟨fun hi => key hi ▸ h.site (by rw [← key hi]; exact hi),
    fun ins ht hi => key hi ▸ h.step ins (key hi ▸ ht) (key hi ▸ hi)⟩

/-- A poll at a state of element 0: the wait's predicate is not a fact, on success the state
`dn`, else the poll again. -/
theorem pollTo {d : D} (dn : D) {r base pc : Nat} {off : Int} {par : Opnd} {acq : Bool}
    {sc : MbarScope} (hp : d.site.pc = pc)
    (hc : kernel.code[pc]? = some ⟨none, .mbarWait r base off par acq sc⟩)
    (hoff : r ∉ ctlLive pc)
    (hn : ∀ m q ok s, succ P L g d ⟨d.site.pc, .wait m q ok acq s⟩ =
      some (some (if ok then dn else d)))
    (he : d.el = 0) (hz : dn.el = 0) (hS : 0 < elems dn.site) (hd : elems d.site = 1)
    (segF : SegU kernel Assumptions.all L g (pc + 1) ((r, .pred false) :: facts P L g d) pc
      (facts P L g d))
    (segT : SegU kernel Assumptions.all L g (pc + 1) ((r, .pred true) :: facts P L g d) dn.site.pc
      (facts P L g dn)) :
    (code P L g w).StepAtU d := by
  have ha : ∀ x : D, x.el = 0 → D.acc x = [] := fun x hx => by
    simp only [D.acc, hx, ↓reduceIte]
  refine Code.waitU (C := code P L g w) (dst := fun ok => if ok then dn else d)
    (hp ▸ hc) (by change _ ∉ (factsFrom _ _).map Prod.fst; rw [factsFrom_keys, hp]; exact hoff)
    hn he (ha d he) (fun ok => ?_) (fun ok => ?_) (fun ok => ?_) (fun ok => ?_)
  · cases ok
    · exact he
    · exact hz
  · cases ok
    · exact ha d he
    · exact ha dn hz
  · cases ok
    · change d.el < elems d.site; omega
    · change dn.el < elems dn.site; omega
  · cases ok
    · change SegU _ _ _ _ (d.site.pc + 1) _ d.site.pc _; rw [hp]; exact segF
    · change SegU _ _ _ _ (d.site.pc + 1) _ dn.site.pc _; rw [hp]; exact segT

set_option hygiene false in
/-- Open a one-element site's state `d` (hypothesis `hs` names its site) at element 0. -/
macro "dq_site" : tactic => `(tactic| (
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  dsimp only at hs; subst hs
  refine one_el rfl ?_))

set_option hygiene false in
/-- A control segment of warpgroup 2 between two states' facts. -/
macro "dq_seg" : tactic => `(tactic| (
  try dsimp only [code, facts, Site.pc, rowBase, Bool.not_true, Bool.not_false, ↓reduceIte]
  ctl_seg))

set_option hygiene false in
/-- A poll at `cw` (branch `cb` on success, jump `cj` back) that goes on to the site `S`. -/
macro "dq_poll " S:term:max " via " cw:term:max ", " cb:term:max ", " cj:term:max : tactic =>
  `(tactic| (
  refine pollTo (Control.D.mk $S 0 ac l0 l1 cnt sb pb) (by rfl) $cw (by decide +kernel)
    (fun m q ok s => by cases ok <;> rfl) rfl rfl (by dsimp only; decide) rfl
    (SegU.comp (SegU.branch false $cb bra_rule noSegments.segFreePc)
      (SegU.of_seg (seg_jmp $cj (fun t _ => bra_rule t) noSegments.segFreePc)))
    (SegU.comp (SegU.branch true $cb bra_rule noSegments.segFreePc) ?_)
  dq_seg))

/-- A scalar data load at a state of element 0 into a register that is not a control register
live at its pc: any payload goes on to `dn` by a segment. -/
theorem loadAt {d dn : D} {a : MemAccess} {r pc : Nat} (hp : d.site.pc = pc)
    (hc : kernel.code[pc]? = some ⟨none, .mem a⟩) (hl : (Op.mem a).isLocal = false)
    (hk : a.kind = .load) (hnc : a.nc = false) (hx : a.ext = .same) (hr : a.regs = [r])
    (hoff : r ∉ ctlLive pc) (he : d.el = 0) (hz : dn.el = 0)
    (hn : ∀ x bs, succ P L g d ⟨pc, .rd x bs⟩ = some (some dn)) (hi : elems dn.site = 1)
    (seg : SegU kernel Assumptions.all L g (pc + 1) (facts P L g d) dn.site.pc (facts P L g dn)) :
    (code P L g w).StepAtU d := by
  subst hp
  exact Code.step_loadU (C := code P L g w) hc hl hk hnc hx hr he
    (by simp only [D.acc, he, ↓reduceIte]) hz (by simp only [D.acc, hz, ↓reduceIte])
    hn (by change dn.el < _; omega)
    (by change _ ∉ (factsFrom _ _).map Prod.fst; rw [factsFrom_keys]; exact hoff) seg

/-- An element of a row's scale load (four elements, the bytes not tracked): before the last the
machine counts the element at the same pc, after the last it goes on to the row's first raw
load by a segment. -/
theorem scaleAt {d : D} {r : Fin 4} {a : MemAccess} {pc : Nat} (hsite : d.site = .scale r)
    (hp : d.site.pc = pc) (hc0 : kernel.code[pc]? = some ⟨none, .mem a⟩)
    (hl : (Op.mem a).isLocal = false) (hk : a.kind = .load) (hnc : a.nc = false)
    (hx : a.ext = .same) (hlen : a.regs.length = 4) (hoff : ∀ x ∈ ctlLive pc, x ∉ a.regs)
    (seg : SegU kernel Assumptions.all L g (pc + 1) (facts P L g d) (Site.raw r 0).pc
      (facts P L g { d with site := .raw r 0, el := 0, ac := [] })) :
    (code P L g w).StepAtU d := by
  refine Code.ldvU (C := code P L g w) (dok := scaleNext r d) (dbad := scaleNext r d (.pred false))
    (by rw [← hp] at hc0; exact hc0) hl hk hnc hx (fun x bs v hv => ?_) (fun x bs f hf => ?_)
    (fun hm v => ?_) rfl (by rw [hp]; exact hoff) (fun hm v => ?_)
  · simp only [code, succ, hsite, hv, Except.toOption, Option.getD_some]
  · simp only [code, succ, hsite, hf, Except.toOption, Option.getD_none]
  · have h4 : d.el + 1 < 4 := by rw [hlen] at hm; exact hm
    have he : scaleNext r d v = { d with el := d.el + 1, ac := D.acc d ++ [v] } := ite_eq_left h4
    rw [he]
    exact ⟨rfl, rfl, by simp only [D.acc, Nat.add_one_ne_zero, ↓reduceIte], rfl,
      by show d.el + 1 < elems d.site; rw [hsite]; exact h4⟩
  · have h4 : ¬ d.el + 1 < 4 := by rw [hlen] at hm; exact hm
    have he : scaleNext r d v = { d with site := .raw r 0, el := 0, ac := [] } := ite_eq_right h4
    rw [he]
    refine ⟨rfl, rfl, Nat.one_pos, ?_⟩
    rw [← hp] at seg; exact seg

set_option hygiene false in
/-- A raw-word load at code lemma `c`: any payload goes on to the next site by a segment. -/
macro "raw_at " c:term:max : tactic => `(tactic| (
  refine loadAt (by rfl) $c rfl rfl rfl rfl rfl (by decide +kernel) rfl rfl (fun _ _ => rfl) rfl ?_
  dq_seg))

set_option hygiene false in
/-- A chunk store at code lemma `c`: on to the next site by a segment. -/
macro "st_at " c:term:max : tactic => `(tactic| (
  refine Code.scalarStoreU $c rfl rfl rfl (fun _ => rfl) rfl rfl rfl rfl
    (by dsimp only [code, storeNext, rowNext]; decide) ?_
  dq_seg))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
