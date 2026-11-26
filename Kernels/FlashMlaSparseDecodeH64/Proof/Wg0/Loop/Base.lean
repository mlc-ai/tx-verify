-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.Machine
public import Lemmas.Flow.LoadFrameU
public import Lemmas.Flow.LandsU
public import Lemmas.Flow.Step.Combinators
public import Lemmas.Flow.Step.TcSteps
public import Lemmas.Flow.AdvanceU
public import Lemmas.Flow.ArriveU
public import Lemmas.Flow.WaitU
public import Lemmas.Flow.BranchU
public import Lemmas.Flow.SegJump
public import Lemmas.Flow.SegCtl
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.RulesFrame
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Havoc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CtlSteps
public import Lemmas.Flow.CtlStepsU

@[expose] public section

/-! # Helpers for the control machine's step obligations

* `el0`: a site of one element is stepped at element 0 (at any other element the invariant is
  false and the obligation is void).
* `pollU`, `pld0U`/`pld1U`, `ostU`: the machine's polls, peer reads and P stores; the
  machine-independent one-step lemmas are in `Lemmas/Flow/CtlStepsU.lean` and
  `Proof/Lib/CtlSteps.lean`.
* Tactics `w0_site`, `w0_seg`, `w0_adv`, `w0_poll`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- A site of one element: the obligation at element 0 is the obligation. -/
theorem el0 {d : D} (h1 : elems d.site = 1)
    (h : (code P L g w).StepAtU { d with el := 0 }) : (code P L g w).StepAtU d := by
  have key : (code P L g w).inv d → d = { d with el := 0 } := by
    intro hi
    change d.el < elems d.site at hi
    cases d; simp only [D.mk.injEq]; simp_all
  exact ⟨fun hi => key hi ▸ h.site (by rw [← key hi]; exact hi),
    fun ins ht hi => key hi ▸ h.step ins (key hi ▸ ht) (key hi ▸ hi)⟩

/-- A site of two elements: the obligations at elements 0 and 1 are the obligation. -/
theorem el01 {d : D} (h2 : elems d.site = 2)
    (h0 : (code P L g w).StepAtU { d with el := 0 })
    (h1 : (code P L g w).StepAtU { d with el := 1 }) :
    (code P L g w).StepAtU d := by
  have key : (code P L g w).inv d → d = { d with el := 0 } ∨ d = { d with el := 1 } := by
    intro hi
    change d.el < elems d.site at hi
    cases d; simp only [D.mk.injEq, and_true, true_and]; simp only [h2] at hi; omega
  refine ⟨fun hi => ?_, fun ins ht hi => ?_⟩
  · rcases key hi with he | he
    · exact he ▸ h0.site (by rw [← he]; exact hi)
    · exact he ▸ h1.site (by rw [← he]; exact hi)
  · rcases key hi with he | he
    · exact he ▸ h0.step ins (he ▸ ht) (he ▸ hi)
    · exact he ▸ h1.step ins (he ▸ ht) (he ▸ hi)

/-- A poll: on success the site `S`, else the poll again (its pc is the wait's). -/
theorem pollU {d : D} (S : Site) {r base pc : Nat} {off : Int} {par : Opnd} {acq : Bool}
    {sc : MbarScope} (hp : d.site.pc = pc)
    (hc : kernel.code[pc]? = some ⟨none, .mbarWait r base off par acq sc⟩)
    (hoff : r ∉ ctlLive pc)
    (hn : ∀ m q ok s, succ P L g w d ⟨d.site.pc, .wait m q ok acq s⟩ =
      some (some (if ok then { d with site := S } else d)))
    (he : d.el = 0) (hS : elems S = 1) (hd : elems d.site = 1)
    (segF : SegU kernel Assumptions.all L g (pc + 1) ((r, .pred false) :: facts P L g w d) pc
      (facts P L g w d))
    (segT : SegU kernel Assumptions.all L g (pc + 1) ((r, .pred true) :: facts P L g w d) S.pc
      (facts P L g w { d with site := S })) :
    (code P L g w).StepAtU d := by
  refine Code.waitU (C := code P L g w) (dst := fun ok => if ok then { d with site := S } else d)
    (hp ▸ hc) (by change _ ∉ (factsFrom _ _).map Prod.fst; rw [factsFrom_keys, hp]; exact hoff)
    hn he ?_
    (fun ok => ?_) (fun ok => ?_) (fun ok => ?_) (fun ok => ?_)
  · change (if d.el = 0 then [] else _) = []; simp only [he, ↓reduceIte]
  · cases ok <;> exact he
  · cases ok <;> (change (if d.el = 0 then [] else _) = []; simp only [he, ↓reduceIte])
  · cases ok
    · change d.el < elems d.site; omega
    · change d.el < elems S; omega
  · cases ok
    · change SegU _ _ _ _ (d.site.pc + 1) _ d.site.pc _; rw [hp]; exact segF
    · change SegU _ _ _ _ (d.site.pc + 1) _ S.pc _; rw [hp]; exact segT

set_option hygiene false in
/-- Open a one-element site's state `d` (hypothesis `hs` names its site) at element 0. -/
macro "w0_site" : tactic => `(tactic| (
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  dsimp only at hs; subst hs
  refine el0 rfl ?_))

set_option hygiene false in
/-- A control segment of warpgroup 0 between two states' facts. -/
macro "w0_seg" : tactic => `(tactic| (
  try dsimp only [code, facts, Site.pc, Bool.not_true, Bool.not_false, ↓reduceIte]
  ctl_seg))

set_option hygiene false in
/-- An event that continues at the next instruction (`ev` proves it from `hf`). -/
macro "w0_adv " code:term:max " by " ev:tacticSeq : tactic => `(tactic| (
  ctl_adv $code by $ev))

set_option hygiene false in
/-- A poll at `cw` (branch `cb` on success, jump `cj` back) that goes on to the site `S`. -/
macro "w0_poll " S:term:max " via " cw:term:max ", " cb:term:max ", " cj:term:max : tactic =>
  `(tactic| (
  refine pollU $S (by rfl) $cw (by decide +kernel) (fun m q ok s => by cases ok <;> rfl) rfl rfl rfl
    (SegU.comp (SegU.branch false $cb bra_rule noSegments.segFreePc)
      (SegU.of_seg (seg_jmp $cj (fun t _ => bra_rule t) noSegments.segFreePc)))
    (SegU.comp (SegU.branch true $cb bra_rule noSegments.segFreePc) ?_)
  w0_seg))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control


namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The site after peer read `k`. -/
abbrev pldNext (k : Fin 8) : Site :=
  [.pld 1, .pld 2, .pld 3, .pld 4, .pld 5, .pld 6, .pld 7].getD k.val .mst

/-- The first element of a peer read: the value is kept as the accumulator. -/
theorem pld0U {d : D} {k : Fin 8} {a : MemAccess} {pc : Nat} (hsite : d.site = .pld k)
    (he : d.el = 0) (hp : d.site.pc = pc) (hc0 : kernel.code[pc]? = some ⟨none, .mem a⟩)
    (hl : (Op.mem a).isLocal = false) (hk : a.kind = .load) (hnc : a.nc = false)
    (hx : a.ext = .same) (hlen : a.regs.length = 2)
    (hoff : ∀ r ∈ ctlLive pc, r ∉ a.regs) :
    (code P L g w).StepAtU d := by
  refine Code.ldvU (C := code P L g w) (dok := fun v => { d with el := 1, a0 := v })
    (dbad := { d with el := 1, a0 := .bits 64 0 }) (by rw [← hp] at hc0; exact hc0) hl hk hnc hx
    (fun x bs v hv => ?_) (fun x bs f hf => ?_) (fun _ v => ⟨rfl, ?_, ?_, rfl, ?_⟩) rfl
    (by rw [hp]; exact hoff) (fun h => absurd ?_ h)
  · simp only [code, succ, hsite, he, hv, ↓reduceIte]; rfl
  · simp only [code, succ, hsite, he, hf, ↓reduceIte]; rfl
  · show 1 = d.el + 1; rw [he]
  · show (if (1 : Nat) = 0 then [] else _) = (if d.el = 0 then [] else _) ++ [v]
    simp only [he, hsite, ↓reduceIte, one_ne_zero, List.nil_append]; rfl
  · show 1 < elems d.site; rw [hsite]; exact Nat.one_lt_two
  · show d.el + 1 < a.regs.length; rw [he, hlen]; decide

/-- The second element of a peer read: the pair is written to data registers and the machine
goes on to the site `S` by a segment. -/
theorem pld1U {d : D} {k : Fin 8} {a : MemAccess} {pc : Nat} (S : Site) (hsite : d.site = .pld k)
    (he : d.el = 1) (hp : d.site.pc = pc) (hc0 : kernel.code[pc]? = some ⟨none, .mem a⟩)
    (hl : (Op.mem a).isLocal = false) (hk : a.kind = .load) (hnc : a.nc = false)
    (hx : a.ext = .same) (hlen : a.regs.length = 2)
    (hS : pldNext k = S) (hoff : ∀ r ∈ ctlLive pc, r ∉ a.regs) (h1 : 0 < elems S)
    (seg : SegU kernel Assumptions.all L g (pc + 1) (facts P L g w d) S.pc
      (facts P L g w { d with el := 0, a0 := .pred false, site := S })) :
    (code P L g w).StepAtU d := by
  refine Code.ldvU (C := code P L g w)
    (dok := fun _ => { d with el := 0, a0 := .pred false, site := S })
    (dbad := { d with el := 0, a0 := .pred false, site := S }) (by rw [← hp] at hc0; exact hc0)
    hl hk hnc hx (fun x bs v hv => ?_) (fun x bs f hf => ?_) (fun h => absurd h ?_) rfl
    (by rw [hp]; exact hoff) (fun _ _ => ⟨rfl, rfl, ?_, ?_⟩)
  · simp only [code, succ, hsite, he, one_ne_zero, ↓reduceIte, ← hS]
  · simp only [code, succ, hsite, he, one_ne_zero, ↓reduceIte, ← hS]
  · show ¬ d.el + 1 < a.regs.length; rw [he, hlen]; decide
  · exact h1
  · show SegU _ _ _ _ (d.site.pc + 1) _ S.pc _; rw [hp]; exact seg

/-- An element of a four-element vector store whose successor is `elemNext d 4 S`: the next
element, after the last the site `S` by a segment. -/
theorem vst4U {d : D} {a : MemAccess} (S : Site)
    (hacc : ∀ d' : D, d'.site = d.site → D.acc d' = []) (h4 : elems d.site = 4)
    (hc0 : kernel.code[d.site.pc]? = some ⟨none, .mem a⟩)
    (hl : (Op.mem a).isLocal = false) (hst : a.kind = .store) (hlen : a.srcs.length = 4)
    (hn : ∀ e, succ P L g w d e = some (some (elemNext d 4 S))) (h1 : 0 < elems S)
    (seg : SegU kernel Assumptions.all L g (d.site.pc + 1) (facts P L g w d) S.pc
      (facts P L g w { d with site := S, el := 0 })) :
    (code P L g w).StepAtU d := by
  refine Code.vstU (C := code P L g w) (dn := elemNext d 4 S) hc0 hl hst hn (hacc d rfl)
    (fun hm => ?_) (fun hm => ?_)
  · rw [hlen] at hm
    have hm' : d.el + 1 < 4 := hm
    have he : elemNext d 4 S = { d with el := d.el + 1 } := by
      simp only [elemNext, hm', ↓reduceIte]
    rw [he]
    exact ⟨rfl, rfl, hacc { d with el := d.el + 1 } rfl, rfl,
      by show d.el + 1 < elems d.site; rw [h4]; exact hm'⟩
  · rw [hlen] at hm
    have hm' : ¬ d.el + 1 < 4 := hm
    have he : elemNext d 4 S = { d with site := S, el := 0 } := by
      simp only [elemNext, hm', ↓reduceIte]
    rw [he]
    exact ⟨rfl, rfl, h1, seg⟩

/-- An element of a P store (four elements): the next element, after the last the site `S`. -/
theorem ostU {d : D} {k : Fin 4} {a : MemAccess} {pc : Nat} (S : Site) (hsite : d.site = .ost k)
    (hp : d.site.pc = pc) (hc0 : kernel.code[pc]? = some ⟨none, .mem a⟩)
    (hl : (Op.mem a).isLocal = false) (hst : a.kind = .store) (hlen : a.srcs.length = 4)
    (hS : [Site.ost 1, .ost 2, .ost 3].getD k.val (afterOst d) = S) (h1 : 0 < elems S)
    (seg : SegU kernel Assumptions.all L g (pc + 1) (facts P L g w d) S.pc
      (facts P L g w { d with site := S, el := 0 })) :
    (code P L g w).StepAtU d :=
  vst4U S (fun d' h => by unfold D.acc; rw [h, hsite]; exact ite_self _) (by rw [hsite]; rfl)
    (hp ▸ hc0) hl hst hlen (fun e => by simp only [succ, hsite, ← hS]) h1 (hp ▸ seg)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
