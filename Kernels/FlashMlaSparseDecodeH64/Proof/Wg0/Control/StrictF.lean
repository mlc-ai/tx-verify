-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictBase
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictLib
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop.StepsSetup
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part001
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part002
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part003
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LdParam
import Lemmas.Flow.NcLoadS
import Lemmas.Flow.CtlStepsU

@[expose] public section

/-! # Warpgroup 0's strict steps at the length loads -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m : Mem0}

theorem lenB_seg (d : D) (x : BitVec 64) (hd : d.site = .lenB) :
    ∃ n, Seg kernel Assumptions.all L g n 182 ((2882, w32 x) :: (code P L g w).facts d) 198
      ((code P L g w).facts { d with site := .bwait, l1 := x }) := by
  w0s_state d
  simp only at hd
  subst hd
  dsimp only [code, facts, Site.pc]
  seg_sym using w0_segS

theorem ldp_ex (hp : Pre P L m) {pc d off x n b : Nat} {ty : DType} {F G : List (Nat × Value)}
    (hc : kernel.code[pc]? = some (ldpIns ty off d))
    (hty : (ty = .int .b 32 ∧ n = 4) ∨ (ty = .int .b 64 ∧ n = 8)) (hal : off % n = 0)
    (hoff : off + n ≤ 304) (hf : (off, x, n) ∈ p0fields P L)
    (h2991 : (2991, .ptr 64 false (.param (param "0")) 0) ∈ F) (hd : d ∉ F.map Prod.fst)
    (rest : ∃ k, Seg kernel Assumptions.all L g k (pc + 1)
      ((d, .bits (8 * n) (BitVec.ofNat 64 (leNat x 0 n))) :: F) b G) :
    ∃ k, Seg kernel Assumptions.all L g k pc F b G :=
  Seg.comp_ex ⟨1, seg_ldp hp hc hty hal hoff hf h2991
    fun _ hq he => hd (by rw [← he]; exact List.mem_map_of_mem hq)⟩ rest

theorem lenA_seg1 (d : D) (x : BitVec 64) (hd : d.site = .lenA) :
    ∃ n, Seg kernel Assumptions.all L g n 169 ((2881, w32 x) :: (code P L g w).facts d) 176
      (factsFrom (ctlLive 176) (valueOf P L g w { d with l0 := x })) := by
  w0s_state d
  simp only at hd
  subst hd
  dsimp only [code, facts, Site.pc]
  seg_sym using w0_segS

set_option hygiene false in
local macro "ldp_at " c:term:max ty:term:max off:term:max d:term:max n:term:max x:term:max :
    tactic => `(tactic| (
  refine ldp_ex (ty := $ty) (off := $off) (d := $d) (n := $n) (x := $x) hp $c (by decide)
    (by decide) (by decide) (by simp [p0fields])
    (by repeat (first | exact mem_factsFrom_eq (by decide +kernel) rfl |
      apply List.mem_cons_of_mem))
    (by simp only [List.map_cons, factsFrom_keys]; decide +kernel) ?_))

/-- After the first length (pc 176), the second pointer is set: the second length's load. -/
theorem segA_lenB (hp : Pre P L m) (d : D) (h : eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = false) :
    ∃ n, Seg kernel Assumptions.all L g n 176 (factsFrom (ctlLive 176) (valueOf P L g w d))
      181 (factsFrom (ctlLive 181) (valueOf P L g w d)) := by
  ldp_at Flow.code_176 (.int .b 64) 144 3003 8 (P.extraTopkLenBase.getD 0)
  seg_sym using w0_segS

/-- The second pointer is unset: the bulk wait with the parameter's length. -/
theorem segA_bwait (hp : Pre P L m) (d : D) (h : eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = true) :
    ∃ n, Seg kernel Assumptions.all L g n 176 (factsFrom (ctlLive 176) (valueOf P L g w d))
      198 (factsFrom (ctlLive 198) (valueOf P L g w { d with l1 := pw P.extra_topk })) := by
  ldp_at Flow.code_176 (.int .b 64) 144 3003 8 (P.extraTopkLenBase.getD 0)
  refine Seg.comp_ex (q := 183) (H := factsFrom (ctlLive 183) (valueOf P L g w d))
    (by seg_sym using w0_segS) ?_
  ldp_at Flow.code_183 (.int .b 32) 120 2882 4 P.extra_topk
  seg_sym using w0_segS

/-- The step over the first length's load. -/
theorem lenA_succ (hp : Pre P L m) (d : D) (x : BitVec 64) :
    ∃ n, Seg kernel Assumptions.all L g n 176
      (factsFrom (ctlLive 176) (valueOf P L g w { d with l0 := x }))
      ((code P L g w).pc (afterA P { d with l0 := x }))
      ((code P L g w).facts (afterA P { d with l0 := x })) := by
  cases h : eqz64 (pw8 (P.extraTopkLenBase.getD 0))
  · rw [show afterA P { d with l0 := x } = { d with l0 := x, site := .lenB } by
      simp only [afterA, h, Bool.false_eq_true, ↓reduceIte]]
    exact segA_lenB hp _ h
  · rw [show afterA P { d with l0 := x } = { d with l0 := x, site := .bwait, l1 := pw P.extra_topk }
      by simp only [afterA, h, ↓reduceIte]]
    exact segA_bwait hp _ h

theorem lenA_land (hp : Pre P L m) (d : D) (hs : d.site = .lenA) (x : BitVec 64) :
    ∃ n, Seg kernel Assumptions.all L g n 169
      ((2881, Value.bits 32 x) :: (code P L g w).facts d)
      ((code P L g w).pc (afterA P { d with l0 := x }))
      ((code P L g w).facts (afterA P { d with l0 := x })) := by
  have h1 := lenA_seg1 (P := P) (L := L) (g := g) (w := w) d x hs
  have h2 := lenA_succ (P := P) (L := L) (g := g) (w := w) hp d x
  obtain ⟨n1, s1⟩ := h1
  obtain ⟨n2, s2⟩ := h2
  exact ⟨n1 + n2, Seg.comp s1 s2⟩

theorem code_sub : (code P L g w).sub = fun d => d.el := rfl

theorem code_acc : (code P L g w).acc = D.acc := rfl

theorem code_inv : (code P L g w).inv = fun d => d.el < elems d.site := rfl

theorem afterA_sub (d : D) : (code P L g w).sub (afterA P d) = d.el := by
  rw [code_sub]; exact afterA_el d

theorem afterA_acc (d : D) (he : d.el = 0) : (code P L g w).acc (afterA P d) = [] := by
  rw [code_acc]; exact acc_nil ((afterA_el d).trans he)

theorem afterA_inv (d : D) (he : d.el = 0) : (code P L g w).inv (afterA P d) := by
  rw [code_inv]; show (afterA P d).el < elems (afterA P d).site
  rw [afterA_el, he]; exact elems_pos _

/-- **A length load**: the strict step, from the instruction's code lemma `hc`. -/
theorem stepAt_ncS {d : D} {pc r : Nat} {a : MemAccess} {base wd : Nat} {sp : Space}
    {f : BitVec 64 → D} (hpc : d.site.pc = pc) (hc : kernel.code[pc]? = some ⟨none, .mem a⟩)
    (hl : (Op.mem a).isLocal = false) (hru : a.rule = some .threadAccess)
    (hloc : a.locSpace? = some sp) (hb : a.addr.base = .reg base wd) (hk : a.kind = .load)
    (hsem : a.sem = .weak) (hnc : a.nc = true) (hr : a.regs = [r]) (he : d.el = 0)
    (hn : ∀ x bs, (code P L g w).next d ⟨pc, .nc x bs⟩ = Code.ncNext f bs)
    (hoff : r ∉ ctlLive pc)
    (hok : ∀ x, (code P L g w).Lands d (pc + 1) ((r, .bits 32 x) :: (code P L g w).facts d) (f x)) :
    (code P L g w).StepAt d := by
  subst hpc
  exact Code.step_loadNc (C := code P L g w) hc hl hru hloc hb hk hsem hnc hr he
    (acc_code he) hn (fresh_live hoff) hok

theorem stepAt_lenAS (hp : Pre P L m) (d : D) (hs : d.site = .lenA) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  refine stepAt_ncS (f := fun x => afterA P { d with l0 := x }) (by rw [hs]; rfl)
    Flow.code_168 rfl rfl rfl rfl rfl rfl rfl rfl he ?_ (by decide +kernel)
    (fun x => ⟨fun _ => ?_, (afterA_sub { d with l0 := x }).trans he,
      afterA_acc { d with l0 := x } he, fun _ => afterA_inv _ he⟩)
  · intro x bs
    simp only [code, succ, hs, ncWord, Code.ncNext]
    rfl
  · exact lenA_land hp d hs x

theorem stepAt_lenBS (d : D) (hs : d.site = .lenB) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  refine stepAt_ncS (f := fun x => { d with site := .bwait, l1 := x }) (by rw [hs]; rfl)
    Flow.code_181 rfl rfl rfl rfl rfl rfl rfl rfl he ?_ (by decide +kernel)
    (fun x => ⟨fun _ => lenB_seg d x hs, ?_, ?_, fun _ => ?_⟩)
  · intro x bs
    simp only [code, succ, hs, ncWord, Code.ncNext]
    rfl
  · rw [code_sub]; exact he
  · rw [code_acc]; exact acc_nil he
  · rw [code_inv]; show d.el < elems Site.bwait
    rw [he]; exact elems_pos _

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
