-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop.Stage
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LdParam
public import Lemmas.Flow.NcLoadU
public import Lemmas.Flow.NcLoadAnyU
public import Lemmas.Flow.Selp
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part001
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part002
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part003
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part028

@[expose] public section

/-! # Warpgroup 0's obligations in the set-up (pcs 103–255)

The `setmaxnreg` (`smr`), the sink's load (`sink`), the two `.nc` length loads (`lenA`, `lenB`),
the bulk-group wait (`bwait`) and the arrival on the last-store barrier (`arrL`). The branches on
the parameter pointers (pcs 149, 153, 165, 178), the batch test (160, to the end at 1836) and the
no-block test (207, to the epilogue) are crossed by naming the predicate's fact and splitting it;
the scalar `ld.param`s of control words are single steps (`seg_ldp`, under `Pre`); the `selp` of
`%r18` (pc 244) on the symbolic `w > 1` is `Seg.selp_imm_eq`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Flow PTX.Proof PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

theorem fresh_live {rs : List Nat} {v : Nat → Value} {r : Nat} (h : r ∉ rs) :
    ∀ q ∈ factsFrom rs v, q.1 ≠ r := by
  intro q hq he
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
  exact h (he ▸ hs)

theorem elems_pos (s : Site) : 0 < elems s := by
  unfold elems; split <;> decide

theorem acc_nil {d : D} (h : d.el = 0) : D.acc d = [] := by
  unfold D.acc; simp only [h, ↓reduceIte]

theorem acc_code {d : D} (h : d.el = 0) : (code P L g w).acc d = [] := acc_nil h

theorem finish_el (d : D) : (finish w d).el = d.el := by
  unfold finish; split <;> rfl

theorem afterA_el (d : D) : (afterA P d).el = d.el := by
  unfold afterA; split <;> rfl

theorem afterSink_el (d : D) : (afterSink P L g w d).el = d.el := by
  unfold afterSink; split
  · exact finish_el d
  · split
    · exact afterA_el _
    · rfl

theorem afterSmr_el (d : D) : (afterSmr P L g w d).el = d.el := by
  unfold afterSmr; split
  · exact afterSink_el d
  · rfl

theorem loopEntry_el (d : D) : (loopEntry d).el = d.el := by
  unfold loopEntry; split <;> rfl

theorem fires_smr_next {A : List Assumption} {t u : TState} {pc n : Nat} {inc : Bool}
    {e : Event} (hf : Fires pc (eventTmpl A L g t (.setMaxReg inc n)) e (some u)) :
    u = PTX.next t := by
  simp only [eventTmpl, SetMaxNReg.tmpl] at hf
  split at hf
  · obtain ⟨_, -, h⟩ := hf
    exact Option.some.inj h
  · exact absurd hf.2 (by simp)

theorem fires_bulkWait_next {A : List Assumption} {t u : TState} {pc n : Nat}
    {mode : BulkGroup.WaitMode} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.bulkWait mode n)) e (some u)) : u = PTX.next t := by
  simp only [eventTmpl, tensorStoreTmpl] at hf
  exact Option.some.inj hf.2

/-- An event that continues at the next instruction, to a state `dn` at element 0. -/
theorem adv0 {d dn : D} {op : Op} (hc : kernel.code[d.site.pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = false)
    (ha : ∀ {t u e}, Fires d.site.pc (eventTmpl Assumptions.all L g t op) e (some u) →
      u = PTX.next t)
    (hn : ∀ e, succ P L g w d e = some (some dn)) (hd : d.el = 0) (hdn : dn.el = 0)
    (seg : SegU kernel Assumptions.all L g (d.site.pc + 1) (facts P L g w d) dn.site.pc
      (facts P L g w dn)) : (code P L g w).StepAtU d :=
  Code.advanceU (C := code P L g w) hc hl ha hn hd (acc_nil hd) hdn (acc_nil hdn)
    (show dn.el < elems dn.site by rw [hdn]; exact elems_pos _) seg

set_option hygiene false in
/-- To the branch at `pc` (code lemma `c`) on the predicate register `p` holding `x`; `h` fixes
the side. -/
macro "w0_br " pc:term:max c:term:max p:term:max x:term:max h:term:max dd:term:max :
    tactic => `(tactic| (
  refine SegU.comp (b := $pc) (G := vF P L g w $pc $dd) (by w0_seg) ?_
  refine SegU.pick (r := $p) (x := .pred $x) (mem_factsFrom_eq (by decide +kernel) rfl) ?_
  refine SegU.comp (SegU.branch _ $c bra_rule noSegments.segFreePc) ?_
  rw [$h:term]))

set_option hygiene false in
/-- Over the `ld.param` at the segment's start (code lemma `c`) of the field `(off, x, n)`. -/
macro "w0_ldp0 " c:term:max off:term:max x:term:max n:term:max : tactic => `(tactic| (
  refine SegU.comp (SegU.of_seg (seg_ldp (off := $off) (x := $x) (n := $n) hp $c (by decide)
    (by decide) (by decide) (by simp [p0fields]) (mem_factsFrom_eq (by decide +kernel) rfl)
    (fresh_live (by decide +kernel)))) ?_))

set_option hygiene false in
/-- To the `ld.param` at `pc` of the field `(off, x, n)` of `param_0`, and over it. -/
macro "w0_ldp " pc:term:max c:term:max off:term:max x:term:max n:term:max dd:term:max :
    tactic => `(tactic| (
  refine SegU.comp (b := $pc) (G := vF P L g w $pc $dd) (by w0_seg) ?_
  refine SegU.comp (SegU.of_seg (seg_ldp (off := $off) (x := $x) (n := $n) hp $c (by decide)
    (by decide) (by decide) (by simp [p0fields]) (mem_factsFrom_eq (by decide +kernel) rfl)
    (fresh_live (by decide +kernel)))) ?_))

/-- From the batch test's jump (pc 1836): warp 0 deallocates, the others return. -/
theorem finSeg (d : D) : SegU kernel Assumptions.all L g 1836 (vF P L g w 160 d)
    (finish w d).site.pc (facts P L g w (finish w d)) := by
  cases h : scmpi .ne .b w 0
  · rw [show finish w d = { d with site := .dealloc } by
      simp only [finish, h, Bool.false_eq_true, ↓reduceIte]]
    w0_br 1837 Flow.code_1837 129 (scmpi .ne .b w 0) h d
    w0_seg
  · rw [show finish w d = { d with site := .exit } by simp only [finish, h, ↓reduceIte]]
    w0_br 1837 Flow.code_1837 129 (scmpi .ne .b w 0) h d
    w0_seg

/-- After the first length (from pc 176): the second length's load, or its parameter and the bulk
wait. -/
theorem segA (hp : Pre P L m) (d : D) : SegU kernel Assumptions.all L g 176 (vF P L g w 176 d)
    (afterA P d).site.pc (facts P L g w (afterA P d)) := by
  w0_ldp0 Flow.code_176 144 (P.extraTopkLenBase.getD 0) 8
  cases h : eqz64 (pw8 (P.extraTopkLenBase.getD 0))
  · rw [show afterA P d = { d with site := .lenB } by
      simp only [afterA, h, Bool.false_eq_true, ↓reduceIte]]
    w0_br 178 Flow.code_178 73 (eqz64 (pw8 (P.extraTopkLenBase.getD 0))) h d
    w0_seg
  · rw [show afterA P d = { d with site := .bwait, l1 := pw P.extra_topk } by
      simp only [afterA, h, ↓reduceIte]]
    w0_br 178 Flow.code_178 73 (eqz64 (pw8 (P.extraTopkLenBase.getD 0))) h d
    w0_ldp 183 Flow.code_183 120 P.extra_topk 4 d
    w0_seg

/-- After the sink (pc 158): the batch test, then the first length's load or parameter. -/
theorem segSink (hp : Pre P L m) (d : D) : SegU kernel Assumptions.all L g 158
    (vF P L g w 158 d) (afterSink P L g w d).site.pc (facts P L g w (afterSink P L g w d)) := by
  w0_ldp 158 Flow.code_158 0 P.b 4 d
  cases h1 : scmp .ge .s (r2W L g) (pw P.b)
  · w0_br 160 Flow.code_160 71 (scmp .ge .s (r2W L g) (pw P.b)) h1 d
    w0_ldp 163 Flow.code_163 80 (P.topkLenBase.getD 0) 8 d
    cases h2 : eqz64 (pw8 (P.topkLenBase.getD 0))
    · rw [show afterSink P L g w d = { d with site := .lenA } by
        simp only [afterSink, h1, h2, Bool.false_eq_true, ↓reduceIte]]
      w0_br 165 Flow.code_165 72 (eqz64 (pw8 (P.topkLenBase.getD 0))) h2 d
      w0_seg
    · rw [show afterSink P L g w d = afterA P { d with l0 := pw P.topk } by
        simp only [afterSink, h1, h2, Bool.false_eq_true, ↓reduceIte]]
      w0_br 165 Flow.code_165 72 (eqz64 (pw8 (P.topkLenBase.getD 0))) h2 d
      w0_ldp 170 Flow.code_170 40 P.topk 4 d
      exact SegU.comp (b := 176) (G := vF P L g w 176 { d with l0 := pw P.topk }) (by w0_seg)
        (segA hp { d with l0 := pw P.topk })
  · rw [show afterSink P L g w d = finish w d by simp only [afterSink, h1, ↓reduceIte]]
    w0_br 160 Flow.code_160 71 (scmp .ge .s (r2W L g) (pw P.b)) h1 d
    exact finSeg d

/-- After `setmaxnreg` (pc 104): the sink's pointer and head tests. -/
theorem segSmr (hp : Pre P L m) (d : D) :
    SegU kernel Assumptions.all L g 104 (vF P L g w 103 d) (afterSmr P L g w d).site.pc
      (facts P L g w (afterSmr P L g w d)) := by
  refine SegU.comp (stageSeg hp d) ?_
  w0_ldp 147 Flow.code_147 88 (P.sinkBase.getD 0) 8 d
  cases h1 : eqz64 (pw8 (P.sinkBase.getD 0))
  · w0_br 149 Flow.code_149 69 (eqz64 (pw8 (P.sinkBase.getD 0))) h1 d
    w0_ldp 151 Flow.code_151 8 64 4 d
    cases h2 : scmp .ge .s (r10W L g) (pw 64)
    · rw [show afterSmr P L g w d = { d with site := .sink } by
        simp only [afterSmr, h1, h2, Bool.or_false, Bool.false_eq_true, ↓reduceIte]]
      w0_br 153 Flow.code_153 70 (scmp .ge .s (r10W L g) (pw 64)) h2 d
      w0_seg
    · rw [show afterSmr P L g w d = afterSink P L g w d by
        simp only [afterSmr, h1, h2, Bool.or_true, ↓reduceIte]]
      w0_br 153 Flow.code_153 70 (scmp .ge .s (r10W L g) (pw 64)) h2 d
      exact SegU.comp (b := 158) (G := vF P L g w 158 d) (by w0_seg) (segSink hp d)
  · rw [show afterSmr P L g w d = afterSink P L g w d by
      simp only [afterSmr, h1, Bool.true_or, ↓reduceIte]]
    w0_br 149 Flow.code_149 69 (eqz64 (pw8 (P.sinkBase.getD 0))) h1 d
    exact SegU.comp (b := 158) (G := vF P L g w 158 d) (by w0_seg) (segSink hp d)

/-- After the last-store arrival (pc 201): the no-block test, then the epilogue or the first
block with the rings at zero. -/
theorem segLoop (d : D) : SegU kernel Assumptions.all L g 201 (vF P L g w 200 d)
    (loopEntry d).site.pc (facts P L g w (loopEntry d)) := by
  refine SegU.comp (b := 207) (G := (2954, w32 (parW (i16 0))) :: factsFrom
    ((ctlLive 207).erase 2954) (valueOf P L g w { d with sl := i32 0, ps := i16 0 }))
    (by w0_seg) ?_
  refine SegU.pick (r := 74) (x := .pred (scmpi .lt .s (r15 d.l0 d.l1) 64))
    (List.mem_cons_of_mem _ (mem_factsFrom_eq (by decide +kernel) rfl)) ?_
  refine SegU.comp (SegU.branch _ Flow.code_207 bra_rule noSegments.segFreePc) ?_
  cases h : scmpi .lt .s (r15 d.l0 d.l1) 64
  · simp only [loopEntry, h, Bool.false_eq_true, ↓reduceIte]
    refine SegU.comp (b := 244) (G := vF P L g w 244 ⟨.bar0, d.el, d.a0, d.l0, d.l1,
      sub32 (i32 1) (nblk d.l0 d.l1), i32 1, i32 0, i16 0, i32 0, i16 0, d.vt⟩) (by w0_seg) ?_
    refine SegU.comp (SegU.of_seg (Seg.selp_imm_eq (v := w32 (r18W w)) Flow.code_244
      (mem_factsFrom_eq (by decide +kernel) rfl) (fresh_live (by decide +kernel))
      (by unfold r18W sel; cases scmpi .gt .s w 1 <;> rfl)
      (fun t ht a ha => asms_localRule_int (by rw [ht]; decide) (by rw [ht]; decide)
        (by rw [ht]; decide) (Assumptions.peerPackRule_of_none (by rw [ht]; rfl)) a ha))) ?_
    w0_seg
  · simp only [loopEntry, h, ↓reduceIte]
    w0_seg

/-! ### The set-up sites -/

theorem stepAt_smr (hp : Pre P L m) (d : D) (hs : d.site = .smr) :
    (code P L g w).StepAtU d := by
  w0_site
  exact adv0 Flow.code_103 rfl fires_smr_next (fun _ => rfl) rfl
    (afterSmr_el ⟨.smr, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩)
    (segSmr hp ⟨.smr, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩)

theorem stepAt_sink (hp : Pre P L m) (d : D) (hs : d.site = .sink) :
    (code P L g w).StepAtU d := by
  w0_site
  exact Code.step_loadNcAnyU (C := code P L g w) Flow.code_156 rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl (afterSink_el ⟨.sink, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩)
    (acc_nil (afterSink_el ⟨.sink, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩))
    (fun _ _ => rfl) (show _ < elems _ by rw [afterSink_el]; exact elems_pos _)
    (fresh_live (rs := ctlLive 156) (by decide +kernel))
    (SegU.comp (b := 158) (G := vF P L g w 158
      ⟨.sink, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩)
      (by w0_seg) (segSink hp ⟨.sink, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩))

theorem stepAt_lenA (hp : Pre P L m) (d : D) (hs : d.site = .lenA) :
    (code P L g w).StepAtU d := by
  w0_site
  refine Code.step_loadNcU (C := code P L g w)
    (f := fun x => afterA P ⟨.lenA, 0, a0, x, l1, cnt, bi, vs, pv, sl, ps, vt⟩) Flow.code_168
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (fun _ _ => rfl)
    (fresh_live (rs := ctlLive 168) (by decide +kernel))
    (fun x => ⟨afterA_el ⟨.lenA, 0, a0, x, l1, cnt, bi, vs, pv, sl, ps, vt⟩,
      acc_code (afterA_el ⟨.lenA, 0, a0, x, l1, cnt, bi, vs, pv, sl, ps, vt⟩),
      show _ < elems _ by rw [afterA_el]; exact elems_pos _, ?_⟩)
  refine SegU.comp (SegU.of_seg (seg_jmp Flow.code_169 (fun t _ => bra_rule t)
    noSegments.segFreePc)) ?_
  dsimp only [code, facts]
  exact SegU.comp (b := 176) (G := vF P L g w 176 ⟨.lenA, 0, a0, x, l1, cnt, bi, vs, pv, sl, ps,
    vt⟩) (by w0_seg) (segA hp ⟨.lenA, 0, a0, x, l1, cnt, bi, vs, pv, sl, ps, vt⟩)

theorem stepAt_lenB (d : D) (hs : d.site = .lenB) : (code P L g w).StepAtU d := by
  w0_site
  refine Code.step_loadNcU (C := code P L g w)
    (f := fun x => ⟨.bwait, 0, a0, l0, x, cnt, bi, vs, pv, sl, ps, vt⟩) Flow.code_181
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (fun _ _ => rfl)
    (fresh_live (rs := ctlLive 181) (by decide +kernel)) (fun x => ⟨rfl, rfl, Nat.one_pos, ?_⟩)
  refine SegU.comp (SegU.of_seg (seg_jmp Flow.code_182 (fun t _ => bra_rule t)
    noSegments.segFreePc)) ?_
  w0_seg

theorem stepAt_bwait (d : D) (hs : d.site = .bwait) : (code P L g w).StepAtU d := by
  w0_site
  w0_adv Flow.code_198 by exact fires_bulkWait_next hf
  w0_seg

theorem stepAt_arrL (d : D) (hs : d.site = .arrL) : (code P L g w).StepAtU d := by
  w0_site
  exact adv0 Flow.code_200 rfl (fun hf => (Code.fires_arrive_next hf)) (fun _ => rfl) rfl
    (loopEntry_el ⟨.arrL, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩)
    (segLoop ⟨.arrL, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
