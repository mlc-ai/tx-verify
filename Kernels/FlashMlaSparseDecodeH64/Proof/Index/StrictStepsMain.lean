-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StepsLen
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StepsMain
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StrictEntry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StrictStepsBase
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StrictWalkHead
public import Lemmas.Flow.ShflRecvQ
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LaunchReads

@[expose] public section

/-! # The index warp's strict steps: the main loop

`stepQ_wA` .. `stepQ_arrA`: the strict obligations of the main loop's wait, the two data
shuffles, the coordinate pair's store, the validity byte and the arrival, as the `stepAt_*` of
`Index/StepsMain.lean`. -/

/-! # The index warp's strict steps: the lengths and the first pairs

`stepQ_lenA`, `stepQ_lenB`, `stepQ_pre`, `stepQ_pf`: the strict obligations
(`Code.StepForQ (QT ixQt) (IxWf P)`) of the two length loads and the main loop's first and
following pair loads, as the UB-tolerant `stepAt_*` of `Index/StepsLen.lean`, `Index/StepsMain.lean`
with the walks' strict versions. -/

/-! # The strict parameter prefix of the index warp (continued)

`qw_entry`: `ixw_entry` (`Lib/IndexEntry.lean`) as a strict segment under `QT ixQt`: from pc 2332
with the entry registers to the first event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Flow.Havoc PTX.Flow.Tagged

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option hygiene false in
/-- An `ld.param` at code lemma `c` (field at `off` of `n` bytes into `d`), the facts before it
the table's at `pc`. -/
local macro "ldpq_at " pc:term:max c:term:max ty:term:max off:term:max d:term:max n:term:max
    x:term:max : tactic => `(tactic| (
  refine SegQ.comp (b := $pc) (G := factsFrom (ixLive $pc) (ixVal P L g (ixCtl0 P)))
    (by ixq_seg) ?_
  refine ix_ldpQ (ty := $ty) (off := $off) (d := $d) (n := $n) (x := $x) hp hP $c (by decide)
    (by decide) (by decide) (by simp [p0fields])
    (mem_factsFrom_eq (show 2991 ∈ ixLive $pc by decide +kernel) rfl)
    (by rw [factsFrom_keys]; decide +kernel) (by decide +kernel) (by decide +kernel)
    (by omega) (by omega) ?_))

/-- The prefix from the extra array's strides to the first length pointer's test
(pcs 2345–2356). -/
theorem qw_params1 (hp : Pre P L m) (hP : Plain L g) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2345
      (factsFrom (ixLive 2345) (ixVal P L g (ixCtl0 P)))
      2357 (factsFrom (ixLive 2357) (ixVal P L g (ixCtl0 P))) := by
  refine ix_ldpQ (ty := .int .b 64) (off := 136) (d := 3012) (n := 8) (x := P.extraIndicesBase)
    hp hP Flow.code_2345 (by decide) (by decide) (by decide) (by simp [p0fields])
    (mem_factsFrom_eq (show 2991 ∈ ixLive 2345 by decide +kernel) rfl)
    (by rw [factsFrom_keys]; decide +kernel) (by decide +kernel) (by decide +kernel)
    (by omega) (by omega) ?_
  refine SegQ.comp (b := 2346) (G := factsFrom (ixLive 2346) (ixVal P L g (ixCtl0 P)))
    (by ixq_seg) ?_
  refine ix_ldp2Q (d1 := 494) (d2 := 561) (x := P.s_q * P.extra_topk) (y := P.extra_topk) hp hP
    Flow.code_2346 (by decide) (by decide) (by simp [p0fields]) (by simp [p0fields])
    (mem_factsFrom_eq (show 2991 ∈ ixLive 2346 by decide +kernel) rfl)
    (by simp only [freshKeys, List.map_cons, factsFrom_keys]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by omega) (by omega) ?_
  refine SegQ.comp (b := 2349) (G := factsFrom (ixLive 2349) (ixVal P L g (ixCtl0 P)))
    (by ixq_seg) ?_
  refine ix_ldp497 hp hP (mem_factsFrom_eq (show 2991 ∈ ixLive 2349 by decide +kernel) rfl)
    (by rw [factsFrom_keys]; decide +kernel) ?_
  refine SegQ.comp (b := 2355) (G := factsFrom (ixLive 2355) (ixVal P L g (ixCtl0 P)))
    (by ixq_seg) ?_
  ldpq_at 2355 Flow.code_2355 (.int .b 32) 116 502 4 P.extraPage
  ixq_seg

/-- A taken branch to the exit (pc 3611): the exit's registers are among the live ones. -/
theorem qw_exit (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 3611 (factsFrom (ixLive 2334) (ixVal P L g c))
      3611 (factsFrom (ixLive 3611) (ixVal P L g c)) := by
  refine SegQ.of_seg (n := 0) (Seg.weaken_end (Seg.refl 3611 _) fun R hR => ?_) fun ht _ _ hu => ?_
  · refine holds_of_pointwise fun r hr => ?_
    have hm : r ∈ ixLive 2334 := by
      have : ∀ r ∈ ixLive 3611, r ∈ ixLive 2334 := by decide +kernel
      exact this r hr
    rw [holds_mem hR (mem_factsFrom hm)]
  · intro r tg h
    simp [hu.1, show ixQt 3611 = [] by decide +kernel] at h

/-- The prefix inside the batch up to the first length pointer's test (pcs 2335–2356). -/
theorem qw_params (hp : Pre P L m) (hP : Plain L g) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2335
      (factsFrom (ixLive 2335) (ixVal P L g (ixCtl0 P)))
      2357 (factsFrom (ixLive 2357) (ixVal P L g (ixCtl0 P))) := by
  ldpq_at 2335 Flow.code_2335 (.int .b 32) 164 490 4 P.blockStride
  ldpq_at 2336 Flow.code_2336 (.int .b 32) 200 491 4 P.extraBlockStride
  ldpq_at 2337 Flow.code_2337 (.int .b 64) 80 3009 8 (P.topkLenBase.getD 0)
  ldpq_at 2338 Flow.code_2338 (.int .b 32) 40 2968 4 P.topk
  ldpq_at 2339 Flow.code_2339 (.int .b 64) 144 3010 8 (P.extraTopkLenBase.getD 0)
  ldpq_at 2340 Flow.code_2340 (.int .b 32) 120 2969 4 P.extra_topk
  ldpq_at 2341 Flow.code_2341 (.int .b 64) 72 3011 8 P.indicesBase
  ldpq_at 2342 Flow.code_2342 (.int .b 32) 172 492 4 (P.s_q * P.topk)
  ldpq_at 2343 Flow.code_2343 (.int .b 32) 176 560 4 P.topk
  refine SegQ.comp (b := 2345) (G := factsFrom (ixLive 2345) (ixVal P L g (ixCtl0 P)))
    (by ixq_seg) (qw_params1 hp hP)

/-- The first length pointer null, the second's test (pcs 2357–2366). -/
theorem qw_nullA (hP : Plain L g) (hA : eqz64 (pw8 (P.topkLenBase.getD 0)) = true) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2357
      (factsFrom (ixLive 2357) (ixVal P L g (ixCtl0 P)))
      (ixAfterA P (ixCtl0 P)).1.pc
      (ixFacts P L g (ixAfterA P (ixCtl0 P)).2 (ixAfterA P (ixCtl0 P)).1) := by
  refine SegQ.pick (r := 15) (x := .pred (eqz64 (pw8 (P.topkLenBase.getD 0))))
    (mem_factsFrom_eq (show 15 ∈ ixLive 2357 by decide +kernel) rfl) ?_
  ixq_bra Flow.code_2357 with hA
  cases hB : eqz64 (pw8 (P.extraTopkLenBase.getD 0))
  · rw [show ixAfterA P (ixCtl0 P) = (.lenB, ixCtl0 P) by unfold ixAfterA; rw [hB]; rfl]
    ixq_br 2362 16 (eqz64 (pw8 (P.extraTopkLenBase.getD 0))) (ixCtl0 P) Flow.code_2362 with hB
    ixq_seg
  · rw [show ixAfterA P (ixCtl0 P) = ixLens (ixCtl0 P) by unfold ixAfterA; rw [hB]; rfl]
    ixq_br 2362 16 (eqz64 (pw8 (P.extraTopkLenBase.getD 0))) (ixCtl0 P) Flow.code_2362 with hB
    exact SegQ.comp (b := 2366) (G := factsFrom (ixLive 2366) (ixVal P L g (ixCtl0 P)))
      (by ixq_seg) (qw_lens hP _)

/-- Inside the batch (pcs 2335–2360). -/
theorem qw_batch (hp : Pre P L m) (hP : Plain L g)
    (hb : scmp .ge .s (r2W L g) (pw P.b) = false) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2335
      (factsFrom (ixLive 2335) (ixVal P L g (ixCtl0 P)))
      (ixFirst P L g).1.pc (ixFacts P L g (ixFirst P L g).2 (ixFirst P L g).1) := by
  refine SegQ.comp (qw_params hp hP) ?_
  cases hA : eqz64 (pw8 (P.topkLenBase.getD 0))
  · rw [show ixFirst P L g = (.lenA, ixCtl0 P) by unfold ixFirst; dsimp only; rw [hb, hA]; rfl]
    refine SegQ.pick (r := 15) (x := .pred (eqz64 (pw8 (P.topkLenBase.getD 0))))
      (mem_factsFrom_eq (show 15 ∈ ixLive 2357 by decide +kernel) rfl) ?_
    ixq_bra Flow.code_2357 with hA
    ixq_seg
  · rw [show ixFirst P L g = ixAfterA P (ixCtl0 P) by
      unfold ixFirst; dsimp only; rw [hb, hA]; rfl]
    exact qw_nullA hP hA

/-- The prefix from the batch's load (pcs 2332–2334). -/
theorem qw_entry0 (hp : Pre P L m) (hP : Plain L g) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2332
      (factsFrom (ixLive 2332) (ixVal P L g (ixCtl0 P)))
      (ixFirst P L g).1.pc (ixFacts P L g (ixFirst P L g).2 (ixFirst P L g).1) := by
  ldpq_at 2332 Flow.code_2332 (.int .b 32) 0 559 4 P.b
  cases hb : scmp .ge .s (r2W L g) (pw P.b)
  · ixq_br 2334 14 (scmp .ge .s (r2W L g) (pw P.b)) (ixCtl0 P) Flow.code_2334 with hb
    exact SegQ.comp (b := 2335) (G := factsFrom (ixLive 2335) (ixVal P L g (ixCtl0 P)))
      (by ixq_seg) (qw_batch hp hP hb)
  · rw [show ixFirst P L g = (.exit, ixCtl0 P) by unfold ixFirst; dsimp only; rw [hb]; rfl]
    ixq_br 2334 14 (scmp .ge .s (r2W L g) (pw P.b)) (ixCtl0 P) Flow.code_2334 with hb
    exact qw_exit _

/-- **The index warp's strict parameter prefix**: from pc 2332 with the entry registers to its
first event. -/
theorem qw_entry (hp : Pre P L m) (hP : Plain L g) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2332 (factsFrom (Flow.live 2332) (entryVal L g))
      (ixFirst P L g).1.pc (ixFacts P L g (ixFirst P L g).2 (ixFirst P L g).1) := by
  refine SegQ.comp (SegQ.of_seg (n := 0) (Seg.weaken_end (Seg.refl 2332 _) ix_entry_facts)
    fun ht _ _ hu => ?_) (qw_entry0 hp hP)
  intro r tg h
  simp [hu.1, ixQt_entry] at h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Flow.Havoc PTX.Flow.Tagged

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

/-- After the first length `x` (pcs 2361–2365). -/
theorem qlenA_seg (hP : Plain L g) (c : IxCtl) (x : BitVec 64) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2361 ((2968, .bits 32 x) :: ixFacts P L g c .lenA)
      (ixAfterA P { c with l0 := x }).1.pc
      (ixFacts P L g (ixAfterA P { c with l0 := x }).2 (ixAfterA P { c with l0 := x }).1) := by
  cases hz : eqz64 (pw8 (P.extraTopkLenBase.getD 0))
  · rw [show ixAfterA P { c with l0 := x } = (.lenB, { c with l0 := x }) by
      unfold ixAfterA; rw [hz]; rfl]
    ixq_br 2362 16 (eqz64 (pw8 (P.extraTopkLenBase.getD 0))) { c with l0 := x } Flow.code_2362
      with hz
    ixq_seg
  · rw [show ixAfterA P { c with l0 := x } = ixLens { c with l0 := x } by
      unfold ixAfterA; rw [hz]; rfl]
    ixq_br 2362 16 (eqz64 (pw8 (P.extraTopkLenBase.getD 0))) { c with l0 := x } Flow.code_2362
      with hz
    exact SegQ.comp (b := 2366) (G := factsFrom (ixLive 2366) (ixVal P L g { c with l0 := x }))
      (by ixq_seg) (qw_lens hP _)

/-- After the second length `x` (pcs 2366 on). -/
theorem qlenB_seg (hP : Plain L g) (c : IxCtl) (x : BitVec 64) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2366 ((2969, .bits 32 x) :: ixFacts P L g c .lenB)
      (ixLens { c with l1 := x }).1.pc
      (ixFacts P L g (ixLens { c with l1 := x }).2 (ixLens { c with l1 := x }).1) :=
  SegQ.comp (segq_weaken fun R hR => lenB_facts c x R hR) (qw_lens hP _)

theorem stepQ_lenA (hP : Plain L g) (d : D) (hs : d.site = .lenA) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  ixq_site
  intro t u ins hat hinv hc hq hw hf
  refine Code.ldNcQ (C := code P L g) (qt := ixQt) (ex := []) (Wf := IxWf P)
    (d := ⟨.lenA, 0, ac, c⟩) (f := fun x => ofC (ixAfterA P { c with l0 := x }))
    Flow.code_2360 rfl rfl rfl rfl rfl rfl rfl (fun e he => he.nc) (fun x bs y hy => ?_) rfl rfl
    (not_mem_factsFrom (live := ixLive 2360) (by decide +kernel)) (fun _ _ => typed_nil)
    (by show Code.afterWrites ixQt 2360 _ = _; decide +kernel)
    (fun x => ⟨rfl, rfl, inv_ofC _, qlenA_seg hP c x⟩) e
    ins hat hinv hc hq hw hf
  show succ P L g ⟨.lenA, 0, ac, c⟩ ⟨2360, .nc x bs⟩ = _
  simp only [succ, lenNext, Code.ncNext, hy]

theorem stepQ_lenB (hP : Plain L g) (d : D) (hs : d.site = .lenB) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  ixq_site
  intro t u ins hat hinv hc hq hw hf
  refine Code.ldNcQ (C := code P L g) (qt := ixQt) (ex := []) (Wf := IxWf P)
    (d := ⟨.lenB, 0, ac, c⟩) (f := fun x => ofC (ixLens { c with l1 := x }))
    Flow.code_2365 rfl rfl rfl rfl rfl rfl rfl (fun e he => he.nc) (fun x bs y hy => ?_) rfl rfl
    (not_mem_factsFrom (live := ixLive 2365) (by decide +kernel)) (fun _ _ => typed_nil)
    (by show Code.afterWrites ixQt 2365 _ = _; decide +kernel)
    (fun x => ⟨rfl, rfl, inv_ofC _, qlenB_seg hP c x⟩) e
    ins hat hinv hc hq hw hf
  show succ P L g ⟨.lenB, 0, ac, c⟩ ⟨2365, .nc x bs⟩ = _
  simp only [succ, lenNext, Code.ncNext, hy]

theorem stepQ_pre (hP : Plain L g) (d : D) (hs : d.site = .pre) (hi : IxInv P d) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  obtain ⟨s, el, ac, c⟩ := d
  dsimp only at hs; subst hs
  exact pairQ (nf := fun y0 y1 => ofC (afterPre P L g { c with m0 := y0, m1 := y1 }))
    (pc := 2403) (r0 := 2974) (r1 := 2973) rfl rfl rfl Flow.code_2403 rfl rfl rfl rfl rfl rfl
    rfl rfl (by decide) (by decide +kernel) (fun _ _ => rfl) (fun _ _ => rfl)
    (by decide +kernel) (fun y => qk_entry hP c (D.w0 ⟨_, el, ac, c⟩) y) e

theorem stepQ_pf (hP : Plain L g) (d : D) (hs : d.site = .pf) (hi : IxInv P d) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  obtain ⟨s, el, ac, c⟩ := d
  dsimp only at hs; subst hs
  refine pairQ (nf := fun y0 y1 => ofC (.wA, { c with n0 := y0, n1 := y1 })) (pc := 2429)
    (r0 := 2976) (r1 := 2975) rfl rfl rfl Flow.code_2429 rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) (by decide +kernel) (fun _ _ => rfl) (fun _ _ => rfl) (by decide +kernel)
    (fun y => ?_) e
  exact SegQ.comp (b := 2432)
    (G := factsFrom (ixLive 2432)
      (ixVal P L g { c with n0 := D.w0 ⟨_, el, ac, c⟩, n1 := y })) (by ixq_seg) (qk_head hP _)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Flow.Havoc PTX.Flow.Tagged

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

theorem stepQ_wA (hP : Plain L g) (d : D) (hs : d.site = .wA) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  ixq_site
  exact pollQ (s := .sA1) (pc := 2446) rfl Flow.code_2446 Flow.code_2447 Flow.code_2448
    (by decide +kernel) rfl (fun m q ok sc' => by cases ok <;> rfl) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (qk_val hP c) e

theorem stepQ_sA1 (hP : Plain L g) (d : D) (hs : d.site = .sA1) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  ixq_site
  intro t u ins hat hinv hc hq hw hf
  refine Code.shflRecvQ (C := code P L g) (qt := ixQt) (ex := []) (Wf := IxWf P)
    (d := ⟨.sA1, 0, ac, c⟩) (dn := fun y => ⟨.sA2, 0, ac, { c with rv1 := .bits 32 y }⟩)
    Flow.code_2464
    (not_mem_factsFrom (live := ixLive 2464) (by decide +kernel))
    (not_mem_factsFrom (live := ixLive 2464) (by decide +kernel)) (by decide)
    (fun e he => he.shfl) (fun _ _ _ _ _ _ => rfl) rfl rfl (fun _ => rfl) (fun _ => rfl)
    (fun _ => IxSite.elems_pos _) (fun _ _ => typed_nil)
    (by show Code.afterWrites ixQt 2464 _ = _; decide +kernel)
    (fun _ _ => by ixq_seg) e ins hat hinv hc hq hw hf

theorem stepQ_sA2 (hP : Plain L g) (d : D) (hs : d.site = .sA2) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  ixq_site
  intro t u ins hat hinv hc hq hw hf
  refine Code.shflRecvQ (C := code P L g) (qt := ixQt) (ex := []) (Wf := IxWf P)
    (d := ⟨.sA2, 0, ac, c⟩) (dn := fun y => ⟨.stA, 0, ac, { c with rv2 := .bits 32 y }⟩)
    Flow.code_2467
    (not_mem_factsFrom (live := ixLive 2467) (by decide +kernel))
    (not_mem_factsFrom (live := ixLive 2467) (by decide +kernel)) (by decide)
    (fun e he => he.shfl) (fun _ _ _ _ _ _ => rfl) rfl rfl (fun _ => rfl) (fun _ => rfl)
    (fun _ => IxSite.elems_pos _) (fun _ _ => typed_nil)
    (by show Code.afterWrites ixQt 2467 _ = _; decide +kernel)
    (fun _ _ => by ixq_seg) e ins hat hinv hc hq hw hf

/-- After the coordinate pair: the validity byte or the arrival, by the lane's test. -/
theorem qstA_seg (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2472 (ixFacts P L g c .stA)
      (afterSt L g .bA .arrA).pc (ixFacts P L g c (afterSt L g .bA .arrA)) := by
  cases hk : ixSkipB L g
  · rw [show afterSt L g .bA .arrA = .bA by unfold afterSt; rw [hk]; rfl]
    ixq_br 2472 20 (ixSkipB L g) c Flow.code_2472 with hk
    ixq_seg
  · rw [show afterSt L g .bA .arrA = .arrA by unfold afterSt; rw [hk]; rfl]
    ixq_br 2472 20 (ixSkipB L g) c Flow.code_2472 with hk
    ixq_seg

theorem stepQ_stA (hP : Plain L g) (d : D) (hs : d.site = .stA) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  obtain ⟨s, el, ac, c⟩ := d
  dsimp only at hs; subst hs
  exact stQ (n := ofC (afterSt L g .bA .arrA, c)) (pc := 2471) rfl rfl rfl Flow.code_2471
    rfl rfl (fun _ => rfl) rfl (by unfold afterSt; split <;> rfl) (by decide +kernel)
    (qstA_seg hP c) e

theorem stepQ_bA (hP : Plain L g) (d : D) (hs : d.site = .bA) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  ixq_site
  intro t u ins hat hinv hc hq hw hf
  refine Code.scalarStoreQ (C := code P L g) (qt := ixQt) (ex := []) (Wf := IxWf P)
    (d := ⟨.bA, 0, ac, c⟩) (dn := ⟨.arrA, 0, ac, c⟩) Flow.code_2474 rfl rfl (fun _ => rfl)
    rfl rfl rfl rfl (IxSite.elems_pos _) (fun _ _ => typed_nil)
    (by show Code.afterWrites ixQt 2474 _ = _; decide +kernel) (by ixq_seg) e
    ins hat hinv hc hq hw hf

theorem stepQ_arrA (hP : Plain L g) (d : D) (hs : d.site = .arrA) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  ixq_site
  intro t u ins hat hinv hc hq hw hf
  refine Code.advanceQ (C := code P L g) (qt := ixQt) (ex := []) (Wf := IxWf P)
    (d := ⟨.arrA, 0, ac, c⟩) (dn := ofC (mainEnd c)) Flow.code_2476
    (fun hf => Code.fires_arrive_next hf) (fun _ => rfl) rfl rfl rfl rfl
    (IxSite.elems_pos _) (fun _ _ => typed_nil)
    (by show Code.afterWrites ixQt 2476 _ = _; decide +kernel) (qk_endA hP c) e
    ins hat hinv hc hq hw hf

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
