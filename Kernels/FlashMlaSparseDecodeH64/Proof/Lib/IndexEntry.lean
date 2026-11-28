-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexWalk
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LdParam
public import Lemmas.Flow.Step.SegSym
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # The index warp's parameter prefix

`ixw_entry`: from pc 2332 with the entry registers (`entryVal`), the index warp's parameter
prefix (pcs 2332–2359: the batch, the two length pointers and budgets by `ld.param` under `Pre`,
the other parameters havocked) leads to its first event `ixFirst`. Warpgroup 1's head composes it
with its dispatch on the word `7`. -/

/-! # A two-word `ld.param.v2.b32` through the parameter pointer, as one step

The index warp reads the extra index array's two row strides with one `ld.param.v2.b32` from
`[%rd2+208]` (pc 2346). `seg_ldp2` states that step as `seg_ldp` states a scalar one: the two
consecutive 4-byte fields `(off, x, 4)` and `(off + 4, y, 4)` of `p0fields` load as `pw x` and
`pw y` into the two destinations. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The shape of a two-word `ld.param.v2.b32` of `param_0` through register 2991. -/
abbrev ldp2Ins (off : Int) (d1 d2 : Nat) : Instr :=
  { guard := none,
    op := Op.mem
      { kind := MemKind.load, space := some StateSpace.param, sem := Sem.weak, scope := none,
        elem := .int .b 32, vec := 2, ext := MemExt.same, nc := false, noftz := false,
        hints := { cop := none, l1 := none, l2 := none, prefetch := none, policy := none },
        addr := { base := AddrBase.reg 2991 64, off := off }, dsts := [some d1, some d2],
        srcs := [], mmio := false } }

/-- **A two-word `ld.param.v2.b32` of two fields of `param_0`, as one step.** -/
theorem seg_ldp2 (hp : Pre P L m) {pc d1 d2 off x y : Nat} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some (ldp2Ins off d1 d2)) (hal : off % 8 = 0)
    (hoff : off + 8 ≤ 304) (hx : (off, x, 4) ∈ p0fields P L) (hy : (off + 4, y, 4) ∈ p0fields P L)
    (h2991 : (2991, .ptr 64 false (.param (param "0")) 0) ∈ F)
    (hd : freshKeys [(d1, .bits 32 (BitVec.ofNat 64 (leNat x 0 4))),
      (d2, .bits 32 (BitVec.ofNat 64 (leNat y 0 4)))] F = true) :
    Seg kernel Assumptions.all L g 1 pc F (pc + 1)
      ((d2, .bits 32 (BitVec.ofNat 64 (leNat y 0 4))) ::
        (d1, .bits 32 (BitVec.ofNat 64 (leNat x 0 4))) :: F) := by
  intro t h
  have hr0 : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) :=
    holds_mem (atHolds h) h2991
  have hbx := p0_bitsFrom hp hx 4 0 (by omega)
  have hby := p0_bitsFrom hp hy 4 0 (by omega)
  simp only [Nat.add_zero] at hbx hby
  refine ⟨_, run_local hc rfl h ?_, At.setRegsL h hd⟩
  rw [execLocalA_noSegment (asms_segment_free L g t)]
  rw [execLocalRule_of_none (fun a ha => ?_)]
  · rw [execLocal_mem rfl]
    have hal4 : (off + 4) % 4 = 0 := by omega
    simp [execMove, MemAccess.regs, paramObjectOf, readReg, hr0, hp.param0Object, scalarsParam,
      loadParamObject, hbx, hby, bind, Except.bind, pure, Except.pure, hal, paramElem,
      Functor.map, Except.map, hoff, DType.width, ParamObjectDecl.bytes, setRegsL]
  · simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Assumptions.paramPointers, Assumptions.sharedBits, Assumptions.deadPackRule,
        h.1] <;> rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A scalar `ld.param` of `param_0` at `pc`, then the rest of the segment. -/
theorem ix_ldp (hp : Pre P L m) {pc d off x n b : Nat} {ty : DType} {F G : List (Nat × Value)}
    (hc : kernel.code[pc]? = some (ldpIns ty off d))
    (hty : (ty = .int .b 32 ∧ n = 4) ∨ (ty = .int .b 64 ∧ n = 8)) (hal : off % n = 0)
    (hoff : off + n ≤ 304) (hf : (off, x, n) ∈ p0fields P L)
    (h2991 : (2991, .ptr 64 false (.param (param "0")) 0) ∈ F) (hd : d ∉ F.map Prod.fst)
    (rest : SegU kernel Assumptions.all L g (pc + 1)
      ((d, .bits (8 * n) (BitVec.ofNat 64 (leNat x 0 n))) :: F) b G) :
    SegU kernel Assumptions.all L g pc F b G :=
  SegU.comp (SegU.of_seg (seg_ldp hp hc hty hal hoff hf h2991
    fun _ hq he => hd (by rw [← he]; exact List.mem_map_of_mem hq))) rest

set_option hygiene false in
/-- An `ld.param` at code lemma `c` (field at `off` of `n` bytes into `d`), the facts before it
the table's at `pc`. -/
local macro "ldp_at " pc:term:max c:term:max ty:term:max off:term:max d:term:max n:term:max
    x:term:max : tactic => `(tactic| (
  refine SegU.comp (b := $pc) (G := factsFrom (ixLive $pc) (ixVal P L g (ixCtl0 P)))
    (by ix_seg) ?_
  refine ix_ldp (ty := $ty) (off := $off) (d := $d) (n := $n) (x := $x) hp $c (by decide)
    (by decide) (by decide) (by simp [p0fields])
    (mem_factsFrom_eq (show 2991 ∈ ixLive $pc by decide +kernel) rfl)
    (by rw [factsFrom_keys]; decide +kernel) ?_))

/-- The prefix from the extra array's strides to the first length pointer's test
(pcs 2345–2356). -/
theorem ixw_params1 (hp : Pre P L m) :
    SegU kernel Assumptions.all L g 2345 (factsFrom (ixLive 2345) (ixVal P L g (ixCtl0 P)))
      2357 (factsFrom (ixLive 2357) (ixVal P L g (ixCtl0 P))) := by
  refine ix_ldp (ty := .int .b 64) (off := 136) (d := 3012) (n := 8) (x := P.extraIndicesBase)
    hp Flow.code_2345 (by decide) (by decide) (by decide) (by simp [p0fields])
    (mem_factsFrom_eq (show 2991 ∈ ixLive 2345 by decide +kernel) rfl)
    (by rw [factsFrom_keys]; decide +kernel) ?_
  refine SegU.comp (b := 2346) (G := factsFrom (ixLive 2346) (ixVal P L g (ixCtl0 P)))
    (by ix_seg) ?_
  refine SegU.comp (SegU.of_seg (seg_ldp2 (d1 := 494) (d2 := 561) (x := P.s_q * P.extra_topk)
    (y := P.extra_topk) hp Flow.code_2346 (by decide) (by decide) (by simp [p0fields])
    (by simp [p0fields]) (mem_factsFrom_eq (show 2991 ∈ ixLive 2346 by decide +kernel) rfl)
    (by simp only [freshKeys, List.map_cons, factsFrom_keys]; decide +kernel))) ?_
  ldp_at 2349 Flow.code_2349 (.int .b 32) 36 497 4 P.page
  ldp_at 2355 Flow.code_2355 (.int .b 32) 116 502 4 P.extraPage
  ix_seg

/-- The prefix inside the batch up to the first length pointer's test (pcs 2335–2356). -/
theorem ixw_params (hp : Pre P L m) :
    SegU kernel Assumptions.all L g 2335 (factsFrom (ixLive 2335) (ixVal P L g (ixCtl0 P)))
      2357 (factsFrom (ixLive 2357) (ixVal P L g (ixCtl0 P))) := by
  ldp_at 2335 Flow.code_2335 (.int .b 32) 164 490 4 P.blockStride
  ldp_at 2336 Flow.code_2336 (.int .b 32) 200 491 4 P.extraBlockStride
  ldp_at 2337 Flow.code_2337 (.int .b 64) 80 3009 8 (P.topkLenBase.getD 0)
  ldp_at 2338 Flow.code_2338 (.int .b 32) 40 2968 4 P.topk
  ldp_at 2339 Flow.code_2339 (.int .b 64) 144 3010 8 (P.extraTopkLenBase.getD 0)
  ldp_at 2340 Flow.code_2340 (.int .b 32) 120 2969 4 P.extra_topk
  ldp_at 2341 Flow.code_2341 (.int .b 64) 72 3011 8 P.indicesBase
  ldp_at 2342 Flow.code_2342 (.int .b 32) 172 492 4 (P.s_q * P.topk)
  ldp_at 2343 Flow.code_2343 (.int .b 32) 176 560 4 P.topk
  refine SegU.comp (b := 2345) (G := factsFrom (ixLive 2345) (ixVal P L g (ixCtl0 P)))
    (by ix_seg) (ixw_params1 hp)

/-- The first length pointer null, the second's test (pcs 2357–2366). -/
theorem ixw_nullA (hA : eqz64 (pw8 (P.topkLenBase.getD 0)) = true) :
    SegU kernel Assumptions.all L g 2357 (factsFrom (ixLive 2357) (ixVal P L g (ixCtl0 P)))
      (ixAfterA P (ixCtl0 P)).1.pc
      (ixFacts P L g (ixAfterA P (ixCtl0 P)).2 (ixAfterA P (ixCtl0 P)).1) := by
  refine SegU.pick (r := 15) (x := .pred (eqz64 (pw8 (P.topkLenBase.getD 0))))
    (mem_factsFrom_eq (show 15 ∈ ixLive 2357 by decide +kernel) rfl) ?_
  refine SegU.comp (SegU.branch _ Flow.code_2357 bra_rule noSegments.segFreePc) ?_
  rw [hA]
  cases hB : eqz64 (pw8 (P.extraTopkLenBase.getD 0))
  · rw [show ixAfterA P (ixCtl0 P) = (.lenB, ixCtl0 P) by unfold ixAfterA; rw [hB]; rfl]
    ix_br 2362 16 (eqz64 (pw8 (P.extraTopkLenBase.getD 0))) (ixCtl0 P) Flow.code_2362
    rw [hB]; ix_seg
  · rw [show ixAfterA P (ixCtl0 P) = ixLens (ixCtl0 P) by unfold ixAfterA; rw [hB]; rfl]
    ix_br 2362 16 (eqz64 (pw8 (P.extraTopkLenBase.getD 0))) (ixCtl0 P) Flow.code_2362
    rw [hB]
    exact SegU.comp (b := 2366) (G := factsFrom (ixLive 2366) (ixVal P L g (ixCtl0 P)))
      (by ix_seg) (ixw_lens _)

/-- Inside the batch (pcs 2335–2360). -/
theorem ixw_batch (hp : Pre P L m) (hb : scmp .ge .s (r2W L g) (pw P.b) = false) :
    SegU kernel Assumptions.all L g 2335 (factsFrom (ixLive 2335) (ixVal P L g (ixCtl0 P)))
      (ixFirst P L g).1.pc (ixFacts P L g (ixFirst P L g).2 (ixFirst P L g).1) := by
  refine SegU.comp (ixw_params hp) ?_
  cases hA : eqz64 (pw8 (P.topkLenBase.getD 0))
  · rw [show ixFirst P L g = (.lenA, ixCtl0 P) by unfold ixFirst; dsimp only; rw [hb, hA]; rfl]
    refine SegU.pick (r := 15) (x := .pred (eqz64 (pw8 (P.topkLenBase.getD 0))))
      (mem_factsFrom_eq (show 15 ∈ ixLive 2357 by decide +kernel) rfl) ?_
    refine SegU.comp (SegU.branch _ Flow.code_2357 bra_rule noSegments.segFreePc) ?_
    rw [hA]; ix_seg
  · rw [show ixFirst P L g = ixAfterA P (ixCtl0 P) by
      unfold ixFirst; dsimp only; rw [hb, hA]; rfl]
    exact ixw_nullA hA

/-- The prefix from the batch's load (pcs 2332–2334). -/
theorem ixw_entry0 (hp : Pre P L m) :
    SegU kernel Assumptions.all L g 2332 (factsFrom (ixLive 2332) (ixVal P L g (ixCtl0 P)))
      (ixFirst P L g).1.pc (ixFacts P L g (ixFirst P L g).2 (ixFirst P L g).1) := by
  ldp_at 2332 Flow.code_2332 (.int .b 32) 0 559 4 P.b
  cases hb : scmp .ge .s (r2W L g) (pw P.b)
  · ix_br 2334 14 (scmp .ge .s (r2W L g) (pw P.b)) (ixCtl0 P) Flow.code_2334
    rw [hb]
    exact SegU.comp (b := 2335) (G := factsFrom (ixLive 2335) (ixVal P L g (ixCtl0 P)))
      (by ix_seg) (ixw_batch hp hb)
  · rw [show ixFirst P L g = (.exit, ixCtl0 P) by unfold ixFirst; dsimp only; rw [hb]; rfl]
    ix_br 2334 14 (scmp .ge .s (r2W L g) (pw P.b)) (ixCtl0 P) Flow.code_2334
    rw [hb]; ix_seg

/-- The entry registers are the table's at pc 2332. -/
theorem ix_entry_facts (R : Nat → Option Value)
    (hR : Holds R (factsFrom (Flow.live 2332) (entryVal L g))) :
    Holds R (factsFrom (ixLive 2332) (ixVal P L g (ixCtl0 P))) := by
  refine holds_of_pointwise fun r hr => ?_
  rw [show ixLive 2332 = [459, 460, 461, 466, 2991] by decide +kernel] at hr
  have hm : r ∈ Flow.live 2332 := by
    rw [show Flow.live 2332 = [459, 460, 461, 466, 2991] by decide +kernel]; exact hr
  rw [holds_mem hR (mem_factsFrom hm)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [entryVal, entryVals, ixVal, ixVals, ixLoop, ixSetup, List.lookup,
      List.cons_append, List.nil_append]
     try rfl)

/-- **The index warp's parameter prefix**: from pc 2332 with the entry registers to its first
event. -/
theorem ixw_entry (hp : Pre P L m) :
    SegU kernel Assumptions.all L g 2332 (factsFrom (Flow.live 2332) (entryVal L g))
      (ixFirst P L g).1.pc (ixFacts P L g (ixFirst P L g).2 (ixFirst P L g).1) :=
  SegU.comp (SegU.of_seg (Seg.weaken_end (Seg.refl 2332 _) ix_entry_facts)) (ixw_entry0 hp)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
