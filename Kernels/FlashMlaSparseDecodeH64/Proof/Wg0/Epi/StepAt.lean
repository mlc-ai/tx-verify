-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Epi.StepsHead
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop.StepsSetup
public import Lemmas.Flow.ElectU
public import Lemmas.Flow.Step.SegSym
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part018
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part020
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part021
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part023
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part024
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part025
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part026
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part028
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part056
import Lemmas.Flow.IssueNext
import Lemmas.Flow.RoleTemplates

@[expose] public section

/-! # Warpgroup 0's obligations in the epilogue

`Wg0.Epi.stepAt`: every state at a site of the epilogue (`Site.inLoop = false`, pc ≥ 1147)
steps, under `Pre`. -/

/-! # Warpgroup 0's obligations at the output chunks' loads and staging stores

Per output chunk `c`: the accumulator load and its wait (`old c`, `oldw c`; the wait's segment
crosses the chunk's scaling and conversion, data only), and the eight four-element staging stores
(`ost2 c k`). Each family is one proof over its indices (`fin_cases`, one tactic; the code lemma
of each pc is found by `code_lookup`). -/

/-! # Warpgroup 0's obligations at the output chunks' tails and the end

Per output chunk `c`: the proxy fence (`ofpx c`), the named barrier and the warp test after it
(`obar c`: warps 2 and 3 go on to the next chunk, warps 0 and 1 elect), the election (`oel c`: the
elected lane goes on to the TMA store, the others to the next chunk; the election writes the
leader and the predicate, and the branch after it is on their copy) and the TMA store (`otma c`).
Then the bulk commit, the closing named barrier with the warp test (`finish`), the deallocation
(warp 0) and the return. -/

/-! # Helpers for the output chunks' obligations

`ost2U`: an element of a staging store (`ost2 c k`, four elements); after the last element the
store `k + 1` of the chunk, after the eighth the chunk's proxy fence. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The site after staging store `k` of chunk `c`. -/
abbrev ost2Next (c : Fin 4) (k : Fin 8) : Site :=
  [.ost2 c 1, .ost2 c 2, .ost2 c 3, .ost2 c 4, .ost2 c 5, .ost2 c 6, .ost2 c 7].getD k.val
    (.ofpx c)

/-- An element of a staging store (four elements): the next element, after the last the site
`S`. -/
theorem ost2U {d : D} {c : Fin 4} {k : Fin 8} {a : MemAccess} (S : Site)
    (hsite : d.site = .ost2 c k) (hc0 : kernel.code[d.site.pc]? = some ⟨none, .mem a⟩)
    (hl : (Op.mem a).isLocal = false) (hst : a.kind = .store) (hlen : a.srcs.length = 4)
    (hS : ost2Next c k = S) (h1 : 0 < elems S)
    (seg : SegU kernel Assumptions.all L g (d.site.pc + 1) (facts P L g w d) S.pc
      (facts P L g w { d with site := S, el := 0 })) :
    (code P L g w).StepAtU d :=
  vst4U S (fun d' h => by unfold D.acc; rw [h, hsite]; exact ite_self _) (by rw [hsite]; rfl)
    hc0 hl hst hlen (fun e => by simp only [succ, hsite, ← hS]) h1 seg

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Flow PTX.Proof PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

theorem stepAt_ofpx (d : D) (c : Fin 4) (hs : d.site = .ofpx c) : (code P L g w).StepAtU d := by
  w0_site
  fin_cases c <;>
  · w0_adv (by code_lookup) by exact Option.some.inj (fires_fence_proxy hf).2
    w0_seg

theorem afterObar_el (k : Fin 4) (d : D) : (afterObar w k d).el = d.el := by
  unfold afterObar; split <;> rfl

set_option hygiene false in
/-- The named barrier of chunk `C`, then the warp test (branch at `B` on `p`). -/
local macro "obar_at " C:term:max B:num p:num : tactic => `(tactic| (
  refine adv0 (by code_lookup) rfl (fun hf => fires_barSyncN_next hf) (fun _ => rfl) rfl
    (afterObar_el (w := w) $C ⟨.obar $C, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩) ?_
  rw [afterObar]
  cases hb : scmpi .gt .s w 1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    w0_br $B (by code_lookup) $p (scmpi .gt .s w 1) hb
      ⟨.obar $C, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩
    w0_seg
  · simp only [↓reduceIte, nextChunk]
    w0_br $B (by code_lookup) $p (scmpi .gt .s w 1) hb
      ⟨.obar $C, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩
    w0_seg))

theorem stepAt_obar (d : D) (c : Fin 4) (hs : d.site = .obar c) : (code P L g w).StepAtU d := by
  w0_site
  fin_cases c
  · obar_at 0 1346 121
  · obar_at 1 1503 123
  · obar_at 2 1660 125
  · obar_at 3 1818 127

set_option hygiene false in
/-- The election of chunk `C` at `E` into the leader `rx` and the predicate `px`; the branch at
`B` on `p` (the predicate's copy) skips the TMA store. -/
local macro "oel_at " C:term:max E:num rx:num px:num B:num p:num : tactic => `(tactic| (
  refine Code.electU (r := $rx) (p := $px) (by code_lookup)
    (by change _ ∉ (factsFrom _ _).map Prod.fst; rw [factsFrom_keys]
        show _ ∉ ctlLive $E; decide +kernel)
    (by change _ ∉ (factsFrom _ _).map Prod.fst; rw [factsFrom_keys]
        show _ ∉ ctlLive $E; decide +kernel)
    (by decide) (fun _ _ _ => rfl) rfl rfl
    (fun _ => by dsimp only [code, nextChunk]; split <;> rfl)
    (fun _ => by dsimp only [code, nextChunk]; split <;> rfl)
    (fun _ => by dsimp only [code, nextChunk]; split <;> exact elems_pos _) (fun ld => ?_)
  by_cases h : PTX.laneOf L g = ld
  · rw [show (PTX.laneOf L g == ld) = true from beq_iff_eq.mpr h]
    dsimp only [code]; simp only [h, ↓reduceIte]
    refine SegU.comp (b := $B) (G := ($p, .pred false) ::
      factsFrom ((ctlLive $B).erase $p)
        (valueOf P L g w ⟨.oel $C, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩)) (by w0_seg) ?_
    refine SegU.comp (SegU.branch false (by code_lookup) bra_rule noSegments.segFreePc) ?_
    w0_seg
  · rw [show (PTX.laneOf L g == ld) = false from beq_eq_false_iff_ne.mpr h]
    dsimp only [code]; simp only [h, ↓reduceIte, nextChunk]
    refine SegU.comp (b := $B) (G := ($p, .pred true) ::
      factsFrom ((ctlLive $B).erase $p)
        (valueOf P L g w ⟨.oel $C, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩)) (by w0_seg) ?_
    refine SegU.comp (SegU.branch true (by code_lookup) bra_rule noSegments.segFreePc) ?_
    w0_seg))

theorem stepAt_oel_0 (d : D) (hs : d.site = .oel 0) : (code P L g w).StepAtU d := by
  w0_site; oel_at 0 1350 4078 4079 1354 122
theorem stepAt_oel_1 (d : D) (hs : d.site = .oel 1) : (code P L g w).StepAtU d := by
  w0_site; oel_at 1 1507 4080 4081 1511 124
theorem stepAt_oel_2 (d : D) (hs : d.site = .oel 2) : (code P L g w).StepAtU d := by
  w0_site; oel_at 2 1664 4082 4083 1668 126
theorem stepAt_oel_3 (d : D) (hs : d.site = .oel 3) : (code P L g w).StepAtU d := by
  w0_site; oel_at 3 1822 4084 4085 1826 128

/-- **The elections** (one declaration per chunk keeps each under its time budget). -/
theorem stepAt_oel (d : D) (c : Fin 4) (hs : d.site = .oel c) : (code P L g w).StepAtU d := by
  fin_cases c
  · exact stepAt_oel_0 d hs
  · exact stepAt_oel_1 d hs
  · exact stepAt_oel_2 d hs
  · exact stepAt_oel_3 d hs

theorem stepAt_otma (d : D) (c : Fin 4) (hs : d.site = .otma c) : (code P L g w).StepAtU d := by
  w0_site
  fin_cases c <;>
  · w0_adv (by code_lookup) by exact fires_cpTensorStore_next hf
    dsimp only [nextChunk]
    w0_seg

theorem stepAt_commit (d : D) (hs : d.site = .commit) : (code P L g w).StepAtU d := by
  w0_site
  w0_adv Flow.code_1832 by exact fires_bulkCommit_next hf
  w0_seg

/-- The closing named barrier, then the warp test (`finish`). -/
theorem stepAt_ebar (d : D) (hs : d.site = .ebar) : (code P L g w).StepAtU d := by
  w0_site
  refine adv0 Flow.code_1835 rfl (fun hf => fires_barSyncN_next hf) (fun _ => rfl) rfl
    (finish_el (w := w) ⟨.ebar, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩) ?_
  rw [finish]
  cases h : scmpi .ne .b w 0
  · simp only [Bool.false_eq_true, ↓reduceIte]
    w0_br 1837 Flow.code_1837 129 (scmpi .ne .b w 0) h
      ⟨.ebar, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩
    w0_seg
  · simp only [↓reduceIte]
    w0_br 1837 Flow.code_1837 129 (scmpi .ne .b w 0) h
      ⟨.ebar, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩
    w0_seg

/-- The deallocation (warp 0), then the jump to the return. -/
theorem stepAt_dealloc (d : D) (hs : d.site = .dealloc) : (code P L g w).StepAtU d := by
  w0_site
  w0_adv Flow.code_1840 by exact fires_tcDealloc_next hf
  refine SegU.comp (SegU.of_seg (seg_jmp Flow.code_1841 (fun t _ => bra_rule t)
    noSegments.segFreePc)) ?_
  w0_seg

/-- The return: no transition (its firing ends the thread). -/
theorem stepAt_exit (d : D) (hs : d.site = .exit) : (code P L g w).StepAtU d := by
  w0_site
  refine ⟨fun _ => ⟨_, Flow.code_3611, rfl, trivial⟩, fun ins _ _ hc hf => ?_⟩
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_3611)
  simp only [eventTmpl, Fires] at hf
  cases hf.2

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

theorem stepAt_old (d : D) (c : Fin 4) (hs : d.site = .old c) : (code P L g w).StepAtU d := by
  w0_site
  fin_cases c <;>
  · refine Code.tcLoadU (by code_lookup) (fun _ h => by cases h) (noLdWait _) rfl
      (by dsimp only; decide +kernel) (fun _ _ => rfl) rfl rfl rfl rfl Nat.one_pos ?_
    w0_seg

theorem stepAt_oldw (d : D) (c : Fin 4) (hs : d.site = .oldw c) : (code P L g w).StepAtU d := by
  w0_site
  fin_cases c <;>
  · refine Code.advanceU (by code_lookup) rfl
      (fun hf => Code.fires_tcPlain_next (.inr (.inr rfl)) hf) (fun _ => rfl) rfl rfl rfl rfl
      (Nat.zero_lt_succ _) ?_
    w0_seg

set_option hygiene false in
/-- The eight staging stores of one chunk (its index fixed): one tactic over the store index. -/
local macro "ost2_tac" : tactic => `(tactic| (
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  dsimp only at hs; subst hs
  fin_cases k <;>
  · refine ost2U _ rfl (by code_lookup) rfl rfl rfl
      (by simp only [ost2Next, List.getD_cons_succ, List.getD_cons_zero, List.getD_nil]; rfl)
      (elems_pos _) ?_
    w0_seg))

theorem stepAt_ost2_0 (d : D) (k : Fin 8) (hs : d.site = .ost2 0 k) :
    (code P L g w).StepAtU d := by ost2_tac
theorem stepAt_ost2_1 (d : D) (k : Fin 8) (hs : d.site = .ost2 1 k) :
    (code P L g w).StepAtU d := by ost2_tac
theorem stepAt_ost2_2 (d : D) (k : Fin 8) (hs : d.site = .ost2 2 k) :
    (code P L g w).StepAtU d := by ost2_tac
theorem stepAt_ost2_3 (d : D) (k : Fin 8) (hs : d.site = .ost2 3 k) :
    (code P L g w).StepAtU d := by ost2_tac

/-- **The staging stores** (one declaration per chunk keeps each under its time budget). -/
theorem stepAt_ost2 (d : D) (c : Fin 4) (k : Fin 8) (hs : d.site = .ost2 c k) :
    (code P L g w).StepAtU d := by
  fin_cases c
  · exact stepAt_ost2_0 d k hs
  · exact stepAt_ost2_1 d k hs
  · exact stepAt_ost2_2 d k hs
  · exact stepAt_ost2_3 d k hs

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Epi
open PTX PTX.Flow Wg0.Control

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

/-- **The epilogue's step obligations.** -/
theorem stepAt (hp : Pre P L m) (d : D) (hl : d.site.inLoop = false) :
    (code P L g w).StepAtU d := by
  cases hs : d.site <;> rw [hs] at hl
  case ebar0 => exact stepAt_ebar0 d hs
  case est => exact stepAt_est d hs
  case ebar1 => exact stepAt_ebar1 d hs
  case eld => exact stepAt_eld hp d hs
  case lse => exact stepAt_lse d hs
  case wsv => exact stepAt_wsv d hs
  case efa => exact stepAt_efa hp d hs
  case old c => exact stepAt_old d c hs
  case oldw c => exact stepAt_oldw d c hs
  case ost2 c k => exact stepAt_ost2 d c k hs
  case ofpx c => exact stepAt_ofpx d c hs
  case obar c => exact stepAt_obar d c hs
  case oel c => exact stepAt_oel d c hs
  case otma c => exact stepAt_otma d c hs
  case commit => exact stepAt_commit d hs
  case ebar => exact stepAt_ebar d hs
  case dealloc => exact stepAt_dealloc d hs
  case exit => exact stepAt_exit d hs
  case sld a k => cases a <;> fin_cases k <;> exact absurd hl (by decide)
  case pst k | pld k => fin_cases k <;> exact absurd hl (by decide)
  case ost c | rld c | rldw c | rst c | rstw c => fin_cases c <;> exact absurd hl (by decide)
  all_goals exact absurd hl (by decide)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Epi
