-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Steps
public import Lemmas.Flow.StrictLdv
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.SegG
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.CoordVal
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.StepsCoord
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.StepsElect
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.StepsLens
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.StepsLoop
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Gen.StepTma

@[expose] public section

/-! # The TMA warp's strict steps

`stepFor_site`: the strict step (`Code.StepFor`) of every state of the TMA warp for an event. The
exact obligations (`Steps.lean`) are strict already; the coordinate loads and the gathers, whose
obligations tolerate faults, are strict for an event whose bytes rebuild (a coordinate element,
`Code.ldvFor`) with the segments after them strict (`coord_segF`, `gather_segF`); a gather's
event is a plain issue. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A strict segment of the TMA warp, closed by the table's terms. -/
macro "tma_segF" : tactic => `(tactic| (
  try simp only [facts, Site.pc, coordPc, afterCoord, afterGather, Fin.isValue,
    Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte,
    Nat.reduceEqDiff, Fin.mk_one, Fin.zero_eta, Fin.reduceFinMk, Nat.reduceSub, Fin.reduceAdd,
    Fin.val_ofNat, Fin.coe_ofNat_eq_mod, Nat.reduceMod]
  seg_sym using tma_seg))

/-- **The segment after gather `k`** is strict. -/
theorem gather_segF (k : Fin 16) (d : D) (hs : d.site = .gather k) :
    ∃ n, Seg kernel Assumptions.all L g n ((Site.gather k).pc + 1) (facts P L g d)
      (afterGather k).pc (facts P L g { d with site := afterGather k }) := by
  tma_state d
  dsimp only at hs
  subst hs
  fin_cases k <;> tma_segF

/-- **From the second quadruple's last element to the first gather**, strict. -/
theorem land_g0F (hp : Pre P L m) (d : D) (v : Value) :
    ∃ n, Seg kernel Assumptions.all L g n 2255
      (factsFrom (Flow.live 2255) (valueOf P L g (afterQuad d 1 v))) 2259
      (facts P L g (afterQuad d 1 v)) := by
  have h2 : Seg kernel Assumptions.all L g 1 2255
      (factsFrom (Flow.live 2255) (valueOf P L g (afterQuad d 1 v))) 2256
      ((3052, .ptr 64 true (.param (param "1")) 0) ::
        factsFrom (Flow.live 2255) (valueOf P L g (afterQuad d 1 v))) :=
      fun t ht =>
    ⟨_, run_cvtaParam (pc := 2255) Flow.code_2255 ht
      (holds_mem (atHolds ht) (r := 2990) (mem_factsFrom (by decide))),
      At.set ht (not_mem_factsFrom (by decide))⟩
  have h3 : Seg kernel Assumptions.all L g 1 2256
      ((3052, .ptr 64 true (.param (param "1")) 0) ::
        factsFrom (Flow.live 2255) (valueOf P L g (afterQuad d 1 v))) 2257
      ((3049, .bits 64
        (BitVec.ofNat 64 (P.param1Base + (sel (scmp .lt .u d.cnt (nmain d.l0)) 768 896).toNat))) ::
        (3052, .ptr 64 true (.param (param "1")) 0) ::
        factsFrom (Flow.live 2255) (valueOf P L g (afterQuad d 1 v))) :=
      fun t ht =>
    ⟨_, run_paramAddReg (pc := 2256) Flow.code_2256 ht (by decide)
      (holds_mem (atHolds ht) (List.mem_cons_self ..))
      (holds_mem (atHolds ht) (r := 3051) (List.mem_cons_of_mem _ (mem_factsFrom (by decide))))
      hp.param1Object, At.set ht (by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · decide
        · exact not_mem_factsFrom (by decide) q hq)⟩
  have h4 : ∃ n, Seg kernel Assumptions.all L g n 2257
      ((3049, .bits 64
        (BitVec.ofNat 64 (P.param1Base + (sel (scmp .lt .u d.cnt (nmain d.l0)) 768 896).toNat))) ::
        (3052, .ptr 64 true (.param (param "1")) 0) ::
        factsFrom (Flow.live 2255) (valueOf P L g (afterQuad d 1 v))) 2259
      (facts P L g (afterQuad d 1 v)) := by
    tma_segF
  exact Seg.comp_ex ⟨2, h2.comp h3⟩ h4

/-- **The segment after the load of quadruple `k`** is strict. -/
theorem coord_segF (hp : Pre P L m) (k : Fin 16) (d : D) (hs : d.site = .coord3 k) (v : Value) :
    ∃ n, Seg kernel Assumptions.all L g n (coordPc k + 1)
      (factsFrom (Flow.live (coordPc k + 1)) (valueOf P L g (afterQuad d k v)))
      (afterCoord k).pc (facts P L g (afterQuad d k v)) := by
  tma_state d
  dsimp only at hs
  subst hs
  fin_cases k
  · tma_segF
  · exact land_g0F hp _ v
  all_goals tma_segF

/-- **An element of the load of quadruple `k`, strict** for an event whose bytes rebuild. -/
theorem coord_stepFor (hp : Pre P L m) (k : Fin 16) (d : D)
    (hs : d.site = .coord0 k ∨ d.site = .coord1 k ∨ d.site = .coord2 k ∨ d.site = .coord3 k)
    (e : Event)
    (hrb : ∀ x bs, e = ⟨(code P L g).pc d, .rd x bs⟩ → ∃ v, rebuild 3 bs = .ok v) :
    (code P L g).StepFor d e := by
  obtain ⟨a, hc, hl, hk, hnc, he, hreg⟩ := coord_code k
  have hlen : a.regs.length = 4 := by rw [hreg]; fin_cases k <;> rfl
  have hnd : a.regs.Nodup := by rw [hreg]; exact ldRegs_nodup k
  intro t u ins ha hi hc' hf
  tma_state d
  dsimp only at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact Code.ldvFor (C := code P L g) (d := ⟨.coord0 k, l0, l1, neg, cnt, buf, slot, pf, pr, ac,
      cp, cq⟩) (dok := fun v => ⟨.coord1 k, l0, l1, neg, cnt, buf, slot,
      pf, pr, { ac with w0 := v }, cp, cq⟩)
      hc hk hnc he hrb (fun x bs v hv => by simp [code, succ, rdAny, hv, Except.toOption])
      (fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩)
      rfl hnd (live' := []) (val' := fun _ _ => .pred false) (fun _ hr => nomatch hr)
      (fun _ _ hr => nomatch hr) (fun _ _ hr => nomatch hr)
      (fun hm => absurd (by simp [Site.sub, hlen]) hm) ins ha hi hc' hf
  · exact Code.ldvFor (C := code P L g) (d := ⟨.coord1 k, l0, l1, neg, cnt, buf, slot, pf, pr, ac,
      cp, cq⟩) (dok := fun v => ⟨.coord2 k, l0, l1, neg, cnt, buf, slot,
      pf, pr, { ac with w1 := v }, cp, cq⟩)
      hc hk hnc he hrb (fun x bs v hv => by simp [code, succ, rdAny, hv, Except.toOption])
      (fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩)
      rfl hnd (live' := []) (val' := fun _ _ => .pred false) (fun _ hr => nomatch hr)
      (fun _ _ hr => nomatch hr) (fun _ _ hr => nomatch hr)
      (fun hm => absurd (by simp [Site.sub, hlen]) hm) ins ha hi hc' hf
  · exact Code.ldvFor (C := code P L g) (d := ⟨.coord2 k, l0, l1, neg, cnt, buf, slot, pf, pr, ac,
      cp, cq⟩) (dok := fun v => ⟨.coord3 k, l0, l1, neg, cnt, buf, slot,
      pf, pr, { ac with w2 := v }, cp, cq⟩)
      hc hk hnc he hrb (fun x bs v hv => by simp [code, succ, rdAny, hv, Except.toOption])
      (fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩)
      rfl hnd (live' := []) (val' := fun _ _ => .pred false) (fun _ hr => nomatch hr)
      (fun _ _ hr => nomatch hr) (fun _ _ hr => nomatch hr)
      (fun hm => absurd (by simp [Site.sub, hlen]) hm) ins ha hi hc' hf
  · have hn : ∀ x : D, x.site = afterCoord k → x.site.sub = 0 ∧ accOf x = [] := by
      intro x hx; rw [accOf, hx]; unfold afterCoord; split <;> exact ⟨rfl, rfl⟩
    refine Code.ldvFor (C := code P L g) (d := ⟨.coord3 k, l0, l1, neg, cnt, buf, slot, pf, pr, ac,
      cp, cq⟩) (dok := afterQuad ⟨.coord3 k, l0, l1, neg, cnt, buf,
      slot, pf, pr, ac, cp, cq⟩ k)
      hc hk hnc he hrb (fun x bs v hv => by simp [code, succ, rdAny, hv, Except.toOption])
      (fun hm => absurd hm (by simp [Site.sub, hlen]))
      rfl hnd (live' := Flow.live (coordPc k + 1))
      (val' := fun v => valueOf P L g
        (afterQuad ⟨.coord3 k, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ k v))
      ?_ ?_ ?_ (fun _ v => ⟨(hn _ rfl).1, (hn _ rfl).2, trivial,
        coord_segF hp k ⟨.coord3 k, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ rfl v⟩)
      ins ha hi hc' hf
    · rw [hreg]; exact live_regs k
    · intro v r hr hn
      rw [hreg] at hn
      exact value_old k _ rfl v r hr hn
    · intro v r hr hin
      rw [hreg] at hin ⊢
      exact value_new k _ rfl v r hr hin

/-- **Gather `k` is strict** for every event. -/
theorem gather_stepFor (k : Fin 16) (d : D) (hs : d.site = .gather k) (e : Event) :
    (code P L g).StepFor d e := by
  obtain ⟨op, hc, hl, ha⟩ := gather_code (L := L) (g := g) k
  have hn : (afterGather k).sub = 0 := by unfold afterGather; split_ifs <;> rfl
  have hn' : accOf { d with site := afterGather k } = [] := by
    rw [accOf]; unfold afterGather; split_ifs <;> rfl
  have hst : (code P L g).StepOk d :=
    Code.step_issue (C := code P L g) (dn := { d with site := afterGather k }) (ins0 := ⟨none, op⟩)
      (by show kernel.code[d.site.pc]? = _; rw [hs]; exact hc)
      (fun hf => ha (by rw [← hs]; exact hf)) (fun e => by simp [code, succ, hs])
      (by show d.site.sub = 0; rw [hs]; rfl) (by show accOf d = []; rw [accOf, hs])
      ⟨fun _ => by
        show ∃ n, Seg _ _ _ _ n (d.site.pc + 1) _ _ _
        rw [hs]; exact gather_segF k d hs, hn, hn', fun _ => trivial⟩
  intro t u ins ha hi hc hf
  exact hst.step ins ha hi hc hf

/-- **Every state of the TMA warp is strict for an event**, a coordinate element's bytes
rebuilding a value. -/
theorem stepFor_site (hp : Pre P L m) (d : D) (e : Event)
    (hrb : (∃ k, d.site = .coord0 k ∨ d.site = .coord1 k ∨ d.site = .coord2 k ∨
        d.site = .coord3 k) →
      ∀ x bs, e = ⟨(code P L g).pc d, .rd x bs⟩ → ∃ v, rebuild 3 bs = .ok v) :
    (code P L g).StepFor d e := by
  cases hs : d.site with
  | elect => exact (stepAt_elect hp d hs).stepFor e
  | loadTopk => exact (stepAt_loadTopk d hs).stepFor e
  | loadExtra => exact (stepAt_loadExtra d hs).stepFor e
  | qWait => exact (stepAt_qWait d hs).stepFor e
  | storeWait => exact (stepAt_storeWait d hs).stepFor e
  | coordWait => exact (stepAt_coordWait d hs).stepFor e
  | rawWait => exact (stepAt_rawWait d hs).stepFor e
  | coord0 k => exact coord_stepFor hp k d (.inl hs) e (hrb ⟨k, .inl hs⟩)
  | coord1 k => exact coord_stepFor hp k d (.inr (.inl hs)) e (hrb ⟨k, .inr (.inl hs)⟩)
  | coord2 k =>
    exact coord_stepFor hp k d (.inr (.inr (.inl hs))) e (hrb ⟨k, .inr (.inr (.inl hs))⟩)
  | coord3 k =>
    exact coord_stepFor hp k d (.inr (.inr (.inr hs))) e (hrb ⟨k, .inr (.inr (.inr hs))⟩)
  | gather k => exact gather_stepFor k d hs e
  | rawArrive => exact (stepAt_rawArrive d hs).stepFor e
  | coordFree => exact (stepAt_coordFree d hs).stepFor e
  | outBar => exact (stepAt_outBar d hs).stepFor e
  | exit => exact (stepAt_exit d hs).stepFor e
  | leave s => exact (stepAt_leave d hs).stepFor e

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
