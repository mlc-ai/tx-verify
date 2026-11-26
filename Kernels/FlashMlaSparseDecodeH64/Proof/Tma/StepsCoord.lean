-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.SegG
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.CoordVal
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CtlSteps
public import Lemmas.Flow.CtlStepsU
public import Lemmas.Flow.CtlStepsDU
public import Lemmas.Flow.TensorIssue
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # The TMA warp's obligations at the coordinate loads and the gathers

The 16 shared loads of a block's coordinate quadruples, four `b32` elements each, continue on any
payload (`Code.ldvU`): an element stays at the load one sub-step on and keeps its value in `ac`;
the fourth continues at the next quadruple (after the first) or at the gather of the quadruple
before. The 16 four-row gathers continue at the next instruction (`Code.advanceU`). The
coordinate words are not facts, so these obligations are UB-tolerant (`StepAtU`): the segments
after them are `SegU`s (`tma_segU`), and a gather whose coordinates are not 32-bit words faults. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The decoded load of quadruple `k`: four `b32` elements into the quadruple's registers. -/
theorem coord_code (k : Fin 16) : ∃ a : MemAccess,
    kernel.code[coordPc k]? = some ⟨none, .mem a⟩ ∧ (Op.mem a).isLocal = false ∧
      a.kind = .load ∧ a.nc = false ∧ a.ext = .same ∧ a.regs = ldRegs k := by
  fin_cases k
  all_goals exact ⟨_, by simp only [coordPc]; code_lookup, rfl, rfl, rfl, rfl, rfl⟩

theorem ldRegs_nodup (k : Fin 16) : (ldRegs k).Nodup := by
  fin_cases k <;> decide

/-- **An element of the load of quadruple `k`**, given the segment after its fourth. -/
theorem coord_step (k : Fin 16) (d : D)
    (hs : d.site = .coord0 k ∨ d.site = .coord1 k ∨ d.site = .coord2 k ∨ d.site = .coord3 k)
    (seg : ∀ d : D, d.site = .coord3 k → ∀ v, SegU kernel Assumptions.all L g (coordPc k + 1)
      (factsFrom (Flow.live (coordPc k + 1)) (valueOf P L g (afterQuad d k v)))
      (afterCoord k).pc (facts P L g (afterQuad d k v))) :
    (code P L g).StepAtU d := by
  obtain ⟨a, hc, hl, hk, hnc, he, hreg⟩ := coord_code k
  have hlen : a.regs.length = 4 := by rw [hreg]; fin_cases k <;> rfl
  have hnd : a.regs.Nodup := by rw [hreg]; exact ldRegs_nodup k
  tma_state d
  dsimp only at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact Code.ldvDU (C := code P L g) (dok := fun v => ⟨.coord1 k, l0, l1, neg, cnt, buf, slot,
      pf, pr, { ac with w0 := v }, cp, cq⟩)
      (dbad := ⟨.coord1 k, l0, l1, neg, cnt, buf, slot, pf, pr, { ac with w0 := .pred false },
        cp, cq⟩)
      hc hl hk hnc he (fun x bs v hv => by simp [code, succ, rdAny, hv, Except.toOption])
      (fun x bs f hf => by simp [code, succ, rdAny, hf, Except.toOption])
      (fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩)
      rfl hnd (live' := []) (val' := fun _ _ => .pred false) (fun _ hr => nomatch hr)
      (fun _ _ hr => nomatch hr) (fun _ _ hr => nomatch hr)
      (fun hm => absurd (by simp [Site.sub, hlen]) hm)
  · exact Code.ldvDU (C := code P L g) (dok := fun v => ⟨.coord2 k, l0, l1, neg, cnt, buf, slot,
      pf, pr, { ac with w1 := v }, cp, cq⟩)
      (dbad := ⟨.coord2 k, l0, l1, neg, cnt, buf, slot, pf, pr, { ac with w1 := .pred false },
        cp, cq⟩)
      hc hl hk hnc he (fun x bs v hv => by simp [code, succ, rdAny, hv, Except.toOption])
      (fun x bs f hf => by simp [code, succ, rdAny, hf, Except.toOption])
      (fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩)
      rfl hnd (live' := []) (val' := fun _ _ => .pred false) (fun _ hr => nomatch hr)
      (fun _ _ hr => nomatch hr) (fun _ _ hr => nomatch hr)
      (fun hm => absurd (by simp [Site.sub, hlen]) hm)
  · exact Code.ldvDU (C := code P L g) (dok := fun v => ⟨.coord3 k, l0, l1, neg, cnt, buf, slot,
      pf, pr, { ac with w2 := v }, cp, cq⟩)
      (dbad := ⟨.coord3 k, l0, l1, neg, cnt, buf, slot, pf, pr, { ac with w2 := .pred false },
        cp, cq⟩)
      hc hl hk hnc he (fun x bs v hv => by simp [code, succ, rdAny, hv, Except.toOption])
      (fun x bs f hf => by simp [code, succ, rdAny, hf, Except.toOption])
      (fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩)
      rfl hnd (live' := []) (val' := fun _ _ => .pred false) (fun _ hr => nomatch hr)
      (fun _ _ hr => nomatch hr) (fun _ _ hr => nomatch hr)
      (fun hm => absurd (by simp [Site.sub, hlen]) hm)
  · have hn : ∀ x : D, x.site = afterCoord k → x.site.sub = 0 ∧ accOf x = [] := by
      intro x hx; rw [accOf, hx]; unfold afterCoord; split <;> exact ⟨rfl, rfl⟩
    refine Code.ldvDU (C := code P L g) (dok := afterQuad ⟨.coord3 k, l0, l1, neg, cnt, buf,
      slot, pf, pr, ac, cp, cq⟩ k)
      (dbad := afterQuad ⟨.coord3 k, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ k
        (.pred false))
      hc hl hk hnc he (fun x bs v hv => by simp [code, succ, rdAny, hv, Except.toOption])
      (fun x bs f hf => by simp [code, succ, rdAny, hf, Except.toOption])
      (fun hm => absurd hm (by simp [Site.sub, hlen]))
      rfl hnd (live' := Flow.live (coordPc k + 1))
      (val' := fun v => valueOf P L g
        (afterQuad ⟨.coord3 k, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ k v))
      ?_ ?_ ?_ (fun _ v => ⟨(hn _ rfl).1, (hn _ rfl).2, trivial,
        seg ⟨.coord3 k, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ rfl v⟩)
    · rw [hreg]; exact live_regs k
    · intro v r hr hn
      rw [hreg] at hn
      exact value_old k _ rfl v r hr hn
    · intro v r hr hin
      rw [hreg] at hin ⊢
      exact value_new k _ rfl v r hr hin

/-- The decoded gather `k`: its firing continues at the next instruction. -/
theorem gather_code (k : Fin 16) : ∃ op, kernel.code[(Site.gather k).pc]? = some ⟨none, op⟩ ∧
    op.isLocal = false ∧ ∀ {t u : TState} {e : Event},
      Fires (Site.gather k).pc (eventTmpl Assumptions.all L g t op) e (some u) →
        u = PTX.next t := by
  fin_cases k
  all_goals exact ⟨_, by simp only [Site.pc]; code_lookup, rfl,
    fun hf => (fires_cpTensor_issue hf).choose_spec.choose_spec.2.1⟩

/-- **Gather `k`**, given the segment after it. -/
theorem gather_step (k : Fin 16) (d : D) (hs : d.site = .gather k)
    (seg : SegU kernel Assumptions.all L g ((Site.gather k).pc + 1) (facts P L g d)
      (afterGather k).pc (facts P L g { d with site := afterGather k })) :
    (code P L g).StepAtU d := by
  obtain ⟨op, hc, hl, ha⟩ := gather_code (L := L) (g := g) k
  have hn : (afterGather k).sub = 0 := by unfold afterGather; split_ifs <;> rfl
  have hn' : accOf { d with site := afterGather k } = [] := by
    rw [accOf]; unfold afterGather; split_ifs <;> rfl
  exact Code.advanceU (C := code P L g) (dn := { d with site := afterGather k })
    (by show kernel.code[d.site.pc]? = _; rw [hs]; exact hc) hl
    (fun hf => ha (by rw [← hs]; exact hf)) (fun e => by simp [code, succ, hs])
    (by show d.site.sub = 0; rw [hs]; rfl) (by show accOf d = []; rw [accOf, hs])
    hn hn' trivial (by show SegU _ _ _ _ (d.site.pc + 1) _ _ _; rw [hs]; exact seg)

/-- The segment after the load of quadruple `k`, from the facts with its four words. -/
theorem coord_seg (hp : Pre P L m) (k : Fin 16) (d : D) (hs : d.site = .coord3 k) (v : Value) :
    SegU kernel Assumptions.all L g (coordPc k + 1)
      (factsFrom (Flow.live (coordPc k + 1)) (valueOf P L g (afterQuad d k v)))
      (afterCoord k).pc (facts P L g (afterQuad d k v)) := by
  tma_state d
  dsimp only at hs
  subst hs
  fin_cases k
  · tma_segU
  · exact land_g0 hp _ rfl v
  all_goals tma_segU

/-- The segment after gather `k`. -/
theorem gather_seg (k : Fin 16) (d : D) (hs : d.site = .gather k) :
    SegU kernel Assumptions.all L g ((Site.gather k).pc + 1) (facts P L g d)
      (afterGather k).pc (facts P L g { d with site := afterGather k }) := by
  tma_state d
  dsimp only at hs
  subst hs
  fin_cases k <;> tma_segU

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
