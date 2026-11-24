-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.InputIssues
public import Lemmas.Flow.TensorCoords

@[expose] public section

/-! # The box a loader's load copies, and its block

The load of block `b`, part `j`, of the trip at block `q` of the tile `(m, n)` copies the box at
column `64 (q + b)` and, for an A part (`j < 2`), row `512 m + 256 r + 128 j` (the CTA's rank `r`),
for the B part row `256 n + 128 r` (`Loader.load_origin`). Along the loader's run the load is of
the task numbered by its successful response polls, whose tile it holds (`LoaderTasks.TileRel`),
at block `q + b` of that task (`loader_block_fact`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The row of the box of part `j` of a load of tile `(m, n)` by a loader of CTA rank `r`. -/
def Loader.loadRow (m n r j : Nat) : Nat := if j < 2 then outputRow m r j 0 else 256 * n + 128 * r

namespace Loader

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

set_option maxHeartbeats 8000000 in
/-- **The origin of a load's box.** -/
theorem load_origin {d : D} {t u : TState} {ins : Instr} {e : Event}
    {b : Fin 8} {j : Fin 3} (hs : d.site = .load b j) (h : At t d.site.pc (facts L g d))
    (hi : Inv d) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    ∀ a sp, e.kind = .tensorIssue a sp → ∀ i : Fin (sp.outer + 1),
      sp.origin i = if i.val = 0 then ((64 * (d.q + b.val) : Nat) : Int)
        else if i.val = 1 then ((loadRow d.m d.n (g / L.block % 2) j.val : Nat) : Int) else 0 := by
  have hm := hi.m
  have hn := hi.n
  have hq := hi.q
  have hr : g / L.block % 2 < 2 := Nat.mod_lt _ (by decide)
  obtain ⟨site, m, n, q, cp, r, x⟩ := d
  simp only at hs h hc hf hm hn hq ⊢
  subst hs
  fin_cases b <;> fin_cases j <;> code_at hc <;> subst hc <;>
    exact fires_cpTensor_origin2 hf
      ((holds_mem h.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by loader_values)))
      ((holds_mem h.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by loader_values; simp [loadRow, outputRow])))
      (by omega) (by simp [loadRow, outputRow]; omega)

/-- A tensor map held as a kernel parameter's pointer is the parameter's map. -/
theorem map_param (hpre : Pre P L mem0) {t : TState} {r : Nat} {name : String} {a : Nat}
    (hr0 : t.regs r = some (.ptr 64 true (.param name) 0))
    (hn : name = "gemm_kernel_param_0" ∨ name = "gemm_kernel_param_1")
    (hma : tensorMapAddress L g t (.reg r) = .ok a) :
    L.paramObjects name = some (mapParam name, a) := by
  obtain ⟨M, hpar, h1, h2⟩ : ∃ M, L.paramObjects name = some (mapParam name, M) ∧ M % 128 = 0 ∧
      M + 128 ≤ 2 ^ 64 := by
    rcases hn with rfl | rfl
    · exact ⟨_, hpre.paramA, hpre.mapAlignment.1, hpre.mapRange.1⟩
    · exact ⟨_, hpre.paramB, hpre.mapAlignment.2.1, hpre.mapRange.2.1⟩
  obtain rfl : a = M := by
    simp only [tensorMapAddress, readValue, readReg, hr0, hpar, mapParam, ParamObjectDecl.bytes,
      bind, Except.bind, pure, Except.pure, le_refl, Nat.ofNat_pos, h1,
      show M + 128 ≤ 2 ^ 64 from h2, and_self, ↓reduceIte, Except.ok.injEq] at hma
    exact hma.symm
  exact hpar

set_option maxHeartbeats 8000000 in
/-- **The map a load reads**: the A parameter's for an A part, the B parameter's for the B part. -/
theorem load_param (hpre : Pre P L mem0) {d : D} {t u : TState} {ins : Instr} {e : Event}
    {b : Fin 8} {j : Fin 3} (hs : d.site = .load b j) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    ∀ a sp, e.kind = .tensorIssue a sp →
      L.paramObjects (if j.val < 2 then "gemm_kernel_param_0" else "gemm_kernel_param_1") =
        some (mapParam (if j.val < 2 then "gemm_kernel_param_0" else "gemm_kernel_param_1"), a) :=
          by
  obtain ⟨site, m, n, q, cp, r, x⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  intro a sp hk
  fin_cases b <;> fin_cases j <;> code_at hc <;> subst hc <;>
    obtain ⟨a', s', he', hma, -⟩ := fires_cpTensor_box hf <;>
    rw [he'] at hk <;> simp only [Kind.tensorIssue.injEq] at hk <;> obtain ⟨rfl, rfl⟩ := hk <;>
    exact map_param hpre ((holds_mem h.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
      (congrArg some (by loader_values; rfl))) (by decide) hma

end Loader

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **A load's block and box.** A loader's tensor issue at block `b`, part `j`, of the trip at `q`
is its load of block `q + b` of the task numbered by its successful response polls, on that task's
tile `(m, n)`; it is the slot's share of the blocks so far; its box is at column `64 (q + b)` and
row `loadRow m n r j`. -/
theorem loader_block_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k pc a : Nat} {sp : TensorCopy.Spec} {l : Loader.D} {b : Fin 8}
    {j : Fin 3} (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.loader l)))) (hs : l.site = .load b j) :
    loaderCount L g ((X.tr g).take k) =
      128 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) + l.q + b.val + 1 ∧
    l.q % 8 = 0 ∧ l.q < 128 ∧
    okPolls (InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b)) ((X.tr g).take k) =
      (loaderCount L g ((X.tr g).take k) + 3 - (InputRing.slotOf b).val) / 4 ∧
    Consumer.TileAt L g ((X.tr g).take k)
      (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k)) l.m l.n ∧
    l.m < 16 ∧ l.n < 32 ∧
    (∀ i : Fin (sp.outer + 1), sp.origin i = if i.val = 0 then ((64 * (l.q + b.val) : Nat) : Int)
      else if i.val = 1 then ((Loader.loadRow l.m l.n (g / L.block % 2) j.val : Nat) : Int)
      else 0) ∧
    L.paramObjects (if j.val < 2 then "gemm_kernel_param_0" else "gemm_kernel_param_1") =
      some (mapParam (if j.val < 2 then "gemm_kernel_param_0" else "gemm_kernel_param_1"), a) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨hC, hT, -⟩ : LoaderTasks.AlongT L g (.inr (.loader l)) ((X.tr g).take k) :=
    LoaderTasks.runT hpre hg htr k _ hσ
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hi : Loader.Inv l := hinv.1
  have hcond : LoaderCond l (lcount L g ((X.tr g).take k)) := hC.cond
  have hresp : LoaderTasks.CountOK l (lcount L g ((X.tr g).take k))
      (okPolls (clcResp L g) ((X.tr g).take k)) := hC.resp
  simp only [LoaderCond, LoaderTasks.CountOK, hs] at hcond hresp
  have hrank := hC.rank (InputRing.slotOf b)
  have hq8 := hi.q8
  have hq := hi.q
  have hb := b.isLt
  cases o with
  | none => exact absurd rfl (fires_none_notTensor hfire _ _)
  | some u =>
    have horig := Loader.load_origin hs hat hi hc hfire a sp rfl
    have hpar := Loader.load_param hpre hs hat hc hfire a sp rfl
    refine ⟨?_, hq8, hq, ?_, hT (by simp [Loader.Site.inTask, hs]), hi.m, hi.n, horig, hpar⟩
    · rw [loaderCount_eq]
      have h1 := hcond.2
      have h2 := hcond.1
      simp only [clcResp] at hresp
      omega
    · rw [loaderCount_eq]
      exact hrank

end

end PTX.Kernels.Fp16Gemm8192.Proof
