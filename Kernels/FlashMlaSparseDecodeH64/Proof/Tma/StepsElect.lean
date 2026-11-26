-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamLoad
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Base
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Gen.StepTma

@[expose] public section

/-! # The TMA warp's obligation at the election

The lanes that lose the election walk to the idle code's first event (`lose_walk`); the elected
lane's walk is cut at pc 2177 (`lead_head`, `LeadParams.lean`), after which the branches on the
length pointers reach the first length load, the second or the wait on `bar_q_utccp`, each one
declaration (`lead_topk`, `lead_extra`, `lead_q`). -/

/-! # The elected lane's parameter reads

After the election the elected lane reads the batch (pc 2170) and, inside the batch, the two
length pointers and the two length budgets from `param_0` (pcs 2173–2176). Each read is a step of
`seg_ldParam0`; the symbolic walk takes the code between them. `lead_head` is the elected lane's
walk from the election to pc 2177 inside the batch, `lead_exit` its return beyond it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The facts after the batch read (pc 2171). -/
noncomputable abbrev F2171 (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  (664, .bits 32 (BitVec.ofNat 64 (leNat P.b 0 (32 / 8)))) ::
    factsFrom (Flow.live 2170) (valueOf P L g { d with site := .elect })

/-- The facts at pc 2173, inside the batch. -/
noncomputable abbrev F2173 (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  factsFrom (Flow.live 2173) (valueOf P L g { d with site := .elect })

/-- The facts after the four parameter reads (pc 2177). -/
noncomputable abbrev F2177 (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  (2963, .bits 32 (BitVec.ofNat 64 (leNat P.extra_topk 0 (32 / 8)))) ::
    (3008, .bits 64 (BitVec.ofNat 64 (leNat (P.extraTopkLenBase.getD 0) 0 (64 / 8)))) ::
    (2962, .bits 32 (BitVec.ofNat 64 (leNat P.topk 0 (32 / 8)))) ::
    (3007, .bits 64 (BitVec.ofNat 64 (leNat (P.topkLenBase.getD 0) 0 (64 / 8)))) ::
    F2173 P L g d

/-- The elected lane from the election to the batch read. -/
theorem lead_b (hp : Pre P L m) (d : D) (ld : Nat) :
    ∃ n, Seg kernel Assumptions.all L g n 2166 ((4117, Value.pred true) ::
      Code.electFacts (some 4116) ld (facts P L g { d with site := .elect })) 2171
      (F2171 P L g d) := by
  dsimp only [PTX.Flow.Code.electFacts]
  refine Seg.comp_ex (q := 2170) (H := factsFrom (Flow.live 2170)
    (valueOf P L g { d with site := .elect })) ?_ ⟨1, ?_⟩
  · seg_auto using tma_seg
  · exact seg_ldParam0 (g := g) (pc := 2170) (w := 32) (off := 0) (d := 664) (x := P.b)
      (ty := .int .b 32) hp (by rw [Flow.code_2170]; rfl) (by simp [p0fields])
      (mem_factsFrom (r := 2991) (by decide)) (by fact_free) (by decide) (by decide)
      (by decide) (by decide) (by decide) rfl rfl

/-- The four parameter reads (pcs 2173–2176). -/
theorem lead_params (hp : Pre P L m) (d : D) :
    ∃ n, Seg kernel Assumptions.all L g n 2173 (F2173 P L g d) 2177 (F2177 P L g d) := by
  have h0 : (2991, Value.ptr 64 false (.param (param "0")) 0) ∈ F2173 P L g d :=
    mem_factsFrom (r := 2991) (by decide)
  refine ⟨_, (seg_ldParam0 (g := g) (pc := 2173) (w := 64) (off := 80) (d := 3007)
    (x := P.topkLenBase.getD 0) (ty := .int .b 64) hp (by rw [Flow.code_2173]; rfl)
    (by simp [p0fields]) h0 (by fact_free) (by decide) (by decide) (by decide) (by decide)
    (by decide) rfl rfl).comp ((seg_ldParam0 (g := g) (pc := 2174) (w := 32) (off := 40)
    (d := 2962) (x := P.topk) (ty := .int .b 32) hp (by rw [Flow.code_2174]; rfl)
    (by simp [p0fields]) (List.mem_cons_of_mem _ h0)
    (List.forall_mem_cons.mpr ⟨by simp, by fact_free⟩)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl).comp
    ((seg_ldParam0 (g := g) (pc := 2175) (w := 64) (off := 144) (d := 3008)
    (x := P.extraTopkLenBase.getD 0) (ty := .int .b 64) hp (by rw [Flow.code_2175]; rfl)
    (by simp [p0fields]) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h0))
    (List.forall_mem_cons.mpr ⟨by simp, List.forall_mem_cons.mpr ⟨by simp, by fact_free⟩⟩)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl).comp
    (seg_ldParam0 (g := g) (pc := 2176) (w := 32) (off := 120) (d := 2963)
    (x := P.extra_topk) (ty := .int .b 32) hp (by rw [Flow.code_2176]; rfl)
    (by simp [p0fields])
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h0)))
    (List.forall_mem_cons.mpr ⟨by simp, List.forall_mem_cons.mpr ⟨by simp,
      List.forall_mem_cons.mpr ⟨by simp, by fact_free⟩⟩⟩)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl)))⟩

set_option hygiene false in
/-- **The elected lane inside the batch**, from the election to pc 2177. -/
theorem lead_head (hp : Pre P L m) (d : D) (ld : Nat)
    (hb : ¬ Arith32.scmp Cmp.ge IType.s (r2W L g) (pw P.b) = true) :
    ∃ n, Seg kernel Assumptions.all L g n 2166 ((4117, Value.pred true) ::
      Code.electFacts (some 4116) ld (facts P L g { d with site := .elect })) 2177
      (F2177 P L g d) := by
  refine Seg.comp_ex (lead_b hp d ld) (Seg.comp_ex (q := 2173) (H := F2173 P L g d) ?_
    (lead_params hp d))
  seg_sym using tma_seg

set_option hygiene false in
/-- **The elected lane beyond the batch** returns. -/
theorem lead_exit (hp : Pre P L m) (d : D) (ld : Nat)
    (hb : Arith32.scmp Cmp.ge IType.s (r2W L g) (pw P.b) = true) :
    ∃ n, Seg kernel Assumptions.all L g n 2166 ((4117, Value.pred true) ::
      Code.electFacts (some 4116) ld (facts P L g { d with site := .elect })) 3611
      (factsFrom (Flow.live 3611) (valueOf P L g
        { d with site := .exit, l0 := pw P.topk, l1 := pw P.extra_topk })) := by
  refine Seg.comp_ex (lead_b hp d ld) ?_
  seg_sym using tma_seg

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option hygiene false in
theorem lead_q (d : D) (h1 : eqz64 (pw8 (P.topkLenBase.getD 0)) = true)
    (h2 : eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = true) :
    ∃ n, Seg kernel Assumptions.all L g n 2177 (F2177 P L g d) 2205
      (factsFrom (Flow.live 2205) (valueOf P L g
        { d with site := .qWait, l0 := pw P.topk, l1 := pw P.extra_topk })) := by
  seg_sym using tma_seg

set_option hygiene false in
theorem lead_extra (d : D) (h1 : eqz64 (pw8 (P.topkLenBase.getD 0)) = true)
    (h2 : ¬ eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = true) :
    ∃ n, Seg kernel Assumptions.all L g n 2177 (F2177 P L g d) 2191
      (factsFrom (Flow.live 2191) (valueOf P L g
        { d with site := .loadExtra, l0 := pw P.topk, l1 := pw P.extra_topk })) := by
  seg_sym using tma_seg

set_option hygiene false in
theorem lead_topk (d : D) (h1 : ¬ eqz64 (pw8 (P.topkLenBase.getD 0)) = true) :
    ∃ n, Seg kernel Assumptions.all L g n 2177 (F2177 P L g d) 2181
      (factsFrom (Flow.live 2181) (valueOf P L g
        { d with site := .loadTopk, l0 := pw P.topk, l1 := pw P.extra_topk })) := by
  seg_sym using tma_seg

/-- **A lane that loses the election** walks the idle code's local prefix to its first event. -/
theorem lose_walk (hp : Pre P L m) (d : D) (ld : Nat) :
    ∃ n, Seg kernel Assumptions.all L g n 2166 ((4117, Value.pred false) ::
      Code.electFacts (some 4116) ld (facts P L g { d with site := .elect }))
      (idleFirst P L g).pc (idleEnd P L g (idleFirst P L g)) := by
  refine Seg.comp_ex (q := 2587) (H := idleWk0 L g) ?_ (IdleWalk.walk hp)
  dsimp only [Code.electFacts]
  seg_auto using tma_seg

theorem stepOk_elect (hp : Pre P L m) (d : D) (hs : d.site = .elect) :
    (code P L g).StepOk d := by
  have hd : d = { d with site := .elect } := by cases d; cases hs; rfl
  rw [hd]
  refine Code.step_elect (dl := leadNext P L g { d with site := .elect })
    (ds := { d with site := .leave (idleFirst P L g) }) (by code_lookup)
    (by fact_free) ?_
    (fun _ _ _ h => by simp [code, succ, electNext, h])
    (fun _ _ _ h => by simp [code, succ, electNext, h]) rfl rfl
    ?_ ?_
  · intro r hr
    cases hr
    exact ⟨by fact_free, by decide⟩
  · intro ld
    refine ⟨fun _ => ?_, by unfold leadNext afterTopk lensD; split_ifs <;> rfl,
      by unfold leadNext afterTopk lensD; split_ifs <;> rfl, fun _ => trivial⟩
    by_cases hb : Arith32.scmp Cmp.ge IType.s (r2W L g) (pw P.b) = true
    · simp only [leadNext, hb, ite_true]
      exact lead_exit hp d ld hb
    · refine Seg.comp_ex (lead_head hp d ld hb) ?_
      simp only [leadNext, hb, Bool.false_eq_true, ↓reduceIte, afterTopk, lensD]
      split_ifs with h1 h2
      · exact lead_q d h1 h2
      · exact lead_extra d h1 h2
      · exact lead_topk d h1
  · intro ld
    refine ⟨fun _ => ?_, rfl, rfl, fun _ => trivial⟩
    have h := lose_walk (g := g) hp d ld
    rw [← facts_leave P L g { d with site := .leave (idleFirst P L g) } (idleFirst P L g) rfl]
      at h
    exact h

/-- **The election.** -/
theorem stepAt_elect (hp : Pre P L m) (d : D) (hs : d.site = .elect) :
    (code P L g).StepAt d := by
  tma_state d
  simp only at hs
  tma_sites s except [.elect => (stepOk_elect hp _ rfl)]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
