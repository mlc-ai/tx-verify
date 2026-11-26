-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamLoad
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.SegQ
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Gen.StepMma

@[expose] public section

/-! # The MMA warp's obligation at the election

The lanes that lose the election walk to the idle code's first event (`lose_walk`); the elected
lane's walk is cut at pc 1866 (`lead_head`, `LeadParams.lean`), after which the branches on the
length pointers and the padded total reach the first length load, the second, the trap or the first
Q load, each one declaration (`lead_topk`, `lead_extra`, `lead_trap`, `lead_q0`). -/

/-! # The elected lane's parameter reads

After the election the elected lane reads the batch, the two length pointers and the two length
budgets from `param_0` (pcs 1858–1864) and forms the generic pointer to `param_1` (pc 1865). Each
read is a step of `seg_ldParam0` (`lead_b`, `lead_params`): the walk under the explicit launch
exceeds a declaration's heartbeats there. `lead_head` is the elected lane's walk from the election
to pc 1866 inside the batch, `lead_exit` its return beyond it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A register outside a list of facts stays outside after another register is set. -/
theorem fresh_cons {r d : Nat} {v : Value} {F : List (Nat × Value)} (hne : r ≠ d)
    (hF : ∀ q ∈ F, q.1 ≠ d) : ∀ q ∈ (r, v) :: F, q.1 ≠ d := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hne
  · exact hF q hq
set_option hygiene false in
theorem lead_params (hp : Pre P L m) (neg cnt pha par : BitVec 64) :
    ∃ n, Seg kernel Assumptions.all L g n 1861
      (factsFrom (Flow.live 1861)
        (valueOf P L g ⟨.elect, pw P.topk, pw P.extra_topk, neg, cnt, pha, par⟩)) 1866
      (factsFrom (Flow.live 1866)
        (valueOf P L g ⟨.elect, pw P.topk, pw P.extra_topk, neg, cnt, pha, par⟩)) := by
  have h0 : (2991, Value.ptr 64 false (.param (param "0")) 0) ∈ factsFrom (Flow.live 1861)
      (valueOf P L g ⟨.elect, pw P.topk, pw P.extra_topk, neg, cnt, pha, par⟩) :=
    mem_factsFrom (r := 2991) (by decide)
  have h1 : (2990, Value.ptr 64 false (.param (param "1")) 0) ∈ factsFrom (Flow.live 1861)
      (valueOf P L g ⟨.elect, pw P.topk, pw P.extra_topk, neg, cnt, pha, par⟩) :=
    mem_factsFrom (r := 2990) (by decide)
  refine ⟨_, (seg_ldParam0 (g := g) (pc := 1861) (w := 64) (off := 80) (d := 3004)
    (x := P.topkLenBase.getD 0) (ty := .int .b 64) hp (by rw [Flow.code_1861]; rfl)
    (by simp [p0fields]) h0 (by fact_free) (by decide) (by decide) (by decide) (by decide)
    (by decide) rfl rfl).comp ((seg_ldParam0 (g := g) (pc := 1862) (w := 32) (off := 40)
    (d := 2957) (x := P.topk) (ty := .int .b 32) hp (by rw [Flow.code_1862]; rfl)
    (by simp [p0fields]) (List.mem_cons_of_mem _ h0) (fresh_cons (by decide) (by fact_free))
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl).comp
    ((seg_ldParam0 (g := g) (pc := 1863) (w := 64) (off := 144) (d := 3005)
    (x := P.extraTopkLenBase.getD 0) (ty := .int .b 64) hp (by rw [Flow.code_1863]; rfl)
    (by simp [p0fields]) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h0))
    (fresh_cons (by decide) (fresh_cons (by decide) (by fact_free)))
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl).comp
    ((seg_ldParam0 (g := g) (pc := 1864) (w := 32) (off := 120) (d := 2958)
    (x := P.extra_topk) (ty := .int .b 32) hp (by rw [Flow.code_1864]; rfl)
    (by simp [p0fields])
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h0)))
    (fresh_cons (by decide) (fresh_cons (by decide) (fresh_cons (by decide) (by fact_free))))
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl).comp (n := 1) ?_)))⟩
  intro t ht
  have htR := atHolds ht
  refine ⟨_, run_cvtaParam (pc := 1865) Flow.code_1865 ht (holds_mem htR
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ h1))))), ?_⟩
  have ha := At.set (r := 3006) (v := .ptr 64 true (.param (param "1")) 0) ht
    (fresh_cons (by decide) (fresh_cons (by decide) (fresh_cons (by decide)
      (fresh_cons (by decide) (by fact_free)))))
  refine At.mono ha (holds_of_pointwise fun r hr => ?_)
  have hR := atHolds ha
  simp only [show Flow.live 1866 = [459, 460, 2957, 2958, 3004, 3005, 3006] from rfl,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact holds_mem hR (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_factsFrom (by decide)))))))
  · exact holds_mem hR (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_factsFrom (by decide)))))))
  · exact holds_mem hR (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
  · exact holds_mem hR (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · exact holds_mem hR (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
  · exact holds_mem hR (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · exact holds_mem hR (List.mem_cons_self ..)
/-- The facts after the batch read (pc 1859). -/
noncomputable abbrev F1859 (P : Params) (L : Launch) (g : Nat) (l0 l1 neg cnt pha par : BitVec 64) :
    List (Nat × Value) :=
  (795, .bits 32 (BitVec.ofNat 64 (leNat P.b 0 (32 / 8)))) ::
    factsFrom (Flow.live 1858) (valueOf P L g ⟨.elect, l0, l1, neg, cnt, pha, par⟩)

/-- The elected lane from the election to the batch read. -/
theorem lead_b (hp : Pre P L m) (l0 l1 neg cnt pha par : BitVec 64) (ld : Nat) :
    ∃ n, Seg kernel Assumptions.all L g n 1854 ((4087, Value.pred true) ::
      Code.electFacts (some 4086) ld (facts P L g ⟨.elect, l0, l1, neg, cnt, pha, par⟩)) 1859
      (F1859 P L g l0 l1 neg cnt pha par) := by
  dsimp only [PTX.Flow.Code.electFacts]
  refine Seg.comp_ex (q := 1858) (H := factsFrom (Flow.live 1858)
    (valueOf P L g ⟨.elect, l0, l1, neg, cnt, pha, par⟩)) ?_ ⟨1, ?_⟩
  · seg_auto using mma_seg
  · exact seg_ldParam0 (g := g) (pc := 1858) (w := 32) (off := 0) (d := 795) (x := P.b)
      (ty := .int .b 32) hp (by rw [Flow.code_1858]; rfl) (by simp [p0fields])
      (mem_factsFrom (r := 2991) (by decide)) (by fact_free) (by decide) (by decide)
      (by decide) (by decide) (by decide) rfl rfl

/-- **The elected lane inside the batch**, from the election to pc 1866. -/
theorem lead_head (hp : Pre P L m) (l0 l1 neg cnt pha par : BitVec 64) (ld : Nat)
    (h : ¬ Arith32.scmp Cmp.ge IType.s (r2W L g) (pw P.b) = true) :
    ∃ n, Seg kernel Assumptions.all L g n 1854 ((4087, Value.pred true) ::
      Code.electFacts (some 4086) ld (facts P L g ⟨.elect, l0, l1, neg, cnt, pha, par⟩)) 1866
      (factsFrom (Flow.live 1866)
        (valueOf P L g ⟨.elect, pw P.topk, pw P.extra_topk, neg, cnt, pha, par⟩)) := by
  refine Seg.comp_ex (lead_b hp l0 l1 neg cnt pha par ld) ?_
  refine Seg.comp_ex (q := 1861) (H := factsFrom (Flow.live 1861)
      (valueOf P L g ⟨.elect, pw P.topk, pw P.extra_topk, neg, cnt, pha, par⟩)) ?_
      (lead_params hp neg cnt pha par)
  seg_sym using mma_seg

/-- **The elected lane beyond the batch** returns. -/
theorem lead_exit (hp : Pre P L m) (l0 l1 neg cnt pha par : BitVec 64) (ld : Nat)
    (h : Arith32.scmp Cmp.ge IType.s (r2W L g) (pw P.b) = true) :
    ∃ n, Seg kernel Assumptions.all L g n 1854 ((4087, Value.pred true) ::
      Code.electFacts (some 4086) ld (facts P L g ⟨.elect, l0, l1, neg, cnt, pha, par⟩)) 3611
      (factsFrom (Flow.live 3611)
        (valueOf P L g ⟨.exit, pw P.topk, pw P.extra_topk, neg, cnt, pha, par⟩)) := by
  refine Seg.comp_ex (lead_b hp l0 l1 neg cnt pha par ld) ?_
  seg_sym using mma_seg

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The facts at pc 1866 of the elected lane: the length words at their budgets. -/
noncomputable abbrev F1866 (P : Params) (L : Launch) (g : Nat) (neg cnt pha par : BitVec 64) :
    List (Nat × Value) :=
  factsFrom (Flow.live 1866)
    (valueOf P L g ⟨.elect, pw P.topk, pw P.extra_topk, neg, cnt, pha, par⟩)

set_option hygiene false in
theorem lead_q0 (hp : Pre P L m) (neg cnt pha par : BitVec 64)
    (h1 : eqz64 (pw8 (P.topkLenBase.getD 0)) = true)
    (h2 : eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = true)
    (h3 : Arith32.scmpi Cmp.gt IType.s (r27 (pw P.topk) (pw P.extra_topk)) 63 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 1866 (F1866 P L g neg cnt pha par) 1906
      (factsFrom (Flow.live 1906)
        (valueOf P L g ⟨.qLoad 0, pw P.topk, pw P.extra_topk, neg, cnt, pha, par⟩)) := by
  seg_sym using mma_seg

theorem lead_trap (neg cnt pha par : BitVec 64)
    (h1 : eqz64 (pw8 (P.topkLenBase.getD 0)) = true)
    (h2 : eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = true)
    (h3 : ¬ Arith32.scmpi Cmp.gt IType.s (r27 (pw P.topk) (pw P.extra_topk)) 63 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 1866 (F1866 P L g neg cnt pha par) 1896
      (factsFrom (Flow.live 1896)
        (valueOf P L g ⟨.trap, pw P.topk, pw P.extra_topk, neg, cnt, pha, par⟩)) := by
  seg_sym using mma_seg

theorem lead_extra (neg cnt pha par : BitVec 64)
    (h1 : eqz64 (pw8 (P.topkLenBase.getD 0)) = true)
    (h2 : ¬ eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = true) :
    ∃ n, Seg kernel Assumptions.all L g n 1866 (F1866 P L g neg cnt pha par) 1886
      (factsFrom (Flow.live 1886)
        (valueOf P L g ⟨.loadExtra, pw P.topk, pw P.extra_topk, neg, cnt, pha, par⟩)) := by
  seg_sym using mma_seg

theorem lead_topk (neg cnt pha par : BitVec 64)
    (h1 : ¬ eqz64 (pw8 (P.topkLenBase.getD 0)) = true) :
    ∃ n, Seg kernel Assumptions.all L g n 1866 (F1866 P L g neg cnt pha par) 1876
      (factsFrom (Flow.live 1876)
        (valueOf P L g ⟨.loadTopk, pw P.topk, pw P.extra_topk, neg, cnt, pha, par⟩)) := by
  seg_sym using mma_seg

/-- **A lane that loses the election** walks the idle code's local prefix to its first event. -/
theorem lose_walk (hp : Pre P L m) (l0 l1 neg cnt pha par : BitVec 64) (ld : Nat) :
    ∃ n, Seg kernel Assumptions.all L g n 1854 ((4087, Value.pred false) ::
      Code.electFacts (some 4086) ld (facts P L g ⟨.elect, l0, l1, neg, cnt, pha, par⟩))
      (idleFirst P L g).pc (idleEnd P L g (idleFirst P L g)) := by
  refine Seg.comp_ex (q := 2587) (H := idleWk0 L g) ?_ (IdleWalk.walk hp)
  dsimp only [Code.electFacts]
  seg_auto using mma_seg

set_option hygiene false in
theorem stepOk_elect (hp : Pre P L m) (l0 l1 neg cnt pha par : BitVec 64) :
    (code P L g).StepOk ⟨.elect, l0, l1, neg, cnt, pha, par⟩ := by
  refine Code.step_elect (dl := leadNext P L g ⟨.elect, l0, l1, neg, cnt, pha, par⟩)
    (ds := ⟨.leave (idleFirst P L g), l0, l1, neg, cnt, pha, par⟩) (by code_lookup)
    (by fact_free) ?_
    (fun _ _ _ h => by simp [code, succ, h]) (fun _ _ _ h => by simp [code, succ, h]) rfl rfl
    ?_ ?_
  · intro r hr
    cases hr
    exact ⟨by fact_free, by decide⟩
  · intro ld
    refine ⟨fun _ => ?_, by unfold leadNext afterTopk lensD; split_ifs <;> rfl,
      by unfold leadNext afterTopk lensD; split_ifs <;> rfl, fun _ => trivial⟩
    by_cases hb : Arith32.scmp Cmp.ge IType.s (r2W L g) (pw P.b) = true
    · simp only [leadNext, hb, ite_true]
      exact lead_exit hp l0 l1 neg cnt pha par ld hb
    · refine Seg.comp_ex (lead_head hp l0 l1 neg cnt pha par ld hb) ?_
      simp only [leadNext, hb, Bool.false_eq_true, ↓reduceIte, afterTopk, lensD]
      split_ifs with h1 h2 h3 <;> site_norm
      · exact lead_q0 hp neg cnt pha par h1 h2 h3
      · exact lead_trap neg cnt pha par h1 h2 h3
      · exact lead_extra neg cnt pha par h1 h2
      · exact lead_topk neg cnt pha par h1
  · intro ld
    refine ⟨fun _ => ?_, rfl, rfl, fun _ => trivial⟩
    have h := lose_walk (g := g) hp l0 l1 neg cnt pha par ld
    rw [← facts_leave P L g (idleFirst P L g) l0 l1 neg cnt pha par] at h
    exact h
/-- **The election.** -/
theorem stepAt_elect (hp : Pre P L m) (d : D) (hs : d.site = .elect) :
    (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  mma_sites s except [.elect => (stepOk_elect hp l0 l1 neg cnt pha par)]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
