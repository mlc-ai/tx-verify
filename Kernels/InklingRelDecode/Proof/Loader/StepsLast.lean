-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.StepsLoop
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.TensorIssue
import Lemmas.Flow.Step.SiteCases
import Lemmas.Flow.SegPieces
import Lemmas.Flow.LandsU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section
variable {Q : Params} {L : Launch} {g : Nat} {w : Value} {rest : Nat → Value} (i n a b : Value)

private theorem lands_last {t : TState}
    (ht : At t 2413 (loopFacts (L := L) (g := g) (w := w) (regs := inputs Q L g rest)
      i n a b 2413)) :
    let C := code L g w (inputs Q L g rest)
    ∃ s, Relation.ReflTransGen (Tau kernel Assumptions.all L g) t s ∧
      C.GoodU (some (afterPacket i n a b)) s := by
  intro C
  apply Code.landsU ht (loop_span i n a b)
  all_goals unfold afterPacket; split <;> first | rfl | (intro h; cases h)

theorem copy_last_step :
    (code L g w (inputs Q L g rest)).StepAtU ⟨.copy 3 true,i,n,a,b⟩ := by
  refine ⟨fun _ => ⟨_, Flow.code_2412, rfl,
    Code.guardTrue_factsFrom (show 24 ∈ Flow.live 2412 by decide) rfl⟩, ?_⟩
  intro t e u ins ht _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2412)
  obtain ⟨_, _, _, rfl, _⟩ := fires_cpTensor_issue hf
  have ht0 := At.next (Code.at_of_atD ht rfl rfl)
  have hp : At (PTX.next t) 2413 (loopFacts (L := L) (g := g) (w := w)
      (regs := inputs Q L g rest) i n a b 2413) := by
    apply At.mono ht0
    obtain ⟨_, _, _, _, hR⟩ := ht0
    exact holds_factsFrom_mono hR (show ∀ r ∈ Flow.live 2413, r ∈ Flow.live 2412 by decide)
  obtain ⟨s, hτ, hs⟩ := lands_last i n a b hp
  exact .inl (.inr ⟨_, s, rfl, hτ, hs⟩)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem skipCopies (ld : Nat) :
    let val := loopValue L g w (inputs Q L g rest) ⟨.elect 3,i,n,a,b⟩
    let F := (24, Value.pred false) :: (609, .bits 32 (BitVec.ofNat 64 ld)) ::
      factsFrom (Flow.live 2409) val
    ∃ k, Seg kernel Assumptions.all L g k 2410 F 2413 (factsFrom (Flow.live 2413) val) := by
  intro val F
  have skip (pc : Nat) {op : Op} (hc : kernel.code[pc]? = some ⟨some (24,false),op⟩) :
      Seg kernel Assumptions.all L g 1 pc F (pc + 1) F :=
    Seg.guardSkip hc List.mem_cons_self rfl
  have middle : Seg kernel Assumptions.all L g 1 2411 F 2412 F := by
    intro t ht
    dsimp only [F] at ht ⊢
    seg_fp ht using rfl
  have keep := (skip 2410 Flow.code_2410).comp (middle.comp (skip 2412 Flow.code_2412))
  refine ⟨_, keep.weaken_end ?_⟩
  rintro R ⟨_, _, hR⟩
  exact holds_factsFrom_mono hR (show ∀ r ∈ Flow.live 2413, r ∈ Flow.live 2409 by decide)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem elect_last_step :
    (code L g w (inputs Q L g rest)).StepAtU ⟨.elect 3,i,n,a,b⟩ := by
  let regs := inputs Q L g rest
  let d : D := ⟨.elect 3,i,n,a,b⟩
  let C := code L g w regs
  refine ⟨fun _ => ⟨_, Flow.code_2409, rfl, trivial⟩, ?_⟩
  intro t e u ins ht _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2409)
  obtain ⟨mk, inst, ld, rfl, rfl⟩ := fires_elect hf
  let t1 := setReg t 609 (.bits 32 (BitVec.ofNat 64 ld))
  have h0 : At t 2409 (C.facts d) := Code.at_of_atD ht rfl rfl
  obtain ⟨hpc, hsub, hacc, hfault, hR⟩ := h0
  let F := (609, Value.bits 32 (BitVec.ofNat 64 ld)) :: C.facts d
  have h1 : At t1 2409 F := ⟨hpc, hsub, hacc, hfault, by simp [t1, setReg],
    holds_update hR (by fact_free)⟩
  have fresh : ∀ q ∈ F, q.1 ≠ 24 := by
    rintro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact (by decide : 609 ≠ 24)
    · exact (show ∀ q ∈ C.facts d, q.1 ≠ 24 by fact_free) q hq
  by_cases h : laneOf L g = ld
  · let dn : D := ⟨.copy 3 false,i,n,a,b⟩
    have go : Seg kernel Assumptions.all L g 0 2410 ((24,.pred true) :: F)
        (C.pc dn) (C.facts dn) := by
      intro u hu
      dsimp only [F, C, d, dn, code] at hu ⊢
      seg_fp hu using rfl
    have ht2 := At.set (v := .pred true) h1 fresh
    obtain ⟨s, hτ, hs⟩ :=
      Code.landsU (C := C) (d := dn) ht2 (SegU.of_seg go) (fun hh => by cases hh) rfl rfl
    rw [beq_iff_eq.mpr h]
    exact .inl (.inr ⟨dn, s, by simp [code, next, h, dn], hτ, hs⟩)
  · have ht2 := At.set (v := .pred false) h1 fresh
    obtain ⟨_, seg⟩ :=
      skipCopies (Q := Q) (L := L) (g := g) (w := w) (rest := rest) i n a b ld
    obtain ⟨u, hτ, hu⟩ := seg _ ht2
    obtain ⟨s, hτ', hs⟩ := lands_last i n a b hu
    rw [beq_eq_false_iff_ne.mpr h]
    exact .inl (.inr ⟨_, s, by simp [code, next, h, finish_last], (run_rtg hτ).trans hτ', hs⟩)

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
