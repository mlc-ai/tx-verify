-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Machine
import Kernels.InklingRelDecode.Proof.Lib.IntStep
import Kernels.InklingRelDecode.Gen.StepMma
import Kernels.InklingRelDecode.Gen.StepMma01
import Lemmas.Flow.LandsU
import Lemmas.Flow.Step.SiteCases

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof

private theorem compare_seven {L : Launch} {g pc r p : Nat} {v : Value}
    {F G : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.setp .ne none, .int .b 32, false, [some p],
      [.reg r, .imm 7]⟩⟩) (hs : Assumptions.emuSites.contains pc = false) (hr : (r,v) ∈ F)
    (hw : ∀ R, Holds R F → Holds (Function.update R p (some (.pred (decide (low v ≠ 7))))) G) :
    SegU kernel Assumptions.all L g pc F (pc + 1) G := by
  apply Lib.scalarStepU hc rfl rfl hs _ hw
  intro t u hF he
  have himm : readBits L g t 32 (.imm 7) = .ok 7 := rfl
  simp only [execInt, DType.width, himm, bind, Except.bind, pure, Except.pure] at he
  cases hx : readBits L g t 32 (.reg r) <;> rw [hx] at he <;> try contradiction
  rw [Lib.readBits_eq_pattern (holds_mem hF hr) hx] at he
  rw [← Except.ok.inj he]
  congr 3
  change decide ((low v : Int) ≠ 7) = decide (low v ≠ 7)
  simp only [decide_eq_decide]
  omega

private theorem broadcast_step {L : Launch} {g r p : Nat} {regs : Nat → Value} {w : Value}
    {d : D} {yes no : Site}
    (hc : kernel.code[d.site.pc]? = some ⟨none, .warp ⟨.shfl .idx, some (.int .b 32),
      [some r], [.reg 464, .imm 0, .imm 31], some (.imm (-1))⟩⟩)
    (htest : kernel.code[d.site.pc + 1]? = some ⟨none, .int ⟨.setp .ne none, .int .b 32,
      false, [some p], [.reg r, .imm 7]⟩⟩)
    (hs : Assumptions.emuSites.contains (d.site.pc + 1) = false)
    (hr : ∀ x ∈ (code L g regs w).facts d, x.1 ≠ r)
    (succ : ∀ a b c v ok, next L g d ⟨d.site.pc, .shfl .idx a b c v ok⟩ =
      some (some {d with site := if low v = 7 then yes else no}))
    (hpc : yes.pc = d.site.pc + 2 ∧ no.pc = yes.pc)
    (hw : ∀ v R, Holds R ((r,v) :: (code L g regs w).facts d) →
      Holds (Function.update R p (some (.pred (decide (low v ≠ 7)))))
        ((code L g regs w).facts {d with site := if low v = 7 then yes else no}))
    (hinv : Inv d → Inv {d with site := yes} ∧ Inv {d with site := no}) :
    (code L g regs w).StepAtU d := by
  refine ⟨fun _ => ⟨_, hc, rfl, trivial⟩, ?_⟩
  intro t e u ins hat hi hc' hf
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨a,b,c,v,ok,rfl,rfl⟩ := fires_shfl (p := none) hf
  let dest := ({d with site := if low v = 7 then yes else no} : D)
  have pc : dest.site.pc = d.site.pc + 2 := by
    dsimp only [dest]
    split <;> first | exact hpc.left | exact hpc.right.trans hpc.left
  have valid : Inv dest := by
    dsimp only [dest]
    split <;> first | exact (hinv hi).left | exact (hinv hi).right
  have seg := compare_seven (L := L) (g := g) htest hs (List.mem_cons_self ..) (hw v)
  rw [← pc] at seg
  obtain ⟨s,hτ,hgood⟩ := Code.landsU (C := code L g regs w) (d := dest)
    (At.set (Code.at_of_atD hat rfl rfl) hr) seg valid rfl rfl
  exact .inl (.inr ⟨dest,s,succ a b c v ok,hτ,hgood⟩)

private theorem keep_reg {L : Launch} {w : Value} {regs : Nat → Value}
    (d : D) (s : Site) {r : Nat} (h8 : r ≠ 8) (h13 : r ≠ 13) :
    valueOf L regs w { d with site := s } r = valueOf L regs w d r := by
  simp only [valueOf, values, D.limit, List.lookup_cons, beq_eq_false_iff_ne.mpr h8,
    beq_eq_false_iff_ne.mpr h13]
  rfl

private theorem broadcast_regs {L : Launch} {w : Value} {regs : Nat → Value}
    {R : Nat → Option Value} {d : D}
    {s : Site} {p : Nat} {b : Bool}
    (hR : Holds R (factsFrom (Flow.live d.site.pc) (valueOf L regs w d)))
    (hp : valueOf L regs w {d with site := s} p = .pred b)
    (hl : ∀ r ∈ Flow.live s.pc, r = p ∨ (r ∈ Flow.live d.site.pc ∧ r ≠ 8 ∧ r ≠ 13)) :
    Holds (Function.update R p (some (.pred b)))
      (factsFrom (Flow.live s.pc) (valueOf L regs w {d with site := s})) := by
  apply holds_of_pointwise
  intro r hr
  by_cases he : r = p
  · subst r
    rw [hp, Function.update_self]
  · obtain ⟨hm,h8,h13⟩ := (hl r hr).resolve_left he
    rw [Function.update_of_ne he, keep_reg d s h8 h13]
    exact holds_mem hR (mem_factsFrom hm)

local macro "bcast_facts" : tactic => `(tactic| (
  intro v R hR
  obtain ⟨_,hold⟩ := hR
  by_cases h : low v = 7 <;> simp only [h, ↓reduceIte, ne_eq, not_true_eq_false,
    not_false_eq_true, decide_false, decide_true] <;>
    apply broadcast_regs hold rfl (by dsimp only; decide +kernel)))

set_option maxRecDepth 16384
theorem qk_broadcast_step {L : Launch} {g : Nat} {regs : Nat → Value} {w : Value}
    (i : Nat) (v : Value) : (code L g regs w).StepAtU ⟨.qkShfl,i,v⟩ := by
  refine broadcast_step (d := ⟨.qkShfl,i,v⟩) (r := 546) (p := 8)
    (yes := .qkBar2) (no := .qkSkip) Flow.code_2464 Flow.code_2465
    (show Assumptions.emuSites.contains 2465 = false by decide) (by fact_free)
    (fun _ _ _ _ _ => rfl) ⟨rfl,rfl⟩ ?_ (fun h => ⟨h,h⟩)
  bcast_facts

theorem pv_broadcast_step {L : Launch} {g : Nat} {regs : Nat → Value} {w : Value}
    (i : Nat) (v : Value) : (code L g regs w).StepAtU ⟨.pvShfl,i,v⟩ := by
  refine broadcast_step (d := ⟨.pvShfl,i,v⟩) (r := 563) (p := 13)
    (yes := .pvBar2) (no := .pvSkip) Flow.code_2512 Flow.code_2513
    (show Assumptions.emuSites.contains 2513 = false by decide) (by fact_free)
    (fun _ _ _ _ _ => rfl) ⟨rfl,rfl⟩ ?_ (fun h => ⟨h,h⟩)
  bcast_facts

end PTX.Kernels.InklingRelDecode.Proof.Mma
