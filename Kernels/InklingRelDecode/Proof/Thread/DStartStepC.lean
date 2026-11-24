-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DStartStepB

@[expose] public section

/-! # The common start's steps: the relinquishment and the shuffle, and the link to the prologue

The relinquishment (`step_relinq`, then `shr.u32 %r3, %r1, 5`) and the shuffle of the warp index
(`step_shfl`). After the shuffle the local code `setp.lt.u32 %p4, %r4, 4`, `@!%p4 bra` (taken
only by the workers) falls through to pc 20 with the registers `ProA` inherits (`bridge20`),
the seven `ld.param` of `ProA.entry` run to the `setmaxnreg.inc` at pc 27, and the registers
there are `ProA`'s first state's (`bridge27`): the last site `toProA` of the machine is the first
site of `ProA.code (inh L g Q tm)`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.DStart
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {Q : Params} {d : D} {t u : TState} {e : Event} {ins : Instr}

theorem live27 : Flow.live 27 = [3, 462, 463, 464, 525, 526, 527, 528, 529, 530, 531, 532, 1949,
    2018, 2019, 2020, 2021, 2022] := by
  decide +kernel

/-! ### The registers the prologue inherits -/

theorem keys20 : ∀ r ∈ Flow.live 20,
    r ∈ [3, 462, 463, 464, 528, 529, 530, 531, 532, 1949, 2020] := by
  table_decide

theorem sub20 : ∀ r ∈ Flow.live 20, r ∈ Flow.live 17 := by
  table_decide

/-- **The registers live at pc 20 are the prologue's inherited ones**: the machine's value of
each is the value `ProA` gives it in its first state (`Dat.start (inh L g Q tm)`). -/
theorem bridge20 (tm : Value) : ∀ r ∈ Flow.live 20,
    ProA.valueOf L g (ProA.Dat.start (inh L g Q (ProA.shW tm)) tm) r = valueOf L g Q tm r := by
  intro r hr
  have hk := keys20 r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **The registers live at pc 27 are the prologue's**: the machine's value of each is `ProA`'s
in its first state; the registers the seven `ld.param` write are not in the machine's table. -/
theorem bridge27 (tm : Value) : ∀ r ∈ Flow.live 27,
    valueOf L g Q tm r = ProA.valueOf L g (ProA.Dat.start (inh L g Q (ProA.shW tm)) tm) r := by
  intro r hr
  rw [live27] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ### The relinquishment (warp 0) -/

theorem step_relinq (hs : d.site = .relinq) (hi : Inv L g Q d) (h : AtS L g Q d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g Q d e u := by
  obtain ⟨site, tm⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemRelinquish_0)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.tcRelinquish _) from trivial) hf
  have hB := seg_shr (L := L) (g := g) (Q := Q) hi.args
  have hC : Seg kernel asms L g 1 16 (factsAt L g Q tm 15) 17 (factsAt L g Q tm 17) :=
    hB.weaken_start fun _ hR => holds_factsFrom_mono hR (by live_dec)
  exact step_of_seg (d' := ⟨.shfl, tm⟩) (by simp [next]) (hi.to _ (by simp)) rfl
    (At.next (h.at rfl)) ⟨1, hC⟩

/-! ### The shuffle, the branch and the prologue's parameter loads -/

/-- No fact of a state is about a register that is not live at its program counter. -/
theorem facts_ne {pc r : Nat} {tm : Value} (hr : r ∉ Flow.live pc) :
    ∀ p ∈ factsAt L g Q tm pc, p.1 ≠ r := by
  intro p hp he
  simp only [factsAt, Flow.factsFrom, List.mem_map] at hp
  obtain ⟨r', hr', rfl⟩ := hp
  exact hr (he ▸ hr')

/-- **The branch**: from the shuffle's site, once the shuffle has written the warp index in
`%r4`, the local code `setp.lt.u32 %p4, %r4, 4`, `@!%p4 bra` (taken only by the workers) falls
through to pc 20 (`%p4` holds in warps 0 to 3), with the registers `ProA` inherits. -/
theorem shfl_20 {tm : Value} (hi : Inv L g Q ⟨.shfl, tm⟩) (h : AtS L g Q ⟨.shfl, tm⟩ t) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g)
      (PTX.next (setReg t 465 (Value.bits 32 (BitVec.ofNat 64 (warpOf L g))))) t' ∧
      At t' 20 (ProA.factsAt L g 20 (ProA.Dat.start (inh L g Q (ProA.shW tm)) tm)) := by
  have h128 : g % L.block < 128 := hi.args.tid
  have h1 : At (PTX.next (setReg t 465 (Value.bits 32 (BitVec.ofNat 64 (warpOf L g))))) 18
      ((465, Value.bits 32 (BitVec.ofNat 64 (warpOf L g))) :: facts L g Q ⟨.shfl, tm⟩) :=
    At.set (h.at rfl) (facts_ne (by live_dec))
  have hp4 : (4, Value.pred true) ∈
      (4, Value.pred true) :: (465, Value.bits 32 (BitVec.ofNat 64 (warpOf L g))) ::
        facts L g Q ⟨.shfl, tm⟩ := List.mem_cons_self
  have hA : Seg kernel asms L g 1 18
      ((465, Value.bits 32 (BitVec.ofNat 64 (warpOf L g))) :: facts L g Q ⟨.shfl, tm⟩) 19
      ((4, Value.pred true) :: (465, Value.bits 32 (BitVec.ofNat 64 (warpOf L g))) ::
        facts L g Q ⟨.shfl, tm⟩) := fun t h => by
    ds_seg h [warpOf, b32]
  have hB := Seg.bra_neg (K := kernel) (A := asms) (L := L) (g := g) (pick := true)
    Flow.code_19 hp4 (fun _ _ => Worker.asms_localRule_bra) (Worker.asms_segFreePc (by decide))
  obtain ⟨t20, hr20, ht20⟩ := (Seg.comp hA hB) _ h1
  refine ⟨t20, run_rtg hr20, ht20.mono (holds_of_pointwise fun r hr => ?_)⟩
  rw [bridge20 tm r hr]
  exact holds_mem ht20.2.2.2.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (Flow.mem_factsFrom (sub20 r hr))))

/-- The shuffle of the warp index: lane 0's operand is the warp index. After it the local code
reaches pc 20 (`shfl_20`), and `ProA.entry` runs the seven `ld.param` to `setmaxnreg.inc`
(pc 27), the site `toProA`. -/
theorem step_shfl (hs : d.site = .shfl) (hi : Inv L g Q d) (h : AtS L g Q d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g Q d e u := by
  obtain ⟨site, tm⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0)
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := none) hf
  simp only [Option.elim]
  cases recv
  case bits wd v =>
    by_cases hv : wd = 32 ∧ v = BitVec.ofNat 64 (warpOf L g)
    · obtain ⟨rfl, rfl⟩ := hv
      obtain ⟨t20, hr20, hP⟩ := shfl_20 hi h
      obtain ⟨t27, hr27, ht27⟩ := ProA.entry (inh L g Q (ProA.shW tm)) hi.args hP
      refine .inl (.inr ⟨⟨.toProA, tm⟩, t27, by simp [next], ?_, ?_, hi.to _ (by simp)⟩)
      · exact hr20.trans (run_rtg hr27)
      · exact ⟨ht27.1, ht27.2.1, ht27.2.2.1, ht27.2.2.2.1,
          (at_congr ht27 (fun r hr => (bridge27 tm r hr).symm)).2.2.2.2⟩
    · exact .inl (.inl (by simp only [next, hv, ↓reduceIte]))
  all_goals exact .inl (.inl (by simp [next]))

end
end PTX.Kernels.InklingRelDecode.Proof.DStart
