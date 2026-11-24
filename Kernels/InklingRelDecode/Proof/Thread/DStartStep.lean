-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DStartBase
public import Lemmas.Flow.Alloc
public import Lemmas.Flow.TmemOperands

@[expose] public section

/-! # The common start's steps: the allocation, the barriers, the base word, the relinquishment

The conclusion of a step (`Step`) and the steps of the sites before the shuffle: the allocation
(`step_alloc`: lane 0 goes on to its address store, the other lanes to the barrier;
`step_allocWr`), the two barriers (`step_bar0`, `step_bar1`: after the second one the thread of
warp 0 is at the relinquishment, the others skip it and run `shr.u32 %r3, %r1, 5`), the load of
the Tensor Memory base word (`step_ld0`) and the relinquishment (`step_relinq`, then
`shr.u32`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.DStart
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {Q : Params} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-- A concrete state of the abstract state `d`: its program counter, sub-step and register
facts. -/
def AtS (L : Launch) (g : Nat) (Q : Params) (d : D) (t : TState) : Prop :=
  t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = [] ∧ t.fault = none ∧
    Holds t.regs (facts L g Q d)

/-- The conclusion of a step of this machine: it leaves the machine, or steps to `d'` at `t'` by
a run of `Tau`, or the event is a fault and the thread is dead. -/
def Step (L : Launch) (g : Nat) (Q : Params) (d : D) (e : Event) (u : TState) : Prop :=
  (next L g d e = some none ∨ ∃ d' t', next L g d e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ AtS L g Q d' t' ∧ Inv L g Q d') ∨
    (next L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u)

/-- The invariant at another site, with the same base word. -/
theorem Inv.to (hi : Inv L g Q d) (s : Site)
    (h : (s = .alloc ∨ s = .allocWr ∨ s = .relinq) → g % L.block < 32) :
    Inv L g Q ⟨s, d.w⟩ := ⟨hi.args, h⟩

/-- A table fact at a checkpoint where the register is live. -/
theorem tbl_mem {pc : Nat} {tm : Value} {r : Nat} {v : Value} (hl : r ∈ Flow.live pc)
    (hv : valueOf L g Q tm r = v) : (r, v) ∈ factsAt L g Q tm pc :=
  hv ▸ Flow.mem_factsFrom hl

theorem AtS.at (h : AtS L g Q d t) (hs : d.site.sub = 0) :
    At t d.site.pc (facts L g Q d) :=
  ⟨h.1, hs ▸ h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- An instruction that only advances (a barrier): to `d'` at the next instruction, with the
facts of the registers still live. -/
theorem step_adv {d' : D} (hn : next L g d e = some (some d')) (hi : Inv L g Q d')
    (hu : u = PTX.next t) (h : AtS L g Q d t) (hs0 : d.site.sub = 0) (hs1 : d'.site.sub = 0)
    (hpc : d'.site.pc = d.site.pc + 1) (htm : d'.w = d.w)
    (hl : ∀ r ∈ Flow.live d'.site.pc, r ∈ Flow.live d.site.pc) : Step L g Q d e u := by
  refine .inl (.inr ⟨d', u, hn, .refl, ?_, hi⟩)
  subst hu
  have h0 := h.at hs0
  refine ⟨by simp [PTX.next, h0.1, hpc], by simp [PTX.next, h0.2.1, hs1], h0.2.2.1,
    h0.2.2.2.1, ?_⟩
  have := (At.next h0).2.2.2.2
  unfold facts factsAt at this ⊢
  rw [htm]
  exact holds_factsFrom_mono this (hpc ▸ hl)

/-! ### The allocation (warp 0) -/

/-- The allocation: lane 0 goes on to the store of the allocated address (second sub-step), the
other lanes to the barrier. -/
theorem step_alloc (hs : d.site = .alloc) (hi : Inv L g Q d) (h : AtS L g Q d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g Q d e u := by
  obtain ⟨site, tm⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
  have hsub : t.sub = 0 := h.2.1
  obtain ⟨dst, n, -, hu⟩ := fires_tcAlloc hsub hf
  by_cases hl : laneOf L g = 0
  · simp only [hl, ↓reduceIte] at hu
    subst hu
    refine .inl (.inr ⟨⟨.allocWr, tm⟩, _, by simp [next, hl], .refl, ?_, hi.to _ (fun _ => hi.lane0
      (.inl rfl))⟩)
    exact ⟨h.1, rfl, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · simp only [hl, ↓reduceIte] at hu
    exact step_adv (d' := ⟨.bar0, tm⟩) (by simp [next, hl]) (hi.to _ (by simp)) hu h rfl rfl
      rfl rfl (by live_dec)

/-- The second sub-step of the allocation: lane 0's store of the address. -/
theorem step_allocWr (hs : d.site = .allocWr) (hi : Inv L g Q d) (h : AtS L g Q d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g Q d e u := by
  obtain ⟨site, tm⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
  obtain ⟨a, bs, -, hu⟩ := fires_tcAlloc_write h.2.1 hf
  refine .inl (.inr ⟨⟨.bar0, tm⟩, u, by simp [next], .refl, ?_, hi.to _ (by simp)⟩)
  subst hu
  refine ⟨by simp [h.1, Site.pc], rfl, h.2.2.1, h.2.2.2.1, ?_⟩
  have := h.2.2.2.2
  unfold facts factsAt at this ⊢
  exact holds_factsFrom_mono this (by live_dec)

/-! ### The barriers and the base word -/

theorem step_bar0 (hs : d.site = .bar0) (hi : Inv L g Q d) (h : AtS L g Q d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g Q d e u := by
  obtain ⟨site, tm⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_0)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSync _ _) from trivial) hf
  exact step_adv (d' := ⟨.ld0, tm⟩) (by simp [next]) (hi.to _ (by simp)) rfl h rfl rfl rfl rfl
    (by live_dec)

end
end PTX.Kernels.InklingRelDecode.Proof.DStart
