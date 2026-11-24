-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LoaderSteps
public import Kernels.InklingRelDecode.Proof.Thread.LoaderRng
public import Lemmas.Flow.Compose

@[expose] public section

/-! # The loader's obligations as a code machine

Every loader site is an event instruction whose guard holds by the facts (`site_ok`: the arrival's
guard `%p20` is the lane test, which holds at the arrival by the invariant; each copy's guard is
the election's predicate, true at the copy), and every event fired at a loader state steps to the
state `next` gives (`step`); both come from `stepAt` (`LoaderSteps`), the obligation of every
state of `code`, the role as a code machine from `setmaxnreg.dec` (`LoaderSiteTac`). `entry`
turns the inherited registers at the role's first instruction into the role's first state.

The role has no `Code.Sound` of its own: its start state is the dispatch's (the worker loop's
`brx.idx` at pc 2343), which composes it, and the role ends at `setmaxnreg.inc` (the abstract
successor `some none`: the next instruction is the dispatch loop's). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-- The instruction of each loader site: an event instruction whose guard holds. -/
theorem site_ok (hi : Inv L g d) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts L g d) ins.guard := by
  obtain ⟨P, _⟩ := hi.pro
  exact (stepAt (L := L) (g := g) P d).site hi

/-- Every event fired at a loader state steps to its successor. -/
theorem step (hi : Inv L g d) (h : AtS L g d t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨P, _⟩ := hi.pro
  rcases (stepAt (L := L) (g := g) P d).step ins h hi hc hf with
    (hn | ⟨d', t', hn, hr, ht, hi'⟩) | ⟨hn, hd⟩
  · exact .inl (.inl hn)
  · exact .inr ⟨d', t', hn, hr, ht, hi'⟩
  · exact .inl (.inr ⟨hn, hd⟩)

/-- **The loader's entry**: the inherited registers at the role's `setmaxnreg.dec` (valued by
`pv`, the prologue's table, which on the registers live there is `Pro.val L g P`) are the facts
of the role's first state, which satisfies the role's invariant. -/
theorem entry {pv : Nat → Value} (P : Pro) {s : TState}
    (hpv : ∀ r ∈ Flow.live Flow.setMaxReg_5, pv r = Pro.val L g P r)
    (h : At s Flow.setMaxReg_5 (Flow.factsFrom (Flow.live Flow.setMaxReg_5) pv)) :
    At s Site.setMaxDec.pc (facts L g (D.start L g P)) ∧ Inv L g (D.start L g P) := by
  refine ⟨at_congr h fun r hr => ?_, ⟨P, fun _ _ _ => rfl⟩, fun h => by
    (rcases h with h | h <;> simp [D.start] at h), fun h => by simp [D.start, Site.bounded,
    Site.inLoop] at h, fun h => by simp [D.start, Site.inLoop] at h,
    fun h => by simp [D.start, Site.inLoop] at h, rfl, fun h => by cases h⟩
  have hr' : r ∈ Flow.live Flow.setMaxReg_5 := hr
  rw [hpv r hr']
  have hl : Flow.live Flow.setMaxReg_5 = [3, 462, 463, 464, 465, 466, 528, 529, 530, 531, 532,
      534, 1949, 2020] := by decide +kernel
  rw [hl] at hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;>
    simp [valueOf, table, D.start, PTX.Flow.lookupLit]

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
