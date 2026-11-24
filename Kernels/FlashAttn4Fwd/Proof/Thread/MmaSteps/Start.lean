-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSteps.Base

@[expose] public section

/-! The pair allocation of the MMA warp: the request, then lane 0's store of the address, the
instruction's second event (sub-step 1). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The pair allocation request: lane 0 goes on to its address store, the others to
`bar.sync 2`. -/
theorem step_alloc {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .alloc) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    mma_cont L g d e u := by
  obtain ⟨site, i, tr, base, pro⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
  obtain ⟨dst, n, rfl, rfl⟩ := fires_tcAlloc h.2.1 hf
  right
  by_cases hl : laneOf L g = 0
  · refine ⟨⟨.allocWrite, i, tr, base, pro⟩, _, by simp [next, hl], .refl, ?_,
      ⟨hi.t, nofun, hi.trip⟩⟩
    simp only [hl, ↓reduceIte]
    exact ⟨h.1, rfl, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · refine ⟨⟨.bar0, i, tr, base, pro⟩, _, by simp [next, hl], .refl, ?_, ⟨hi.t, nofun, hi.trip⟩⟩
    simp only [hl, ↓reduceIte]
    have hv : valueOf L g ⟨.bar0, i, tr, base, pro⟩ = valueOf L g ⟨.alloc, i, tr, base, pro⟩ :=
      rfl
    refine atS_of_at rfl (At.mono (At.next h) ?_)
    show Holds _ (Flow.factsFrom (Flow.live Flow.bar_0) _)
    rw [hv]
    exact Flow.holds_factsFrom_mono h.2.2.2.2 (by table_decide)

/-- Lane 0's address store, then `bar.sync 2`. -/
theorem step_allocWrite {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .allocWrite) (hi : Inv L g d) (h : AtS L g t d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    mma_cont L g d e u := by
  obtain ⟨site, i, tr, base, pro⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
  obtain ⟨a, bs, rfl, rfl⟩ := fires_tcAlloc_write h.2.1 hf
  right
  have hv : valueOf L g ⟨.bar0, i, tr, base, pro⟩ =
      valueOf L g ⟨.allocWrite, i, tr, base, pro⟩ := rfl
  refine ⟨⟨.bar0, i, tr, base, pro⟩, _, by simp [next], .refl, ?_, ⟨hi.t, nofun, hi.trip⟩⟩
  refine ⟨by simp only [h.1]; rfl, rfl, h.2.2.1, h.2.2.2.1, ?_⟩
  show Holds _ (Flow.factsFrom (Flow.live Flow.bar_0) _)
  rw [hv]
  exact Flow.holds_factsFrom_mono h.2.2.2.2 (by table_decide)

theorem stepOk_alloc {L : Launch} {g : Nat} {pro : Nat → Value} (i tr : Nat) (base : Value)
    (pr : Nat → Value) : (code asms L g pro).StepOk ⟨.alloc, i, tr, base, pr⟩ :=
  stepOk_of (fun hn => by simp only [next] at hn; split_ifs at hn <;> cases hn <;> exact nofun)
    fun hi h hc hf => .inl (step_alloc rfl hi (at_of_atS rfl h) hc hf)

theorem stepOk_allocWrite {L : Launch} {g : Nat} {pro : Nat → Value} (i tr : Nat) (base : Value)
    (pr : Nat → Value) : (code asms L g pro).StepOk ⟨.allocWrite, i, tr, base, pr⟩ :=
  stepOk_of (fun hn => by cases hn; exact nofun)
    fun hi h hc hf => .inl (step_allocWrite rfl hi h hc hf)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
