-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Safety.Tmem
public import Lemmas.MBarrier.BarrierOrdinal
public import Lemmas.CtaBarrier.CtaBarrierFault
public import Kernels.TcGemm.Proof.NoBarArrive

@[expose] public section

/-! # The CTA barrier branches of `Unsafe`

Every arrival is the aligned `bar.sync 0` for the whole CTA, at `Flow.bar_0` as a thread's first
arrival and at `Flow.bar_1` as its second (`pc_of`). So two lanes of a warp at one ordinal are at
one source instruction, and a thread that exited made both arrivals (`trace_full`): no mismatch
(`no_barMismatch`); every arrival has the same count, so none faults (`no_ctaBarFault`). -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof PTX.Flow CtaBarrier
noncomputable section
variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}
variable (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
  (hW : Wit A B D L.sharedBase X P m u)
include hpre hX hW

omit hpre hX in
/-- An arrival's source line is fixed by its ordinal. -/
theorem pc_of {g j id pc : Nat} {count : Option Nat} (he : X.IsBarrier (g, j) id count pc) :
    pc = if ((X.tr g).take j).countP Execution.isBar = 0 then Flow.bar_0 else Flow.bar_1 := by
  have hcount := hW.bar_full he
  subst hcount
  obtain ⟨hg, hj, -, -⟩ := hW.bar he
  have hk := hW.barK (k := ((X.tr g).take j).countP Execution.isBar) ⟨⟨id, pc, he⟩, rfl⟩
  have hget : fullAt A B D L.sharedBase g (P g) j = some ⟨pc, .bar id⟩ := by
    change X.get (g, j) = some ⟨pc, .bar id⟩ at he
    rw [hW.get_of_lt hg hj] at he
    exact he
  rcases hk.2.2 with ⟨hi, hn⟩ | ⟨hi, hn⟩
  · have hpos := hd_pos (g := g)
    rw [show j = hd g - 1 by omega, fullAt_bar0] at hget
    simp only [bar0E, Option.some.injEq, Event.mk.injEq] at hget
    rw [hn]; simpa using hget.1.symm
  · rw [hi, show ldIdx g (P g) + 11 = ldIdx g (P g) + 1 + 10 by omega, fullAt_post] at hget
    simp [postAt, bar1E, Option.some.injEq, Event.mk.injEq] at hget
    rw [hn]; simpa using hget.1.symm

omit hpre hX in
/-- Every barrier event is an aligned whole-CTA barrier. -/
theorem bars_aligned : ∀ g ev, ev ∈ X.tr g → ∀ id count, ev.kind = .bar id count →
    count = none ∧ kernel.alignedAt ev.pc = true := by
  intro g ev hm id count hk
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hm
  obtain ⟨pc, kd⟩ := ev
  dsimp only at hk
  subst hk
  have he : X.IsBarrier (g, j) id count pc := hj
  refine ⟨hW.bar_full he, ?_⟩
  dsimp only
  rw [pc_of hW he]
  split <;> decide +kernel

omit hpre in
/-- **Barriers are matched.** -/
theorem no_barMismatch : ¬ BarMismatch L X := by
  rintro (⟨g, h, i, j, id, id', count, count', pc, pc', -, hi, hj, -, hne⟩ | hna)
  · have hc := hW.bar_full hi
    have hc' := hW.bar_full hj
    obtain ⟨-, -, rfl, -⟩ := hW.bar (show X.get (g, i) = some ⟨pc, .bar id⟩ by subst hc; exact hi)
    obtain ⟨-, -, rfl, -⟩ := hW.bar
      (show X.get (h, j) = some ⟨pc', .bar id'⟩ by subst hc'; exact hj)
    rcases hne with hn | hn <;> simp_all
  · exact hX.not_barArriveMismatch Fact.out hna

omit hpre in
/-- **Two lanes of a warp at one barrier ordinal are at one source instruction.** -/
theorem no_barDivergent : ¬ AlignedClass.bar.Divergent L kernel X := by
  rw [AlignedClass.divergent_bar_iff]
  rintro ⟨g, h, i, j, id, id', count, count', mode, mode', pc, pc', -, hi, hj, hord, -, hne⟩
  cases mode
  case arrive => exact hX.noBarArrive Fact.out _ _ _ _ hi
  cases mode'
  case arrive => exact hX.noBarArrive Fact.out _ _ _ _ hj
  have hpc := pc_of hW (show X.IsBarrier (g, i) id count pc from hi)
  have hpc' := pc_of hW (show X.IsBarrier (h, j) id' count' pc' from hj)
  rw [hord] at hpc
  exact hne (hpc.trans hpc'.symm)

omit hpre in
/-- **No thread exits before an aligned barrier its CTA's other threads reach.** -/
theorem no_barExited : ¬ AlignedClass.bar.Exited L kernel X := by
  rintro ⟨e, f, ev, -, he, hev, -, hs⟩
  change kernel.isAlignedCtaBar ev = true at hev
  change X.ExitedShort kernel.isAlignedCtaBar f
    (((X.tr e.1).take e.2).countP kernel.isAlignedCtaBar) at hs
  generalize hk : ((X.tr e.1).take e.2).countP kernel.isAlignedCtaBar = k at hs
  obtain ⟨pc0, id, mode, rfl, -⟩ := Kernel.isAlignedCtaBar_iff hev
  cases mode
  case arrive => exact (hX.noBarArrive Fact.out _ _ _ _ he).elim
  have hbe : X.IsBarrier e id none pc0 := he
  rw [Execution.countP_isAlignedCtaBar (fun ev hm =>
    bars_aligned hW e.1 ev (List.mem_of_mem_take hm))
    (fun ev hm => hX.noBarArrive_tr Fact.out e.1 ev (List.mem_of_mem_take hm))] at hk
  have hkk := hW.barK (k := k) ⟨⟨id, pc0, hbe⟩, hk⟩
  obtain ⟨pcx, hx⟩ := hs.1
  obtain ⟨hgf, hmf, -⟩ := trace_full hX hW hx
  have := ldIdx_eq (g := f.1) (P f.1)
  have := tl_ge (g := f.1) (P f.1)
  have := hd_pos (g := f.1)
  have hfull := fullE_length (A := A) (B := B) (D := D) (S := L.sharedBase) (g := f.1) (P f.1)
  have b0 : X.IsBarrier (f.1, hd f.1 - 1) 0 none Flow.bar_0 := by
    show X.get _ = _
    rw [hW.get_of_lt hgf (by rw [hmf, hfull]; split <;> omega), fullAt_bar0]; rfl
  have b1 : X.IsBarrier (f.1, ldIdx f.1 (P f.1) + 11) 0 none Flow.bar_1 := by
    show X.get _ = _
    rw [hW.get_of_lt hgf (by rw [hmf, hfull]; split <;> omega),
      show ldIdx f.1 (P f.1) + 11 = ldIdx f.1 (P f.1) + 1 + 10 by omega, fullAt_post]
    rfl
  have k0 := hW.barK (k := ((X.tr f.1).take (hd f.1 - 1)).countP Execution.isBar)
    ⟨⟨0, _, b0⟩, rfl⟩
  have k1 := hW.barK (k := ((X.tr f.1).take (ldIdx f.1 (P f.1) + 11)).countP Execution.isBar)
    ⟨⟨0, _, b1⟩, rfl⟩
  rcases hkk.2.2 with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · rcases k0.2.2 with ⟨-, h0⟩ | ⟨h0, -⟩
    · exact Execution.not_exitedShort_of_barK X (bars_aligned hW) (hX.noBarArrive_tr Fact.out)
        ⟨⟨0, _, b0⟩, h0⟩ hs
    · omega
  · rcases k1.2.2 with ⟨h0, -⟩ | ⟨-, h0⟩
    · omega
    · exact Execution.not_exitedShort_of_barK X (bars_aligned hW) (hX.noBarArrive_tr Fact.out)
        ⟨⟨0, _, b1⟩, h0⟩ hs

omit hpre in
/-- **No barrier faults.** -/
theorem no_ctaBarFault : ¬ CtaBarFault L X :=
  not_ctaBarFault hX fun _ _ _ _ _ _ _ _ h1 h2 => (hW.bar_full h1).trans (hW.bar_full h2).symm

end
end PTX.Kernels.TcGemm.Proof
