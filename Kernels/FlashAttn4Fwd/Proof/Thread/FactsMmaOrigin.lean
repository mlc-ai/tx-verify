-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaEvQk
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaEvPv
public import Kernels.FlashAttn4Fwd.Proof.Thread.Origin
public import Kernels.FlashAttn4Fwd.Proof.Thread.ElectFull
public import Lemmas.Flow.NotTcMma

@[expose] public section

/-! # Where an MMA comes from

Every MMA instruction of the kernel is one of the MMA warp's (`kernel_mma_pcs`), and no site of
another role is at one. So in an execution whose threads the machine follows, an MMA issue is
fired from an MMA state of a thread of warp 12 at an MMA site `.mma b j`, with the role's run
invariant and state invariant there, and its destination, operands, enable flag and masks are
those `MmaEv` names (`mma_origin`).

A thread that issues an MMA led every election of its trace (`mma_electLead`): its elections
all use the full mask (`elect_full`), so it led all or none (`electLead_or_nonLead`), and a
thread that led none never reaches an MMA site (`Counts.nonLead`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Mma

/-- **The MMA of an MMA site**, for every block. -/
theorem site_ev (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) {b j : Fin 8} {i tt : Nat}
    {base : Value} {pro : Nat → Value} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : Holds t.regs (facts L g ⟨.mma b j, i, tt, base, pro⟩))
    (hc : kernel.code[(Site.mma b j).pc]? = some ins)
    (hf : Fires (Site.mma b j).pc (eventTmpl asms L g t ins.op) e o) :
    e.kind = .tc (.mma (mmaCol b) (mmaSpec L g ⟨.mma b j, i, tt, base, pro⟩ b j)
      (mmaAcc ⟨.mma b j, i, tt, base, pro⟩ b j) (List.replicate 8 0)) := by
  cases hb : isPv b
  · exact qk_site_ev hpre hg hb h hc hf
  · exact pv_site_ev hpre hg hb h hc hf

end Mma

/-- Every MMA instruction of the kernel is at an MMA site's position. -/
theorem kernel_mma_pcs : OpPcsFast kernel.code tcMmaOp Flow.mma.toList = true := by
  decide +kernel

abbrev mmaPcs : List Nat := Flow.mma.toList

theorem Prologue.site_not_mma (s : Prologue.Site) : s.pc ∉ mmaPcs := by
  cases s <;> site_decide

theorem Loader.site_not_mma (s : Loader.Site) : s.pc ∉ mmaPcs := by
  cases s <;> site_decide

theorem Store.site_not_mma (s : Store.Site) : s.pc ∉ mmaPcs := by
  cases s <;> site_decide

theorem Idle.site_not_mma (s : Idle.Site) : s.pc ∉ mmaPcs := by
  cases s <;> site_decide

theorem Correction.site_not_mma (s : Correction.Site) : s.pc ∉ mmaPcs := by
  cases s <;> site_decide

theorem Softmax.site_not_mma (s : Softmax.Site) : s.pc ∉ mmaPcs := by
  cases s <;> site_decide

/-- **The origin of an MMA**: an MMA issue is fired from an MMA state at an MMA site of a
thread of warp 12, with the role's run invariant and state invariant, and is the site's MMA. -/
theorem mma_origin (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k dd : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (hi : X.MmaIssue (g, k) dd s acc mask) :
    ∃ (d : Mma.D) (b j : Fin 8), Frame.stateAt (code L) X g k = some (some (.inr (.mma d))) ∧
      d.site = .mma b j ∧ Mma.Counts L g d ((X.tr g).take k) ∧ Mma.Inv L g d ∧
      g < L.threads ∧ warpOf L g = 12 ∧ dd = Mma.mmaCol b ∧ s = Mma.mmaSpec L g d b j ∧
      acc = Mma.mmaAcc d b j ∧ mask = List.replicate 8 0 := by
  obtain ⟨pc, he⟩ := hi
  obtain ⟨d, t, ins, o, hσ, hJ, hat, hinv, hc, hf⟩ :=
    event_origin hpre hX ht (fun g hg => roleJ_run hpre hg) he nofun
  have hg := Frame.lt_of_get hX he
  have hop := fires_tcMma_op hf (e := ⟨pc, _⟩) rfl
  have hpc := OpPcsFast.mem kernel_mma_pcs hc hop
  rcases d with p | r
  · exact absurd hpc (Prologue.site_not_mma p.site)
  cases r with
  | idle s => exact absurd hpc (Idle.site_not_mma s.site)
  | loader l => exact absurd hpc (Loader.site_not_mma l.site)
  | store s => exact absurd hpc (Store.site_not_mma s.site)
  | softmax s => exact absurd hpc (Softmax.site_not_mma s.site)
  | corr c => exact absurd hpc (Correction.site_not_mma c.site)
  | mma m =>
    have hw : RoleKind.Warp .mma (warpOf L g) :=
      role_warp_run hpre hg (Frame.trace (C := code L) (fun _ hg => sound hpre hg) hX hg) k
        (.mma m) hσ
    have hev := Mma.site_event hpre hg hat.2.2.2.2 hc hf
    obtain ⟨site, i, tt, base, pro⟩ := m
    cases site
    case mma b j =>
      have hk := Mma.site_ev hpre hg hat.2.2.2.2 hc hf
      simp only [Kind.tc.injEq, TcKind.mma.injEq] at hk
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hk
      exact ⟨_, b, j, hσ, rfl, hJ, hinv.1, hg, hw, rfl, rfl, rfl, rfl⟩
    all_goals
      have := Mma.isMma_ev hev rfl
      simp [Mma.isMma] at this

/-- Every election of a consistent execution's thread uses the full mask. -/
theorem electMask_full (hX : Consistent L kernel asms mem0 X) (g : Nat) :
    ElectMask 4294967295 (X.tr g) := by
  intro e he mask inst ld hk
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem he
  have hx : (X.tr g)[n] = ⟨(X.tr g)[n].pc, .elect mask inst ld⟩ := by rw [← hk]
  exact elect_full hX (e := (g, n)) (pc := (X.tr g)[n].pc) (inst := inst) (l := ld)
    (show (X.tr g)[n]? = _ by rw [List.getElem?_eq_getElem hn, ← hx])

/-- **A thread that issues an MMA led every election of its trace.** -/
theorem mma_electLead (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k : Nat} (hi : IsMma X (g, k)) :
    ElectLead L g (X.tr g) := by
  obtain ⟨dd, s, acc, mask, hi⟩ := hi
  rcases electLead_or_nonLead hX.elect (electMask_full hX g) with h | h
  · exact h
  · obtain ⟨d, b, j, -, hs, hJ, -⟩ := mma_origin hpre hX ht hi
    have := (hJ.nonLead (h.take k)).1
    rw [hs] at this
    cases this

end
end PTX.Kernels.FlashAttn4Fwd.Proof
