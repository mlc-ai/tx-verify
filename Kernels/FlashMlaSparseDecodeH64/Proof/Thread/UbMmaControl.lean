-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbRoles
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingCommitEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
import Lemmas.Flow.TmplOkSync

public section

/-! # Defined templates for the MMA warp's control events -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbMma

open PTX PTX.Proof PTX.Flow Wg1Mma

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

private theorem barrier_template (hpre : Pre P L mem0) {d : D} {t : TState}
    (hp : d.site.pc = 2160) (ha : (Wg1Mma.code P L g).AtD d t) :
    eventTmpl Assumptions.all L g t (.barSyncN (.reg 918) (.reg 919) false) =
      .bar 12 (PTX.next t) none .sync := by
  have h918 : t.regs 918 = some (b32 12) := atD_reg ha hp (by decide +kernel)
  have h919 : t.regs 919 = some (b32 384) := atD_reg ha hp (by decide +kernel)
  have h12 : readBits L g t 32 (.reg 918) = .ok (BitVec.ofNat 64 12) :=
    readBits_b32 h918 (by decide)
  have h384 : readBits L g t 32 (.reg 919) = .ok (BitVec.ofNat 64 384) :=
    readBits_b32 h919 (by decide)
  simp only [eventTmpl, barTmpl, h12, h384, BitVec.toNat_ofNat,
    show (12 : Nat) < 2 ^ 64 by omega, show (384 : Nat) < 2 ^ 64 by omega, Nat.mod_eq_of_lt,
    show ¬ (16 ≤ 12) by omega, ↓reduceIte, show (384 : Nat) % 32 = 0 by decide, hpre.block,
    show (BarMode.sync = BarMode.arrive) = False by decide, false_implies, true_and, or_true,
    reduceCtorEq]

/-- Valid MMA control templates include all waits, commits, fences, dispatch and length reads. -/
theorem control_tmpl_ok (hpre : Pre P L mem0) (hg : g < L.threads)
    {d : D} {t : TState} {ins : Instr} (ha : (Wg1Mma.code P L g).AtD d t)
    (hi : Inv P L g d) (hc : kernel.code[d.site.pc]? = some ins)
    (hLoad : ∀ k, d.site ≠ .qLoad k) (hCopy : ∀ k, d.site ≠ .qCopy k)
    (hQk : ∀ k, d.site ≠ .qkMma k) (hPv : ∀ k, d.site ≠ .pvMma k) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  intro hu
  let e : Event := ⟨t.pc, .ub f⟩
  have hf : (Machine.machine P L g).Fired (some (.mma d)) e none := by
    refine ⟨t, ⟨ha, hi⟩, ?_⟩
    change Fires t.pc (match kernel.code[d.site.pc]? with
      | some ins => eventTmpl Assumptions.all L g t ins.op
      | none => .ub .pcOutOfRange) e none
    rw [hc]
    change Fires t.pc (eventTmpl Assumptions.all L g t ins.op) e none
    rw [hu]
    exact ⟨rfl, rfl⟩
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have noWait (hw : d.site = .qWait ∨ d.site = .qCopyWait ∨
      d.site = .kvWait ∨ d.site = .soWait) : False := by
    obtain ⟨_, _, _, _, hk⟩ := RingEvents.mma_wait_object hpre hw hf
    cases hk
  have noCommit (hw : d.site = .qCopyCommit ∨ d.site = .qkCommit ∨ d.site = .pvCommit) :
      False := by
    obtain ⟨_, hk, _, _⟩ := RingCommitEvents.commit_issue hpre hg hw hf
    cases hk
  cases h : d.site
  case qLoad k => exact hLoad k h
  case qCopy k => exact hCopy k h
  case qkMma k => exact hQk k h
  case pvMma k => exact hPv k h
  case head =>
    have hp : d.site.pc = 1843 := by rw [h]; rfl
    rw [hp] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_2)
    have hr : t.regs 464 = some (b32 (warpOf L g)) := atD_reg ha hp (by decide +kernel)
    exact shfl_imm_ok (d := 558) (p := some 10) (.inr rfl) hb hr f hu
  case elect =>
    have hp : d.site.pc = 1853 := by rw [h]; rfl
    rw [hp] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_6)
    have hr : t.regs 794 = some (b32 4294967295) := atD_reg ha hp (by decide +kernel)
    exact elect_ok hr f hu
  case loadTopk =>
    have hp : d.site.pc = 1876 := by rw [h]; rfl
    rw [hp] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_15)
    have hAt := atD_at ha
    change At t d.site.pc (Wg1Mma.factsAt P L g d.site.pc d) at hAt
    rw [hp] at hAt
    rw [event_loadTopk hpre hAt] at hu
    cases hu
  case loadExtra =>
    have hp : d.site.pc = 1886 := by rw [h]; rfl
    rw [hp] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_16)
    have hAt := atD_at ha
    change At t d.site.pc (Wg1Mma.factsAt P L g d.site.pc d) at hAt
    rw [hp] at hAt
    rw [event_loadExtra hpre hAt] at hu
    cases hu
  case qArrive => cases RingEvents.query_expectTx hpre h hf
  case qWait => exact noWait (.inl h)
  case qCopyWait => exact noWait (.inr (.inl h))
  case kvWait => exact noWait (.inr (.inr (.inl h)))
  case soWait => exact noWait (.inr (.inr (.inr h)))
  case qCopyCommit => exact noCommit (.inl h)
  case qkCommit => exact noCommit (.inr (.inl h))
  case pvCommit => exact noCommit (.inr (.inr h))
  case qFence =>
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcFence_5)
    exact plainOk_tmpl hb rfl f hu
  case qCopyFence =>
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcFence_6)
    exact plainOk_tmpl hb rfl f hu
  case kvFence =>
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcFence_7)
    exact plainOk_tmpl hb rfl f hu
  case soFence =>
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcFence_8)
    exact plainOk_tmpl hb rfl f hu
  case outBar =>
    have hp : d.site.pc = 2160 := by rw [h]; rfl
    rw [hp] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_11)
    rw [barrier_template hpre hp ha] at hu
    cases hu
  case exit =>
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    cases hu

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbMma
