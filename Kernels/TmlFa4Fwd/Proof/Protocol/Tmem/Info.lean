-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.JR
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Machine
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.NoLdSt
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Shape
public import Kernels.TmlFa4Fwd.Proof.Lib.TmemAccess
public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
public import Kernels.TmlFa4Fwd.Proof.Mma.Machine
public import Kernels.TmlFa4Fwd.Proof.Mma.Shape
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Startup.Machine
public import Kernels.TmlFa4Fwd.Proof.Startup.Shape
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Execution.NoTcCp
public import Lemmas.Flow.FmaRun
public import Lemmas.Flow.NotTcShift
import Kernels.TmlFa4Fwd.Proof.Lib.MmaLayout
import Kernels.TmlFa4Fwd.Proof.Lib.CtaGroup
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.FollowView
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Kernels.TmlFa4Fwd.Proof.Top.JRStub
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Correction.Export.TmemAddr
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemAddrSt
import Lemmas.Flow.NotBulk
import Lemmas.Tcgen05.TcMmaResultLayout
import Std.Tactic.BVDecide.Normalize.Prop

import Lemmas.Kernel.FrameU

@[expose] public section

/-! # Every Tensor Memory access is of the thread's CTA, below column 512 (`Tmem1.AccessInfo`)

* An MMA's cells (`mma_access`): every MMA is of group one with the issuer's CTA group
  (`Mma.actualMmaOwnership`), which is the issuer's CTA alone (`Mma.singleCtaGroup`), so every
  result and A cell is in the issuer's CTA; Core's layouts put result cells below column 512
  (`resultCell_bounds`) and A cells too (`aCell_col`).
* A load's or store's cells (`ldst_access`): a load or store event is fired from a correction or
  softmax state (every other role's shape table has none), where its shape is `.32x32b` and its
  address column plus its register count is at most 512 (`Correction.corr_tc`,
  `Softmax.soft_tc`); the `.32x32b` cell of register `j` is the address column plus `j`.
* No `tcgen05.cp` or `tcgen05.shift` is issued: the code has neither instruction. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- An A cell is in one of the group's CTAs and below column 512. -/
theorem aCell_col {s : TcMma.OperandSpec} {index : Nat} {c : TcMma.Cell} {b : Nat}
    (h : TcMma.aCell s index = some (c, b)) :
    (c.cta = s.lowCta ∨ c.cta = s.highCta) ∧ c.column < 512 := by
  unfold TcMma.aCell at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨a, -, h⟩ := h
  have hb : 0 < s.descriptor.kind.k * s.descriptor.kind.width := by
    cases s.descriptor.kind <;> simp [TcMma.Kind.k, TcMma.Kind.width]
  have hm := Nat.mod_lt index hb
  have hq : index % (s.descriptor.kind.k * s.descriptor.kind.width) / 4 <
      (s.descriptor.kind.k * s.descriptor.kind.width + 3) / 4 := by omega
  split_ifs at h with hc <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, -⟩ := h <;> exact ⟨by simp, by have := hc.2.2.1; dsimp only; omega⟩

/-- **An MMA's Tensor Memory cells** are in the issuer's CTA, below column 512. -/
theorem mma_access (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {e : EvId}
    {cell : TcMma.Cell} (h : X.MmaAccess e cell) :
    e.1 < L.threads ∧ cell.cta = e.1 / L.block ∧ cell.column < 512 ∧ Tmem1.IsMma X e := by
  have key : ∀ {d s acc mask}, X.MmaIssue e d s acc mask →
      e.1 < L.threads ∧ s.lowCta = e.1 / L.block ∧ s.highCta = e.1 / L.block := by
    intro d s acc mask hi
    obtain ⟨pc, he⟩ := hi
    have hg : e.1 < L.threads := Frame.lt_of_get hX (k := e.2) he
    obtain ⟨hgrp, ctas, hc, hl, hh⟩ := Mma.actualMmaOwnership hX ⟨pc, he⟩
    rw [hgrp, Mma.singleCtaGroup hp hg] at hc
    cases hc
    simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hl hh
    exact ⟨hg, hl.symm, hh.symm⟩
  rcases h with ⟨d, s, acc, mask, row, col, hi, hw⟩ | ⟨d, s, mask, row, col, hi, hr⟩ |
      ⟨d, s, acc, mask, idx, b, hi, ha⟩
  · obtain ⟨hg, hl, hh⟩ := key hi
    have hr := TcMma.writeCell_resultCell hw
    refine ⟨hg, ?_, (TcMma.resultCell_bounds hr).2, ⟨_, _, _, _, hi⟩⟩
    rcases TcMma.resultCell_cta hr with h | h <;> rw [h] <;> assumption
  · obtain ⟨hg, hl, hh⟩ := key hi
    refine ⟨hg, ?_, (TcMma.resultCell_bounds hr).2, ⟨_, _, _, _, hi⟩⟩
    rcases TcMma.resultCell_cta hr with h | h <;> rw [h] <;> assumption
  · obtain ⟨hg, hl, hh⟩ := key hi
    obtain ⟨hc, hcol⟩ := aCell_col ha
    refine ⟨hg, ?_, hcol, ⟨_, _, _, _, hi⟩⟩
    rcases hc with h | h <;> rw [h] <;> assumption

/-- An event fired from a state of a code machine whose states all step is its site's. -/
theorem fired_at_site {C : Code kernel Assumptions.all L g} (hC : ∀ d, C.StepAt d) {d : C.D}
    {e : Event} {o : Option TState} (hf : C.toMachine.Fired (some d) e o) :
    ∃ t ins, C.AtD d t ∧ C.inv d ∧ kernel.code[C.pc d]? = some ins ∧
      Fires (C.pc d) (eventTmpl Assumptions.all L g t ins.op) e o := by
  obtain ⟨t, ⟨hat, hi⟩, hf⟩ := hf
  obtain ⟨ins, hc, -, -⟩ := (hC d).site hi
  change Fires t.pc (C.tmpl (some d) t) e o at hf
  simp only [Code.tmpl, hc] at hf
  rw [hat.1] at hf
  exact ⟨t, ins, hat, hi, hc, hf⟩

/-- An MMA's CTAs match the launch. -/
theorem mma_matches (hX : Consistent L kernel Assumptions.all m X) {i : EvId} {d : Nat}
    {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat} (hi : X.MmaIssue i d s acc mask) :
    s.MatchesLaunch L (i.1 / L.block) :=
  (Mma.actualMmaOwnership hX hi).2

/-- The bound a Tensor Memory load or store event meets. -/
def LdStOk (e : Event) : Prop :=
  (∀ a vals sh, e.kind = .tc (.ld a vals sh) → sh = .s32x32b ∧ a % 65536 + vals.length ≤ 512) ∧
  (∀ a vals sh, e.kind = .tc (.st a vals sh) → sh = .s32x32b ∧ a % 65536 + vals.length ≤ 512)

/-- An event of a shape table that has no Tensor Memory load or store meets the bound. -/
theorem ldStOk_of {e : Event} (h1 : ∀ a vals sh, e.kind ≠ .tc (.ld a vals sh))
    (h2 : ∀ a vals sh, e.kind ≠ .tc (.st a vals sh)) : LdStOk e :=
  ⟨fun a vals sh h => absurd h (h1 a vals sh), fun a vals sh h => absurd h (h2 a vals sh)⟩

set_option maxHeartbeats 4000000 in
theorem mma_noldst {d : Mma.D} {pc : Nat} {k : Kind} (hk : IsLdSt k)
    (hev : Mma.Ev p L g d ⟨pc, k⟩) : False := by
  obtain ⟨s, rest⟩ := d
  cases s <;> simp only [Mma.Ev] at hev
  all_goals first | exact (epi_noldst hk hev).elim | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try subst_vars)
  all_goals simp_all [IsLdSt]

set_option maxHeartbeats 4000000 in
theorem ld_noldst {w : Nat} {d : Loader.D} {pc : Nat} {k : Kind} (hk : IsLdSt k)
    (hev : Loader.Ev p L g w d ⟨pc, k⟩) : False := by
  obtain ⟨s, rest⟩ := d
  cases s <;> simp only [Loader.Ev] at hev
  all_goals first | exact (epi_noldst hk hev).elim | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try subst_vars)
  all_goals simp_all [IsLdSt]

theorem start_noldst {s : Startup.D} {n : Cls → Nat} (hJ : JR p L g (.inl s, n)) {pc : Nat}
    {k : Kind} (hk : IsLdSt k) (hev : Startup.Ev L g s ⟨pc, k⟩) : False := by
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site
  case bar => simp only [Startup.Ev, Kind.bar.injEq] at hev; subst hev; exact hk
  case enter r => exact absurd rfl (jr_start_site hJ r)
  case sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk'⟩ := hev <;> subst hk' <;>
      exact hk
  all_goals simp only [Startup.Ev] at hev
  all_goals first
    | (subst hev; exact hk)
    | (rcases hev with ⟨_, _, -, hk'⟩ | ⟨_, hk'⟩ <;> subst hk' <;> exact hk)
    | (rcases hev with ⟨_, _, hk'⟩ | ⟨_, hk'⟩ <;> subst hk' <;> exact hk)

set_option maxHeartbeats 8000000 in
/-- **Every Tensor Memory load or store event** is a `.32x32b` access of at most 512 columns past
its address column. -/
theorem ldst_ok (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) : LdStOk e := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨σ, hσ, hJ, hi, hev⟩ :=
    ev_at hp hX (table_shape_of hp hFw) (table_followed hp hX hFw) he hub
  obtain ⟨σ1, n⟩ := σ
  obtain ⟨pc, kind⟩ := e
  rcases σ1 with s | ⟨i, d⟩
  · refine ldStOk_of (fun a vals sh h => ?_) (fun a vals sh h => ?_) <;> simp only at h <;>
      subst h <;> exact start_noldst (hev := hev) hJ (by trivial)
  cases i with
  | correction =>
    obtain ⟨t, ins, _, hat, hinv, hc, hfi⟩ :=
      Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ hub
    exact Correction.corr_tc hp hat hinv hc hfi
  | softmax =>
    obtain ⟨t, ins, _, hat, hinv, hc, hfi⟩ :=
      Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ hub
    exact Softmax.soft_tc hp hat hinv hc hfi
  | stub r =>
    exact (jr_stub hJ).elim
  | epilogue =>
    refine ldStOk_of (fun a vals sh h => ?_) (fun a vals sh h => ?_) <;> simp only at h <;>
      subst h <;> exact epi_noldst (hev := hev) (by trivial)
  | mma =>
    refine ldStOk_of (fun a vals sh h => ?_) (fun a vals sh h => ?_) <;> simp only at h <;>
      subst h <;> rcases d with d | ⟨⟨⟩, d⟩
    all_goals first
      | (rcases hev with ⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk)
      | exact mma_noldst (hev := hev) (by trivial)
  | loader b =>
    refine ldStOk_of (fun a vals sh h => ?_) (fun a vals sh h => ?_) <;> simp only at h <;>
      subst h <;> exact ld_noldst (hev := hev) (by trivial)

theorem kernel_noTcCp : kernel.NoTcCp = true := by decide +kernel

theorem kernel_noShift : kernel.code.all (fun ins => !tcShiftOp ins.op) = true := by
  decide +kernel

/-- The kernel issues no `tcgen05.shift`. -/
theorem no_shift (hX : Consistent L kernel Assumptions.all m X) {i : EvId} {s : TcShift.Spec} :
    ¬ X.ShiftIssue i s := by
  rintro ⟨pc, he⟩
  exact no_kind_of_code hX tcShiftOp (fun k => ∃ spec, k = .tc (.shift spec))
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, h⟩ => fires_tcShift_op hf h) kernel_noShift he
    ⟨s, rfl⟩

/-- **Every Tensor Memory access is a launched thread's MMA, load or store of a cell of its CTA
below column 512, and no copy or shift is issued.** -/
theorem tmem_info (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) :
    Tmem1.AccessInfo L X := by
  refine ⟨fun {e cell} h => ?_, noCp_of_consistent kernel_noTcCp hX,
    fun i s => no_shift hX⟩
  obtain ⟨g, k⟩ := e
  rcases h with h | ⟨j, a, vals, sh, ⟨pc, he⟩, hj, rfl⟩ | ⟨a, vals, sh, j, ⟨pc, he⟩, hj, rfl⟩ |
      ⟨c, -, -, -, hc, -⟩ | ⟨s, hs, -⟩ | ⟨s, hs, -⟩
  · obtain ⟨h1, h2, h3, h4⟩ := mma_access hp hX h
    exact ⟨h1, h2, h3, Or.inl h4⟩
  · have hg := Frame.lt_of_get hX he
    obtain ⟨rfl, hb⟩ := (ldst_ok hp hX hFw he (by intro f hf; cases hf)).1 a vals sh rfl
    rw [tcDataCell_s32x32b]
    refine ⟨hg, rfl, ?_, Or.inr (Or.inl ⟨a, vals, .s32x32b, pc, he⟩)⟩
    simp only [tcDataCell32]
    omega
  · have hg := Frame.lt_of_get hX he
    obtain ⟨rfl, hb⟩ := (ldst_ok hp hX hFw he (by intro f hf; cases hf)).2 a vals sh rfl
    rw [tcDataCell_s32x32b]
    refine ⟨hg, rfl, ?_, Or.inr (Or.inr ⟨a, vals, .s32x32b, pc, he⟩)⟩
    simp only [tcDataCell32]
    omega
  · exact absurd hc (noCp_of_consistent kernel_noTcCp hX _ _)
  · exact absurd hs (no_shift hX)
  · exact absurd hs (no_shift hX)

end
end PTX.Kernels.TmlFa4Fwd.Proof
