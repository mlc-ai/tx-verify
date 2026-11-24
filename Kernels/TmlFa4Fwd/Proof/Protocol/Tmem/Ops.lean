-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Mma.Shape
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Top.Table
public import Lemmas.Tmem.Tmem1Protocol
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Mma.Export.SafePre
import Kernels.TmlFa4Fwd.Proof.Top.JRStub
import Kernels.TmlFa4Fwd.Proof.Top.JRView
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Mma.Export.TmemCount
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The Tensor Memory operations of the MMA warp (`Tmem.One.Tmem1Ops`)

Every Tensor Memory resource event is the MMA warp's (warp 12), in group one, and its thread's
`n`-th has the shape `n` (`TmemShape`): the allocation of 512 columns from the allocation prefix
(no operation before it), the relinquishment (one before it), the deallocation of 512 columns
(two before it). Every other role's shape table and the startup's admit no resource event
(`tev_res`); the counts are `mma_count`'s. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

set_option maxHeartbeats 8000000 in
/-- **A resource event is fired from a state of the MMA warp.** -/
theorem tev_res {σ : (thread p L g).D} {e : Event} {grp : CtaGroup} {dst : Option Loc}
    {act : Tmem.Request} (hJ : JR p L g σ) (hi : (thread p L g).inv σ) (hev : TEv p L g σ e)
    (hk : e.kind = .tc (.resource grp dst act)) :
    ∃ d n, σ = (.inr ⟨.mma, d⟩, n) := by
  obtain ⟨σ1, n⟩ := σ
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  rcases σ1 with s | ⟨i, d⟩
  · exfalso
    have := start_nores (L := L) (g := g) (s := s) (e := ⟨pc, _⟩) hev hi.2
    simp [Tmem.Pair.isTmemOp] at this
  cases i with
  | mma => exact ⟨d, n, rfl⟩
  | epilogue => exact (epi_nores hev rfl).elim
  | correction =>
    exfalso
    rcases hev.1.data_or_vote with hev | ⟨_,_,h⟩
    case inr => cases h
    unfold Correction.Ev at hev
    split at hev <;> first
      | exact (epi_nores hev rfl).elim
      | simp_all [Correction.rdOrUb]
  | softmax =>
    exfalso
    have hev := hev.1
    unfold Softmax.Ev at hev
    split at hev <;> first
      | exact (epi_nores hev rfl).elim
      | simp_all [Softmax.rdOrUb, Softmax.tcLdOrUb]
  | loader b =>
    exfalso
    simp only [TEv] at hev
    unfold Loader.Ev at hev
    split at hev <;> first
      | exact (epi_nores hev rfl).elim
      | simp_all
  | stub r =>
    exact (jr_stub hJ).elim

set_option maxHeartbeats 8000000 in
/-- **The Tensor Memory operations of the MMA warp.** -/
theorem tmem1Ops (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) :
    Tmem.One.Tmem1Ops L X 12 := by
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  refine ⟨by rw [hp.block]; decide, fun {g k pc grp dst act} hg he => ?_⟩
  obtain ⟨σ, hσ, hJ, hi, hev⟩ := ev_at hp hX hT hF he (by intro f hf; cases hf)
  obtain ⟨d, n, rfl⟩ := tev_res hJ hi hev rfl
  have h12 := jr_mma hJ
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp
    (show (X.tr g)[k]? = _ from he)).1
  have hc := mma_count hp hX hg h12 k hk _ hσ
  refine ⟨h12, ?_⟩
  obtain ⟨t, ins, o, hat, hinv, hcd, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (by intro f h; cases h)
  rcases d with s0 | ⟨⟨⟩, d⟩
  · have hk3 := Mma.pre_kind hp hat hcd hf
    cases s0 with
    | set => obtain ⟨_, h⟩ := hk3.1 rfl; cases h
    | wr => obtain ⟨_, h⟩ := hk3.2.2 rfl; cases h
    | enter => exact absurd hinv.2 (by simp [Mma.Start.exit])
    | alloc =>
      have h := hk3.2.1 rfl
      simp only [Kind.tc.injEq, TcKind.resource.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      refine ⟨rfl, ?_⟩
      rw [hc]
      rfl
  · have hrd := Mma.ev_res (Mma.mfired hp hX he hσ).1 rfl
    have hkd := Mma.rd_kind hp hat hcd hf (by intro f hf; cases hf)
    rw [hc]
    obtain ⟨site, v⟩ := d
    cases site <;> simp only [Mma.isRD, reduceCtorEq] at hrd
    · have h := hkd.1 ⟨_, rfl⟩
      simp only [Kind.tc.injEq, TcKind.resource.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    · obtain ⟨a, h⟩ := hkd.2 ⟨_, rfl⟩
      simp only [Kind.tc.injEq, TcKind.resource.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      exact ⟨rfl, a, rfl⟩

set_option maxHeartbeats 8000000 in
/-- The MMA warp's role returns only at its exit site. -/
theorem Mma.ev_exit {d : Mma.D} {e : Event} (hev : Mma.Ev p L g d e) (hk : e.kind = .exit) :
    ∃ l, d.site = .exit l := by
  obtain ⟨site, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  unfold Mma.Ev at hev
  split at hev <;> first
    | exact ⟨_, rfl⟩
    | (subst ‹site = _›; exact ⟨_, rfl⟩)
    | (unfold Epilogue.Ev at hev; split at hev <;> simp_all [Epilogue.isStore, Mma.Site.toE])
    | simp_all

set_option maxHeartbeats 8000000 in
/-- **A lane of the MMA warp returns after its three operations.** -/
theorem tmem1_exit (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {k pc : Nat}
    (hg : g < L.threads) (h12 : g % L.block / 32 = 12) (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    Tmem.Pair.tmemOps ((X.tr g).take k) = 3 := by
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  obtain ⟨⟨σ1, n⟩, hσ, hJ, hi, hev⟩ := ev_at hp hX hT hF he (by intro f hf; cases hf)
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp
    (show (X.tr g)[k]? = _ from he)).1
  have hc := mma_count hp hX hg h12 k hk _ hσ
  rw [hc]
  rcases σ1 with s | ⟨i, d⟩
  · exfalso
    obtain ⟨site, x1, x2, x3⟩ := s
    simp only [TEv] at hev
    have hx := hi.2
    cases site <;> simp_all [Startup.Ev, exit]
    rename_i j
    fin_cases j <;> simp_all
  have hJ' : Mma.Ref p L g (.inr ⟨i, d⟩, n) := by
    rw [JR_eq] at hJ; unfold RefAll at hJ
    simp only [Prologue.warpIndex, h12] at hJ
    simpa using hJ
  cases i with
  | mma =>
    rcases d with s0 | ⟨⟨⟩, d⟩
    · exfalso
      simp only [TEv, Mma.PreEv] at hev
      simp_all
    · obtain ⟨l, hl⟩ := Mma.ev_exit (Mma.mfired hp hX he hσ).1 rfl
      show Mma.tsite d.site = 3
      rw [hl]; rfl
  | _ => exact (by simp [Mma.Ref] at hJ')

end
end PTX.Kernels.TmlFa4Fwd.Proof
