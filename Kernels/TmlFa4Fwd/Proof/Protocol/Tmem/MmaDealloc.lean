-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Core.Assembly.Execution
public import Core.Data.Types
public import Core.Data.Value
public import Core.Isa.Tc
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Pred
public import Kernels.TmlFa4Fwd.Proof.Mma.Machine
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
public import Lemmas.Kernel.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Mma.Export.SafePre
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.AccBar2
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Entry
import Kernels.TmlFa4Fwd.Proof.Mma.Export.TmemCount
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Ops
import Std.Tactic.BVDecide.Normalize.Prop
set_option linter.unnecessarySeqFocus false

@[expose] public section

/-! # The MMA warp deallocates after its second barrier-2 event

The role's code reaches the deallocation site only from `bar2` (`pred_dealloc`, on the role's
`succ`), and a state of the code that is not its initial state was reached from a state of the code
(`mma_pred`). The deallocation event is fired at the deallocation site (`Mma.ev_res`,
`Mma.rd_kind`; the allocation prefix fires only the allocation), so before it the lane made its
`bar2` sync and, before that, its `bar1` sync (`mma_bar1_before`): two barrier-2 events
(`dealloc_bar2`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem wtNext_ne (k : Fin 10) (l : Bool) : Mma.wtNext k ≠ .dealloc l := by
  fin_cases k <;> simp [Mma.wtNext]
theorem shNext_ne (k : Fin 14) (l : Bool) : Mma.shNext k ≠ .dealloc l := by
  fin_cases k <;> simp [Mma.shNext]
theorem qkDone_ne (b : Fin 4) (l : Bool) : Mma.qkDone b ≠ .dealloc l := by
  fin_cases b <;> simp [Mma.qkDone]
theorem pvDone_ne (b : Fin 4) (l : Bool) : Mma.pvDone b ≠ .dealloc l := by
  fin_cases b <;> simp [Mma.pvDone]

theorem afterTiles_ne {d d' : Mma.D} {x : BitVec 64}
    {l : Bool} (h : Mma.afterTiles p L g d x = some d') : d'.site ≠ .dealloc l := by
  simp only [Mma.afterTiles] at h
  repeat' split at h
  all_goals (cases h <;> (try split) <;> (try simp))

set_option maxHeartbeats 16000000 in
/-- **The deallocation site is entered only from `bar2`.** -/
theorem pred_dealloc {d d' : Mma.D} {e : Event} {l : Bool}
    (hn : Mma.succ p L g d e = some (some d')) (hs : d'.site = .dealloc l) : d.site = .bar2 l := by
  obtain ⟨s, v⟩ := d
  cases s
  case tiles late =>
    exfalso
    simp only [Mma.succ] at hn
    split at hn
    · split at hn
      · split at hn
        · cases hn; simp at hs
        · obtain ⟨d0, h0, h1⟩ := Option.map_eq_some_iff.mp hn
          cases h1
          exact afterTiles_ne h0 hs
      · cases hn
    · cases hn
  all_goals simp only [Mma.succ, Mma.word32, Mma.afterTiles, Mma.passStart,
    Option.map] at hn <;> (repeat' split at hn) <;>
    first | (cases hn; done) | (cases hn; simp_all) | skip
  all_goals first
    | (simp only [Mma.afterTotal, Mma.ceNext, Mma.scanExit, Mma.loopHead, Mma.enterLoop,
        Mma.loopEnd, Mma.passStart] at hs; (repeat' split at hs) <;> simp_all; done)
    | (rename_i c; fin_cases c <;> simp [Mma.ceNext, Mma.enterLoop, Mma.loopEnd, Mma.passStart,
        Mma.scanExit, Mma.loopHead] at hs <;> (repeat' split at hs) <;> simp_all; done)
    | exact absurd hs (wtNext_ne _ _)
    | exact absurd hs (shNext_ne _ _)
    | exact absurd hs (qkDone_ne _ _)
    | exact absurd hs (pvDone_ne _ _)

set_option maxHeartbeats 8000000 in
/-- **A deallocation follows two barrier-2 events of its lane.** -/
theorem dealloc_bar2 (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {j pc : Nat}
    {grp : CtaGroup} {dst : Option Loc} {da nn : Nat}
    (he : X.get (g, j) = some ⟨pc, .tc (.resource grp dst (.dealloc da nn))⟩) :
    2 ≤ ((X.tr g).take j).countP (Execution.isBarId 2) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨σ, hσ, hJ, hi, hev⟩ := ev_at hp hX (table_shape_of hp hFw)
    (table_followed hp hX hFw) he (by intro f hf; cases hf)
  obtain ⟨d2, n2, rfl⟩ := tev_res hJ hi hev rfl
  obtain ⟨t, ins, o, hat, hinv, hcd, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (by intro f h; cases h)
  rcases d2 with s0 | ⟨⟨⟩, d⟩
  · exfalso
    have hk3 := Mma.pre_kind hp hat hcd hf
    cases s0 with
    | set => obtain ⟨_, h⟩ := hk3.1 rfl; cases h
    | wr => obtain ⟨_, h⟩ := hk3.2.2 rfl; cases h
    | enter => exact absurd hinv.2 (by simp [Mma.Start.exit])
    | alloc => have h := hk3.2.1 rfl; cases h
  -- the state is at the deallocation site
  have hrd := Mma.ev_res (Mma.mfired hp hX he hσ).1 rfl
  have hkd := Mma.rd_kind hp hat hcd hf (by intro f hf; cases hf)
  obtain ⟨site, v⟩ := d
  obtain ⟨l, rfl⟩ : ∃ l, site = .dealloc l := by
    cases site <;> simp only [Mma.isRD, reduceCtorEq, Bool.false_eq_true] at hrd
    · have h := hkd.1 ⟨_, rfl⟩; cases h
    · exact ⟨_, rfl⟩
  -- the state before is at `bar2`
  obtain ⟨j1, rfl⟩ : ∃ j1, j = j1 + 1 := by
    rcases j with _ | j1
    · rw [Frame.stateAt_zero] at hσ
      simp [thread, glued, Code.counted, Code.glue, Code.enter, exit, Startup.code] at hσ
    · exact ⟨j1, rfl⟩
  have hj1 : j1 < (X.tr g).length := by
    have := (List.getElem?_eq_some_iff.mp (show (X.tr g)[j1 + 1]? = _ from he)).1
    omega
  have hk1 : (X.tr g)[j1]? = some ((X.tr g)[j1]'hj1) := List.getElem?_eq_getElem hj1
  obtain ⟨d0, n0, hσ0, hs0⟩ := mma_pred hk1 hσ (by intro h; cases h)
  have hb2 := pred_dealloc hs0 rfl
  have he0 : X.get (g, j1) = some ((X.tr g)[j1]'hj1) := hk1
  have hev0 := (Mma.mfired hp hX he0 hσ0).1
  obtain ⟨s0, v0⟩ := d0
  simp only at hb2
  subst hb2
  simp only [Mma.Ev] at hev0
  obtain ⟨j', hj', pc', hget⟩ := mma_bar1_before hp hX he0 hσ0 (by simp)
  have h1 := bar2_pos hj' hget
  rw [List.take_add_one, hk1, Option.toList_some, List.countP_append]
  have : Execution.isBarId 2 ((X.tr g)[j1]'hj1) = true := by
    generalize (X.tr g)[j1]'hj1 = x at hev0 ⊢
    obtain ⟨pc0, kd0⟩ := x
    simp only at hev0
    subst hev0
    rfl
  simp only [List.countP_singleton, this, ite_true]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
