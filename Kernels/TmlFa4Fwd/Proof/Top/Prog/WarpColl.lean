-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Defs
public import Lemmas.Kernel.NextReads
public import Lemmas.Kernel.Progress.WarpCollPair
public import Lemmas.Kernel.Progress.WarpCollRel
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Correction.Export.CollPair
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.CollPair
import Kernels.TmlFa4Fwd.Proof.Loader.Export.CollPair
import Kernels.TmlFa4Fwd.Proof.Mma.Export.CollPair
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Obj
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.CollPair

import Lemmas.Kernel.Progress.WarpCollRelU
import Lemmas.Kernel.Progress.WarpCollPairU

@[expose] public section

/-! # A released lane at a warp collective steps

The progress class this file owns, shared by the roles' released-lane classes: a released pending
lane whose next instruction is a warp collective (`CollAt`: an instruction outside the released
template, `RestAt`, of kind `warp`: a shuffle, an election, a vote or a warp barrier) steps, by
the library's
`Sched.warpColl_steps_rel`. The classes `start`, `epilogue`, `correction`, `mma`,
`loaderOther` and `softmax` exclude these states (their `At` predicates ask `¬ CollAt`), and the
dispatcher of `Top/Assembly.lean` sends them here.

Proved here: the code has no mode vote (`kernel_noVoteMode`); no event is a CLC request
(`no_clc`), so every thread is launched and none is canceled. The kernel's warp-collective facts
(`Sched.WarpCollRel`) follow from facts of two lanes of a warp (`Sched.WarpPair`: at their `n`-th
collective they are at one position with one static part, the release of the lanes at one
collective, the collective count at a lane's exit, and the time table's lag of a lane not at the
collective). They are proved for every warp (`soft_pair`, `corr_pair`, `mma_pair`, `out_pair`,
`ld_pair`), so nothing is open here. The lanes past the batch skip the
read before the first collective of a pass, so a warp's last events before it differ (a register
request or a barrier arrival, or a read), and the library's `WarpCollFacts` does not hold. The
assumptions hold of appended collective lanes and of a lane's undefined behaviour
(`Assumption.WfStep.quiet`), so those premises of the template are proved here. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0}

/-- The code has no mode vote. -/
theorem kernel_noVoteMode : kernel.code.all (fun ins => !Sched.voteModeOp ins.op) = true := by
  decide +kernel

/-- The static part of a collective state, by its warp. -/
private noncomputable def warpShape (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) :
    Sched.CollShape :=
  if Prologue.warpIndex L g < 8 then softShape p L g σ
  else if Prologue.warpIndex L g < 12 then corrShape p L g σ
  else if Prologue.warpIndex L g = 12 then mmaShape p L g σ
  else if Prologue.warpIndex L g = 13 then outShape p L g σ else ldShape p L g σ

private theorem warp_cases (hp : Pre p L m) (g : Nat) : Prologue.warpIndex L g < 8 ∨
    (8 ≤ Prologue.warpIndex L g ∧ Prologue.warpIndex L g ≤ 11) ∨ Prologue.warpIndex L g = 12 ∨
    Prologue.warpIndex L g = 13 ∨ ∃ b, Prologue.warpIndex L g = Loader.wOf b := by
  have h16 := Prologue.warpIndex_lt hp g
  by_cases h14 : Prologue.warpIndex L g = 14
  · exact .inr (.inr (.inr (.inr ⟨false, h14⟩)))
  · by_cases h15 : Prologue.warpIndex L g = 15
    · exact .inr (.inr (.inr (.inr ⟨true, h15⟩)))
    · omega

private theorem soft_shape {g : Nat} (h : Prologue.warpIndex L g < 8) :
    warpShape p L g = softShape p L g := by
  funext σ; simp only [warpShape, h, ite_true]

private theorem corr_shape {g : Nat}
    (h : 8 ≤ Prologue.warpIndex L g ∧ Prologue.warpIndex L g ≤ 11) :
    warpShape p L g = corrShape p L g := by
  funext σ
  simp only [warpShape, show ¬ Prologue.warpIndex L g < 8 by omega,
    show Prologue.warpIndex L g < 12 by omega, ite_false, ite_true]

private theorem mma_shape {g : Nat} (h : Prologue.warpIndex L g = 12) :
    warpShape p L g = mmaShape p L g := by
  funext σ; simp [warpShape, h]

private theorem out_shape {g : Nat} (h : Prologue.warpIndex L g = 13) :
    warpShape p L g = outShape p L g := by
  funext σ; simp [warpShape, h]

private theorem ld_shape {g : Nat} {b : Bool} (h : Prologue.warpIndex L g = Loader.wOf b) :
    warpShape p L g = ldShape p L g := by
  have hb : 14 ≤ Loader.wOf b := by cases b <;> decide
  funext σ
  simp only [warpShape, show ¬ Prologue.warpIndex L g < 8 by omega,
    show ¬ Prologue.warpIndex L g < 12 by omega, show ¬ Prologue.warpIndex L g = 12 by omega,
    show ¬ Prologue.warpIndex L g = 13 by omega, ite_false]

/-- **The kernel's warp-collective facts** (`soft_pair`, `corr_pair`, `mma_pair`, `out_pair`,
`ld_pair`). -/
theorem warpColl_facts (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) {X : Execution}
    (hmax : Maximal L kernel Assumptions.all m X) :
    Sched.WarpCollRel m (Progress.timed p L) X (warpKey L) (CollAt p L) := by
  have hX := hmax.1
  have hub := Sched.safe_noUb (hs.2 X hX)
  have hFw := launchFollow hp hX
  refine Sched.warpCollRel_of_pairsU (S := warpShape p L)
    (fun {g h} hg hh hk => ?_) (fun g hg => thread_sound hp hg) hX
    (fun {g k d} hg hP => ?_) (fun {g h} hsw => ?_)
  · simp only [warpKey, Prod.mk.injEq] at hk
    exact ⟨⟨hg, hh, hk.1⟩, hk.2⟩
  · have key : ∀ S : ∀ g, (thread p L g).D → Sched.CollShape, warpShape p L g = S g →
        Sched.ShapeAt (Progress.timed p L) S g d →
        Sched.ShapeAt (Progress.timed p L) (warpShape p L) g d := by
      intro S hS h
      unfold Sched.ShapeAt at h ⊢
      rw [hS]
      exact h
    rcases warp_cases hp g with hw | hw | hw | hw | ⟨b, hw⟩
    · exact key _ (soft_shape hw) (soft_shapeAt hp hX hFw hub hg hw rfl hP)
    · exact key _ (corr_shape hw) (corr_shapeAt hp hX hFw hub hg hw rfl hP)
    · exact key _ (mma_shape hw) (mma_shapeAt hp hX hFw hub hg hw hP)
    · exact key _ (out_shape hw) (out_shapeAt hp hX hFw hg hw hP)
    · exact key _ (ld_shape hw) (ld_shapeAt hp hX hFw hub hg hw hP)
  · have hwh : Prologue.warpIndex L h = Prologue.warpIndex L g := hsw.2.symm
    have key : ∀ S : ∀ g, (thread p L g).D → Sched.CollShape, warpShape p L g = S g →
        warpShape p L h = S h →
        Sched.WarpPair m (Progress.timed p L) X (CollAt p L) S g h →
        Sched.WarpPair m (Progress.timed p L) X (CollAt p L) (warpShape p L) g h := by
      rintro S hS hS' ⟨h1, h2, h3, h4, h5⟩
      refine ⟨fun hP hP' hn => ?_, h2, h3, h4, h5⟩
      rw [hS, hS']
      exact h1 hP hP' hn
    rcases warp_cases hp g with hw | hw | hw | hw | ⟨b, hw⟩
    · exact key _ (soft_shape hw) (soft_shape (by rw [hwh]; exact hw))
        (soft_pair hp hX hub hsw hw)
    · exact key _ (corr_shape hw) (corr_shape (by rw [hwh]; exact hw))
        (corr_pair hp hX hub hsw hw)
    · exact key _ (mma_shape hw) (mma_shape (hwh.trans hw)) (mma_pair hp hX hub hsw hw)
    · exact key _ (out_shape hw) (out_shape (hwh.trans hw)) (out_pair hp hX hub hsw hw)
    · exact key _ (ld_shape hw) (ld_shape (hwh.trans hw)) (ld_pair hp hX hub hsw hw)

/-- **A released lane at a warp collective steps**, for every consistent execution. -/
theorem Prog.warpColl (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) :
    RelSteps p L m (CollAt p L) := by
  intro X hmax g σ hpd hrel hσ hc
  have hX := hmax.1
  have hnc := no_clc hp hX (launchFollow hp hX)
  have hlaunch : ∀ h, Step.Launched L X h := fun h ⟨i, s, ts, pc, hi⟩ =>
    (hnc i.1 i.2 pc s ts hi).elim
  have hcl : ∀ h, ¬ ClcCanceled L X h := by
    rintro h ⟨-, r, hr⟩
    obtain ⟨i, s, ts, -, ⟨pc, hi⟩, -⟩ := hX.clc.canceled_has_issue hr
    exact hnc i.1 i.2 pc s ts hi
  have hwf : Assumption.WfStep (fun _ => true) L kernel m Assumptions.all :=
    fun X Y hX hle hord hr =>
      Assumptions.wfStep X Y hX hle (fun e r h1 h2 j pc sp hj _ hlt hno =>
        hord e r h1 h2 j pc sp hj rfl hlt hno) hr
  have happ : ∀ (ds : List Nat) (ev : Nat → Event), (∀ x, (ev x).kind.readsMem = false) →
      ∀ a ∈ Assumptions.all, a.wf L m (X.appendLanes ds ev) := fun ds ev hev =>
    hwf.quiet hX le_appendLanes rfl (noNewRead_appendLanes hev)
  have hubx : ∀ {h : Nat} {t t1 : TState} {f : Fault}, h < L.threads → Step.Released L X h →
      Run kernel Assumptions.all L h {} (X.tr h) (some t) →
      Relation.ReflTransGen (Tau kernel Assumptions.all L h) t t1 →
      out kernel Assumptions.all L h t1 = .ev (.ub f) →
      ∃ Y, Consistent L kernel Assumptions.all m Y ∧ X.le Y ∧ X.size L < Y.size L :=
    fun hh hrl hrun hl hout => Step.plain_counted_extension hX hh (.inr (hlaunch _)) hrl hrun hl
      (o := none) ⟨_, hout, rfl, rfl⟩ trivial rfl nofun nofun nofun rfl
      (hX.tmemPairResult.snoc_not_wr nofun)
      (hwf.quiet hX le_snoc rfl (Execution.noNewRead_snoc rfl))
  exact Sched.warpColl_steps_relU kernel_noVoteMode (fun hsw => by
      simp only [warpKey]; rw [hsw.1.2.2, hsw.2])
    (fun g hg => thread_sound hp hg) hs (fun h k hh => (goodR' hp hX hh k).1)
    (warpColl_facts hp hs hmax) (by rw [hp.block]) hlaunch hcl happ hubx hmax hpd hσ hc hrel

end PTX.Kernels.TmlFa4Fwd.Proof.Top
