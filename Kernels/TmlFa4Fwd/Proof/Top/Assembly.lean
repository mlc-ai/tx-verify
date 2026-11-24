-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Async
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Blocked
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Correction
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Epilogue
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.LoaderOther
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.LoaderWait
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Mma
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.MmaSoft
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Next
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Softmax
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Start
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.WarpColl
public import Lemmas.Kernel.NextInOrder
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Lag
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Lag
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Arrive
import Std.Tactic.BVDecide.Normalize.Prop

import Lemmas.Kernel.FrameTrackedU

@[expose] public section

/-! # The progress assembly: every open obligation steps

`ProgressGoal` by ranked descent (`Descent.progress_of_steps` with `Sched.rank (timed p L)`),
given safety. Every open obligation of a maximal execution
steps (`obl_steps`):

* a pending thread whose machine has stopped performs its undefined behaviour
  (`Descent.dead_steps_inOrder`); a machine at `some none` is excluded by the role table's
  following (`goodR'`);
* a released lane of warp 12 at a poll is an `MbarAt` below its time (`Progress.mma_mbarAt`) from
  `MmaFullLag`, whose loader half is `kv_lag` (K/V polls) and `q_lag` (Q polls); a released
  lane of warp 13 at a ready poll from `ReadyLag` (`Progress.ready_mbarAt`, `readyArrive`);
* everything else is a progress class with its own file (`Top/Prog/<Class>.lean`), called here
  as `Prog.<class> hp hs`: the softmax polls of warp 12 (`mmaSoft`), the released
  lanes of each role at their other states (`loaderWait`, `loaderOther`, `softmax`, `correction`,
  `mma`, `epilogue`, `start`), the execution facts of a step outside `Rest` (`next`), the blocked
  lanes (`blocked`) and the asynchronous obligations (`async`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The Q polls of warp 12** (offsets 0 and 8): `Progress.MmaLagFrom true` at the polls that
are not the K/V ring's. -/
def MmaLagQ (p : Params) (L : Launch) (m : Mem0) : Prop :=
  ∀ X, Consistent L kernel Assumptions.all m X → ¬ HasUb X → ∀ g (d : Mma.D) (n : Cls → Nat) r,
    g < L.threads → Prologue.warpIndex L g = 12 →
    Frame.stateAt (thread p L) X g (X.tr g).length = some (some (Mma.minj p L g d n)) →
    Progress.isPoll d.site = true → Mma.RefCounts p L g (d, Mma.rc n) →
    (∃ w, Mma.RefQ p L g d.site.ord d.v (Mma.rc n) r w) →
    (Progress.pollO r d.site = 0 ∨ Progress.pollO r d.site = 8) →
    ∃ before, MBarrier.stateBefore (X.objects (Mma.bl L g (Progress.pollO r d.site)))
        (X.objects (Mma.bl L g (Progress.pollO r d.site))).length = some before ∧
      (before.phase % 2 = n (.mma (.acquire (Mma.bl L g (Progress.pollO r d.site)))) % 2 →
        Sched.Blk (Progress.timed p L) X g)

/-! ### The proved classes -/

/-- The assumptions' constraints hold of every extension that performs all its new commit
arrive-ons in order. -/
theorem wfStep_all : Assumption.WfStep (fun _ => true) L kernel m Assumptions.all :=
  fun X Y hX hle hord hr =>
    Assumptions.wfStep X Y hX hle (fun e r h1 h2 j pc sp hj _ hlt hno =>
      hord e r h1 h2 j pc sp hj rfl hlt hno) hr

/-- An object record of a safe execution has no fault. -/
theorem fault_free (hT : ¬ TmaUnsafe L m X) : ∀ l, ∀ r ∈ X.objects l, r.fault = none := by
  intro l r hr
  cases hf : r.fault with
  | none => rfl
  | some f => exact (hT (.inl ⟨l, r, hr, by simp [hf]⟩)).elim

/-- The barrier offset of a poll: a Q stage, a K/V slot, or a P half. -/
theorem pollO_cases (r : Nat) (s : Mma.Site) :
    Progress.pollO r s = 0 ∨ Progress.pollO r s = 8 ∨ 96 ≤ Progress.pollO r s ∨
      ∃ j : Fin 3, Progress.pollO r s = 32 + 8 * j.val := by
  cases s <;> simp only [Progress.pollO]
  case wt k =>
    fin_cases k <;> simp
    all_goals first
      | exact .inr (.inr ⟨⟨(2 * r + 1) % 3, Nat.mod_lt _ (by decide)⟩, rfl⟩)
      | exact .inr (.inr ⟨⟨(2 * r + 2) % 3, Nat.mod_lt _ (by decide)⟩, rfl⟩)
  case mw b ld => split <;> simp
  all_goals simp

/-- **The Q polls of warp 12** (`q_lag`). -/
theorem mmaLagQ (hp : Pre p L m)
    (hsafe : SafeGoal kernel Assumptions.all L m) : MmaLagQ p L m :=
  fun _ hX hub _ _ _ _ hg hw hσ hs _ ⟨_, hRQ⟩ ho =>
    q_lag hp hX (launchFollow hp hX) (fault_free (noTma_of_safe hsafe hX)) hub hg hw hσ hs
      hRQ ho

/-- **The loader half of the MMA warp's poll premise**, from the K/V polls (`kv_lag`) and the Q
polls (`q_lag`); the records are fault-free by safety. -/
theorem mmaLagLoader (hp : Pre p L m)
    (hsafe : SafeGoal kernel Assumptions.all L m) :
    Progress.MmaLagFrom true p L m := by
  have hQ := mmaLagQ hp hsafe
  intro X hX hub g d n r hg hw hσ hs hR ⟨w, hRQ⟩ hb
  rcases pollO_cases r d.site with h | h | h | ⟨j, hj⟩
  · exact hQ X hX hub g d n r hg hw hσ hs hR ⟨w, hRQ⟩ (.inl h)
  · exact hQ X hX hub g d n r hg hw hσ hs hR ⟨w, hRQ⟩ (.inr h)
  · simp [Progress.fromLoader] at hb; omega
  · exact kv_lag hp hX (launchFollow hp hX)
      (fault_free (noTma_of_safe hsafe hX)) hub hg hw hσ hs hRQ hj

/-! ### The assembly -/

variable (hp : Pre p L m)
include hp

/-- **A pending thread of a maximal execution steps.** -/
theorem thread_steps (hs : SafeGoal kernel Assumptions.all L m)
    (hmax : Maximal L kernel Assumptions.all m X) {g : Nat} (hpd : Frame.Pending L X g) :
    StepsAt p L m X (.thread g) := by
  have hX := hmax.1
  have hub := Sched.safe_noUb (hs.2 X hX)
  have hg := hpd.1
  have PloaderWait := Prog.loaderWait hp hs
  have PloaderOther := Prog.loaderOther hp hs
  have Psoftmax := Prog.softmax hp hs
  have Pcorrection := Prog.correction hp hs
  have Pepilogue := Prog.epilogue hp hs
  have Pmma := Prog.mma hp hs
  by_cases hrel : Step.Released L X g
  swap
  · exact Prog.blocked hp hs X hmax g hpd hrel
  have hF := goodR' hp hX hg
  cases hσ : Frame.stateAt (thread p L) X g (X.tr g).length with
  | none =>
    exact Descent.dead_steps_inOrderU wfStep_all hmax hub (fun _ hg => thread_sound hp hg)
      hpd hσ hrel
  | some o =>
    cases o with
    | none => exact absurd hσ (hF _).1
    | some σ =>
      by_cases hrest : RestAt p L g σ
      swap
      · exact nonRest_steps hp hs wfStep_all (Prog.next hp hs) X hmax g σ hpd hrel hσ
          hrest
      by_cases hcoll : CollAt p L g σ
      · exact Prog.warpColl hp hs X hmax g σ hpd hrel hσ hcoll
      have hJ := (hF _).2 σ hσ
      have hne : ∀ {i d n}, Frame.stateAt (thread p L) X g (X.tr g).length =
          some (some (.inr ⟨i, d⟩, n)) → X.tr g ≠ [] := by
        intro i d n h h0
        have : (X.tr g).length = 0 := by rw [h0]; rfl
        rw [this, Frame.stateAt_zero] at h
        simp [thread, glued, Code.glue, Code.counted, Code.enter, Startup.code, exit] at h
      obtain ⟨σ0, n⟩ := σ
      rcases σ0 with s | ⟨i, d⟩
      · exact absurd (Prog.start hp hs X hmax g _ hpd hσ ⟨⟨s, n, rfl⟩, hrest⟩) hcoll
      cases i with
      | loader b =>
        by_cases hw : Loader.isWait d.site
        · exact PloaderWait X hmax g _ hpd hrel hσ ⟨⟨b, d, n, rfl, hw⟩, hrest⟩
        · exact PloaderOther X hmax g _ hpd hrel hσ ⟨⟨b, d, n, rfl, hw⟩, hrest, hcoll⟩
      | softmax => exact Psoftmax X hmax g _ hpd hrel hσ ⟨⟨d, n, rfl⟩, hrest, hcoll⟩
      | correction => exact Pcorrection X hmax g _ hpd hrel hσ ⟨⟨d, n, rfl⟩, hrest, hcoll⟩
      | stub r => exact (JR.not_stub hJ).elim
      | epilogue =>
        by_cases hready : ∃ st, d.site = .ready st
        · obtain ⟨st, hst⟩ := hready
          have hw : Prologue.warpIndex L g = 13 := (JR.epilogue hJ).1
          have hRL := Progress.readyLag_of (readyArrive hp)
          obtain ⟨b, hb, hlt, h2⟩ := Progress.ready_mbarAt hp hRL hX hub hg hw hσ hst
          exact Sched.mbar_at_steps wfStep_all hub hmax hpd hrel (hne hσ) hb hlt h2
        · push Not at hready
          exact Pepilogue X hmax g _ hpd hrel hσ ⟨⟨d, n, rfl, hready⟩, hrest, hcoll⟩
      | mma =>
        rcases d with s0 | ⟨⟨⟩, d⟩
        · exact Pmma X hmax g _ hpd hrel hσ ⟨⟨.inl s0, n, rfl, fun _ h => by cases h⟩, hrest,
            hcoll⟩
        by_cases hpoll : Progress.isPoll d.site = true
        · have hw : Prologue.warpIndex L g = 12 := (JR.mma hJ).1
          have hM := Progress.mmaFullLag_of (mmaLagLoader hp hs)
            (Prog.mmaSoft hp hs)
          obtain ⟨b, hb, hlt, h2⟩ := Progress.mma_mbarAt hp hM hX hub hg hw hσ hpoll
          exact Sched.mbar_at_steps wfStep_all hub hmax hpd hrel (hne hσ) hb hlt h2
        · exact Pmma X hmax g _ hpd hrel hσ ⟨⟨.inr ⟨(), d⟩, n, rfl, fun d' h => by
            cases h; simpa using hpoll⟩, hrest, hcoll⟩

/-- **Every open obligation of a maximal execution steps.** -/
theorem obl_steps (hs : SafeGoal kernel Assumptions.all L m)
    (hmax : Maximal L kernel Assumptions.all m X) {o : Descent.Obligation}
    (ho : Descent.Obl L X o) : StepsAt p L m X o := by
  cases o with
  | thread g => exact thread_steps hp hs hmax ho
  | _ => exact Prog.async hp hs X _ hmax (fun g h => by cases h) ho

/-- **Progress by ranked descent**, given safety. -/
theorem progress (hs : SafeGoal kernel Assumptions.all L m) :
    ProgressGoal kernel Assumptions.all L m :=
  Descent.progress_of_steps (Descent.Obl L) (Sched.rank (Progress.timed p L))
    (fun _ _ hc => Descent.cover hc) fun _ _ hmax ho => obl_steps hp hs hmax ho

end
end PTX.Kernels.TmlFa4Fwd.Proof.Top
