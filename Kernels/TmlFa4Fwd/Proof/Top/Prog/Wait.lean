-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Final
public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Defs
public import Lemmas.Kernel.Progress.WaitSite
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Top.Prog.Issue
import Kernels.TmlFa4Fwd.Proof.Top.Table

import Lemmas.Kernel.Progress.WaitSiteU

@[expose] public section

/-! # A released lane at a wait steps

The kernel's instance of `Sched.wait_site_steps`: the barriers have final states (`final_exists`),
so a lane at a wait steps when the polled barrier has the poll's parity only with a blocker. The
blocker's proof gets a consistent execution with the failed poll appended, in which the facts about
poll events (`soft_mbar_use`, `corr_mbar_use`, …) give the poll's barrier and parity. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The failed poll appended to lane `g`'s trace, in a consistent execution. -/
def PollExt (L : Launch) (m : Mem0) (X : Execution) (g pc : Nat) (l : Loc) (q : Nat)
    (sc : MbarScope) : Prop :=
  ∃ Y, Consistent L kernel Assumptions.all m Y ∧
    (Y.tr g).take (X.tr g).length = X.tr g ∧
    Y.get (g, (X.tr g).length) = some ⟨pc, .wait l q false true sc⟩

theorem fault_free' (hs : SafeGoal kernel Assumptions.all L m)
    (hX : Consistent L kernel Assumptions.all m X) : ∀ l, ∀ r ∈ X.objects l, r.fault = none := by
  intro l r hr
  cases hf : r.fault with
  | none => rfl
  | some f => exact (noTma_of_safe hs hX (.inl ⟨l, r, hr, by simp [hf]⟩)).elim

/-- **A released lane at a wait steps.** -/
theorem wait_rel (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hmax : Maximal L kernel Assumptions.all m X) {i : Role} {d : (frag p L g i).D} {n : Cls → Nat}
    (hpd : Frame.Pending L X g) (hrel : Step.Released L X g)
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (.inr ⟨i, d⟩, n)))
    (hE : ¬ IsEntry i d)
    (hk : ∀ ins, kernel.code[(thread p L g).pc (.inr ⟨i, d⟩, n)]? = some ins →
      Sched.waitOp ins.op = true)
    (hloc : ∀ pc l q ok sc, TEv p L g (.inr ⟨i, d⟩, n) ⟨pc, .wait l q ok true sc⟩ →
      ∃ o c, l = obj L g o ∧ ObjOff o ∧ PairTmaRing.InitFirst X l c)
    (hblk : ∀ pc l q sc f, TEv p L g (.inr ⟨i, d⟩, n) ⟨pc, .wait l q false true sc⟩ →
      Final X l f → PollExt L m X g pc l q sc → f.phase % 2 = q % 2 →
      Sched.Blk (Progress.timed p L) X g) :
    StepsAt p L m X (.thread g) := by
  have hX := hmax.1
  have hJ := (goodR' hp hX hpd.1 _).2 _ hσ
  have hT := table_shape_of hp (launchFollow hp hX)
  refine Sched.wait_site_stepsU wfStepAll hmax (Sched.safe_noUb (hs.2 X hX))
    (fun g hg => thread_sound hp hg) hpd hσ (role_ne hσ) hrel hk
    (P := TEv p L g (.inr ⟨i, d⟩, n))
    (fun hat hi hc hf => hT.shape g hpd.1 _ _ _ _ _ hJ hat hi hc hf)
    (fun l q ok sc hP => ?_)
    (fun l q sc before hP hst hY hpar => hblk _ l q sc before hP hst hY hpar)
    ?_
  · obtain ⟨o, c, rfl, ho, hin⟩ := hloc _ l q ok sc hP
    exact final_exists hp hX (launchFollow hp hX) hpd.1 hσ hE ho hin
  · have := Progress.roleTime_ge (p := p) (L := L) (g := g) i d n
    show 2 ≤ Progress.roleTime p L g i d n
    simp only [Progress.scanBase] at this
    omega

end PTX.Kernels.TmlFa4Fwd.Proof.Top
