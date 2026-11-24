-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Defs
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Kind
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Bytes
import Kernels.TmlFa4Fwd.Proof.Protocol.Soft.BiasBlk
import Kernels.TmlFa4Fwd.Proof.Protocol.Soft.Blk
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.PollLag
import Kernels.TmlFa4Fwd.Proof.Top.Prog.Wait

@[expose] public section

/-! # E4: a released softmax lane

`Prog.softmax` proves this progress class, given safety (`SafeGoal`, rule P3: progress reads
safety only through it). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0}

/-- A softmax state at an instruction in `Rest`. -/
def Prog.Softmax.At (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Prop :=
  (∃ d n, σ = (.inr ⟨.softmax, d⟩, n)) ∧ RestAt p L g σ ∧
    ¬ CollAt p L g σ

/-- A released softmax lane at a poll steps. -/
theorem soft_poll_rel (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) {X : Execution}
    (hmax : Maximal L kernel Assumptions.all m X) {g : Nat} {d : (frag p L g .softmax).D}
    {n : Cls → Nat} (hpd : Frame.Pending L X g) (hrel : Step.Released L X g)
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (.inr ⟨.softmax, d⟩, n)))
    (hw : d.site.isPoll = true) : StepsAt p L m X (.thread g) := by
  have hX := hmax.1
  have hFw := launchFollow hp hX
  have hub := Sched.safe_noUb (hs.2 X hX)
  have hff := fault_free' hs hX
  have hw8 := (soft_end hp hX hFw hub hpd.1 hσ).1
  refine wait_rel hp hs hmax hpd hrel hσ (fun h => ?_) (fun ins hi => soft_wait hw hi)
    (fun pc l q ok sc he => ?_) fun pc l q sc f he hst hY hpar => ?_
  · simp only [IsEntry] at h
    rw [h] at hw
    cases hw
  · obtain ⟨rfl, ho⟩ := soft_wait_loc hw8 he
    have ho' : ObjOff (8 * (Prologue.warpIndex L g / 4) + Softmax.pollOff d.scheduler.site) := by
      unfold ObjOff; omega
    obtain ⟨q', hq⟩ := objOff_init ho'
    exact ⟨_, _, rfl, ho', by have := obj_initFirst hp hX hFw g q'; rwa [hq] at this⟩
  · obtain ⟨rfl, ho⟩ := soft_wait_loc hw8 he
    obtain ⟨Y, hcY, htake, hget⟩ := hY
    rcases soft_mbar_use hp hcY (launchFollow hp hcY) hw8 hget rfl (fun c h => by cases h) with
      ⟨a, ha, hl, hk⟩ | ⟨a, ok, ha, hl, hk⟩
    · cases hk
    · simp only [Kind.wait.injEq] at hk
      obtain ⟨-, hq, -⟩ := hk
      have ha' : a = Softmax.pollOff d.scheduler.site := by
        have := obj_inj hl
        omega
      subst ha'
      rw [htake] at hq
      rcases ho with ho | ho
      · rw [ho] at hst hq
        exact credit_lag hp hX hFw hff hub hpd.1 hσ ho hst (by
          rw [hpar, hq]; simp [softΔ])
      · rcases soft_site_of_off ho with ⟨r, hsite⟩ | ⟨b, hsite⟩
        · rw [hsite] at hst hq
          exact s_lag hp hX hFw hff hub hpd.1 hσ hsite hst (by
            rw [hpar, hq]; simp [softΔ, soft_ws_off])
        · rw [hsite] at hst hq
          exact bias_lag hp hX hFw hff hub (tmaBytes hp hX hFw) hpd.1 hσ hsite hst (by
            rw [hpar, hq]; simp [softΔ, soft_wb_off])

/-- **A released softmax lane steps**, from its open part: every site that is no poll has an
instruction a released lane performs (`soft_kind`). -/
theorem Prog.softmax (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) :
    RelSteps p L m (Prog.Softmax.At p L) := by
  rintro X hmax g σ hpd hrel hσ ⟨⟨d, n, rfl⟩, hr, hc⟩
  cases hw : d.site.isPoll with
  | true =>
    exact soft_poll_rel hp hs hmax hpd hrel hσ hw
  | false =>
    exact site_rel hp hs hmax hpd hrel hσ hr hc (soft_kind hw) fun he => by
      simpa [IsEntry] using he

end PTX.Kernels.TmlFa4Fwd.Proof.Top
