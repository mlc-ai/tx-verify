-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Defs
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Kind
import Kernels.TmlFa4Fwd.Proof.Correction.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.Correction.Export.PollLag
import Kernels.TmlFa4Fwd.Proof.Protocol.Corr.Blk
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Top.Prog.Wait

@[expose] public section

/-! # A released correction lane

`Prog.correction` proves this progress class, given safety (`SafeGoal`, rule P3: progress reads
safety only through it). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0}

/-- A correction state at an instruction in `Rest`. -/
def Prog.Correction.At (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Prop :=
  (∃ d n, σ = (.inr ⟨.correction, d⟩, n)) ∧ RestAt p L g σ ∧
    ¬ CollAt p L g σ

/-- A released correction lane at a poll steps. -/
theorem corr_poll_rel (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) {X : Execution}
    (hmax : Maximal L kernel Assumptions.all m X) {g : Nat} {d : (frag p L g .correction).D}
    {n : Cls → Nat} (hpd : Frame.Pending L X g) (hrel : Step.Released L X g)
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length =
      some (some (.inr ⟨.correction, d⟩, n)))
    (hw : d.site.isPoll = true) : StepsAt p L m X (.thread g) := by
  have hX := hmax.1
  have hFw := launchFollow hp hX
  have hub := Sched.safe_noUb (hs.2 X hX)
  have hff := fault_free' hs hX
  obtain ⟨hw8, -⟩ := corr_end hp hX hFw hub hpd.1 hσ
  have hE : d.site ≠ .setmax := by
    intro h
    rw [h] at hw
    cases hw
  refine wait_rel hp hs hmax hpd hrel hσ (fun h => hE h) (fun ins hi => corr_wait hw hi)
    (fun pc l q ok sc he => ?_) fun pc l q sc f he hst hY hpar => ?_
  · obtain ⟨rfl, ho⟩ := corr_wait_loc he
    have ho' : ObjOff (Correction.pollOff d.scheduler.site) := by
      unfold ObjOff
      rcases ho with ⟨st, k, -, ho⟩ | ⟨-, ho⟩ <;> omega
    obtain ⟨q', hq⟩ := objOff_init ho'
    exact ⟨_, _, rfl, ho', by have := obj_initFirst hp hX hFw g q'; rwa [hq] at this⟩
  · obtain ⟨rfl, ho⟩ := corr_wait_loc he
    obtain ⟨Y, hcY, htake, hget⟩ := hY
    rcases corr_mbar_use hp hcY (launchFollow hp hcY) hw8.1 hw8.2 hget rfl
        (fun c h => by cases h) with ⟨a, ha, hl, hk⟩ | ⟨a, ok, ha, hl, hk⟩
    · cases hk
    simp only [Kind.wait.injEq] at hk
    obtain ⟨-, hq, -⟩ := hk
    obtain rfl : Correction.pollOff d.scheduler.site = a := obj_inj hl
    rw [htake] at hq
    rcases ho with ⟨st, k, hsite, ho⟩ | ⟨⟨b, hsite⟩, ho⟩
    · obtain ⟨R, -, -, hok, h0⟩ := corr_fw_at hp hX hFw hub hpd.1 hσ hsite
      rw [hok] at hq
      fin_cases k
      · have ho' : Correction.pollOff d.scheduler.site = 144 + 8 * st.val := ho
        rw [ho'] at hst hq
        refine o_lag hp hX hFw hub hpd.1 hσ hsite hst ?_
        rw [hpar, hq]
        fin_cases st <;> simp [corrΔ]
      · have ho' : Correction.pollOff d.scheduler.site = 224 + 8 * st.val := by rw [ho]; simp; omega
        rw [ho'] at hst hq
        have hph := free_first hp hX hFw hpd.1 hσ hE st hw8 h0 hst
        exfalso
        rw [hph, hq] at hpar
        revert hpar
        fin_cases st <;> simp [corrΔ]
    · obtain ⟨hok, h0, -⟩ := corr_wend_at hp hX hFw hub hpd.1 hσ hsite
      rw [ho] at hst hq
      rw [hok] at hq
      cases b with
      | true =>
        exact free_last hp hX hFw hff hub hpd.1 hσ hsite hst (by rw [hpar, hq]; simp [corrΔ])
      | false =>
        have hph := free_first hp hX hFw hpd.1 hσ hE 1 hw8 (h0 rfl) hst
        exfalso
        rw [hph, hq] at hpar
        revert hpar
        simp [corrΔ]

/-- **A released correction lane steps**: every site that is no poll has an instruction a released
lane performs (`corr_kind`), and a blocked poll has an earlier blocker. -/
theorem Prog.correction (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) :
    RelSteps p L m (Prog.Correction.At p L) := by
  rintro X hmax g σ hpd hrel hσ ⟨⟨d, n, rfl⟩, hr, hc⟩
  cases hw : d.site.isPoll with
  | true => exact corr_poll_rel hp hs hmax hpd hrel hσ hw
  | false =>
    exact site_rel hp hs hmax hpd hrel hσ hr hc (corr_kind hw) fun he => by
      simpa [IsEntry] using he

end PTX.Kernels.TmlFa4Fwd.Proof.Top
