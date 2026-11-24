-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.TmaWait
public import Kernels.TmlFa4Fwd.Proof.Lib.LdKvWait
public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Defs
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Tma
import Kernels.TmlFa4Fwd.Proof.Loader.Export.Kind
import Kernels.TmlFa4Fwd.Proof.Protocol.Ld.Blk
import Kernels.TmlFa4Fwd.Proof.Protocol.Ld.TmaBlk
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Bytes
import Kernels.TmlFa4Fwd.Proof.Top.Prog.Wait

@[expose] public section

/-! # E3: a released loader lane at one of its waits

`Prog.loaderWait` proves this progress class, given safety (`SafeGoal`, rule P3: progress reads
safety only through it). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0}

/-- A loader state at one of its waits, at an instruction in `Rest`. -/
def Prog.LoaderWait.At (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Prop :=
  (∃ b d n, σ = (.inr ⟨.loader b, d⟩, n) ∧ Loader.isWait d.site) ∧ RestAt p L g σ

/-- **A released loader lane at a wait for an empty K/V slot steps.** -/
theorem kv_wait_rel (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) {X : Execution}
    (hmax : Maximal L kernel Assumptions.all m X) {g : Nat} {b : Bool}
    {d : (frag p L g (.loader b)).D} {n : Cls → Nat} (hpd : Frame.Pending L X g)
    (hrel : Step.Released L X g)
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (.inr ⟨.loader b, d⟩, n)))
    (hw : kvSite d.site = true) : StepsAt p L m X (.thread g) := by
  have hX := hmax.1
  have hFw := launchFollow hp hX
  have hub := Sched.safe_noUb (hs.2 X hX)
  have hff := fault_free' hs hX
  obtain ⟨hw14, i, hi, hloc⟩ := ld_kv_wait hp hX hFw hub hpd.1 hσ hw
  refine wait_rel hp hs hmax hpd hrel hσ (fun h => ?_) (fun ins hc => ld_kv_wait_op hw hc)
    (fun pc l q ok sc he => ?_) fun pc l q sc f he hst _ hpar => ?_
  · simp only [IsEntry] at h
    rw [h] at hw
    cases hw
  · obtain ⟨rfl, -⟩ := hloc he
    have ho' : ObjOff (56 + 8 * (i % 3)) := by unfold ObjOff; omega
    obtain ⟨q', hq⟩ := objOff_init ho'
    exact ⟨_, _, rfl, ho', by have := obj_initFirst hp hX hFw g q'; rwa [hq] at this⟩
  · obtain ⟨rfl, hq⟩ := hloc he
    exact kvE_lag hp hX hFw hff hub hpd.1 hσ hw14 hi hst (hpar.trans hq)

/-- A wait at one of the loader's other sites is a TMA group's or the drain's Q wait. -/
theorem tma_of_wait {s : Loader.Site} (h : Loader.isWait s) (hk : kvSite s = false) :
    tmaWaitSite s = true := by
  revert h hk
  cases s <;> simp [Loader.isWait, kvSite, tmaWaitSite]

/-- **A released loader lane at a wait of a TMA group or of the drain's Q slot steps.** -/
theorem tma_wait_rel (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) {X : Execution}
    (hmax : Maximal L kernel Assumptions.all m X) {g : Nat} {b : Bool}
    {d : (frag p L g (.loader b)).D} {n : Cls → Nat} (hpd : Frame.Pending L X g)
    (hrel : Step.Released L X g)
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (.inr ⟨.loader b, d⟩, n)))
    (hw : tmaWaitSite d.site = true) : StepsAt p L m X (.thread g) := by
  have hX := hmax.1
  have hFw := launchFollow hp hX
  have hub := Sched.safe_noUb (hs.2 X hX)
  have hff := fault_free' hs hX
  obtain ⟨hw14, o, K, hW, hloc⟩ := ld_tma_wait hp hX hFw hub hpd.1 hσ hw
  refine wait_rel hp hs hmax hpd hrel hσ (fun h => ?_) (fun ins hc => ld_tma_wait_op hw hc)
    (fun pc l q ok sc he => ?_) fun pc l q sc f he hst hY hpar => ?_
  · simp only [IsEntry] at h
    rw [h] at hw
    cases hw
  · obtain rfl := hloc he
    have ho' : ObjOff (o + 16) := by
      have := hW.off
      unfold LdTmaOff at this
      unfold ObjOff; omega
    obtain ⟨q', hq⟩ := objOff_init ho'
    exact ⟨_, _, rfl, ho', by have := obj_initFirst hp hX hFw g q'; rwa [hq] at this⟩
  · obtain rfl := hloc he
    obtain ⟨Y, hcY, htake, hget⟩ := hY
    obtain ⟨-, hq⟩ := ld_tma_empty_par hp hcY (launchFollow hp hcY) (.inl hw14) hW.off hget
    rw [htake, hW.ok] at hq
    exact tma_lag hp hX hFw hff hub (tmaBytes hp hX hFw) hpd.1 hσ hw14 hW hst (hpar.trans hq)

/-- **A released loader lane at one of its waits (the empty-slot, TMA-group and drain polls)
steps**, for every consistent execution. -/
theorem Prog.loaderWait (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) :
    RelSteps p L m (Prog.LoaderWait.At p L) := by
  rintro X hmax g σ hpd hrel hσ ⟨⟨b, d, n, rfl, hw⟩, -⟩
  cases hk : kvSite d.site with
  | true => exact kv_wait_rel hp hs hmax hpd hrel hσ hk
  | false => exact tma_wait_rel hp hs hmax hpd hrel hσ (tma_of_wait hw hk)

end PTX.Kernels.TmlFa4Fwd.Proof.Top
