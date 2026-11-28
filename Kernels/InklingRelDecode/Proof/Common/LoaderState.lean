-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.LoaderScript
public import Kernels.InklingRelDecode.Proof.Common.Time
public import Kernels.InklingRelDecode.Proof.Common.ClsBuild
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import all Kernels.InklingRelDecode.Proof.Common.Time

@[expose] public section

/-! # The states of the loader's warp against its script

`loader_script`: a lane of warp 6 at any state has the facts of `ScriptFacts` for the loader's
script, at the number of collectives it has made: from the startup's count, the dispatch states'
(`loader_dispatch_count`) and the ledger of the loop's sites. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- **A lane of the loader's warp** has the script's facts at its state, and is past the script
at the exit pc. -/
private theorem loader_script (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hg : g < L.threads) (hw : g % L.block / 32 = 6)
    (hk : k ≤ (X.tr g).length) (nu : Frame.NoUbBefore X g k) {σ : (thread Q L g).D}
    (hs : Frame.stateAt (thread Q L) X g k = some (some σ)) :
    ScriptFacts (loaderCn (Iface.preloadCount Q L (g / L.block)) (iterCount Q L (g / L.block)))
      (loaderSlot (Iface.preloadCount Q L (g / L.block))) (σ.2 .coll) ((thread Q L g).pc σ)
      ((schedule Q L).time g σ) ∧ ((thread Q L g).pc σ = 2855 → ∀ c,
      (loaderCn (Iface.preloadCount Q L (g / L.block)) (iterCount Q L (g / L.block)) c).isSome
        = true → c < σ.2 .coll) := by
  have bound : iterCount Q L (g / L.block) < 2 ^ 31 := Lib.blocksOf_lt hp hg
  rcases worker_lane hp hX (by omega) hk hs with ⟨d, n, rfl⟩ | ⟨w, x, d, n, rfl⟩
  · have e : n .coll = startCount d.site := by
      rw [startup_coll_count hp hX hf hg nu hs]; cases d.site <;> rfl
    have t : (schedule Q L).time g ((.inl d, n) : (thread Q L g).D) = startClock d.site := by
      cases h : d.site <;> simp [schedule, siteClock, startupClock, startClock, h]
    refine ⟨?_, fun h => absurd h (start_pc_ne d.site)⟩
    rw [show ((.inl d, n) : (thread Q L g).D).2 .coll = n .coll from rfl, e, t]
    exact start_script (by simp [loaderCn]) (by simp [loaderSlot])
      (fun _ h => by have := loaderSlot_big (Iface.preloadCount Q L (g / L.block)) h; omega)
      (fun r h => by
        have := loaderCn_one _ _ _ h
        cases r <;> simp [Startup.Entry.pc] at this) d.site
  have inv := (reached_table hf hg nu hs).2
  rcases d with dd | ⟨i, s⟩
  · have cnt := loader_dispatch_count hp hX hf hg hw nu hs
    change DispatchRef _ _ _ dd n at inv
    rw [show (g % L.block / 32) = 6 from hw] at inv
    refine loader_dispatch_facts inv cnt fun h => ?_
    obtain ⟨s, r⟩ := dd
    have busy := inv.2.1 (.inl rfl) h
    subst h
    rcases busy with rfl | rfl | rfl | rfl | rfl <;> simp [schedule, siteClock, workerClock,
      dispatchClock, Lib.Slots.enter, Lib.Slots.publish]
  · rcases i with r | r
    · obtain ⟨-, ref, poll, -⟩ := inv
      exact ⟨loader_site_facts bound ref poll (loader_coll_count hp hX hf hg hw nu hs),
        fun h => absurd h (loader_pc_ne _)⟩
    · exact absurd hw (by have := inv.1; omega)

/-- **The classification of the loader's warp.** -/
theorem loader_cls (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hw : g % L.block / 32 = 6)
    (nu : ∀ x, SameWarp L g x → NoUbLane X x)
    (released : WarpRel Q L m X (SameWarp L g)) (dead : WarpDead Q L X (SameWarp L g)) :
    Sched.WarpCls (schedule Q L) m X (SameWarp L g) (CollAt Q L)
      (loaderCn (Iface.preloadCount Q L (g / L.block)) (iterCount Q L (g / L.block)))
      (loaderSlot (Iface.preloadCount Q L (g / L.block))) := by
  refine warpCls_script hp hX ?_ (fun hab _ => loaderSlot_mono _ hab) released dead
  intro x k σ hx hk hs
  have e : x / L.block = g / L.block := hx.1.2.2.symm
  have hxw : x % L.block / 32 = 6 := by have := hx.2; omega
  have a := loader_script hp hX hf hx.1.2.1 hxw hk ((nu x hx).before k) (σ := σ) hs
  have c : σ.2 .coll = Sched.collCount X x k := fcount hs .coll
  rw [e, c] at a
  exact a

end PTX.Kernels.InklingRelDecode.Proof
