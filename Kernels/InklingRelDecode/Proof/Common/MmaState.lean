-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.MmaScript
public import Kernels.InklingRelDecode.Proof.Common.Time
public import Kernels.InklingRelDecode.Proof.Common.ClsBuild
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
import Kernels.InklingRelDecode.Proof.Mma.Export.Skip
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import all Kernels.InklingRelDecode.Proof.Common.Time

@[expose] public section

/-! # The states of the MMA warp against its script

`mma_cls`: the classification of warp 7. A lane's states are the startup's, the dispatch warp's
and the MMA loop's; the counts come from the ledger, the references and the facts that no
broadcast of the loop is skipped. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- **A lane of the MMA warp** has the script's facts at its state, and is past the script at
the exit pc. -/
private theorem mma_script (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (hg : g < L.threads)
    (hw : g % L.block / 32 = 7) (hk : k ≤ (X.tr g).length) (nu : Frame.NoUbBefore X g k)
    {σ : (thread Q L g).D} (hs : Frame.stateAt (thread Q L) X g k = some (some σ)) :
    ScriptFacts (mmaCn (Mma.runCount (iterCount Q L (g / L.block))))
      (mmaSlot (Mma.runCount (iterCount Q L (g / L.block)))) (σ.2 .coll) ((thread Q L g).pc σ)
      ((schedule Q L).time g σ) ∧ ((thread Q L g).pc σ = 2855 → ∀ c,
      (mmaCn (Mma.runCount (iterCount Q L (g / L.block))) c).isSome = true → c < σ.2 .coll) := by
  have sk : σ.2 .skip = 0 := by
    rw [fcount hs .skip]; exact skip_zero hp hX hf words hw k
  rcases worker_lane hp hX (by omega) hk hs with ⟨d, n, rfl⟩ | ⟨w, x, d, n, rfl⟩
  · have e : n .coll = startCount d.site := by
      rw [startup_coll_count hp hX hf hg nu hs]; cases d.site <;> rfl
    have t : (schedule Q L).time g ((.inl d, n) : (thread Q L g).D) = startClock d.site := by
      cases h : d.site <;> simp [schedule, siteClock, startupClock, startClock, h]
    refine ⟨?_, fun h => absurd h (start_pc_ne d.site)⟩
    rw [show ((.inl d, n) : (thread Q L g).D).2 .coll = n .coll from rfl, e, t]
    exact start_script (by simp [mmaCn]) (by simp [mmaSlot])
      (fun _ h => by have := mmaSlot_big (Mma.runCount (iterCount Q L (g / L.block))) h; omega)
      (fun r h => by
        have := mmaCn_warp h
        cases r <;> simp [Startup.Entry.pc] at this <;>
          exact absurd this (by decide +kernel)) d.site
  have inv := (reached_table hf hg nu hs).2
  rcases d with dd | ⟨i, s⟩
  · have cnt := mma_dispatch_count hp hX hf hg hw nu hs
    change DispatchRef _ _ _ dd n at inv
    rw [show (g % L.block / 32) = 7 from hw] at inv
    refine mma_dispatch_facts inv sk cnt fun h => ?_
    obtain ⟨s, r⟩ := dd
    have busy := inv.2.1 (.inr rfl) h
    subst h
    rcases busy with rfl | rfl | rfl | rfl | rfl <;> simp [schedule, siteClock, workerClock,
      dispatchClock, Lib.Slots.enter, Lib.Slots.publish]
  · rcases i with r | r
    · exact absurd hw (by have := inv.1; omega)
    · obtain ⟨-, ref, p1, p2, fin, -⟩ := inv
      have led := mma_coll_count hp hX hf hg hw nu hs
      have skd := mma_skipped hp hX hf hg hw nu hs
      have sk' : n .skip = 0 := sk
      exact ⟨mma_site_facts ref (reached_table hf hg nu hs).1.1 ⟨p1, p2, fin, led, sk', by omega⟩,
        fun h => absurd h (mma_pc_ne _)⟩

/-- **The classification of the MMA warp.** -/
theorem mma_cls (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (hw : g % L.block / 32 = 7)
    (nu : ∀ x, SameWarp L g x → NoUbLane X x)
    (released : WarpRel Q L m X (SameWarp L g)) (dead : WarpDead Q L X (SameWarp L g)) :
    Sched.WarpCls (schedule Q L) m X (SameWarp L g) (CollAt Q L)
      (mmaCn (Mma.runCount (iterCount Q L (g / L.block))))
      (mmaSlot (Mma.runCount (iterCount Q L (g / L.block)))) := by
  refine warpCls_script hp hX ?_ (fun hab hb => mmaSlot_mono _ ?_ hab hb) released dead
  · intro x k σ hx hk hs
    have e : x / L.block = g / L.block := hx.1.2.2.symm
    have hxw : x % L.block / 32 = 7 := by have := hx.2; omega
    have a := mma_script hp hX hf words hx.1.2.1 hxw hk ((nu x hx).before k) (σ := σ) hs
    have c : σ.2 .coll = Sched.collCount X x k := fcount hs .coll
    rw [e, c] at a
    exact a
  · unfold Mma.runCount; split_ifs <;> omega

end PTX.Kernels.InklingRelDecode.Proof
