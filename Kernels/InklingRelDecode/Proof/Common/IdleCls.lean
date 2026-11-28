-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.ClsBuild
public import Kernels.InklingRelDecode.Proof.Common.WorkerBalance
public import Kernels.InklingRelDecode.Proof.Common.Time
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import all Kernels.InklingRelDecode.Proof.Common.Time

@[expose] public section

/-! # The classification of the idle warps

Warps 4 and 5 make one collective, the startup's shuffle: their script is `[17]`. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- The idle warps' script: the startup's shuffle. -/
def idleCn (n : Nat) : Option Nat := if n = 0 then some 17 else none

def idleSlot (n : Nat) : Nat := 24 + 100 * n

private theorem idle_script (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hg : g < L.threads) (h6 : g % L.block / 32 ≠ 6)
    (h7 : g % L.block / 32 ≠ 7) (hw : 128 ≤ g % L.block) (hk : k ≤ (X.tr g).length)
    (nu : Frame.NoUbBefore X g k) {σ : (thread Q L g).D}
    (hs : Frame.stateAt (thread Q L) X g k = some (some σ)) :
    ScriptFacts idleCn idleSlot (σ.2 .coll) ((thread Q L g).pc σ) ((schedule Q L).time g σ) ∧
      ((thread Q L g).pc σ = 2855 → ∀ n, (idleCn n).isSome = true → n < σ.2 .coll) := by
  have inv := (reached_table hf hg nu hs).2
  rcases worker_lane hp hX hw hk hs with ⟨d, n, rfl⟩ | ⟨w, x, d, n, rfl⟩
  · have c := startup_coll_count hp hX hf hg nu hs
    have e : n .coll = startCount d.site := by rw [c]; cases d.site <;> rfl
    have t : (schedule Q L).time g ((.inl d, n) : (thread Q L g).D) = startClock d.site := by
      cases h : d.site <;> simp [schedule, siteClock, startupClock, startClock, h]
    refine ⟨?_, fun h => absurd h ?_⟩
    · rw [show ((.inl d, n) : (thread Q L g).D).2 .coll = n .coll from rfl, e, t]
      exact start_script (by simp [idleCn]) (by simp [idleSlot])
        (fun _ h => by simp only [idleSlot]; omega) (fun r h => by simp [idleCn] at h) d.site
    · exact start_pc_ne d.site
  rcases d with dd | ⟨i, s⟩
  · have cnt := idle_coll_count hp hX hf hg h6 h7 nu hs
    have ok : ∀ s : Dispatch.Site, isWarpAt s.pc = false := fun s => by
      cases s <;> decide +kernel
    change ScriptFacts idleCn idleSlot (n .coll) dd.site.pc _ ∧
      (dd.site.pc = 2855 → ∀ j, (idleCn j).isSome = true → j < n .coll)
    refine ⟨⟨?_, fun h => absurd h (by rw [ok]; simp), fun _ j hn hle => ?_⟩, fun _ j hn => ?_⟩
    · rw [ok, cnt]
      simp [idleCn]
    · rw [cnt] at hle
      simp [idleCn, show j ≠ 0 by omega] at hn
    · rw [cnt]
      by_cases j0 : j = 0
      · omega
      · simp [idleCn, j0] at hn
  · rcases i with r | r <;> exact absurd inv.1 (by omega)

/-- **The classification of an idle warp** (4 or 5). -/
theorem idle_cls (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (h6 : g % L.block / 32 ≠ 6) (h7 : g % L.block / 32 ≠ 7)
    (hw : 128 ≤ g % L.block) (nu : ∀ x, SameWarp L g x → NoUbLane X x)
    (released : WarpRel Q L m X (SameWarp L g)) (dead : WarpDead Q L X (SameWarp L g)) :
    Sched.WarpCls (schedule Q L) m X (SameWarp L g) (CollAt Q L) idleCn idleSlot := by
  refine warpCls_script hp hX ?_ (fun {a b} hab hb => ?_) released dead
  · intro x k σ hx hk hs
    have hxw : x % L.block / 32 = g % L.block / 32 := hx.2.symm
    have c : σ.2 .coll = Sched.collCount X x k := fcount hs .coll
    have := idle_script hp hX hf hx.1.2.1 (by omega) (by omega) (by omega) hk
      ((nu x hx).before k) (σ := σ) hs
    rw [c] at this
    exact this
  · have : b ≠ 0 := by omega
    simp [idleCn, this] at hb

end PTX.Kernels.InklingRelDecode.Proof
