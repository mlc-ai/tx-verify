-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueRoleTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaTracking
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1IndexRendezvous
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmaTracking
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2ReadTracking
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry

@[expose] public section

/-! # Tracking the composed machine from actual role events -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof

/-- An idle role never dismisses its thread. -/
theorem idle_next_tracked {P : Params} {L : Launch} {g : Nat}
    (s : Thread.Site) (e : Event) :
    Machine.next P L g (.idle s) e ≠ some none := by
  cases s <;> cases hk : e.kind <;> simp [Machine.next, Thread.next, hk]
  all_goals split <;> simp
  all_goals rename_i h
  all_goals split at h <;> cases h

/-- The warps of warpgroup 1 follow their actual events independently of the dequantization
and softmax value guards. -/
theorem tracked_wg1_warp {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    {g : Nat} (hw : 4 ≤ warpOf L g ∧ warpOf L g ≤ 7) (k : Nat) :
    Frame.stateAt (Machine.code P L) X g k ≠ some none := by
  have hwg : wgOf L g = 1 := by
    unfold wgOf warpOf at *
    omega
  have within (j : Nat) (hj : j ≤ (X.tr g).length) :
      Frame.stateAt (Machine.code P L) X g j ≠ some none := by
    induction j with
    | zero => rw [Frame.stateAt_zero]; simp
    | succ j ih =>
      obtain ⟨e, he⟩ : ∃ e, X.get (g, j) = some e :=
        ⟨_, List.getElem?_eq_getElem (by omega : j < (X.tr g).length)⟩
      rw [Frame.stateAt_succ he]
      cases hst : Frame.stateAt (Machine.code P L) X g j with
      | none => intro h; cases h
      | some d =>
        cases d with
        | none => exact (ih (by omega) hst).elim
        | some d =>
          change Machine.next P L g d e ≠ some none
          have hg := Frame.lt_of_get hX he
          have hRole := RingRoleGeometry.of_trace hX hg (hs g hg) hst
          cases d with
          | prologue s => exact PrologueRoleTrace.prologue_next_tracked hpre hX hs he hst
          | head => exact PrologueRoleTrace.dispatch_next_tracked hpre hX hs he hst
          | mma d => exact MmaTracking.next_tracked hpre hX (hs g hg) he hst
          | index d => exact Wg1Index.next_tracked hpre hX hs he hst
          | idle s => exact idle_next_tracked s e
          | wg0 d => change wgOf L g = 0 at hRole; omega
          | wg2 d => change wgOf L g = 2 at hRole; omega
          | tma d => exact TmaTracking.next_tracked hpre hX (hs g hg) he hst
          | done => intro h; cases h
  by_cases hk : k ≤ (X.tr g).length
  · exact within k hk
  · rw [Frame.stateAt_of_le (by omega)]
    exact within _ le_rfl

/-- The MMA, idle and index warps follow their actual events. -/
theorem tracked_nonconsumer_warp {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    {g : Nat} (hw : warpOf L g = 4 ∨ warpOf L g = 6 ∨ warpOf L g = 7) (k : Nat) :
    Frame.stateAt (Machine.code P L) X g k ≠ some none :=
  tracked_wg1_warp hpre hX hs (by omega) k

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
