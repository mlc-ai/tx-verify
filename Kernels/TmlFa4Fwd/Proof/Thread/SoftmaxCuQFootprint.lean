-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxScheduleEntry
import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsAllocationExclusion
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
import Lemmas.Flow.ContinuingEvent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue

noncomputable section

private theorem schedulerSuffixNotFirstRead {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {o : Option TState} {k : Nat} {e : Event}
    (hs : 3111 ≤ s.pc) (hr : Run kernel Assumptions.all l g s events o)
    (he : events[k]? = some e) : 3111 ≤ e.pc := by
  obtain ⟨u, _, hTrace, hStep⟩ := hr.before_event he
  have hFloor := Thread.resourceSuffixFloor .softmaxScheduler hTrace hs
  rw [estep_source_pc hStep]
  exact hFloor

/-- Every actual softmax lane-word read has the launch CuQ footprint for that lane.
The address and lane bound follow from the executing prefix for arbitrary returned bytes. -/
theorem firstCuQReadFootprint {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} (hWarp : warpIndex l g < 8) {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g,j) = some ⟨3110,.rd a bs⟩) :
    laneOf l g ≤ p.batch ∧ a = laneCuQAcc p l g := by
  let warp : Fin 8 := ⟨warpIndex l g,hWarp⟩
  obtain ⟨i, t, o, hIndex, ht, hRun⟩ : ∃ i t o, i ≤ j ∧
      At t 3104 (schedulerEntry p l g warp) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop i) o := by
    rcases Nat.eq_zero_or_pos (warpIndex l g) with hZero | hNonzero
    · obtain ⟨i,t,o,hi,_,ht,hr⟩ :=
        zeroSchedulerEntryAfterBarrier hp hX he (by change 3103 < 3110; decide) hZero
      have hEq : warp = 0 := Fin.ext hZero
      exact ⟨i,t,o,hi,hEq.symm ▸ ht,hr⟩
    · obtain ⟨t,o,_,_,_,ht,hr,hi,_⟩ :=
        nonzeroSchedulerEntryAfterBarrier hp hX he (by change 3103 < 3110; decide) hNonzero hWarp
      exact ⟨7,t,o,hi,ht,hr⟩
  have hLen : j < (X.tr g).length := len_of_get he
  have hNonempty : (X.tr g).drop i ≠ [] :=
    fun h => Nat.not_le_of_lt hLen ((List.drop_eq_nil_iff.mp h).trans hIndex)
  by_cases hLane : laneOf l g ≤ p.batch
  · obtain ⟨u, hPc, hn, _⟩ := schedulerReadNext hp ht hLane
    have hRead := hn.uniqueScalarReadAt hPc hRun hIndex he (fun v events hNext hTail e hm => by
      obtain ⟨k,hGet⟩ := List.mem_iff_getElem?.mp hm
      exact schedulerSuffixNotFirstRead hNext hTail hGet)
    exact ⟨hLane,hRead.2⟩
  · obtain ⟨u, hu, htau⟩ := schedulerSkipLocal hp ht (Nat.lt_of_not_ge hLane)
    have hIndexed : ((X.tr g).drop i)[j-i]? = some ⟨3110,.rd a bs⟩ := by
      rw [List.getElem?_drop, Nat.add_sub_of_le hIndex]
      exact he
    have hBad := schedulerSuffixNotFirstRead (le_of_eq hu.1.symm)
      (hRun.after_local_nonempty htau hNonempty) hIndexed
    exact ((by decide : ¬ 3111 ≤ 3110) hBad).elim

end
end PTX.Kernels.TmlFa4Fwd.Softmax
