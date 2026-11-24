-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

theorem loaderSliceEventBounds {l : Launch} {g lo hi : Nat} {s : TState} {es : List Event}
    {visits : List Visit} (hWalk : Walk kernel Assumptions.all l g s es visits)
    {e : Event} (he : e ∈ loaderSliceEvents lo hi visits) : lo ≤ e.pc ∧ e.pc < hi := by
  induction hWalk with
  | stop => simp [loaderSliceEvents] at he
  | @tau t u es vs ht hw ih =>
    by_cases hPc : lo ≤ t.pc ∧ t.pc < hi
    · apply ih
      simpa [loaderSliceEvents, visit, hPc.1, hPc.2] using he
    · simp [loaderSliceEvents, visit, hPc] at he
  | @ev t u here es vs hStep hw ih =>
    by_cases hPc : lo ≤ t.pc ∧ t.pc < hi
    · simp [loaderSliceEvents, visit, hPc.1, hPc.2] at he
      rcases he with rfl | hTail
      · simpa only [estep_source_pc hStep] using hPc
      · exact ih (List.mem_filterMap.mpr hTail)
    · simp [loaderSliceEvents, visit, hPc] at he
  | @last t er hStep =>
    by_cases hPc : lo ≤ t.pc ∧ t.pc < hi
    · have same : e = er := by simpa [loaderSliceEvents, visit, hPc.1, hPc.2] using he
      rw [same, estep_source_pc hStep]
      exact hPc
    · simp [loaderSliceEvents, visit, hPc] at he

/-- The ordinal of a recorded event identifies its bounded initial visit to a loader slice. -/
theorem loaderRankedEventBounds {l : Launch} {X : Execution} {g index start cut : Nat}
    {s : TState} {ending : Option TState} {F : List (Nat × Value)}
    (hRange : 174 ≤ start ∧ start ≤ cut ∧ cut ≤ 1901)
    (hAudit : ∀ bound, ((kernel.code.drop start).take (cut - start)).all
      (fun i => loaderPipelineCutOp start cut bound [] i.op) = true)
    (hRanked : (((kernel.code.drop start).take (cut - start)).zipIdx start).all
      (fun (i, pc) => LoaderRankedInstr cut pc i) = true)
    (hs : At s start F)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    {j : Nat} {e : Event} (he : X.get (g, j) = some e) (hBefore : index ≤ j)
    (hRank : ((X.tr g).take j).countP Execution.isShfl <
      ((X.tr g).take index).countP Execution.isShfl + loaderShuffleTail cut start) :
    start ≤ e.pc ∧ e.pc < cut := by
  have hGet : ((X.tr g).drop index)[j - index]? = some e := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hBefore]
    exact he
  have hBudget : (((X.tr g).drop index).take (j - index)).countP Execution.isShfl <
      loaderShuffleTail cut s.pc := by
    conv at hRank => left; rw [← Nat.add_sub_of_le hBefore, List.take_add, List.countP_append]
    rw [hs.1]
    omega
  obtain ⟨visits, hWalk⟩ := Mma.walkFromRun hr
  have hi : e ∈ loaderSliceEvents start cut visits :=
    loaderEventInRankedSlice hRange le_rfl hAudit hRanked hWalk
      (by rw [hs.1]; exact ⟨le_rfl, hRange.2.1⟩) (ringShapeOfAt hs) hGet hBudget
  exact loaderSliceEventBounds hWalk hi

end
end PTX.Kernels.TmlFa4Fwd.Loader
