-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVMaskReplay
import Kernels.TmlFa4Fwd.Flow.Code.Part010

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

private theorem primingMaskCompareWithFrame {p : Params} {l : Launch}
    {g batch queryHead queryTile tile warp lane : Nat}
    (hLen : p.kLength batch < 2 ^ 31) (hRow : kvCopyRow tile (32 * warp + lane) 0 < 2 ^ 31)
    (pair : Fin 16) (hPositive : 0 < pair.val) {s : TState}
    (hs : At s (primingKPredicatePc pair)
      (primingMaskFrame p l batch queryHead queryTile tile warp lane pair.val)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (primingKPredicatePc pair + 1)
        (primingMaskPred (p.kLength batch) tile (32 * warp + lane) pair ::
          primingMaskFrame p l batch queryHead queryTile tile warp lane pair.val) := by
  let F := primingMaskFrame p l batch queryHead queryTile tile warp lane pair.val
  obtain ⟨t, ht, htAt⟩ := primingMaskCompare (g := g) hLen hRow pair hPositive s
    (hs.mono ⟨holds_lookup hs.2.2.2.2 (by fin_cases pair <;> rfl), trivial⟩)
  obtain ⟨htA, keep⟩ := loaderLinear (regs := F.map Prod.fst)
    (by fin_cases pair <;> decide) (by fin_cases pair <;> decide) hs.1
    (by fin_cases pair <;> (set_option maxRecDepth 100000 in kernel_rfl)) (by rfl) ht
  have hF := holdsSchedulerFrame hs.2.2.2.2 keep (fun _ hm => List.mem_map_of_mem hm)
  exact ⟨t, run_rtg htA, htAt.mono ⟨htAt.2.2.2.2.1, hF⟩⟩

private theorem splitIndexedEvents (xs : List Event) {i j k : Nat}
    (hStart : i ≤ j) (hEnd : j ≤ k) :
    (xs.drop i).take (k-i) = (xs.drop i).take (j-i) ++ (xs.drop j).take (k-j) := by
  rw [show k-i = (j-i)+(k-j) by omega,List.take_add,List.drop_drop,Nat.add_sub_of_le hStart]

private theorem composeIndexedReach {l : Launch} {X : Execution} {g i j k : Nat}
    {s t u : TState} (hi : i ≤ j) (hk : j ≤ k)
    (hs : TraceReach kernel Assumptions.all l g s (((X.tr g).drop i).take (j-i)) t)
    (hu : TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take (k-j)) u) :
    TraceReach kernel Assumptions.all l g s (((X.tr g).drop i).take (k-i)) u := by
  rw [splitIndexedEvents _ hi hk]
  exact hs.append hu

set_option maxRecDepth 100000 in
/-- One decoded pair adds a tail-byte mask and advances exactly two actual shuffles. -/
private theorem primingMaskInPrefixWithReach {p : Params} {l : Launch} {X : Execution}
    {g batch queryHead queryTile tile warp lane index : Nat}
    (hLen : p.kLength batch < 2 ^ 31) (hRow : kvCopyRow tile (32 * warp + lane) 0 < 2 ^ 31)
    (pair : Fin 16) {s : TState} {ending : Option TState}
    (hs : At s (primingMaskCountPc pair.val)
      (primingMaskFrame p l batch queryHead queryTile tile warp lane pair.val))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    {j : Nat} {target : Event} (he : X.get (g, j) = some target) (hBefore : index ≤ j)
    (hLater : 672 < target.pc) (hSafe : ∀ f, target.kind ≠ .ub f) :
    ∃ u atIndex stop, atIndex ≤ j ∧ At u (primingMaskCountPc (pair.val + 1))
      (primingMaskFrame p l batch queryHead queryTile tile warp lane (pair.val + 1)) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop atIndex) stop ∧
      ((X.tr g).take atIndex).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl + 2 ∧
      index ≤ atIndex ∧ TraceReach kernel Assumptions.all l g s
        (((X.tr g).drop index).take (atIndex-index)) u := by
  let F := primingMaskFrame p l batch queryHead queryTile tile warp lane pair.val
  let pred := primingMaskPred (p.kLength batch) tile (32 * warp + lane) pair
  let select := kCopyPc pair - 1
  have hSelect : select ≤ target.pc := by
    have hBound : select ≤ 672 := by fin_cases pair <;> decide
    omega
  have hSelectCode := primingMaskSelectNonvector pair
  have hStep : ∃ t pos stop, pos ≤ j ∧ At t select (pred :: F) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) stop ∧
      ((X.tr g).take pos).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl + 2 ∧
      index ≤ pos ∧ TraceReach kernel Assumptions.all l g s
        (((X.tr g).drop index).take (pos-index)) t := by
    by_cases hZero : pair = 0
    · subst pair
      have hFrame : At s 543 (pred :: F) :=
        hs.mono ⟨holds_lookup hs.2.2.2.2 rfl, hs.2.2.2.2⟩
      obtain ⟨t, front, stop, hSplit, hAt, hTail, hRank, hPos,hReach⟩ :=
        prefixCountedShuffleCutWithReach (start := 543) (stop := 549) (by decide) (by
          intro branch
          set_option maxRecDepth 100000 in kernel_rfl) (by
          set_option maxRecDepth 100000 in kernel_rfl)
          hSelectCode hFrame hr he hBefore (.inl hSelect) hSafe
      have hCount : loaderShuffleTail 549 543 = 2 := by
        set_option maxRecDepth 100000 in kernel_rfl
      refine ⟨t, _, stop, hPos, hAt, hTail, hRank.trans (congrArg (_ + ·) hCount),
        Nat.le_add_right ..,?_⟩
      rw [hSplit,Nat.add_sub_cancel_left,List.take_append_length]
      exact hReach
    let start := primingMaskCountPc pair.val
    let compare := primingKPredicatePc pair
    have hPositive : 0 < pair.val := by by_contra! h; exact hZero (Fin.ext (by omega))
    have hCompareLe : compare ≤ target.pc := by
      have hBound : compare ≤ 672 := by fin_cases pair <;> decide
      omega
    obtain ⟨t, front, stop, hSplit, ht, hTail, htRank, htPos,hTReach⟩ :=
      prefixQuietCutWithReach (start := start) (stop := compare) (by fin_cases pair <;> decide) (by
        intro branch
        fin_cases pair <;> (set_option maxRecDepth 100000 in kernel_rfl)) (by
        fin_cases pair <;> (set_option maxRecDepth 100000 in kernel_rfl))
        (primingMaskCompareNonvector pair hPositive) hs hr he hBefore hCompareLe hSafe
    obtain ⟨u, hu, huAt⟩ := primingMaskCompareWithFrame (g := g) hLen hRow pair hPositive ht
    have huRun := hTail.after_local_nonempty hu (traceAfterObservedEvent he htPos)
    obtain ⟨v, more, stop', hMore, hv, hvRun, hvRank, hvPos,hVReach⟩ :=
      prefixCountedShuffleCutWithReach (start := compare + 1) (stop := select)
        (by fin_cases pair <;> decide) (by
          intro branch
          fin_cases pair <;> (set_option maxRecDepth 100000 in kernel_rfl)) (by
          fin_cases pair <;> (set_option maxRecDepth 100000 in kernel_rfl))
          hSelectCode huAt huRun he htPos (.inl hSelect) hSafe
    have hCount : loaderShuffleTail select (compare + 1) = 2 := by
      fin_cases pair <;> first | exact (hZero rfl).elim |
        (set_option maxRecDepth 100000 in kernel_rfl)
    refine ⟨v, _, stop', hvPos, hv, hvRun, by rw [hvRank, htRank, hCount],by omega,?_⟩
    have hStart : TraceReach kernel Assumptions.all l g s
        (((X.tr g).drop index).take ((index+front.length)-index)) u := by
      rw [hSplit,Nat.add_sub_cancel_left,List.take_append_length]
      simpa only [List.append_nil] using hTReach.append (TraceReach.of_local hu)
    have hNext : TraceReach kernel Assumptions.all l g u
        (((X.tr g).drop (index+front.length)).take
          ((index+front.length+more.length)-(index+front.length))) v := by
      rw [hMore,Nat.add_sub_cancel_left,List.take_append_length]
      exact hVReach
    exact composeIndexedReach (by omega) (by omega) hStart hNext
  obtain ⟨t, pos, stop, hPos, ht, hRun, hRank,hStart,hReached⟩ := hStep
  obtain ⟨u, hu, hU⟩ := primingMaskSelect (g := g) pair t (ht.mono ⟨ht.2.2.2.2.1, trivial⟩)
  obtain ⟨huA, keep⟩ := loaderLinear (regs := F.map Prod.fst)
    (by fin_cases pair <;> decide) (by fin_cases pair <;> decide) ht.1
    (by fin_cases pair <;> (set_option maxRecDepth 100000 in kernel_rfl)) (by rfl) hu
  have hF := holdsSchedulerFrame ht.2.2.2.2.2 keep (fun _ hm => List.mem_map_of_mem hm)
  refine ⟨u, pos, stop, hPos, ?_,
    hRun.after_local_nonempty (run_rtg huA) (traceAfterObservedEvent he hPos), hRank,hStart,
    by simpa only [List.append_nil] using hReached.append (TraceReach.of_local (run_rtg huA))⟩
  have hSite : primingMaskCountPc (pair.val + 1) = kCopyPc pair := by fin_cases pair <;> decide
  rw [hSite]
  apply hU.mono
  obtain ⟨hPre, hBase⟩ := (holds_append ..).mp hF
  have hExtend : primingMaskPrefix (p.kLength batch) tile (32 * warp + lane) (pair.val + 1) =
      primingMaskPrefix (p.kLength batch) tile (32 * warp + lane) pair.val ++
        [primingMaskFact (p.kLength batch) tile (32 * warp + lane) pair] := by
    fin_cases pair <;> rfl
  unfold primingMaskFrame
  rw [hExtend, List.append_assoc]
  exact (holds_append ..).mpr ⟨hPre, hU.2.2.2.2.1, hBase⟩

variable {p : Params} {l : Launch} {X : Execution}
    {g batch queryHead queryTile tile warp lane index : Nat} (hLen : p.kLength batch < 2 ^ 31)
    (hRow : kvCopyRow tile (32 * warp + lane) 0 < 2 ^ 31) {s : TState} {ending : Option TState}
    (hs : At s 538 (primingKMaskInputs p l batch tile warp lane ++
      primingVAdmissionCarry p l batch queryHead queryTile))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending) {j : Nat} {target : Event}
    (he : X.get (g, j) = some target) (hBefore : index ≤ j) (hLater : 672 < target.pc)
include hLen hRow hs hr he hBefore hLater

/-- The actual K masks and V arguments at their first commit, with a live
continuation witnessed by a later event instead of a completed kernel. -/
theorem primingVMasksAtKCommitInPrefixWithReach (hSafe : ∀ f, target.kind ≠ .ub f) :
    ∃ u pos stop, pos ≤ j ∧
      At u 673 (primingMaskFrame p l batch queryHead queryTile tile warp lane 16) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) stop ∧
      ((X.tr g).take pos).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl + 32 ∧
      index ≤ pos ∧ TraceReach kernel Assumptions.all l g s
        (((X.tr g).drop index).take (pos-index)) u := by
  let C := primingKMaskInputs p l batch tile warp lane ++
    primingVAdmissionCarry p l batch queryHead queryTile
  obtain ⟨t, ht, hT⟩ := primingKFirstMaskResidual l g hLen hRow s (hs.mono
    ⟨holds_lookup hs.2.2.2.2 rfl, holds_lookup hs.2.2.2.2 rfl, holds_lookup hs.2.2.2.2 rfl,
      holds_lookup hs.2.2.2.2 rfl, holds_lookup hs.2.2.2.2 rfl, trivial⟩)
  obtain ⟨htA, keep⟩ := loaderLinear (regs := C.map Prod.fst) (by decide) (by decide) hs.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) ht
  have hCF := holdsSchedulerFrame hs.2.2.2.2 keep (fun _ hm => List.mem_map_of_mem hm)
  have init : At t 543 (primingMaskFrame p l batch queryHead queryTile tile warp lane 0) :=
    hT.mono ⟨hT.2.2.2.2.2.1, hT.2.2.2.2.1, hCF⟩
  have stage (n : Nat) (hn : n ≤ 16) :
      ∃ u pos stop, pos ≤ j ∧ At u (primingMaskCountPc n)
        (primingMaskFrame p l batch queryHead queryTile tile warp lane n) ∧
        Run kernel Assumptions.all l g u ((X.tr g).drop pos) stop ∧
        ((X.tr g).take pos).countP Execution.isShfl =
          ((X.tr g).take index).countP Execution.isShfl + 2 * n ∧
        index ≤ pos ∧ TraceReach kernel Assumptions.all l g s
          (((X.tr g).drop index).take (pos-index)) u := by
    induction n with
    | zero =>
      exact ⟨t, index, ending, hBefore, init,
        hr.after_local_nonempty (run_rtg htA) (traceAfterObservedEvent he hBefore), rfl,le_rfl,
        by simpa only [Nat.sub_self,List.take_zero] using TraceReach.of_local (run_rtg htA)⟩
    | succ n ih =>
      obtain ⟨a, pos, stop, hPos, ha, hRun, hOrdinal,hOrder,hReach⟩ := ih (by omega)
      let pair : Fin 16 := ⟨n, by omega⟩
      obtain ⟨u, nextPos, stop', hNext, hu, hTail, hRank,hOrder',hReach'⟩ :=
        primingMaskInPrefixWithReach hLen hRow pair ha hRun he hPos hLater hSafe
      exact ⟨u, nextPos, stop', hNext, hu, hTail, by rw [hRank, hOrdinal]; omega,
        hOrder.trans hOrder',composeIndexedReach hOrder hOrder' hReach hReach'⟩
  obtain ⟨last, pos, stop, hPos, hl, hRun, hRank,hOrder,hReach⟩ := stage 16 (by decide)
  obtain ⟨u, front, stop', hSplit, hu, hTail, hOrdinal, hBefore',hReach'⟩ :=
    prefixQuietCutWithReach (by decide) (by
      intro branch
      set_option maxRecDepth 100000 in kernel_rfl) (by
        set_option maxRecDepth 100000 in kernel_rfl)
      ⟨_, Flow.code_673, rfl⟩ hl hRun he hPos hLater hSafe
  refine ⟨u, pos + front.length, stop', hBefore', hu, hTail, hOrdinal.trans hRank,
    by omega,composeIndexedReach hOrder (Nat.le_add_right ..) hReach ?_⟩
  rw [hSplit,Nat.add_sub_cancel_left,List.take_append_length]
  exact hReach'


/-- The actual K masks and V arguments at the first K commit. -/
theorem primingVMasksAtKCommitInPrefix (hSafe : ∀ f, target.kind ≠ .ub f) :
    ∃ u pos stop, pos ≤ j ∧
      At u 673 (primingMaskFrame p l batch queryHead queryTile tile warp lane 16) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) stop ∧
      ((X.tr g).take pos).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl + 32 := by
  obtain ⟨u,pos,stop,hPos,hu,hTail,hCount,_,_⟩ :=
    primingVMasksAtKCommitInPrefixWithReach hLen hRow hs hr he hBefore hLater hSafe
  exact ⟨u,pos,stop,hPos,hu,hTail,hCount⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
