-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPrefixPointer
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVSecondSlot
import Kernels.TmlFa4Fwd.Flow.Code.Part012
import Kernels.TmlFa4Fwd.Flow.Code.Part013
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

private theorem vColumnBytes (l : Launch) (g tid : Nat) :
    Seg kernel [] l g 1 808 [(1082, b32 (kvCopyColumn tid false))]
      809 [primingVColumn tid] := by
  have hCol : kvCopyColumn tid false < 2 ^ 32 := by
    have := Nat.mod_lt tid (by decide : 0 < 8)
    simp [kvCopyColumn]
    omega
  intro t ht
  unfold primingVColumn
  seg_fp ht using norm_bits [Nat.mod_eq_of_lt hCol]

variable {p : Params} {l : Launch}

/-- The first V pair computes the same BF16 byte column used by every later pair. -/
theorem primingVColumnFrameInPrefix {X : Execution} {g batch tile warp lane index rank base : Nat}
    {residual : Nat → Nat} {s : TState} {ending : Option TState}
    (hs : At s 805 (primingVReloadWords 0 base ++ vPacketFrame p l batch tile warp lane residual))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hRank : ((X.tr g).take index).countP Execution.isShfl = rank) {j : Nat} {target : Event}
    (he : X.get (g, j) = some target) (hBefore : index ≤ j)
    (hLater : 808 ≤ target.pc ∨ (Execution.isShfl target = true ∧
      rank + 2 ≤ ((X.tr g).take j).countP Execution.isShfl)) (hSafe : ∀ f, target.kind ≠ .ub f) :
    ∃ t pos stop, pos ≤ j ∧
      At t 809 (primingVReloadWords 0 base ++ vPacketCarry p l batch tile warp lane residual) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) stop ∧
      ((X.tr g).take pos).countP Execution.isShfl = rank + 2 := by
  let F := primingVReloadWords 0 base ++ vPacketFrame p l batch tile warp lane residual
  have hCount : loaderShuffleTail 808 805 = 2 := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨u, front, stop, _, hu, hTail, hOrd, hPos⟩ :=
    prefixCountedShuffleCutAtEntry (F := F) (start := 805) (stop := 808)
      (by decide) (by intro branch; set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hs hr he hBefore
      (by simpa only [hRank, hCount] using hLater) hSafe
  have hInput : At u 808 [(1082, b32 (kvCopyColumn (32 * warp + lane) false))] :=
    hu.mono ⟨holds_lookup hu.2.2.2.2 rfl, trivial⟩
  obtain ⟨t, ht, hT⟩ := vColumnBytes l g (32 * warp + lane) u hInput
  obtain ⟨htA, hKeep⟩ := loaderLinear (regs := F.map Prod.fst)
    (by decide) (by decide) hu.1 (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) ht
  have hFrame := holdsSchedulerFrame hu.2.2.2.2 hKeep (fun _ hm => List.mem_map_of_mem hm)
  refine ⟨t, index + front.length, stop, hPos, hT.mono ?_,
    hTail.after_local_nonempty (run_rtg htA) (traceAfterObservedEvent he hPos), ?_⟩
  · exact ⟨hFrame.1, hFrame.2.1, hT.2.2.2.2.1, hFrame.2.2⟩
  · rw [hOrd, hRank, hCount]

/-- The real address window between V reloads preserves the saved second pointer. -/
theorem primingVSecondPointerInPrefix {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index rank read base : Nat}
    (hw : 14 ≤ warpIndex l g) (hBase : base < 2 ^ 64) {s : TState} {ending : Option TState}
    {F : List (Nat × Value)} (hs : At s 809 F)
    (hStable : ∀ branch, ((kernel.code.drop 809).take (854 - 809)).all
      (fun ins => loaderPipelineCutOp 809 854 branch (F.map Prod.fst) ins.op) = true)
    (hLocal : (7292, b64 l.localBase) ∈ F) (hFresh : ∀ pair ∈ F, pair.1 ≠ 1945 ∧ pair.1 ≠ 1946)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hRank : ((X.tr g).take index).countP Execution.isShfl = rank) {a : Acc}
    {bytes : List (Option Byte)} (hFirst : X.get (g, read) = some ⟨804, .rd a bytes⟩)
    (hSaved : PrimingCellValue X g read 799 (sourceScratchAccess l g 1) (b64 base).toBytes)
    {j : Nat} {target : Event} (he : X.get (g, j) = some target) (hBefore : index ≤ j)
    (hLater : 854 < target.pc ∨ (Execution.isShfl target = true ∧
      rank + 14 ≤ ((X.tr g).take j).countP Execution.isShfl)) (hSafe : ∀ f, target.kind ≠ .ub f) :
    ∃ t pos stop, pos ≤ j ∧ At t 855 (primingVReloadWords 1 base ++ F) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) stop ∧
      ((X.tr g).take pos).countP Execution.isShfl = rank + 14 := by
  have hCount : loaderShuffleTail 854 809 = 14 := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hReach : 854 ≤ target.pc ∨ (Execution.isShfl target = true ∧
      ((X.tr g).take index).countP Execution.isShfl + loaderShuffleTail 854 809 ≤
      ((X.tr g).take j).countP Execution.isShfl) := by
    rw [hRank, hCount]
    exact hLater.imp_left Nat.le_of_lt
  obtain ⟨u, front, stop, _, hu, huRun, huRank, huPos⟩ :=
    prefixCountedShuffleCutAtEntry (start := 809) (stop := 854) (F := F) (by decide) hStable
      (by set_option maxRecDepth 100000 in kernel_rfl) hs hr he hBefore hReach hSafe
  let pos := index + front.length
  let site := primingVPointerReload 1
  have hAddr : l.localBase + site.offset < 2 ^ 64 := by
    have := hp.localMemory.2.1
    change l.localBase + 8 < 2 ^ 64
    omega
  have hAlign : (l.localBase + site.offset) % 8 = 0 := by
    have := hp.localMemory.1
    change (l.localBase + 8) % 8 = 0
    omega
  have huAddr : At u 854 [(7292, b64 l.localBase)] :=
    hu.mono ⟨holds_mem hu.2.2.2.2 hLocal, trivial⟩
  have hMore := traceAfterObservedEvent he huPos
  obtain ⟨bs, hGet⟩ := site.firstReadOccursInPrefix (by decide) Flow.code_854
    hAddr hAlign huAddr huRun hMore
  obtain ⟨w, hwBefore, hwAt, hLast⟩ :=
    primingVSecondSlotLatestOfEvent hp hX hw hFirst rfl hGet rfl hSaved
  have advance {i : Nat} {e : Event} (hi : X.get (g, i) = some e)
      (hPC : e.pc = 854) (hMark : Execution.isShfl e = false) (hOrder : i ≤ j) :
      i + 1 ≤ j := by
    by_contra! hBad
    have hEq : i = j := by omega
    rw [hEq] at hi
    obtain rfl := Option.some.inj (he.symm.trans hi)
    rcases hLater with hLate | ⟨hRank, _⟩
    · omega
    · exact Bool.noConfusion (hMark.symm.trans hRank)
  have hNext : pos + 1 ≤ j := advance hGet rfl rfl huPos
  have hStore : X.Writes (g, w) (site.cell g l.localBase) (b64 base).toBytes := ⟨799, hwAt⟩
  obtain ⟨v, hv, hvFrame, hvRun, hRead0, hRead1⟩ :=
    site.observedWithPrefix hX (by decide) Flow.code_854
      hAddr hAlign (by decide) hBase hwBefore (hu.mono ⟨huAddr.2.2.2.2.1, hu.2.2.2.2⟩)
      hFresh huRun hMore (fun _ _ => traceAfterObservedEvent he hNext) hStore hLast
  have hNext2 : pos + 2 ≤ j := advance hRead1 rfl rfl hNext
  have hC0 := Flow.countP_take_succ_false (p := Execution.isShfl) hRead0 rfl
  have hC1 := Flow.countP_take_succ_false (p := Execution.isShfl) hRead1 rfl
  refine ⟨v, pos + 2, stop, hNext2, hv.mono ⟨hv.2.2.2.2.1, hv.2.2.2.2.2.1, hvFrame⟩,
    hvRun, ?_⟩
  rw [show pos + 2 = pos + 1 + 1 by omega, hC1, hC0, huRank, hRank, hCount]

end
end PTX.Kernels.TmlFa4Fwd.Loader
