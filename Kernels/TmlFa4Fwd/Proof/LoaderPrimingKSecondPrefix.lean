-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKLaterPrefixReady
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSecondSlot
import Kernels.TmlFa4Fwd.Flow.Code.Part009
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

private theorem traceAfter {X : Execution} {g i j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hle : i ≤ j) : (X.tr g).drop i ≠ [] := by
  intro h
  exact Nat.not_le_of_lt (List.getElem?_eq_some_iff.mp he).1
    ((List.drop_eq_nil_iff.mp h).trans hle)

/-- The second saved K pointer and pair-eight predicate in a live prefix. A later shuffle
of sufficiently high ordinal witnesses the reload even when its source lane is unfinished. -/
theorem primingKSecondPointerInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g batch head tile warp lane index rank stored : Nat} {bases : Nat → Nat}
    {s : TState} {ending : Option TState}
    (hWarp : 14 ≤ Prologue.warpIndex l g) (hb : batch < p.batch) (hh : head < p.kvHeads)
    (hTile : 128 * tile + 127 < 2 ^ 31)
    (hs : At s 544 (primingKSourceInputs p l batch tile warp bases lane))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hRank : ((X.tr g).take index).countP Execution.isShfl = rank)
    {a : Acc} {bs : List (Option Byte)} (hFirst : X.get (g, stored) = some ⟨543, .rd a bs⟩)
    (hSaved : PrimingCellValue X g stored 534 (sourceScratchAccess l g 1)
      (b64 (primingKRowPointer p batch head (primingLaneRow tile (32 * warp + lane) + 64))).toBytes)
    {j : Nat} {target : Event} (he : X.get (g, j) = some target) (hBefore : index ≤ j)
    (hLater : 609 < target.pc ∨ (Execution.isShfl target = true ∧
      rank + 16 ≤ ((X.tr g).take j).countP Execution.isShfl))
    (hSafe : ∀ f, target.kind ≠ .ub f) :
    let tid := 32 * warp + lane
    let base := primingKRowPointer p batch head (primingLaneRow tile tid + 64)
    let F := primingKPacketFrame p l batch tile warp bases lane
    ∃ t pos stop, pos ≤ j ∧
      At t 610 ([(1871, b32 (base % 2 ^ 32)), (1872, b32 (base / 2 ^ 32)),
        (132, .pred (decide (kvCopyRow tile tid 8 < p.kLength batch)))] ++ F) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) stop ∧
      ((X.tr g).take pos).countP Execution.isShfl = rank + 16 := by
  let tid := 32 * warp + lane
  let base := primingKRowPointer p batch head (primingLaneRow tile tid + 64)
  let F := primingKPacketFrame p l batch tile warp bases lane
  obtain ⟨v, k, _, hk, hv, hRun, hOrd⟩ :=
    primingKColumnFrameInPrefix hs hr hRank he hBefore
      (hLater.imp (fun h => by omega) (fun ⟨hShfl, hCount⟩ => ⟨hShfl, by omega⟩)) hSafe
  have hCount : loaderShuffleTail 608 548 = 14 := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hReach : 608 ≤ target.pc ∨ (Execution.isShfl target = true ∧
      ((X.tr g).take k).countP Execution.isShfl + loaderShuffleTail 608 548 ≤
        ((X.tr g).take j).countP Execution.isShfl) := by
    rw [hOrd, hCount]
    exact hLater.imp_left (fun h => by omega)
  obtain ⟨u, passed, stop, _, hu, huRun, huRank, huOrder⟩ :=
    prefixCountedShuffleCut (F := F) (by decide) (by
      intro branch
      set_option maxRecDepth 100000 in kernel_rfl) (by
      set_option maxRecDepth 100000 in kernel_rfl)
      ⟨_, Flow.code_608, rfl⟩ hv hRun he hk hReach hSafe
  let index' := k + passed.length
  have hLen : p.kLength batch < 2 ^ 31 := by have := (hp.lengths batch hb).2.2; omega
  have hRow : kvCopyRow tile tid 0 < 2 ^ 31 := by
    have := Nat.mod_lt (tid / 8) (by decide : 0 < 8)
    simp only [kvCopyRow, Nat.mul_zero, Nat.add_zero]
    omega
  have huArg : At u 608 [(1852, b32 ((p.kLength batch + 2 ^ 32 - kvCopyRow tile tid 0) %
      2 ^ 32))] := hu.mono ⟨holds_lookup hu.2.2.2.2 rfl, trivial⟩
  obtain ⟨w, hw, hwMask⟩ := primingKLaterMaskForAll (l := l) (g := g) hLen hRow
    (7 : Fin 15) u huArg
  obtain ⟨hwA, hKeep⟩ := loaderLinear (regs := F.map Prod.fst)
    (by decide) (by decide) hu.1 (by set_option maxRecDepth 100000 in kernel_rfl) (by simp) hw
  let regs := (132, .pred (decide (kvCopyRow tile tid 8 < p.kLength batch))) :: F
  have hwAt : At w 609 regs := hwMask.mono
    ⟨hwMask.2.2.2.2.1, holdsSchedulerFrame hu.2.2.2.2 hKeep (fun _ h => List.mem_map_of_mem h)⟩
  have hMore := traceAfter he huOrder
  have hwRun := huRun.after_local_nonempty (run_rtg hwA) hMore
  let site := primingKSecondReload
  have hAddr : l.localBase + site.offset < 2 ^ 64 := by
    have := hp.localMemory.2.1
    change l.localBase + 8 < 2 ^ 64
    omega
  have hAlign : (l.localBase + site.offset) % 8 = 0 := by
    have := hp.localMemory.1
    change (l.localBase + 8) % 8 = 0
    omega
  have hBase : base < 2 ^ 64 := (primingStoredPointerBounds hp hb hh).1
  have hwAddr : At w 609 [(7292, b64 l.localBase)] :=
    hwAt.mono ⟨holds_lookup hwAt.2.2.2.2 rfl, trivial⟩
  obtain ⟨bytes, hGet⟩ := site.firstReadOccursInPrefix (by decide) Flow.code_609
    hAddr hAlign hwAddr hwRun hMore
  obtain ⟨write, hWriteBefore, hWrite, hLatest⟩ :=
    primingSecondSlotLatest hp hX hWarp hFirst hGet hSaved
  have afterRead {e' : Event} (loc : Nat) (hRead : X.get (g, loc) = some e')
      (hPc : e'.pc = 609) (hNoShfl : Execution.isShfl e' = false) (hBefore : loc ≤ j) :
      loc + 1 ≤ j := by
    by_contra! hSame
    have hEq : loc = j := by omega
    rw [hEq] at hRead
    obtain rfl := Option.some.inj (he.symm.trans hRead)
    rcases hLater with h | ⟨h, _⟩
    · omega
    · exact Bool.noConfusion (h.symm.trans hNoShfl)
  have hNext : index' + 1 ≤ j := afterRead _ hGet rfl rfl huOrder
  have hStore : X.Writes (g, write) (site.cell g l.localBase) (b64 base).toBytes := ⟨534, hWrite⟩
  obtain ⟨t, ht, hRegs, hTail, hRead0, hRead1⟩ :=
    site.observedWithPrefix hX (by decide) Flow.code_609 hAddr hAlign (by decide)
      hBase hWriteBefore (F := regs) (hwAt.mono ⟨hwAddr.2.2.2.2.1, hwAt.2.2.2.2⟩)
      (by simp [regs, F, primingKPacketFrame, primingKSourceInputs, primingKSourceFrame, site,
        primingKSecondReload]) hwRun hMore (fun _ _ => traceAfter he hNext) hStore hLatest
  have hEnd : index' + 2 ≤ j := by
    have h := afterRead _ hRead1 rfl rfl hNext
    omega
  have noShuffle {i : Nat} {e' : Event} (hRead : X.get (g, i) = some e')
      (hIs : Execution.isShfl e' = false) :
      ((X.tr g).take (i + 1)).countP Execution.isShfl = ((X.tr g).take i).countP Execution.isShfl :=
    Flow.countP_take_succ_false hRead hIs
  refine ⟨t, index' + 2, stop, hEnd, ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, hRegs⟩,
    hTail, ?_⟩
  rw [show index' + 2 = index' + 1 + 1 by omega, noShuffle hRead1 rfl, noShuffle hRead0 rfl]
  rw [huRank, hOrd, hCount]

end
end PTX.Kernels.TmlFa4Fwd.Loader
