-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderScratchIndex
public import Kernels.TmlFa4Fwd.Proof.LoaderScratchRows
public import Kernels.TmlFa4Fwd.Proof.ResultGeometry

public import Kernels.TmlFa4Fwd.Proof.LoaderPrefixDemand

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The first page-table loop's unchanged row, address and iteration operands. -/
def primingPageCarry (p : Params) (l : Launch) (batch row : Nat) (entry : Fin 2) :
    List (Nat × Value) :=
  [(1096, b32 row), (1097, b32 (row / 16)), (7172, b32 entry.val),
   (7295, b64 (l.localBase + 96)), (7294, b64 (l.localBase + 64)),
   (7296, b64 16), (4, .pred (entry.val == 0)),
   (7299, b64 (p.pageTableBase + 4 * (batch * p.pageTableStride))),
   (1095, b32 (row - 64 * entry.val)), (7302, b64 1), (1093, b32 1), (1094, b32 3),
   (1086, b32 (p.kLength batch)), (2535, b32 l.sharedBase)]

/-- The selected page-table word is immutable under the global-write footprint. -/
theorem primingPageProtected {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {X : Execution} {batch row : Nat}
    (hb : batch < p.batch) (hRow : row < p.kLength batch)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) :
    ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (pageWordAddress p batch (row / 16))).at k) := by
  intro k hk w a bytes hWrite
  have hStride := (hp.pageTable batch hb).1
  have hPage : row / 16 < p.pageTableStride := by omega
  have hBatch := Nat.mul_le_mul_right p.pageTableStride (show batch + 1 ≤ p.batch by omega)
  rw [Nat.add_mul, Nat.one_mul] at hBatch
  apply hp.inputByte_unwritten writes (region := ⟨p.pageTableBase, 4 * p.batch * p.pageTableStride⟩)
  · simp [Params.inputRegions]
  · refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only [Loc.at, globalLoc, pageWordAddress, Nat.mul_assoc]
    all_goals omega
  · exact hWrite

/-- Additional facts carried across the two decoded page-read and page-save blocks. -/
structure PrimingPageExtra (G : List (Nat × Value)) : Prop where
  readKeep : ((kernel.code.drop 501).take 2).all
    (fun ins => (G.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true
  readFresh : ∀ x ∈ G, x.1 ≠ 7173
  saveKeep : ((kernel.code.drop 504).take 2).all
    (fun ins => (G.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true

/-- Combine independent register preservation checks for the same decoded block. -/
theorem primingKeepAppend {G F : List (Nat × Value)} {pc n : Nat}
    (hf : ((kernel.code.drop pc).take n).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hg : ((kernel.code.drop pc).take n).all
      (fun ins => (G.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true) :
    ((kernel.code.drop pc).take n).all
      (fun ins => ((F ++ G).map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) =
      true := by
  apply List.all_eq_true.mpr
  intro ins hi
  rw [List.map_append, List.all_append, List.all_eq_true.mp hf ins hi,
    List.all_eq_true.mp hg ins hi]
  rfl

set_option maxRecDepth 3000 in
/-- A live row prepares its checked page-table read and retains the scratch operands. -/
theorem primingPageReadNext {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch row : Nat} (hb : batch < p.batch) (hRow : row < p.kLength batch)
    (entry : Fin 2) {t : TState} {G : List (Nat × Value)}
    (hG : PrimingPageExtra G) (ht : At t 501 (primingPageCarry p l batch row entry ++ G)) :
    let loc := globalLoc (pageWordAddress p batch (row/16))
    let word := b32 (p.page batch (row/16))
    ∃ v, Next kernel Assumptions.all l g t v (.read {loc := loc,size := 4} (afterLoad v [7173])) ∧
      At v 503 (primingPageCarry p l batch row entry ++ G) ∧
      afterLoad v [7173] (word.toBytes.map some) = next (setReg v 7173 word) ∧
      At (next (setReg v 7173 word)) 504
        ((7173,word) :: (primingPageCarry p l batch row entry ++ G)) := by
  dsimp only
  let F := primingPageCarry p l batch row entry
  let word := b32 (p.page batch (row / 16))
  let acc : Acc := {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4}
  have hi : row / 16 < (p.kLength batch + 15) / 16 := by omega
  have hArgs : At t 501 [(1097, b32 (row / 16)),
      (7299, b64 (p.pageTableBase + 4 * (batch * p.pageTableStride)))] := by
    apply ht.mono
    repeat' apply And.intro
    all_goals first | trivial | (apply holds_lookup ht.2.2.2.2; rfl)
  obtain ⟨v, hv, hV⟩ := pageReadAddress hp (g := g) hb hi t hArgs
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := (F ++ G).map Prod.fst) (by decide) (by decide) ht.1
    (primingKeepAppend (by set_option maxRecDepth 100000 in kernel_rfl) hG.readKeep) rfl hv
  have hNext : Next kernel Assumptions.all l g t v (.read acc (afterLoad v [7173])) :=
    ⟨run_rtg hvA, pageReadTemplate hp hb hi hV⟩
  have hRebuild := PTX.Proof.rebuild_scalar (v := word) (show 0 < 4 by decide) rfl
  have hAfter : afterLoad v [7173] (word.toBytes.map some) = next (setReg v 7173 word) := by
    rw [afterLoad_ok hV.2.1 hV.2.2.1 hRebuild]
    simp [next, setReg, hV.2.1, hV.2.2.1]
  have hH := holdsSchedulerFrame ht.2.2.2.2 hvFrame (fun _ hm => List.mem_map_of_mem hm)
  have hFresh : ∀ x ∈ F, x.1 ≠ 7173 := by
    intro x hx heq
    exact (of_decide_eq_true rfl : 7173 ∉ F.map Prod.fst) (heq ▸ List.mem_map_of_mem hx)
  have hNewFresh : ∀ x ∈ F ++ G, x.1 ≠ 7173 := by
    intro x hx
    exact (List.mem_append.mp hx).elim (hFresh x) (hG.readFresh x)
  exact ⟨v,hNext,hV.mono hH,hAfter,(hV.mono hH).set hNewFresh⟩

private theorem primingPageRead {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i batch row : Nat} (hb : batch < p.batch) (hRow : row < p.kLength batch)
    (entry : Fin 2) {t : TState} {G : List (Nat × Value)}
    (hG : PrimingPageExtra G) (ht : At t 501 (primingPageCarry p l batch row entry ++ G))
    {ending : Option TState} (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hMore : (X.tr g).drop i ≠ [])
    (hProtect : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (pageWordAddress p batch (row / 16))).at k)) :
    let n := p.page batch (row / 16)
    ∃ u,
      X.get (g, i) = some ⟨503,
        .rd {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4}
          ((b32 n).toBytes.map some)⟩ ∧
      At u 504 ((7173, b32 n) :: (primingPageCarry p l batch row entry ++ G)) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + 1)) ending := by
  dsimp only
  let word := b32 (p.page batch (row / 16))
  let acc : Acc := {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4}
  have hi : row / 16 < (p.kLength batch + 15) / 16 := by omega
  obtain ⟨v,hNext,hV,hAfter,hAt⟩ :=
    primingPageReadNext (g := g) hp hb hRow entry hG ht
  obtain ⟨_, _, he, ⟨bs, _, rfl, hv⟩, hTail⟩ := hNext.continuing_at_nonempty (by
    rintro e ⟨_, _, _, hBad⟩
    cases hBad) hr hMore
  obtain rfl := Option.some.inj hv
  rw [hV.1] at he
  have hMem : X.MemReads (.thread (g, i)) acc bs := .inl ⟨503, he⟩
  have hBytes : bs = word.toBytes.map some := by
    apply hX.launch_value hMem rfl hProtect
    exact hp.pageBytes batch hb (row / 16) hi
  subst bs
  rw [hAfter] at hTail
  exact ⟨_,he,hAt,hTail⟩

set_option maxRecDepth 3000 in
/-- With the page-table guard resolved, the actual store writes either the physical
page obtained from the global read or the initialized zero of a masked row. -/
theorem primingPageStoreNext {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch row n : Nat} (entry : Fin 2) {t : TState}
    {G : List (Nat × Value)} (hG : PrimingPageExtra G)
    (ht : At t 504 ((7173,b32 n) :: (primingPageCarry p l batch row entry ++ G))) :
    ∃ v, At v 506 ((7532,b64 (4 * entry.val)) :: (primingPageCarry p l batch row entry ++ G)) ∧
      Next kernel Assumptions.all l g t v
        (.write (scratchWordAccess l g 0 entry) (b32 n).toBytes (next v)) := by
  let F := (7173, b32 n) :: primingPageCarry p l batch row entry
  have hArgs : At t 504 [(7172, b32 entry.val), (7295, b64 (l.localBase + 96))] := by
    apply ht.mono
    repeat' apply And.intro
    all_goals first | trivial | (apply holds_lookup ht.2.2.2.2; rfl)
  obtain ⟨v, hv, hV⟩ := pageScratchAddress (g := g) entry hp.localMemory.2.1 t hArgs
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := (F ++ G).map Prod.fst)
    (by decide) (by decide) ht.1
    (primingKeepAppend (by set_option maxRecDepth 100000 in kernel_rfl) hG.saveKeep) rfl hv
  have hF : Holds v.regs (F ++ G) := holdsSchedulerFrame ht.2.2.2.2 hvFrame
    (fun _ hm => List.mem_map_of_mem hm)
  have hAt : At v 506 [(7533, b64 (l.localBase + kvLocalOffset 3 entry)), (7173, b32 n)] :=
    hV.mono ⟨hV.2.2.2.2.1, hF.1, trivial⟩
  have hNext : Next kernel Assumptions.all l g t v
      (.write (scratchWordAccess l g 0 entry) (b32 n).toBytes (next v)) :=
    ⟨run_rtg hvA, pageScratchTemplate hp entry hAt⟩
  have hOff : v.regs 7532 = some (b64 (4 * entry.val)) := by
    simpa only [Nat.mul_comm entry.val 4] using hV.2.2.2.2.2.1
  have hCarry : At v 506
      ((7532, b64 (4 * entry.val)) :: (primingPageCarry p l batch row entry ++ G)) :=
    hV.mono ⟨hOff, hF.2⟩
  exact ⟨v,hCarry,hNext⟩

/-- The actual page-index store in a nonempty trace suffix. -/
private theorem primingPageStoreFrameInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g i batch row n : Nat} (entry : Fin 2) {t : TState}
    {G : List (Nat × Value)} (hG : PrimingPageExtra G)
    (ht : At t 504 ((7173, b32 n) :: (primingPageCarry p l batch row entry ++ G)))
    {ending : Option TState} (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hMore : (X.tr g).drop i ≠ []) :
    ∃ u, X.get (g, i) = some ⟨506,
        .wr (scratchWordAccess l g 0 entry) (b32 n).toBytes⟩ ∧
      At u 507 ((7532, b64 (4 * entry.val)) :: (primingPageCarry p l batch row entry ++ G)) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + 1)) ending := by
  obtain ⟨v,hV,hNext⟩ := primingPageStoreNext (g := g) hp entry hG ht
  obtain ⟨_, _, he, ⟨rfl, hv⟩, hTail⟩ := hNext.continuing_at_nonempty (by
    rintro e ⟨_, hBad⟩
    cases hBad) hr hMore
  obtain rfl := Option.some.inj hv
  exact ⟨_,by simpa only [hV.1] using he,hV.next,hTail⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g i batch row : Nat} (hb : batch < p.batch)
    (entry : Fin 2)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) {t : TState}
include hp hX hb entry writes

/-- A live row reads and stores its physical page. A masked row emits no page-table read
and stores zero in the same lane-owned address. Both paths rejoin at the row store. -/
theorem primingPagesObservedFrameInPrefix {G : List (Nat × Value)} (hG : PrimingPageExtra G)
    (ht : At t 500 ((122, .pred (decide (p.kLength batch ≤ row))) ::
        (7173, b32 0) :: (primingPageCarry p l batch row entry ++ G))) {ending : Option TState}
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hDemand : PrefixDemand X g i 514 ending) :
    let advance := if row < p.kLength batch then 1 else 0
    let n := if row < p.kLength batch then p.page batch (row / 16) else 0
    ∃ u, (row < p.kLength batch → X.get (g, i) = some ⟨503,
        .rd {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4}
          ((b32 n).toBytes.map some)⟩) ∧
      X.get (g, i + advance) =
        some ⟨506, .wr (scratchWordAccess l g 0 entry) (b32 n).toBytes⟩ ∧
      At u 507 ((7532, b64 (4 * entry.val)) :: (primingPageCarry p l batch row entry ++ G)) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + advance + 1)) ending := by
  dsimp only
  obtain ⟨v, hv, hV⟩ := primingScratchPageGuard (g := g) ht
  have hMore := hDemand.nonempty hr
  have hRest := hr.after_local_nonempty (run_rtg hv) hMore
  by_cases hRow : row < p.kLength batch
  · simp only [ite_eq_left hRow] at hV ⊢
    obtain ⟨w, hRead, hW, hTail⟩ := primingPageRead hp hX hb hRow entry hG
      (hV.mono hV.2.2.2.2.2) hRest hMore (primingPageProtected hp hb hRow writes)
    have hNext := hDemand.advance hRead (by change 503 ≤ 514; decide)
    obtain ⟨u, hWrite, hU, hSuffix⟩ :=
      primingPageStoreFrameInPrefix hp entry hG hW hTail (hNext.nonempty hTail)
    exact ⟨u, fun _ => hRead, hWrite, hU, hSuffix⟩
  · simp only [ite_eq_right hRow, Nat.add_zero] at hV ⊢
    obtain ⟨u, hWrite, hU, hSuffix⟩ :=
      primingPageStoreFrameInPrefix hp entry hG hV hRest hMore
    exact ⟨u, fun h => (hRow h).elim, hWrite, hU, hSuffix⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
