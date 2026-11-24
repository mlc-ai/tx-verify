-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingPage
public import Kernels.TmlFa4Fwd.Proof.LoaderScratchStore

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

def primingScratchFrame (p : Params) (l : Launch) (batch base : Nat) : List (Nat × Value) :=
  [(1095, b32 base), (7302, b64 1), (1093, b32 1), (1094, b32 3),
   (1086, b32 (p.kLength batch)), (7299, b64 (p.pageTableBase + 4 * (batch * p.pageTableStride))),
   (7295, b64 (l.localBase + 96)), (7294, b64 (l.localBase + 64)),
   (7296, b64 16), (2535, b32 l.sharedBase)]

def primingScratchFacts (p : Params) (l : Launch) (batch base : Nat) (entry : Fin 2) :
    List (Nat × Value) :=
  (7172, b32 entry.val) :: (772, .pred (entry.val == 0)) :: primingScratchFrame p l batch base

def primingScratchPage (p : Params) (batch row : Nat) : Nat :=
  if row < p.kLength batch then p.page batch (row / 16) else 0

def primingScratchReads (p : Params) (batch row : Nat) : Nat :=
  if row < p.kLength batch then 1 else 0

/-- An iteration performs the optional page read, the page-number store and the
row-in-page store. The two scratch writes belong to separate arrays. -/
def primingScratchEvents (p : Params) (l : Launch) (g batch base : Nat)
    (entry : Fin 2) : List Event :=
  let row := base + 64 * entry.val
  let n := primingScratchPage p batch row
  (if row < p.kLength batch then [⟨503,
      .rd {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4}
        ((b32 n).toBytes.map some)⟩] else []) ++
  [⟨506, .wr (scratchWordAccess l g 0 entry) (b32 n).toBytes⟩,
   ⟨511, .wr (rowScratchAccess l g entry) (b32 (row % 16)).toBytes⟩]

/-- All observed scratch events precede the initial K wait. -/
theorem primingScratchEvents_before {p : Params} {l : Launch} {g batch base : Nat}
    {entry : Fin 2} (e : Event) (he : e ∈ primingScratchEvents p l g batch base entry) :
    e.pc ≤ 514 := by
  dsimp only [primingScratchEvents] at he
  split at he <;> simp only [List.singleton_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at he
  · rcases he with rfl | rfl | rfl
    · exact (by decide : 503 ≤ 514)
    · exact (by decide : 506 ≤ 514)
    · exact (by decide : 511 ≤ 514)
  · rcases he with rfl | rfl
    · exact (by decide : 506 ≤ 514)
    · exact (by decide : 511 ≤ 514)

/-- Static certificates for registers carried through both scratch iterations. -/
structure PrimingScratchExtra (extra : List (Nat × Value)) : Prop where
  page : PrimingPageExtra extra
  indexKeep : ((kernel.code.drop 488).take 12).all
    (fun ins => (extra.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true
  rowKeep : ((kernel.code.drop 507).take 4).all
    (fun ins => (extra.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true
  backKeep : ((kernel.code.drop 512).take 3).all
    (fun ins => (extra.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true

private theorem primingScratchExtra_nil : PrimingScratchExtra [] := by
  constructor
  · constructor
    · set_option maxRecDepth 100000 in kernel_rfl
    · simp
    · set_option maxRecDepth 100000 in kernel_rfl
  · set_option maxRecDepth 100000 in kernel_rfl
  · set_option maxRecDepth 100000 in kernel_rfl
  · set_option maxRecDepth 100000 in kernel_rfl

set_option maxRecDepth 3000 in
/-- Prepare the ordinary row-in-page store from the decoded scratch row. -/
theorem primingScratchRowNext {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch row : Nat} (hRow : row < 2 ^ 31) (entry : Fin 2)
    {t : TState} {extra : List (Nat × Value)} (hExtra : PrimingScratchExtra extra)
    (ht : At t 507
      ((7532,b64 (4 * entry.val)) :: (primingPageCarry p l batch row entry ++ extra))) :
    ∃ v, At v 511 (primingPageCarry p l batch row entry ++ extra) ∧
      Next kernel Assumptions.all l g t v
        (.write (rowScratchAccess l g entry) (b32 (row%16)).toBytes (next v)) := by
  let F := primingPageCarry p l batch row entry
  have hArgs : At t 507 [(7294, b64 (l.localBase + 64)), (7532, b64 (4 * entry.val)),
      (7296, b64 16), (1096, b32 row), (1097, b32 (row / 16))] := by
    apply ht.mono
    repeat' apply And.intro
    all_goals first | trivial | (apply holds_lookup ht.2.2.2.2; rfl)
  obtain ⟨v, hv, hV⟩ := scratchRowSetup hp g entry hRow t hArgs
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := (F ++ extra).map Prod.fst)
    (by decide) (by decide) ht.1 (primingKeepAppend (F := F) (G := extra) (pc := 507) (n := 4)
      (by set_option maxRecDepth 100000 in kernel_rfl) hExtra.rowKeep) rfl hv
  have hn : Next kernel Assumptions.all l g t v
      (.write (rowScratchAccess l g entry) (b32 (row % 16)).toBytes (next v)) :=
    ⟨run_rtg hvA, scratchRowStoreTemplate hp entry hV⟩
  have hF : Holds v.regs (F ++ extra) := holdsSchedulerFrame ht.2.2.2.2.2 hvFrame
    (fun _ hm => List.mem_map_of_mem hm)
  exact ⟨v,hV.mono hF,hn⟩

private theorem primingRowWithFrame {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g i batch row : Nat} (hRow : row < 2 ^ 31) (entry : Fin 2)
    {t : TState} {extra : List (Nat × Value)} (hExtra : PrimingScratchExtra extra)
    (ht : At t 507 ((7532, b64 (4 * entry.val)) :: (primingPageCarry p l batch row entry ++ extra)))
    {ending : Option TState} (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hMore : (X.tr g).drop i ≠ []) :
    ∃ u, X.get (g, i) = some ⟨511, .wr (rowScratchAccess l g entry) (b32 (row % 16)).toBytes⟩ ∧
      At u 512 (primingPageCarry p l batch row entry ++ extra) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + 1)) ending := by
  obtain ⟨v,hV,hn⟩ := primingScratchRowNext (g := g) hp hRow entry hExtra ht
  obtain ⟨_, _, he, ⟨rfl, hu⟩, hTail⟩ := hn.continuing_at_nonempty (by
    rintro e ⟨_, hBad⟩
    cases hBad) hr hMore
  obtain rfl := Option.some.inj hu
  exact ⟨_,by simpa only [hV.1] using he,hV.next,hTail⟩

/-- Compute the guarded page-table address from the current scratch selector. -/
theorem primingScratchPrepare {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch base : Nat} (hb : batch < p.batch) (entry : Fin 2)
    (hRow : base + 64 * entry.val < 2 ^ 31) {t : TState} {extra : List (Nat × Value)}
    (hExtra : PrimingScratchExtra extra)
    (ht : At t 488 (primingScratchFacts p l batch base entry ++ extra)) :
    let row := base + 64 * entry.val
    ∃ v, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t v ∧
      At v 500 ((122,.pred (decide (p.kLength batch ≤ row))) ::
        (7173,b32 0) :: (primingPageCarry p l batch row entry ++ extra)) := by
  let row := base + 64 * entry.val
  let F := primingScratchFacts p l batch base entry
  have hLen : p.kLength batch < 2 ^ 31 := by have := (hp.lengths batch hb).2.2; omega
  have hArith : At t 488 [(7172, b32 entry.val), (1095, b32 base), (7302, b64 1),
      (1093, b32 1), (1094, b32 3), (1086, b32 (p.kLength batch)),
      (772, .pred (entry.val == 0))] := by
    apply ht.mono
    repeat' apply And.intro
    all_goals first | trivial | (apply holds_lookup ht.2.2.2.2; rfl)
  obtain ⟨v, hv, hV⟩ := primingScratchIndex (g := g) entry hRow hLen t hArith
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := (F ++ extra).map Prod.fst)
    (by decide) (by decide) ht.1
    (primingKeepAppend (F := F) (G := extra) (pc := 488) (n := 12)
      (by set_option maxRecDepth 100000 in kernel_rfl) hExtra.indexKeep)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hF : Holds v.regs (F ++ extra) := holdsSchedulerFrame ht.2.2.2.2 hvFrame
    (fun _ hm => List.mem_map_of_mem hm)
  have hBase : row - 64 * entry.val = base := Nat.add_sub_cancel _ _
  have hPageAt : At v 500 ((122, .pred (decide (p.kLength batch ≤ row))) ::
      (7173, b32 0) :: (primingPageCarry p l batch row entry ++ extra)) := by
    apply hV.mono
    simp only [primingPageCarry, hBase, List.cons_append, List.nil_append, Holds]
    repeat' apply And.intro
    all_goals first
      | (apply holds_lookup hV.2.2.2.2; rfl)
      | (apply holds_lookup hF; rfl)
      | exact (holds_append ..).mp hF |>.2
  exact ⟨v,run_rtg hvA,hPageAt⟩

/-- Advance to the second scratch iteration or to the empty-slot preparation. -/
theorem primingScratchFinish {p : Params} {l : Launch} {g batch base : Nat} (entry : Fin 2)
    {s : TState} {extra : List (Nat × Value)} (hExtra : PrimingScratchExtra extra)
    (hS : At s 512 (primingPageCarry p l batch (base + 64 * entry.val) entry ++ extra)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (if entry.val == 0 then 488 else 515)
        (primingScratchFacts p l batch base 1 ++ extra) := by
  let G := primingScratchFrame p l batch base
  have hGuard : At s 512 [(4, .pred (entry.val == 0))] := by
    apply hS.mono
    refine ⟨?_, trivial⟩
    apply holds_lookup hS.2.2.2.2
    rfl
  obtain ⟨u, hu, hU⟩ := primingScratchBackedgeCore (l := l) (g := g) entry hGuard
  obtain ⟨huA, huFrame⟩ := loaderLinear (regs := (G ++ extra).map Prod.fst)
    (by decide) (by decide) hS.1
    (primingKeepAppend (F := G) (G := extra) (pc := 512) (n := 3)
      (by set_option maxRecDepth 100000 in kernel_rfl) hExtra.backKeep)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hG : Holds s.regs G := by
    simp only [primingScratchFrame, G, Holds]
    repeat' apply And.intro
    all_goals first
      | trivial
      | (apply holds_lookup hS.2.2.2.2; first | rfl | simp [primingPageCarry, List.lookup])
  have hGExtra : Holds s.regs (G ++ extra) :=
    (holds_append ..).mpr ⟨hG, (holds_append ..).mp hS.2.2.2.2 |>.2⟩
  have hSave := holdsSchedulerFrame hGExtra huFrame (fun _ hm => List.mem_map_of_mem hm)
  have hAt : At u (if entry.val == 0 then 488 else 515)
      (primingScratchFacts p l batch base 1 ++ extra) :=
    hU.mono ⟨hU.2.2.2.2.1, hU.2.2.2.2.2.1, hSave⟩
  exact ⟨u,run_rtg huA,hAt⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g i batch base : Nat} (hb : batch < p.batch)
    (entry : Fin 2) (hRow : base + 64 * entry.val < 2 ^ 31)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) {t : TState}
include hp hX hb entry hRow writes

/-- One actual priming iteration, including its optional memory read and both ordinary
local stores, returns with the second iteration seeded or at the first barrier preparation. -/
theorem primingScratchIterationFrameInPrefix {extra : List (Nat × Value)}
    (hExtra : PrimingScratchExtra extra)
    (ht : At t 488 (primingScratchFacts p l batch base entry ++ extra)) {ending : Option TState}
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hDemand : PrefixDemand X g i 514 ending) :
    let es := primingScratchEvents p l g batch base entry
    ∃ u, (X.tr g).drop i = es ++ (X.tr g).drop (i + es.length) ∧
      At u (if entry.val == 0 then 488 else 515) (primingScratchFacts p l batch base 1 ++ extra) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + es.length)) ending := by
  dsimp only
  let row := base + 64 * entry.val
  obtain ⟨v,hv,hPageAt⟩ := primingScratchPrepare (g := g) hp hb entry hRow hExtra ht
  obtain ⟨w, hRead, hPage, hW, hTail⟩ :=
    primingPagesObservedFrameInPrefix hp hX hb entry writes hExtra.page hPageAt
    (hr.after_local_nonempty hv (hDemand.nonempty hr)) hDemand
  let num := if row < p.kLength batch then 1 else 0
  have hAfterRead : PrefixDemand X g (i + num) 514 ending := by
    by_cases hi : row < p.kLength batch
    · simpa only [num, ite_eq_left hi] using
        hDemand.advance (hRead hi) (by change 503 ≤ 514; decide)
    · simpa only [num, ite_eq_right hi, Nat.add_zero] using hDemand
  have hAfterPage := hAfterRead.advance hPage (by change 506 ≤ 514; decide)
  obtain ⟨s, hWrite, hS, hMore⟩ :=
    primingRowWithFrame hp hRow entry hExtra hW hTail (hAfterPage.nonempty hTail)
  have hAfterRow := hAfterPage.advance hWrite (by change 511 ≤ 514; decide)
  obtain ⟨u,hu,hAt⟩ := primingScratchFinish (g := g) entry hExtra hS
  refine ⟨u, ?_, hAt, ?_⟩
  · by_cases live : row < p.kLength batch
    · have hR := List.getElem?_eq_some_iff.mp (hRead live)
      have hP := List.getElem?_eq_some_iff.mp (show X.get (g, i + 1) = _ from by
        simpa [row,live] using hPage)
      have hW := List.getElem?_eq_some_iff.mp (show X.get (g, i + 1 + 1) = _ from by
        simpa [row,live] using hWrite)
      rw [List.drop_eq_getElem_cons hR.1, hR.2, List.drop_eq_getElem_cons hP.1, hP.2,
        List.drop_eq_getElem_cons hW.1, hW.2]
      simp [primingScratchEvents, primingScratchPage, row, live, Nat.add_assoc]
    · have hP := List.getElem?_eq_some_iff.mp (show X.get (g, i) = _ from by
        simpa [row,live] using hPage)
      have hW := List.getElem?_eq_some_iff.mp (show X.get (g, i + 1) = _ from by
        simpa [row,live] using hWrite)
      rw [List.drop_eq_getElem_cons hP.1, hP.2, List.drop_eq_getElem_cons hW.1, hW.2]
      simp [primingScratchEvents, primingScratchPage, row, live, Nat.add_assoc]
  · have hSuffix := hMore.after_local_nonempty hu (hAfterRow.nonempty hMore)
    by_cases live : row < p.kLength batch <;>
      simpa [primingScratchEvents, row, live, Nat.add_assoc] using hSuffix

/-- One scratch iteration in a terminated trace. -/
theorem primingScratchIterationFrame {extra : List (Nat × Value)}
    (hExtra : PrimingScratchExtra extra)
    (ht : At t 488 (primingScratchFacts p l batch base entry ++ extra))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    let es := primingScratchEvents p l g batch base entry
    ∃ u, (X.tr g).drop i = es ++ (X.tr g).drop (i + es.length) ∧
      At u (if entry.val == 0 then 488 else 515) (primingScratchFacts p l batch base 1 ++ extra) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + es.length)) none :=
  primingScratchIterationFrameInPrefix hp hX hb entry hRow writes hExtra ht hr (.inl rfl)

/-- One actual priming iteration, including its optional memory read and both ordinary
local stores, returns with the second iteration seeded or at the first barrier preparation. -/
theorem primingScratchIteration (ht : At t 488 (primingScratchFacts p l batch base entry))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    let es := primingScratchEvents p l g batch base entry
    ∃ u, (X.tr g).drop i = es ++ (X.tr g).drop (i + es.length) ∧
      At u (if entry.val == 0 then 488 else 515) (primingScratchFacts p l batch base 1) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + es.length)) none :=
  primingScratchIterationFrame hp hX hb entry hRow writes primingScratchExtra_nil ht hr
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g i batch base : Nat} (hb : batch < p.batch)
    (hRows : base + 64 < 2 ^ 31)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) {t : TState}
include hp hX hb hRows writes

/-- The priming page loop performs exactly two decoded iterations before the KV acquire.
Each local slot is written once, and an out-of-range row contributes no page-table access. -/
theorem primingScratchLoopObservedFrameInPrefix {extra : List (Nat × Value)}
    (hExtra : PrimingScratchExtra extra)
    (ht : At t 488 (primingScratchFacts p l batch base 0 ++ extra)) {ending : Option TState}
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hDemand : PrefixDemand X g i 514 ending) :
    let es := primingScratchEvents p l g batch base 0 ++ primingScratchEvents p l g batch base 1
    ∃ u, (X.tr g).drop i = es ++ (X.tr g).drop (i + es.length) ∧
      At u 515 (primingScratchFacts p l batch base 1 ++ extra) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + es.length)) ending := by
  dsimp only
  obtain ⟨v, hTrace, hV, hRest⟩ :=
    primingScratchIterationFrameInPrefix hp hX hb 0 (by change base + 64 * 0 < 2 ^ 31; omega)
      writes hExtra ht hr hDemand
  have hAfter := hDemand.advanceList hTrace (fun e he => primingScratchEvents_before e he)
  obtain ⟨u, hTrace', hU, hTail⟩ :=
    primingScratchIterationFrameInPrefix hp hX hb 1 hRows writes hExtra hV hRest hAfter
  refine ⟨u, ?_, hU, ?_⟩
  · rw [hTrace, hTrace', List.append_assoc, List.length_append, Nat.add_assoc]
  · simpa only [List.length_append, Nat.add_assoc] using hTail

end
end PTX.Kernels.TmlFa4Fwd.Loader
