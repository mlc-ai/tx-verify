-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsWriteSites
public import Kernels.TmlFa4Fwd.Proof.MmaStartup
import Kernels.TmlFa4Fwd.Proof.AllocationBarrierEntry
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow PTX.EventFrame PTX.Assumption Prologue Mma Correction Epilogue

/-- Audited lower bounds for a role suffix after allocation startup. -/
inductive ResourceTail
  | allocation
  | allocationRead
  | firstGroup
  | softmaxScheduler
  | relinquish
  | release

def ResourceTail.start : ResourceTail → Nat
  | .allocation => 1910
  | .allocationRead => 1912
  | .firstGroup => 1985
  | .softmaxScheduler => 3111
  | .relinquish => 2764
  | .release => 2767

private def afterResource (cut : ResourceTail) (i : Instr) : Bool :=
  (i.op.isLocal || Epilogue.ordinaryEvent i.op) &&
    match i.op with
    | .bra dst _ => cut.start ≤ dst
    | .brx .. => false
    | _ => true

set_option maxRecDepth 100000 in
private theorem afterResourceCode (cut : ResourceTail) {pc : Nat} {i : Instr}
    (hl : cut.start ≤ pc)
    (hc : kernel.code[pc]? = some i) : afterResource cut i = true := by
  have hAll : (kernel.code.drop cut.start).all (afterResource cut) = true := by
    cases cut <;> kernel_rfl
  apply List.all_eq_true.mp hAll i
  apply List.mem_of_getElem? (i := pc - cut.start)
  rw [List.getElem?_drop, Nat.add_sub_of_le hl, hc]

private theorem afterResourceSegment (cut : ResourceTail) {pc : Nat} {m : SegMatch CuteSlot}
    (hs : pc ∈ Assumptions.swExp2Sites) (hm : cuteExp2.matchAt kernel pc = some m) :
    cut.start ≤ m.stop := by
  have hAll : Assumptions.swExp2Sites.all (fun src =>
      match cuteExp2.matchAt kernel src with
      | none => false
      | some mat => 3111 ≤ mat.stop) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hAll _ hs
  rw [hm] at h
  have hStart : cut.start ≤ 3111 := by cases cut <;> decide
  exact hStart.trans (of_decide_eq_true h)

private theorem resourceFloorStep (cut : ResourceTail) {l : Launch} {g : Nat}
    {s u : TState} {e : Option Event} (hLow : cut.start ≤ s.pc)
    (hStep : WStep kernel Assumptions.all l g s e u) : cut.start ≤ u.pc := by
  rcases hStep with ⟨rfl, hTau⟩ | ⟨e, rfl, hEvent⟩
  · obtain ⟨i, hc, _, hLocal⟩ := Softmax.tauScoreSource hTau
    rcases hLocal with ⟨rfl, _⟩ | ⟨_, _, hLocal⟩
    · change cut.start ≤ s.pc + 1
      omega
    rcases Softmax.scoreExecLocal hLocal with hFrame | ⟨mat, hs, hm, hRun⟩
    · have hCode := (Bool.and_eq_true_iff.mp (afterResourceCode cut hLow hc)).2
      have hPc := hFrame.pc
      cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
      case bra dst uni => rw [hPc]; simpa [ho] using hCode
      case brx => simp [ho] at hCode
      all_goals omega
    · exact (Softmax.scoreSegmentFrame hRun).1.symm ▸ afterResourceSegment cut hs hm
  · obtain ⟨i, hc, hl, hf⟩ := estep_event_source hEvent
    have hOp := (Bool.and_eq_true_iff.mp (afterResourceCode cut hLow hc)).1
    simp only [hl, Bool.false_or] at hOp
    rcases callbackFrame_fires (Epilogue.ordinaryEventFrame hOp) hf with h | h <;> omega

/-- The local suffix after an allocator instruction cannot reach that instruction again. -/
theorem resourceSuffixFloor (cut : ResourceTail) {l : Launch} {g : Nat} {s u : TState}
    {es : List Event} (hr : TraceReach kernel Assumptions.all l g s es u)
    (hLow : cut.start ≤ s.pc) :
    cut.start ≤ u.pc := by
  induction hr with
  | refl => exact hLow
  | tau ht _ ih => exact ih (resourceFloorStep cut hLow (.inl ⟨rfl, ht⟩))
  | event he _ ih => exact ih (resourceFloorStep cut hLow (.inr ⟨_, rfl, he⟩))

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem allocatorAtFirstSite {g j : Nat} {e : Event} (he : X.get (g,j) = some e)
    (hLater : 1907 < e.pc) (hw : warpIndex l g = 12) :
    6 ≤ j ∧ ∃ t o inst,
      At t 1909 [(2451, b32 512), (1062, b32 12), (2535, b32 l.sharedBase)] ∧
      X.get (g, 5) = some ⟨1907, .setMaxReg false 80 inst⟩ ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop 6) o := by
  have hg := event_thread_lt hX he
  obtain ⟨t, o, hIndex, ht, hr⟩ :=
    nonzeroCommonPrefixOfLateEvent hp hX hg (by rw [hw]; decide) he (show 173 < e.pc by omega)
  have hAt : At t 174 [(1062, b32 12), (2535, b32 l.sharedBase)] :=
    ht.mono ⟨hw ▸ ht.2.2.2.2.1, ht.2.2.2.2.2.1, trivial⟩
  have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hNonempty {k : Nat} (hk : k ≤ j) : (X.tr g).drop k ≠ [] :=
    fun hn => (Nat.not_le_of_lt hLen) ((List.drop_eq_nil_iff.mp hn).trans hk)
  obtain ⟨u, inst, hHint, hu, hThen⟩ :=
    firstRegisterHintFromCommon hp hg (⟨12, by decide⟩ : Fin 16)
      hAt hr (hNonempty hIndex)
  have hn : 5 < j := by
    by_contra! h
    have hEq : 5 = j := by omega
    rw [hEq, he] at hHint
    have hPc := congrArg Event.pc (Option.some.inj hHint)
    change e.pc = 1907 at hPc
    omega
  let v := next (setReg u 2451 (b32 512))
  have hu : At u 1908 [(1062, b32 12), (2535, b32 l.sharedBase)] := hu
  have hLocal : run kernel [] l g 1 u = some v := run_local Flow.code_1908 rfl hu rfl
  have hStep := schedulerLocalTransport (A := Assumptions.all) (lo := 1908) (len := 1)
    rfl (fun hl hh => startupOut_eq_nil (by omega) (by omega)) hLocal
    (by rw [hu.1]) (by rw [hu.1])
  have hv : At v 1909 [(2451, b32 512), (1062, b32 12), (2535, b32 l.sharedBase)] :=
    hu.set (by simp)
  exact ⟨by omega, v, o, inst, hv, hHint, hThen.after_local_nonempty (run_rtg hStep)
    (hNonempty (by omega))⟩

/-- The allocation-result store belongs to the allocator warp. -/
theorem allocatorStoreWarp {g j : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g,j) = some ⟨1909, .wr a bs⟩) :
    warpIndex l g = 12 := by
  have hRole := roleBodyPcOfEvent hp hX he
    (show 173 < 1909 by decide) (show 1909 ∉ registerHintSites by decide)
  change roleBodyPc (warpIndex l g) 1909 at hRole
  rcases hRole with h | h
  · omega
  · split_ifs at h <;> omega

/-- Every allocation result comes from the actual request on lane zero. -/
theorem allocatorStoreOrigin {g j : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g,j) = some ⟨1909, .wr a bs⟩) :
    a = {loc := allocationSlot l g, size := 4} ∧ laneOf l g = 0 ∧ j = 7 ∧
      ∃ inst, X.get (g, 5) = some ⟨1907, .setMaxReg false 80 inst⟩ ∧
        X.get (g, 6) = some ⟨1909, .tc (.resource .one (some (allocationSlot l g))
          (.alloc 512))⟩ := by
  have hw := allocatorStoreWarp hp hX he
  obtain ⟨hIndex, t, o, inst, ht, hHint, hRun⟩ := allocatorAtFirstSite hp hX he
    (show 1907 < 1909 by decide) hw
  have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hNonempty {k : Nat} (hk : k ≤ j) : (X.tr g).drop k ≠ [] :=
    fun hn => (Nat.not_le_of_lt hLen) ((List.drop_eq_nil_iff.mp hn).trans hk)
  have hBase : t.regs 2535 = some (b32 l.sharedBase) := ht.2.2.2.2.2.2.1
  have hCols : t.regs 2451 = some (b32 512) := ht.2.2.2.2.1
  let after := if laneOf l g = 0 then {t with sub := 1} else next t
  have hNext : Next kernel Assumptions.all l g t t
      (.tc (.resource .one (some (allocationSlot l g)) (.alloc 512)) after) :=
    ⟨.refl, by rw [allocationTemplate hp ht.1 ht.2.2.2.1 hBase hCols, ht.2.1]; rfl⟩
  obtain ⟨_, _, hFirst, ⟨rfl, hOut⟩, hTail⟩ :=
    hNext.continuing_at_nonempty (by rintro _ ⟨_, h⟩; cases h) hRun
      (hNonempty hIndex)
  obtain rfl := Option.some.inj hOut
  have hPassed : 6 < j := by
    by_contra! h
    have hEq : 6 = j := by omega
    rw [hEq, he] at hFirst
    exact Kind.noConfusion (congrArg Event.kind (Option.some.inj hFirst))
  have noLater {k : Nat} (h : Run kernel Assumptions.all l g (next t)
      ((X.tr g).drop k) o) (hk : k ≤ j) : False := by
    have hGet : ((X.tr g).drop k)[j-k]? = some ⟨1909, .wr a bs⟩ := by
      rw [List.getElem?_drop, Nat.add_sub_of_le hk]
      exact he
    obtain ⟨s, _, hReach, hEvent⟩ := h.before_event hGet
    have hLow := resourceSuffixFloor .allocation hReach
      (show 1910 ≤ (next t).pc by rw [ht.next.1])
    change 1910 ≤ s.pc at hLow
    have hPc : 1909 = s.pc := estep_source_pc hEvent
    omega
  by_cases hLeader : laneOf l g = 0
  · obtain ⟨_, _, hStore, hLater⟩ :=
      allocationStorePrefix hp hLeader ht hBase hCols hTail (hNonempty (by omega))
    by_cases hEq : j = 5 + 2
    · rw [hEq] at he
      have hFootprint :=
        (Kind.wr.inj (congrArg Event.kind (Option.some.inj (he.symm.trans hStore)))).1
      exact ⟨hFootprint, hLeader, hEq, inst, hHint, by simpa only [ht.1] using hFirst⟩
    · exact (noLater hLater (by omega)).elim
  · exact (noLater (by simpa only [after, hLeader, ↓reduceIte] using hTail) (by omega)).elim

/-- The actual allocation collective occupies the same startup slot in every allocator lane. -/
theorem allocatorIssueAtEntryAllLanes {g j : Nat} {group : CtaGroup} {dst : Option Loc}
    {r : Tmem.Request} (he : X.get (g,j) = some ⟨1909, .tc (.resource group dst r)⟩)
    : j = 6 ∧ group = .one ∧ dst = some (allocationSlot l g) ∧ r = .alloc 512 := by
  have hRole := roleBodyPcOfEvent hp hX he
    (show 173 < 1909 by decide) (show 1909 ∉ registerHintSites by decide)
  have hw : warpIndex l g = 12 := by
    change roleBodyPc (warpIndex l g) 1909 at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  obtain ⟨hIndex, t, o, _, ht, _, hRun⟩ := allocatorAtFirstSite hp hX he
    (show 1907 < 1909 by decide) hw
  have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hNonempty {k : Nat} (hk : k ≤ j) : (X.tr g).drop k ≠ [] :=
    fun hn => (Nat.not_le_of_lt hLen) ((List.drop_eq_nil_iff.mp hn).trans hk)
  have hBase : t.regs 2535 = some (b32 l.sharedBase) := ht.2.2.2.2.2.2.1
  have hCols : t.regs 2451 = some (b32 512) := ht.2.2.2.2.1
  let after := if laneOf l g = 0 then {t with sub := 1} else next t
  have hNext : Next kernel Assumptions.all l g t t
      (.tc (.resource .one (some (allocationSlot l g)) (.alloc 512)) after) :=
    ⟨.refl, by rw [allocationTemplate hp ht.1 ht.2.2.2.1 hBase hCols, ht.2.1]; rfl⟩
  obtain ⟨_, _, hFirst, ⟨rfl, hOut⟩, hTail⟩ :=
    hNext.continuing_at_nonempty (by rintro _ ⟨_, h⟩; cases h) hRun (hNonempty hIndex)
  obtain rfl := Option.some.inj hOut
  have hPosition : j = 6 := by
    by_contra hDifferent
    have hLater : 7 ≤ j := by omega
    have noRepeat {k : Nat} (hr : Run kernel Assumptions.all l g (next t)
        ((X.tr g).drop k) o) (hk : k ≤ j) : False := by
      have hGet : ((X.tr g).drop k)[j - k]? = some ⟨1909, .tc (.resource group dst r)⟩ := by
        rw [List.getElem?_drop, Nat.add_sub_of_le hk]
        exact he
      obtain ⟨u, _, hReach, hStep⟩ := hr.before_event hGet
      have hLow := resourceSuffixFloor .allocation hReach
        (show 1910 ≤ (next t).pc by rw [ht.next.1])
      change 1910 ≤ u.pc at hLow
      have hPc : 1909 = u.pc := estep_source_pc hStep
      omega
    by_cases hLane : laneOf l g = 0
    · obtain ⟨_, _, hStore, hAfter⟩ :=
        allocationStorePrefix hp hLane ht hBase hCols hTail (hNonempty hLater)
      rcases Nat.eq_or_lt_of_le hLater with hSeven | hPast
      · rw [← hSeven, hStore] at he
        exact Kind.noConfusion (congrArg Event.kind (Option.some.inj he))
      · exact noRepeat hAfter (by omega)
    · exact noRepeat (by simpa only [after, hLane, ↓reduceIte] using hTail) hLater
  rw [ht.1, ← hPosition, he] at hFirst
  exact ⟨hPosition, TcKind.resource.inj (Kind.tc.inj (Event.mk.inj
    (Option.some.inj hFirst)).2)⟩

/-- The lane-zero allocator request occurs in the startup prefix. -/
theorem allocatorIssueAtEntry {g j : Nat} {group : CtaGroup} {dst : Option Loc} {r : Tmem.Request}
    (he : X.get (g,j) = some ⟨1909, .tc (.resource group dst r)⟩) (_hLane : laneOf l g = 0)
    : j = 6 :=
  (allocatorIssueAtEntryAllLanes hp hX he).1

private theorem allocatorStoreFootprint {g j : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g,j) = some ⟨1909, .wr a bs⟩) :
    a = {loc := allocationSlot l g, size := 4} :=
  (allocatorStoreOrigin hp hX he).1

/-- Every byte of the allocation result lies in the CTA's scratch words. -/
theorem allocatorWriteBelowScratchLimit {i : EvId} {a : Acc} {data : List Byte} {loc : Loc}
    (hi : X.get i = some ⟨1909, .wr a data⟩) (hCover : a.Covers loc) :
    loc.addr < l.sharedBase + 3072 := by
  have hend := hCover.2.2.2
  rw [allocatorStoreFootprint hp hX hi] at hend
  change loc.addr < l.sharedBase + 312 + 4 at hend
  omega

/-- The real allocation publication is below the terminal statistics region. -/
theorem allocatorWriteDoesNotCoverStatistics {i : EvId} {a : Acc} {bs : List Byte}
    (hi : X.get i = some ⟨1909, .wr a bs⟩) {g : Nat} {stage : Fin 2} {kind : StatsKind} {k : Nat} :
    ¬ a.Covers ((statsLoc l g stage kind).at k) := by
  rcases i with ⟨writer, index⟩
  rw [allocatorStoreFootprint hp hX hi]
  intro h
  have hEnd := h.2.2.2
  cases kind <;> simp only [allocationSlot, statsLoc, statsOff, Loc.at] at hEnd <;> omega

end PTX.Kernels.TmlFa4Fwd.Thread
