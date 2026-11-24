-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyRoundPageWords
import Kernels.TmlFa4Fwd.Proof.LoaderRecurringScratchSave
import Kernels.TmlFa4Fwd.Proof.LoaderRankedObservation
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderLocalWriteCell
import Lemmas.Flow.NotRmw
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Thread.Loader.LocalAccessCode

noncomputable section

private theorem accessOfObservedWrite {X : Execution} {i : EvId} {a dst : Acc}
    {pc : Nat} {words : List Byte} (h : X.get i = some ⟨pc, .wr a words⟩)
    (hw : X.Access i dst true) : dst = a := by
  rcases hw with ⟨_, _, hf⟩ | ⟨_, ⟨_, hGet⟩, _⟩ | ⟨_, _, _, hGet⟩
  · cases hf
  · exact (Kind.wr.inj (congrArg Event.kind (Option.some.inj (hGet.symm.trans h)))).1
  · cases Option.some.inj (hGet.symm.trans h)

variable {p : Params}

private theorem SteadyPageWords.writtenInSlot {l : Launch} {X : Execution} {g pos batch row j : Nat}
    {slot : Fin 2} {a : Acc} (h : SteadyPageWords p l X g pos batch row slot) (hLo : pos ≤ j)
    (hHi : j < pos + primingScratchReads p batch row + 2) (hw : X.Access (g, j) a true) :
    (j = pos + primingScratchReads p batch row ∧ a = pageRefreshAccess l g 1 false slot) ∨
    (j = pos + primingScratchReads p batch row + 1 ∧ a = pageRefreshAccess l g 1 true slot) := by
  let skips := primingScratchReads p batch row
  have hFirst : pos + skips ≤ j := by
    by_cases hlive : row < p.kLength batch
    · by_contra! hPast
      have hj : j = pos := by simp [skips, primingScratchReads, hlive] at hPast; omega
      subst j
      exact observedReadNoWrite (h.read hlive) hw
    · simpa [skips, primingScratchReads, hlive] using hLo
  rcases Nat.eq_or_lt_of_le hFirst with hEq | hLater
  · exact .inl ⟨hEq.symm, accessOfObservedWrite h.page (hEq ▸ hw)⟩
  · have hEq : j = pos + skips + 1 := by change j < pos + skips + 2 at hHi; omega
    exact .inr ⟨hEq, accessOfObservedWrite h.rowWord (hEq ▸ hw)⟩

private theorem laterScratchWordApart (l : Launch) (g k : Nat) (hk : k < 4)
    (write target : Bool) (slot : Fin 2) (hDifferent : write ≠ target ∨ slot ≠ 0) :
    ¬ (pageRefreshAccess l g 1 write slot).Covers
      ((pageRefreshAccess l g 1 target 0).loc.at k) := by
  cases write <;> cases target <;> fin_cases slot <;>
    simp [pageRefreshAccess, recurringPageStoreSite, scratchReloadAccess, recurringScratchWord,
      kvLocalOffset, Acc.Covers, Loc.InRange, Loc.at] at hDifferent ⊢ <;> omega

private theorem firstSteadyWordLatest {l : Launch} {X : Execution} {g pos batch row index : Nat}
    (target : Bool) (hFirst : SteadyPageWords p l X g pos batch row 0)
    (hSecond : SteadyPageWords p l X g (pos + primingScratchReads p batch row + 2)
      batch (row + 64) 1)
    (hUnwritten : let second := pos + primingScratchReads p batch row + 2
      let next := second + primingScratchReads p batch (row + 64) + 2
      ∀ k, next ≤ k → k < index → ∀ a, ¬ X.Access (g, k) a true) :
    ∀ k < 4, ∀ j dst, X.Access (g, j) dst true →
      dst.Covers ((pageRefreshAccess l g 1 target 0).loc.at k) →
      j ≤ pos + primingScratchReads p batch row + (if target then 1 else 0) ∨ index ≤ j := by
  intro k hk j dst ha hc
  let idx := pos + primingScratchReads p batch row
  let second := idx + 2
  let nextIndex := second + primingScratchReads p batch (row + 64) + 2
  by_contra! hPast
  by_cases hTail : nextIndex ≤ j
  · exact hUnwritten j hTail hPast.2 dst ha
  by_cases hSecondStart : second ≤ j
  · rcases hSecond.writtenInSlot hSecondStart (by omega) ha with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact laterScratchWordApart l g k hk false target 1 (.inr (by decide)) hc
    · exact laterScratchWordApart l g k hk true target 1 (.inr (by decide)) hc
  have hFirstOrd : idx < j := by
    have hWord := hPast.1
    change idx + (if target then 1 else 0) < j at hWord
    omega
  have hFirstStart : pos ≤ j := by dsimp [idx] at hFirstOrd; omega
  rcases hFirst.writtenInSlot hFirstStart (Nat.lt_of_not_ge hSecondStart) ha with
      ⟨hEq, _⟩ | ⟨hEq, rfl⟩
  · exact Nat.ne_of_lt hFirstOrd hEq.symm
  have hTarget : target = false := by
    cases target
    · rfl
    · have hWord : idx + 1 < j := by simpa only [↓reduceIte] using hPast.1
      omega
  exact laterScratchWordApart l g k hk true target 0 (.inl (by simp [hTarget])) hc

private theorem secondSteadyWordLatest {l : Launch} {X : Execution} {g pos batch row index : Nat}
    (target : Bool) (hSecond : SteadyPageWords p l X g pos batch row 1)
    (hUnwritten : ∀ k, pos + primingScratchReads p batch row + 2 ≤ k → k < index →
      ∀ a, ¬ X.Access (g, k) a true) :
    ∀ k < 4, ∀ j dst, X.Access (g, j) dst true →
      dst.Covers ((pageRefreshAccess l g 1 target 1).loc.at k) →
      j ≤ pos + primingScratchReads p batch row + (if target then 1 else 0) ∨ index ≤ j := by
  intro k hk j dst ha hc
  let idx := pos + primingScratchReads p batch row
  by_contra! hPast
  by_cases hTail : idx + 2 ≤ j
  · exact hUnwritten j hTail hPast.2 dst ha
  have hFirstOrd : idx < j := by
    have hWord := hPast.1
    change idx + (if target then 1 else 0) < j at hWord
    omega
  have hFirstStart : pos ≤ j := by dsimp [idx] at hFirstOrd; omega
  rcases hSecond.writtenInSlot hFirstStart (Nat.lt_of_not_ge hTail) ha with
      ⟨hEq, _⟩ | ⟨hEq, rfl⟩
  · exact Nat.ne_of_lt hFirstOrd hEq.symm
  have hTarget : target = false := by
    cases target
    · rfl
    · have hWord : idx + 1 < j := by simpa only [↓reduceIte] using hPast.1
      omega
  have hAddr : ¬ (pageRefreshAccess l g 1 true 1).Covers
        ((pageRefreshAccess l g 1 target 1).loc.at k) := by
    subst target
    simp [pageRefreshAccess, recurringPageStoreSite, scratchReloadAccess, recurringScratchWord,
      kvLocalOffset, Acc.Covers, Loc.InRange, Loc.at]
    omega
  exact hAddr hc

/-- Each refreshed metadata word remains the latest covering write when the
two-entry steady page loop finishes. -/
theorem steadyPageWordsLatestAtExit {l : Launch} {X : Execution} {g pos batch row : Nat}
    (hFirst : SteadyPageWords p l X g pos batch row 0)
    (hSecond : SteadyPageWords p l X g (pos + primingScratchReads p batch row + 2)
      batch (row + 64) 1) (slot : Fin 2) (target : Bool) :
    let second := pos + primingScratchReads p batch row + 2
    let stop := second + primingScratchReads p batch (row + 64) + 2
    let write := (if slot.val = 0 then pos + primingScratchReads p batch row
        else second + primingScratchReads p batch (row + 64)) + if target then 1 else 0
    ∀ k < 4, ∀ j < stop, ∀ a, X.Access (g, j) a true →
      a.Covers ((pageRefreshAccess l g 1 target slot).loc.at k) → j ≤ write := by
  dsimp only
  intro k hk j hj a hAccess hCover
  fin_cases slot
  · have h := firstSteadyWordLatest (index :=
      pos + primingScratchReads p batch row + 2 + primingScratchReads p batch (row + 64) + 2)
      target hFirst hSecond (by intro _ hLo hHi; omega)
      k hk j a hAccess hCover
    exact h.resolve_right (Nat.not_le.mpr hj)
  · have h := secondSteadyWordLatest (index :=
      pos + primingScratchReads p batch row + 2 + primingScratchReads p batch (row + 64) + 2)
      target hSecond (by intros n hLo hHi; omega) k hk j a hAccess hCover
    exact h.resolve_right (Nat.not_le.mpr hj)

set_option maxRecDepth 100000 in
private theorem noSteadyMetaWriteAfterPageLoop {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g i : Nat} {e : Event}
    (he : X.get (g, i) = some e) (hPc : 1427 ≤ e.pc ∧ e.pc < 1634) {a : Acc}
    (hA : X.Access (g, i) a true) (slot : Fin 2) (target : Bool) {byte : Nat} (hByte : byte < 4) :
    ¬ a.Covers ((pageRefreshAccess l g 1 target slot).loc.at byte) := by
  intro hc
  have hChecked : (((kernel.code.drop 1427).take (1634 - 1427)).zipIdx 1427).all
      (fun (ins, pc) => !atomicOp ins.op && (!writeOp ins.op || pc == 1447 || pc == 1628)) =
      true := by
    kernel_rfl
  have codeAt {ins : Instr} (hCode : kernel.code[e.pc]? = some ins) :
      (!atomicOp ins.op && (!writeOp ins.op || e.pc == 1447 || e.pc == 1628)) = true := by
    have hGet : ((kernel.code.drop 1427).take (1634 - 1427))[e.pc - 1427]? = some ins := by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hPc.1]
      exact hCode
    have hIndex : (((kernel.code.drop 1427).take (1634 - 1427)).zipIdx 1427)[e.pc - 1427]? =
        some (ins, e.pc) := by
      rw [List.getElem?_zipIdx, hGet]
      simp [Nat.add_sub_of_le hPc.1]
    exact List.all_eq_true.mp hChecked _ (List.mem_of_getElem? hIndex)
  rcases hA with ⟨_, _, hFalse⟩ | ⟨data, ⟨pc, hGet⟩, _⟩ | ⟨old, new, pc, hGet⟩
  · cases hFalse
  · obtain rfl := Option.some.inj (he.symm.trans hGet)
    rcases get_source hX he with ⟨_, h⟩ | ⟨_, ins, _, _, hCode, hf⟩
    · cases h
    have hSite : pc = 1447 ∨ pc = 1628 := by
      have h := (Bool.and_eq_true_iff.mp (codeAt hCode)).2
      simp [fires_write_op hf rfl] at h
      exact h
    have hSpace : a.loc.space = .local := by
      have h := hc.1
      cases target <;> exact h.symm
    obtain ⟨site, hs, entry, hIssue, hAcc⟩ :=
      Thread.Loader.localWriteCell hp hX ⟨pc, hGet⟩ hSpace
    have hSitePc := congrArg Event.pc (Option.some.inj (hIssue.symm.trans hGet))
    have hArray : site.array.val < 2 := by
      have hAudit : scalarSites.all (fun s =>
        decide ((s.accessPc = 1447 ∨ s.accessPc = 1628) → s.array.val < 2)) = true := by
        decide
      apply of_decide_eq_true (List.all_eq_true.mp hAudit site hs)
      rw [show site.accessPc = pc from hSitePc]
      exact hSite
    rw [hAcc] at hc
    have ha := site.array.isLt
    have he := entry.isLt
    cases target <;> fin_cases slot <;>
      simp [pageRefreshAccess, recurringPageStoreSite, scratchReloadAccess, recurringScratchWord,
        kvLocalOffset, ScalarSite.word, hArray, Acc.Covers, Loc.InRange, Loc.at] at hc <;> omega
  · obtain rfl := Option.some.inj (he.symm.trans hGet)
    rcases get_source hX he with ⟨_, h⟩ | ⟨_, ins, _, _, hCode, hf⟩
    · cases h
    have ha := (Bool.and_eq_true_iff.mp (codeAt hCode)).1
    rw [fires_rmw_op hf rfl] at ha
    cases ha

set_option maxRecDepth 100000 in
/-- The K packet and its handoff can only update pointer arrays. The two page
and row cells carry their refreshed bytes into the steady K/V save loops. -/
theorem steadyPageWordsLatest {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g pos batch row stop : Nat} {s : TState}
    {ending : Option TState} (hFirst : SteadyPageWords p l X g pos batch row 0)
    (hSecond : SteadyPageWords p l X g (pos + primingScratchReads p batch row + 2)
      batch (row + 64) 1) (hs : At s 1427 [])
    (hr : Run kernel Assumptions.all l g s
      ((X.tr g).drop (pos + primingScratchReads p batch row + 2 +
        primingScratchReads p batch (row + 64) + 2)) ending)
    (hRank : ((X.tr g).take stop).countP Execution.isShfl ≤
      ((X.tr g).take (pos + primingScratchReads p batch row + 2 +
        primingScratchReads p batch (row + 64) + 2)).countP Execution.isShfl + 32) (slot : Fin 2)
    (target : Bool) :
    let second := pos + primingScratchReads p batch row + 2
    let write := (if slot.val = 0 then pos + primingScratchReads p batch row
        else second + primingScratchReads p batch (row + 64)) + if target then 1 else 0
    ∀ byte < 4, ∀ j < stop, ∀ a, X.Access (g, j) a true →
      a.Covers ((pageRefreshAccess l g 1 target slot).loc.at byte) → j ≤ write := by
  intro second write byte hByte j hj a hAccess hCover
  let start := second + primingScratchReads p batch (row + 64) + 2
  by_cases hBefore : j < start
  · exact steadyPageWordsLatestAtExit hFirst hSecond slot target byte hByte j hBefore
      a hAccess hCover
  have hAudit (bound : Nat) : ((kernel.code.drop 1427).take (1634 - 1427)).all
      (fun ins => loaderPipelineCutOp 1427 1634 bound [] ins.op) = true := by kernel_rfl
  have hRanked : (((kernel.code.drop 1427).take (1634 - 1427)).zipIdx 1427).all
      (fun (ins, pc) => LoaderRankedInstr 1634 pc ins) = true := by kernel_rfl
  have hCount : loaderShuffleTail 1634 1427 = 33 := by kernel_rfl
  have hFew : ((X.tr g).take j).countP Execution.isShfl <
      ((X.tr g).take start).countP Execution.isShfl + loaderShuffleTail 1634 1427 := by
    rw [hCount]
    exact (countP_take_mono Execution.isShfl _ hj.le).trans_lt
      (Nat.lt_succ_of_le hRank)
  have observed : ∃ e, X.get (g, j) = some e := by
    rcases hAccess with ⟨_, _, hFalse⟩ | ⟨_, ⟨pc, he⟩, _⟩ | ⟨_, _, pc, he⟩
    · cases hFalse
    · exact ⟨_, he⟩
    · exact ⟨_, he⟩
  obtain ⟨e, he⟩ := observed
  have hBounds := loaderRankedEventBounds (by decide) hAudit hRanked hs hr he
    (Nat.le_of_not_gt hBefore) hFew
  exact (noSteadyMetaWriteAfterPageLoop hp hX he hBounds hAccess slot target hByte hCover).elim

end
end PTX.Kernels.TmlFa4Fwd.Loader
