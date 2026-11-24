-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmValueStart
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerPrefix
import Kernels.TmlFa4Fwd.Proof.LoaderRankedObservation
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderLocalWriteCell
import Lemmas.Flow.NotRmw
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Thread.Loader.LocalAccessCode

noncomputable section

set_option maxRecDepth 100000 in
private theorem noWarmMetaWriteAfterPageLoop {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i : Nat} {e : Event} (he : X.get (g, i) = some e)
    (hPc : 957 ≤ e.pc ∧ e.pc < 1240) {a : Acc} (hA : X.Access (g, i) a true)
    (slot : Fin 2) (target : Bool) {byte : Nat} (hByte : byte < 4) :
    ¬ a.Covers ((pageRefreshAccess l g 0 target slot).loc.at byte) := by
  intro hc
  have hChecked : (((kernel.code.drop 957).take (1240 - 957)).zipIdx 957).all
      (fun (ins, pc) => !atomicOp ins.op && (!writeOp ins.op || pc == 977 || pc == 1223)) =
      true := by
    kernel_rfl
  have codeAt {ins : Instr} (hCode : kernel.code[e.pc]? = some ins) :
      (!atomicOp ins.op && (!writeOp ins.op || e.pc == 977 || e.pc == 1223)) = true := by
    have hGet : ((kernel.code.drop 957).take (1240 - 957))[e.pc - 957]? = some ins := by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hPc.1]
      exact hCode
    have hIndex : (((kernel.code.drop 957).take (1240 - 957)).zipIdx 957)[e.pc - 957]? =
        some (ins, e.pc) := by
      rw [List.getElem?_zipIdx, hGet]
      simp [Nat.add_sub_of_le hPc.1]
    exact List.all_eq_true.mp hChecked _ (List.mem_of_getElem? hIndex)
  rcases hA with ⟨_, _, hFalse⟩ | ⟨data, ⟨pc, hGet⟩, _⟩ | ⟨old, new, pc, hGet⟩
  · cases hFalse
  · obtain rfl := Option.some.inj (he.symm.trans hGet)
    rcases get_source hX he with ⟨_, h⟩ | ⟨_, ins, _, _, hCode, hf⟩
    · cases h
    have hSite : pc = 977 ∨ pc = 1223 := by
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
        decide ((s.accessPc = 977 ∨ s.accessPc = 1223) → s.array.val < 2)) = true := by
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
and row cells therefore still contain their actual refresh bytes during the warm V save loop. -/
theorem warmValuePageWordsLatest {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pos batch row stop : Nat} {s : TState} {ending : Option TState}
    (hFirst : WarmPageWords p l X g pos batch row 0)
    (hSecond : WarmPageWords p l X g (pos + primingScratchReads p batch row + 2)
      batch (row + 64) 1)
    (hs : At s 957 [])
    (hr : Run kernel Assumptions.all l g s
      ((X.tr g).drop (pos + primingScratchReads p batch row + 2 +
        primingScratchReads p batch (row + 64) + 2)) ending)
    (hRank : ((X.tr g).take stop).countP Execution.isShfl ≤
      ((X.tr g).take (pos + primingScratchReads p batch row + 2 +
        primingScratchReads p batch (row + 64) + 2)).countP Execution.isShfl + 32)
    (slot : Fin 2) (target : Bool) :
    let second := pos + primingScratchReads p batch row + 2
    let write := (if slot.val = 0 then pos + primingScratchReads p batch row
        else second + primingScratchReads p batch (row + 64)) + if target then 1 else 0
    ∀ byte < 4, ∀ j < stop, ∀ a, X.Access (g, j) a true →
      a.Covers ((pageRefreshAccess l g 0 target slot).loc.at byte) → j ≤ write := by
  intro second write byte hByte j hj a hAccess hCover
  let start := second + primingScratchReads p batch (row + 64) + 2
  by_cases hBefore : j < start
  · exact warmPageWordsLatestAtExit hFirst hSecond slot target byte hByte j hBefore a hAccess hCover
  have hAudit (bound : Nat) : ((kernel.code.drop 957).take (1240 - 957)).all
      (fun ins => loaderPipelineCutOp 957 1240 bound [] ins.op) = true := by kernel_rfl
  have hRanked : (((kernel.code.drop 957).take (1240 - 957)).zipIdx 957).all
      (fun (ins, pc) => LoaderRankedInstr 1240 pc ins) = true := by kernel_rfl
  have hCount : loaderShuffleTail 1240 957 = 33 := by kernel_rfl
  have hFew : ((X.tr g).take j).countP Execution.isShfl <
      ((X.tr g).take start).countP Execution.isShfl + loaderShuffleTail 1240 957 := by
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
  exact (noWarmMetaWriteAfterPageLoop hp hX he hBounds hAccess slot target hByte hCover).elim

end
end PTX.Kernels.TmlFa4Fwd.Loader
