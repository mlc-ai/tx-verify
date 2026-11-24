-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderLocalAccess
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Flow.Code.Part029
import Lemmas.Step.CtaBar

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader.LocalAccessCode
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue
open PTX.Kernels.TmlFa4Fwd.Loader (RingShape pipelineAtCut pipelineCutStep ringShapeOfAt)

noncomputable section

def DoesNotClobber (cell : Acc) (e : Event) : Prop :=
  ∀ dst data, e.kind = .wr dst data → ¬ cell.Overlap dst

/-- A save to an exact cell and the suffix that keeps this saved value live. -/
def LatestCellWrite (pc : Nat) (cell : Acc) (history : List Event) : Prop :=
  ∃ before data tail, history = before ++ ⟨pc, .wr cell data⟩ :: tail ∧
    ∀ e ∈ tail, DoesNotClobber cell e

theorem LatestCellWrite.step {pc : Nat} {cell : Acc} {history : List Event}
    {ev : Option Event} (h : LatestCellWrite pc cell history)
    (hKeep : ∀ e ∈ ev.toList, DoesNotClobber cell e) :
    LatestCellWrite pc cell (history ++ ev.toList) := by
  obtain ⟨before, data, tail, rfl, hTail⟩ := h
  refine ⟨before, data, tail ++ ev.toList, by simp, ?_⟩
  intro e hm
  rcases List.mem_append.mp hm with h | h
  · exact hTail e h
  · exact hKeep e h

/-- Turn a save in the actual prefix into an indexed latest writer for every byte of its cell. -/
theorem LatestCellWrite.record {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g index pc : Nat} {cell a : Acc} {bs : List (Option Byte)}
    (hr : X.Reads (g, index) a bs)
    (hLatest : LatestCellWrite pc cell ((X.tr g).take index)) :
    ∃ write data, write < index ∧
      X.get (g, write) = some ⟨pc, .wr cell data⟩ ∧
      ∀ byte < cell.size, ∀ j dst, X.Access (g, j) dst true →
        dst.Covers (cell.loc.at byte) → j ≤ write ∨ index < j := by
  obtain ⟨site, he⟩ := hr
  obtain ⟨before, data, tail, hTrace, hNoClobber⟩ := hLatest
  have hLen : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hCut : index = before.length + (1 + tail.length) := by
    simpa [List.length_take, Nat.min_eq_left hLen.le, Nat.add_comm] using
      congrArg List.length hTrace
  have hWrite : X.get (g, before.length) = some ⟨pc, .wr cell data⟩ := by
    change (X.tr g)[before.length]? = _
    rw [← List.getElem?_take_of_lt (by omega : before.length < index), hTrace]
    simp
  refine ⟨before.length, data, by omega, hWrite, ?_⟩
  intro byte hByte j dst hAccess hCover
  by_contra! hBad
  obtain ⟨hBefore, hAfter⟩ := hBad
  rcases hAccess with ⟨_, _, hf⟩ | ⟨other, ⟨pos, he'⟩, _⟩ | ⟨old, new, hRmw⟩
  · cases hf
  · have hNe : j ≠ index := by
      intro hEq
      subst j
      rw [he] at he'
      cases he'
    have hBound : j < index := by omega
    have hE : (before ++ ⟨pc, .wr cell data⟩ :: tail)[j]? = some ⟨pos, .wr dst other⟩ := by
      rw [← hTrace, List.getElem?_take_of_lt hBound]
      exact he'
    have hTail : tail[j - (before.length + 1)]? = some ⟨pos, .wr dst other⟩ := by
      rw [List.getElem?_append_right (by omega : before.length ≤ j)] at hE
      have hJ : j - before.length = (j - (before.length + 1)) + 1 := by omega
      rwa [hJ] at hE
    exact hNoClobber _ (List.mem_of_getElem? hTail) dst other rfl
      ⟨_, Acc.covers_at hByte, hCover⟩
  · exact noActualRmw hX hRmw

/-- A history invariant sees each performed event and the actual frame before that event. -/
def HistoryStep (l : Launch) (g : Nat) (Inv : TState → List Event → Prop) : Prop :=
  ∀ {s u : TState} {ev : Option Event} {history : List Event},
    174 ≤ s.pc → s.pc < 1901 → RingShape s → addressInvariant l s →
    Inv s history → WStep kernel Assumptions.all l g s ev u → Inv u (history ++ ev.toList)

private theorem framedWalk {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {warp : Fin 2} {g : Nat} {s : TState} {events : List Event}
    {visits : List Visit} (hw : Walk kernel Assumptions.all l g s events visits)
    (hLo : 174 ≤ s.pc) (hHi : s.pc ≤ 1901) (hShape : RingShape s)
    (hRoots : Holds s.regs (roots l warp)) (hIndex : indexInvariant s)
    (hAddress : addressInvariant l s)
    (Inv : TState → List Event → Prop) (hStep : HistoryStep l g Inv)
    {history : List Event} (hHistory : Inv s history)
    {j : Nat} {e : Event} (he : events[j]? = some e) (hEnd : e.pc < 1901) :
    ∃ t o, t.pc = e.pc ∧ RingShape t ∧ Holds t.regs (roots l warp) ∧
      addressInvariant l t ∧ Inv t (history ++ events.take j) ∧
      EStep kernel Assumptions.all l g t e o := by
  have tail {s : TState} {es : List Event} {vs : List Visit}
      (hW : Walk kernel Assumptions.all l g s es vs) (hPc : s.pc = 1901)
      (hSh : RingShape s) (hRt : Holds s.regs (roots l warp))
      (hf : s.fault = none) (hE : e ∈ es) : False := by
    have ht := pipelineAtCut hPc hSh hRt hf ⟨_, Flow.code_1901, rfl⟩
    have hRole : At s 1901 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] :=
      ht.mono ⟨hRt.1, hRt.2.1, trivial⟩
    have he := Epilogue.loaderTailEventPcs warp hRole hW e hE
    omega
  have advance {s t : TState} {history : List Event} {ev : Option Event}
      (hw : WStep kernel Assumptions.all l g s ev t)
      (hL : 174 ≤ s.pc) (hH : s.pc < 1901)
      (hShape : RingShape s) (hR : Holds s.regs (roots l warp))
      (hI : indexInvariant s) (hA : addressInvariant l s) (hW : Inv s history) :
      174 ≤ t.pc ∧ t.pc ≤ 1901 ∧ RingShape t ∧ Holds t.regs (roots l warp) ∧
      indexInvariant t ∧ addressInvariant l t ∧ Inv t (history ++ ev.toList) := by
    have cert : ((kernel.code.drop 174).take (1901 - 174)).all (fun ins =>
        Loader.loaderPipelineCutOp 174 1901 t.pc ((roots l warp).map Prod.fst) ins.op) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    obtain ⟨hL', hH', hS', hR'⟩ := pipelineCutStep (by decide) (by decide) ⟨hL, hH⟩ cert
      hw hShape hR
    exact ⟨hL', hH'.resolve_right (Nat.lt_irrefl _), hS', hR', indexStep hL hH hI hw,
      addressStep hL hH hp.localMemory.2.1 hR hI hA hw, hStep hL hH hShape hA hW hw⟩
  induction hw generalizing j history with
  | stop => simp at he
  | @tau s u es vs ht hw ih =>
    by_cases hTail : s.pc = 1901
    · obtain ⟨_, _, hf, _⟩ := Softmax.tauScoreSource ht
      exact (tail (.tau ht hw) hTail hShape hRoots hf (List.mem_of_getElem? he)).elim
    obtain ⟨hL', hH', hS', hR', hI, hA, hW⟩ :=
      advance (.inl ⟨rfl, ht⟩) hLo (by omega) hShape hRoots hIndex hAddress hHistory
    exact ih hL' hH' hS' hR' hI hA (by simpa using hW) he
  | @ev s u ev es vs he' hw ih =>
    cases j with
    | zero =>
      obtain rfl : e = ev := by simpa using he.symm
      exact ⟨s, some u, (estep_source_pc he').symm, hShape, hRoots, hAddress,
        by simpa using hHistory, he'⟩
    | succ j =>
      by_cases hTail : s.pc = 1901
      · have hf : s.fault = none := by
          obtain ⟨tm, hout, hFire⟩ := he'
          cases hf : s.fault
          · rfl
          · simp only [out, hf, Out.ev.injEq] at hout
            subst tm
            cases hFire.2
        exact (tail (.ev he' hw) hTail hShape hRoots hf (List.mem_of_getElem? he)).elim
      obtain ⟨hL', hH', hS', hR', hI, hA, hW⟩ :=
        advance (.inr ⟨ev, rfl, he'⟩) hLo (by omega) hShape hRoots hIndex hAddress hHistory
      have hTailGet : es[j]? = some e := he
      simpa only [List.take_succ_cons, Option.toList_some, List.append_assoc, List.singleton_append]
        using ih hL' hH' hS' hR' hI hA hW hTailGet
  | @last s ev he' =>
    have hJ : j = 0 := by have := (List.getElem?_eq_some_iff.mp he).1; simp at this; omega
    subst j
    obtain rfl : e = ev := by simpa using he.symm
    exact ⟨s, none, (estep_source_pc he').symm, hShape, hRoots, hAddress,
      by simpa using hHistory, he'⟩

/-- Recover an invariant of the actual prefix at a loader memory event. -/
theorem historyAtLoaderEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {e : Event} (he : X.get (g, j) = some e)
    (hRange : 506 ≤ e.pc ∧ e.pc < 1901)
    (Inv : TState → List Event → Prop)
    (hInitial : ∀ s hist, s.pc = 174 → Inv s hist) (hStep : HistoryStep l g Inv) :
    ∃ (t : TState) (o : Option TState) (warp : Fin 2),
      t.pc = e.pc ∧ RingShape t ∧ Holds t.regs (roots l warp) ∧
      addressInvariant l t ∧ Inv t ((X.tr g).take j) ∧
      EStep kernel Assumptions.all l g t e o := by
  have hHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hWarp : 14 ≤ warpIndex l g := by
    rcases roleBodyPcOfEvent hp hX he (by omega) hHint with h | h
    · omega
    · split_ifs at h <;> omega
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hWord : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hWarp
  have hg := Step.CtaBar.thread_lt_of_get hX he
  have hNZ : 0 < warpIndex l g := Nat.lt_of_lt_of_le (by decide : 0 < 14) hWarp
  obtain ⟨s, _, hn, hs, hr⟩ := nonzeroCommonPrefixOfLateEvent hp hX hg hNZ he (by omega)
  have hR : Holds s.regs (roots l warp) := by
    refine ⟨hs.2.2.2.2.2.1, hWord.symm ▸ hs.2.2.2.2.1, ?_, ?_, ?_, ?_, trivial⟩
    all_goals
      apply holds_mem hs.2.2.2.2
      simp [nonzeroBarrierFacts, abiFacts]
  obtain ⟨_, hw⟩ := Mma.walkFromRun hr
  have inside : ((X.tr g).drop 5)[j - 5]? = some e := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hn]
    exact he
  have hJoin : (X.tr g).take 5 ++ ((X.tr g).drop 5).take (j - 5) = (X.tr g).take j := by
    conv_rhs => rw [← List.take_append_drop 5 ((X.tr g).take j)]
    rw [List.take_take, Nat.min_eq_left hn, List.drop_take]
  obtain ⟨t, o, ht, hShape, hRoots, hAddr, hInv, hNext⟩ :=
    framedWalk hp (warp := warp) hw (by rw [hs.1]) (by rw [hs.1]; decide)
      (ringShapeOfAt hs) hR (indexInitial hs.1) (addressInitial hs.1) Inv hStep
      (hInitial s ((X.tr g).take 5) hs.1) inside hRange.2
  exact ⟨t, o, warp, ht, hShape, hRoots, hAddr, hJoin ▸ hInv, hNext⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader.LocalAccessCode
