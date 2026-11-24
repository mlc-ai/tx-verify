-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderReuseCheckpoint
public import Kernels.TmlFa4Fwd.Proof.LoaderArrivalSites
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Flow.Code.Part029

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.AsyncCopy Epilogue Prologue Softmax

noncomputable section

private def pastPriming : Fin 2 → Nat
  | 0 => 675
  | 1 => 905

private theorem pastPrimingBounds (first : Fin 2) :
    174 ≤ pastPriming first ∧ pastPriming first ≤ 1901 := by
  fin_cases first <;> decide

private theorem pastPrimingCode (first : Fin 2) :
    ((kernel.code.drop (pastPriming first)).take (1901 - pastPriming first)).all
      (fun ins => loaderPipelineCutOp (pastPriming first) 1901 1901 [] ins.op) = true := by
  fin_cases first <;> (set_option maxRecDepth 100000 in kernel_rfl)

private theorem publicationOutsideEgress {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} {e : Event} {loc : Loc}
    (warp : Fin 2) (hEq : s.pc = 1901) (hFrame : LoaderRingFrame l warp s)
    (hw : Walk kernel Assumptions.all l g s es vs) (hMem : e ∈ es)
    (hKind : e.kind = .asyncArrive loc true) (hEarly : e.pc < 1901) : False := by
  have hClean := walkWithArrivalClean hw hMem hKind
  have hAt := pipelineAtCut hEq hFrame.1 hFrame.2.1 hClean ⟨_, Flow.code_1901, rfl⟩
  have hOut := loaderTailEventPcs warp hAt hw e hMem
  omega

private theorem staysPastPriming {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (warp : Fin 2) (first : Fin 2)
    {s : TState} {es : List Event} {vs : List Visit} {e : Event} {loc : Loc}
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hPc : pastPriming first ≤ s.pc ∧ s.pc ≤ 1901) (hF : LoaderRingFrame l warp s)
    (hMem : e ∈ es) (hKind : e.kind = .asyncArrive loc true) (hEarly : e.pc < 1901) :
    pastPriming first ≤ e.pc := by
  have step {s u : TState} {ev : Option Event} {es : List Event} {vs : List Visit}
      (hStep : WStep kernel Assumptions.all l g s ev u)
      (hW : Walk kernel Assumptions.all l g s (ev.toList ++ es) (visit kernel l g s ev :: vs))
      (hPC : pastPriming first ≤ s.pc ∧ s.pc ≤ 1901) (hFrame : LoaderRingFrame l warp s)
      (hE : e ∈ es)
      (ih : (pastPriming first ≤ u.pc ∧ u.pc ≤ 1901) →
        LoaderRingFrame l warp u → e ∈ es → pastPriming first ≤ e.pc) :
      pastPriming first ≤ e.pc := by
    by_cases he : s.pc = 1901
    · exact (publicationOutsideEgress warp he hFrame hW (List.mem_append_right _ hE)
        hKind hEarly).elim
    obtain ⟨_, hh, hf⟩ := loaderRingStep hp ((pastPrimingBounds first).1.trans hPC.1)
      (by omega) hFrame hStep
    have hLo := (pipelineCutStep (branch := 1901) (F := [])
      (pastPrimingBounds first).1 (by decide : 1901 ≤ 1901)
      ⟨hPC.1, by omega⟩ (pastPrimingCode first) hStep hFrame.1 (by trivial)).1
    exact ih ⟨hLo, hh⟩ hf hE
  induction hw with
  | stop => cases hMem
  | tau h hw ih =>
    exact step (.inl ⟨rfl, h⟩) (.tau h hw) hPc hF hMem ih
  | ev h hw ih =>
    rcases List.mem_cons.mp hMem with rfl | hMem
    · rw [estep_source_pc h]
      exact hPc.1
    · exact step (.inr ⟨_, rfl, h⟩) (.ev h hw) hPc hF hMem ih
  | last h =>
    obtain rfl := List.mem_singleton.mp hMem
    rw [estep_source_pc h]
    exact hPc.1

private theorem publicationThreshold {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (warp : Fin 2) (first : Fin 2) (site : Fin 6)
    {s : TState} {es : List Event} {vs : List Visit} {a b : Loc} {pc : Nat}
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hPc : 174 ≤ s.pc ∧ s.pc ≤ 1901) (hF : LoaderRingFrame l warp s)
    {i j : Nat} (hi : es[i]? = some ⟨copyCommitPc site + 1, .asyncArrive a true⟩)
    (hj : es[j]? = some ⟨pc, .asyncArrive b true⟩) (hEarlier : i < j)
    (hHigh : pastPriming first ≤ copyCommitPc site + 2) (hLate : pc < 1901) :
    pastPriming first ≤ pc := by
  have hSite : copyCommitPc site + 1 < 1901 := by fin_cases site <;> decide
  have step {s u : TState} {ev : Option Event} {es : List Event} {vs : List Visit}
      (hW : WStep kernel Assumptions.all l g s ev u)
      (hFull : Walk kernel Assumptions.all l g s (ev.toList ++ es) (visit kernel l g s ev :: vs))
      (hPC : 174 ≤ s.pc ∧ s.pc ≤ 1901) (hFrame : LoaderRingFrame l warp s)
      (hMem : ∃ e ∈ es, e.pc = copyCommitPc site + 1 ∧ e.kind = .asyncArrive a true)
      (ih : (174 ≤ u.pc ∧ u.pc ≤ 1901) → LoaderRingFrame l warp u → pastPriming first ≤ pc) :
      pastPriming first ≤ pc := by
    by_cases hx : s.pc = 1901
    · obtain ⟨e, he, hSrc, hType⟩ := hMem
      exact (publicationOutsideEgress warp hx hFrame hFull (List.mem_append_right _ he)
        hType (hSrc ▸ hSite)).elim
    obtain ⟨hlo, hhi, hf⟩ := loaderRingStep hp hPC.1 (by omega) hFrame hW
    exact ih ⟨hlo, hhi⟩ hf
  induction hw generalizing i j with
  | stop => simp at hi
  | tau h hw ih =>
    exact step (.inl ⟨rfl, h⟩) (.tau h hw) hPc hF
      ⟨_, List.mem_of_getElem? hi, rfl, rfl⟩ (fun hPc' hF' => ih hPc' hF' hi hj hEarlier)
  | @ev t u e es vs h hw ih =>
    cases i with
    | zero =>
      obtain rfl := Option.some.inj hi
      have ht : t.pc = copyCommitPc site + 1 := (estep_source_pc h).symm
      obtain ⟨_, hHi, hNext⟩ := loaderRingStep hp hPc.1 (by omega) hF (.inr ⟨_, rfl, h⟩)
      obtain ⟨_, _, hPc'⟩ := packetArrivalStep site ht h
      cases j with
      | zero => omega
      | succ j =>
        have hGet : es[j]? = some ⟨pc, .asyncArrive b true⟩ := hj
        exact staysPastPriming hp warp first hw ⟨hPc'.symm ▸ hHigh, hHi⟩ hNext
          (List.mem_of_getElem? hGet) rfl hLate
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        have hGet : es[i]? = some ⟨copyCommitPc site + 1, .asyncArrive a true⟩ := hi
        have hOther : es[j]? = some ⟨pc, .asyncArrive b true⟩ := hj
        exact step (.inr ⟨_, rfl, h⟩) (.ev h hw) hPc hF
          ⟨_, List.mem_of_getElem? hGet, rfl, rfl⟩
          (fun hPc' hF' => ih hPc' hF' hGet hOther (by omega))
  | last h =>
    cases j with
    | zero => omega
    | succ j => simp at hj

/-- Two actual publications of one producer to the same slot cannot end in a startup
packet. The two startup sites use different fixed slots and cannot be reentered. -/
theorem laterPublicationIsRecurring {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g prior index : Nat} {loc : Loc} (hlt : prior < index)
    (hPrior : X.AsyncArrive (g, prior) loc true) (hIssue : X.AsyncArrive (g, index) loc true) :
    ∃ site : Fin 4, X.get (g, index) = some ⟨reuseArrival site, .asyncArrive loc true⟩ := by
  obtain ⟨prev, he⟩ := hPrior
  obtain ⟨pc, he'⟩ := hIssue
  obtain ⟨⟨is, rfl⟩, _, _, _⟩ := actualAsyncArrival hX he
  obtain ⟨⟨js, rfl⟩, _, _, _⟩ := actualAsyncArrival hX he'
  have hPrev : 173 < copyCommitPc is + 1 := by fin_cases is <;> decide
  have hHint : copyCommitPc is + 1 ∉ registerHintSites := by fin_cases is <;> decide
  have hWarp : 14 ≤ warpIndex l g := by
    have hPc : copyCommitPc is + 1 ≤ 1735 := by fin_cases is <;> decide
    rcases roleBodyPcOfEvent hp hX he hPrev hHint with h | h
    · dsimp only at h
      omega
    · split_ifs at h <;> dsimp only at h <;> omega
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hWord : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hWarp
  have hg := event_thread_lt hX he
  obtain ⟨start, t, o, hStart, ht, hr⟩ := commonDispatchOfLateEvent hp hX hg he hPrev
  have hRoot : At t 174 (loaderRingRoots l warp) :=
    ht.mono ⟨ht.2.2.2.2.2.1, hWord.symm ▸ ht.2.2.2.2.1, trivial⟩
  obtain ⟨vs, hw⟩ := Mma.walkFromRun hr
  have hI : ((X.tr g).drop start)[prior - start]? =
      some ⟨copyCommitPc is + 1, .asyncArrive loc true⟩ := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hStart]
    exact he
  have hJ : ((X.tr g).drop start)[index - start]? =
      some ⟨copyCommitPc js + 1, .asyncArrive loc true⟩ := by
    rw [List.getElem?_drop, Nat.add_sub_of_le (hStart.trans hlt.le)]
    exact he'
  have hPC : 174 ≤ t.pc ∧ t.pc ≤ 1901 := by rw [ht.1]; decide
  have hFrame := loaderRingFrameAtDispatch hRoot
  have bound (b : Fin 2) (hB : pastPriming b ≤ copyCommitPc is + 2) :
      pastPriming b ≤ copyCommitPc js + 1 :=
    publicationThreshold hp warp b is hw hPC hFrame hI hJ (by omega) hB (by
      fin_cases js <;> decide)
  fin_cases js
  · have hB : pastPriming 0 ≤ copyCommitPc is + 2 := by fin_cases is <;> decide
    have h := bound 0 hB
    exact (by decide : ¬ pastPriming 0 ≤ copyCommitPc 0 + 1) h |>.elim
  · by_cases his : is = 0
    · subst is
      have hA := loaderStartupAsyncAddress hp hX he (by decide)
      have hB := loaderStartupAsyncAddress hp hX he' (by decide)
      have ha := congrArg Loc.addr (hA.symm.trans hB)
      simp [copyCommitPc] at ha
    · have hB : pastPriming 1 ≤ copyCommitPc is + 2 := by
        fin_cases is <;> contradiction
      have h := bound 1 hB
      exact (by decide : ¬ pastPriming 1 ≤ copyCommitPc 1 + 1) h |>.elim
  · exact ⟨0, he'⟩
  · exact ⟨1, he'⟩
  · exact ⟨2, he'⟩
  · exact ⟨3, he'⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
