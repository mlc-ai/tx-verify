-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxPriorMaximum
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxRecordedEntry
public import Kernels.TmlFa4Fwd.Proof.Thread.RescalePublicationFinite
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Lemmas.Execution.EventFrameSource
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningMaximumNotice
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedScoreWait
import Kernels.TmlFa4Fwd.Flow.Code.Part068

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof PTX.Flow PTX.EventFrame PTX.Kernels.TmlFa4Fwd.Softmax

private theorem event_eq {e : Event} {pc : Nat} {kind : Kind}
    (hPc : e.pc = pc) (hKind : e.kind = kind) : e = ⟨pc,kind⟩ := by
  cases e
  cases hPc
  cases hKind
  rfl

private theorem openingNoticeKind {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hs : s.pc = 4397) (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ id count mode, e.kind = .bar id count mode := by
  obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source he
  rw [hs,Flow.code_4397] at hCode
  obtain rfl := Option.some.inj hCode
  simp only [eventTmpl] at hFire
  unfold barTmpl at hFire
  repeat' split at hFire
  all_goals solve
    | exact ⟨_,_,_,congrArg Event.kind hFire.1⟩
    | cases hFire.2

/-- Earlier running maxima are read at the physical source states of their recorded stores. -/
def EarlierRescaleMaximums (l : Launch) (X : Execution) (g index : Nat) : Prop :=
  ∀ j < index, ∀ biased a bytes s o,
    StatisticsStore X (g,j) (rescaleStore biased) a bytes →
    TraceReach kernel Assumptions.all l g {} ((X.tr g).take j) s →
    EStep kernel Assumptions.all l g s ⟨(statsStore (rescaleStore biased)).pc,.wr a bytes⟩ o →
    CanonicalMaximum s 7256

/-- The opening notice and already visited rescale publications determine the maximum
frame at the next observed event, with the original initialization and event index. -/
theorem maximumFrameOfEarlierPublications {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g index : Nat} {target : Event} (he : X.get (g,index) = some target)
    (hLo : 3420 ≤ target.pc) (hHi : target.pc < 7742)
    (hEarlier : EarlierRescaleMaximums l X g index) :
    ∃ t o, TraceReach kernel Assumptions.all l g {} ((X.tr g).take index) t ∧
      MaximumFrame t ∧ EStep kernel Assumptions.all l g t target o := by
  obtain ⟨warp,hWarp,_,_,_,_,_,_⟩ := softmaxBodySuffix hp hX he hLo hHi
  obtain ⟨w,_,base,s,_,hIndex,hAt,hPath,hRun⟩ := softmaxRoleEntryRecorded hp hX he
    (by omega) (by omega) (hWarp ▸ warp.isLt)
  let Inv (j : Nat) (u : TState) :=
    TraceReach kernel Assumptions.all l g {} ((X.tr g).take j) u ∧
    (j ≤ index → MaximumFrame u)
  have hInit : Inv base s := ⟨hPath,fun _ => initialMaximumFrame hAt.1⟩
  have hStep {v u : TState} {ev : Option Event} {j : Nat}
      (hMin : 3103 ≤ v.pc) (hMax : v.pc < 7742) (hSub : v.sub ≤ 3)
      (hInv : Inv j v) (hW : WStep kernel Assumptions.all l g v ev u)
      (hGet : ∀ e, ev = some e → X.get (g,j) = some e) :
      Inv (j+ev.toList.length) u := by
    have hNext : TraceReach kernel Assumptions.all l g {}
        ((X.tr g).take (j+ev.toList.length)) u := by
      rcases hW with ⟨rfl,hTau⟩ | ⟨e,rfl,hEvent⟩
      · simpa only [Option.toList,List.length_nil,Nat.add_zero,List.append_nil] using
          hInv.1.append (.tau hTau (.refl _))
      · have hGet' := hGet e rfl
        change (X.tr g)[j]? = some e at hGet'
        simp only [Option.toList,List.length_singleton,List.take_add_one,hGet']
        exact hInv.1.append (.event hEvent (.refl _))
    refine ⟨hNext,fun hEnd => ?_⟩
    apply maximumFrameStep hMin hMax hSub (hInv.2 (by omega)) hW
    intro e hEvent hSite
    have hEStep : EStep kernel Assumptions.all l g v e (some u) := by
      rcases hW with ⟨hNone,_⟩ | ⟨k,hK,hFire⟩
      · rw [hEvent] at hNone
        cases hNone
      · obtain rfl := Option.some.inj (hEvent.symm.trans hK)
        exact hFire
    have hCurrent := hGet e hEvent
    rcases hSite with hOpen | hBias | hPlain
    · obtain ⟨id,count,mode,hKind⟩ := openingNoticeKind hOpen hEStep
      have hEq : e = ⟨4397,.bar id count mode⟩ :=
        event_eq ((estep_source_pc hEStep).trans hOpen) hKind
      have hOpenGet : X.get (g,j) = some ⟨4397,.bar id count mode⟩ := hEq ▸ hCurrent
      obtain ⟨w,mx,_,hAt,hReach,hAfter⟩ := openingMaximumOfNotice hp hX hFootprint hOpenGet
      have hOne : ((X.tr g).drop j)[0]? = some ⟨4397,.bar id count mode⟩ := by
        rwa [List.getElem?_drop,Nat.add_zero]
      obtain ⟨t,o,hLocal,hAtEvent⟩ := hAfter.before_event hOne
      have hStop : Stops kernel Assumptions.all l g w := by
        have hEq : t = w := by
          rcases hLocal with h | h | h
          · rfl
          · obtain ⟨i,hCode,_,hMode⟩ := tauScoreSource h
            rw [hAt.1,Flow.code_4397] at hCode
            obtain rfl := Option.some.inj hCode
            rcases hMode with ⟨_,hSkip⟩ | ⟨_,hIsLocal,_⟩
            · cases hSkip
            · cases hIsLocal
        exact hEq ▸ stops_of_estep hAtEvent
      have hV := reachedEventSourceUnique hInv.1 hReach (stops_of_estep hEStep) hStop
      exact ⟨mx,hV ▸ hAt.2.2.2.2.1⟩
    · have hs : v.pc = (statsStore (rescaleStore true)).pc := hBias
      obtain ⟨a,bytes,hKind⟩ := rescaleStoreEventKind true hs hEStep
      have hEq : e = ⟨(statsStore (rescaleStore true)).pc,.wr a bytes⟩ :=
        event_eq ((estep_source_pc hEStep).trans hs) hKind
      have hLess : j < index := by rw [hEvent] at hEnd; simp [Option.toList] at hEnd; omega
      exact hEarlier j hLess true a bytes v (some u)
        (by simpa only [StatisticsStore,hEq] using hCurrent) hInv.1 (hEq ▸ hEStep)
    · have hs : v.pc = (statsStore (rescaleStore false)).pc := hPlain
      obtain ⟨a,bytes,hKind⟩ := rescaleStoreEventKind false hs hEStep
      have hEq : e = ⟨(statsStore (rescaleStore false)).pc,.wr a bytes⟩ :=
        event_eq ((estep_source_pc hEStep).trans hs) hKind
      have hLess : j < index := by rw [hEvent] at hEnd; simp [Option.toList] at hEnd; omega
      exact hEarlier j hLess false a bytes v (some u)
        (by simpa only [StatisticsStore,hEq] using hCurrent) hInv.1 (hEq ▸ hEStep)
  obtain ⟨u,o,hInv,hEvent⟩ := softmaxRoleReplayFromEntry hp w hAt hRun he hIndex hHi Inv hInit hStep
  exact ⟨u,o,hInv.1,hInv.2 le_rfl,hEvent⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
