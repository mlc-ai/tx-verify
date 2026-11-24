-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairCompletionFrame
public import Lemmas.Tmem.TmemPairHistory

@[expose] public section

namespace PTX.Tmem.Pair
noncomputable section

private theorem get_old {X Y : Execution}
    (htr : ∀g,X.tr g <+: Y.tr g) {i : EvId} {ev : Event}
    (hb : i.2<(X.tr i.1).length) (he : Y.get i=some ev) : X.get i=some ev := by
  obtain ⟨suffix,hs⟩ := htr i.1
  change (Y.tr i.1)[i.2]?=some ev at he
  rwa [←hs,List.getElem?_append_left hb] at he

private theorem tcK_old {X Y : Execution}
    (htr : ∀g,X.tr g <+: Y.tr g) {i : EvId} {k : Nat}
    (hb : i.2<(X.tr i.1).length) (hk : Y.TcK i k) : X.TcK i k := by
  obtain ⟨⟨ev,he,hcoll⟩,hc⟩ := hk
  refine ⟨⟨ev,get_old htr hb he,hcoll⟩,?_⟩
  obtain ⟨suffix,hs⟩ := htr i.1
  rwa [←hs,List.take_append_of_le_length hb.le] at hc

/-- All source lanes of an earlier request are old whenever its later owner
warp is already actual in the old execution. -/
theorem completion_warp_valid_of_growth_before {L : Launch} {X Y : Execution}
    (htr : ∀g,X.tr g <+: Y.tr g) {early late : WarpRequest}
    {earlyGroup lateGroup : CtaGroup} (he : early.Valid L Y earlyGroup)
    (hl : late.Valid L X lateGroup) (hb : early.Before late) :
    early.Valid L X earlyGroup := by
  have hbound (lane : Fin 32) : (early.event L lane).2 <
      (X.tr (early.event L lane).1).length := by
    have hget := hl.2.2.1 lane
    have hlen := (List.getElem?_eq_some_iff.mp hget).1
    have hidx := hb.2.2 lane
    have hg : (early.event L lane).1=(late.event L lane).1 := by
      simp only [WarpRequest.event,hb.1,hb.2.1]
    rw [hg]
    exact Nat.lt_trans hidx hlen
  obtain ⟨hcta,hwarp,hget,k,hk⟩ := he
  exact ⟨hcta,hwarp,fun lane=>get_old htr (hbound lane) (hget lane),k,
    fun lane=>tcK_old htr (hbound lane) (hk lane)⟩

/-- Every nonresource-completion extension transports the law using only
source prefixes, unchanged histories and pairings, and actual old origins. -/
theorem completionClosed_of_trace_growth {L : Launch} {X Y : Execution}
    (htr : ∀g,X.tr g <+: Y.tr g)
    (hhistory : Y.tmemHistory=X.tmemHistory) (hpairing : Y.tmemPairing=X.tmemPairing)
    (hactual : HistoriesOk L X)
    (hX : CompletionClosed L X) : CompletionClosed L Y := by
  intro ws hws w hw w' group hv hb i hp
  have hold : Completed X ws := by simpa only [Completed,hhistory,hpairing] using hws
  obtain ⟨g,hwv⟩ := hold.valid hactual hw
  have hc := hX ws hold w hw w' group (completion_warp_valid_of_growth_before htr hv hwv hb) hb i hp
  simpa only [Covered,Completed,hhistory,hpairing] using hc

/-- Execution.le supplies the required actual source-prefix transportation;
resource metadata growth is handled separately by append readiness. -/
theorem completionClosed_of_growth {L : Launch} {X Y : Execution}
    (hle : X.le Y) (hhistory : Y.tmemHistory=X.tmemHistory)
    (hpairing : Y.tmemPairing=X.tmemPairing)
    (hactual : HistoriesOk L X) (hX : CompletionClosed L X) : CompletionClosed L Y :=
  completionClosed_of_trace_growth hle.1 hhistory hpairing hactual hX
end
end PTX.Tmem.Pair
