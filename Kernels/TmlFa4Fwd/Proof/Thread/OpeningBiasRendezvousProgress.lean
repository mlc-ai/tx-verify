-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SelectedOpeningBiasReads
public import Kernels.TmlFa4Fwd.Proof.PrologueFenceProgress
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasRendezvous
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Lemmas.Step.Object
public import Kernels.TmlFa4Fwd.Proof.Thread.FirstBiasRendezvous

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Prologue Thread

private theorem biasProxyCanIssue {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hNonempty : X.tr g ≠ []) (hReleased : Step.Released l X g) {t u : TState}
    (hRun : Run kernel Assumptions.all l g {} (X.tr g) (some t))
    (hTau : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u)
    {site : Nat} {proxy : ProxyFence}
    (hStep : EStep kernel Assumptions.all l g u ⟨site,.fenceProxy proxy none⟩ (some (next u))) :
    ∃ Y, Consistent l kernel Assumptions.all m Y ∧ X.le Y ∧ X.size l < Y.size l := by
  let e : Event := ⟨site,.fenceProxy proxy none⟩
  let Y := X.snoc g e (fun _ => none)
  have hTc : ∀ k, e.kind ≠ .tc k := by intro _ h; cases h
  have hWait : e.kind.WaitFree := ⟨trivial,hTc⟩
  have hShuffle : ∀ mode a b mask recv ok, e.kind ≠ .shfl mode a b mask recv ok := by
    intro _ _ _ _ _ _ h
    cases h
  have hRead : ∀ a bs, e.kind ≠ .rd a bs := by intro _ _ h; cases h
  have hWrite : ∀ a bs, e.kind ≠ .wr a bs := by intro _ _ h; cases h
  have hAtomic : ∀ a old new, e.kind ≠ .rmw a old new := by intro _ _ _ h; cases h
  have hOld {a b : EvId} (hb : b.2 < (X.tr b.1).length) :
      baseCausality l Y a b ↔ baseCausality l X a b :=
    Step.snoc_baseCausality_old hX.effectValidity hX.cluster
      (by intro _ _ _ h; cases h) (by intro _ _ h; cases h) (.of_rfWf hX.rf)
      (by intro _ h; cases h) hb
  have hVisibility loc v f (hf : X.RefPresent f) :
      modelCausality l Y loc v f ↔ modelCausality l X loc v f :=
    Kind.AsyncSilent.modelCausality_snoc_old (by trivial) hOld
      (snoc_allocResultBefore_old hX.dependency.ready) (refPresent_issuer_lt hX.effectValidity hf)
  refine ⟨Y,?_,le_snoc,?_⟩
  · refine consistent_snoc_preserving hX hg hRun hTau hStep hShuffle
      (by intro h; cases h) hReleased.ready (Step.snoc_new_ready hWait hShuffle rfl rfl)
      (fun _ _ _ hv => (snoc_memReads_control hX.effectValidity hTc hRead hAtomic).mp hv)
      (fun _ _ _ => snoc_memWrites_control hX.effectValidity hWrite hAtomic) hVisibility
      (snoc_plain_orderOk hX hWait hShuffle (by intro h; cases h) rfl rfl
        (by intro _ _ _ _ h; cases h) (fun a old new h => (hAtomic a old new h).elim))
      (Assumptions.wfStep.quiet hX le_snoc rfl (Execution.noNewRead_snoc rfl))
      (hX.tmaOk_snoc_unobserved hTc (by intro loc; simp [AsyncCopy.objectAction,snoc_get_new,e]))
      (ExtensionObligations.snoc_plain hX trivial (.inl hNonempty) (by intro h; cases h)
        hAtomic rfl (by intro _ h; cases h)
        (hX.tmemPairResult.snoc_not_wr fun _ _ _ h => hWrite _ _ (congrArg Event.kind h)))
  · change X.size l < (X.snoc g e (fun _ => none)).size l
    rw [size_snoc hX hg (show e.counts = true from rfl)]
    omega

private theorem biasFenceOfMaximal {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (repeated : Bool)
    {F : List (Nat × Value)} {ending : Option TState}
    (c : OpeningLaneCursor l X g (biasFencePc repeated) F ending) :
    X.get (g,c.pos) = some
        ⟨biasFencePc repeated,.fenceProxy (.async (some (.shared .cta))) none⟩ ∧
    Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+1)) (some (next c.ready)) ∧
    Run kernel Assumptions.all l g (next c.ready) ((X.tr g).drop (c.pos+1)) ending := by
  let proxy : ProxyFence := .async (some (.shared .cta))
  let e : Event := ⟨c.ready.pc,.fenceProxy proxy none⟩
  have hOut := biasFenceTemplate (l := l) (g := g) repeated c.checkpoint
  have hEvent : EStep kernel Assumptions.all l g c.ready e (some (next c.ready)) :=
    ⟨_,hOut,rfl,rfl⟩
  have hLt : c.pos < (X.tr g).length := by
    by_contra! hLong
    have hEnd := Nat.le_antisymm c.bounded hLong
    have hStarted : X.tr g ≠ [] := by
      intro h
      have hPos := c.positive
      rw [h,List.length_nil] at hEnd
      omega
    have hPrefix := c.recorded
    rw [List.take_of_length_le hLong] at hPrefix
    apply hMax.not_grows
    exact biasProxyCanIssue hMax.1 hg hStarted (c.released hEnd) hPrefix c.localSteps hEvent
  have hTail := c.continuation
  rw [List.drop_eq_getElem_cons hLt] at hTail
  have hNext : Next kernel Assumptions.all l g c.before c.ready
      (.fenceProxy proxy none (next c.ready)) := ⟨c.localSteps,hOut⟩
  obtain ⟨_,⟨hGet,hReturned⟩,hRest⟩ := hNext.continuing_event
    (by rintro ⟨_,h⟩; cases h) hTail
  obtain rfl := Option.some.inj hReturned
  refine ⟨?_,?_,hRest⟩
  · change (X.tr g)[c.pos]? = _
    rw [List.getElem?_eq_getElem hLt,hGet,c.checkpoint.1]
  · rw [List.take_succ_eq_append_getElem hLt,hGet]
    exact c.recorded.snoc c.localSteps hEvent

/-- At the real Bias fence cursor, a maximal lane records the proxy fence and then
the rendezvous arrival. The selector for that arrival leaves the loaded operands live. -/
theorem biasRendezvousOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (warp : Fin 8) (repeated : Bool)
    {F : List (Nat × Value)} {ending : Option TState}
    (c : OpeningLaneCursor l X g (biasFencePc repeated) F ending)
    (hFrame : Holds c.ready.regs (biasFenceFacts l g warp repeated)) :
    ∃ u, X.get (g,c.pos) = some
        ⟨biasFencePc repeated,.fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      X.get (g,c.pos+1) = some
        ⟨biasFencePc repeated+2,.bar (11+(stageOf warp).val) (some 128) .sync⟩ ∧
      At u (biasFencePc repeated+3) (biasKeep l g warp repeated) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+2)) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (c.pos+2)) ending ∧
      ∀ r, r ≠ biasBarReg repeated → u.regs r = c.ready.regs r := by
  obtain ⟨hFence,hPast,hTail⟩ := biasFenceOfMaximal hMax hg repeated c
  obtain ⟨v,hReplay,hV⟩ := (biasBarSetup l g warp repeated).apply
    (c.checkpoint.mono hFrame).next
  let id := 11+(stageOf warp).val
  let e : Event := ⟨v.pc,.bar id (some 128) .sync⟩
  have hOut := biasBarTemplate hp.block warp repeated hV
  have hLocal := run_rtg hReplay
  have hEvent : EStep kernel Assumptions.all l g v e (some (next v)) := ⟨_,hOut,rfl,rfl⟩
  have hBound := len_of_get hFence
  have hLt : c.pos+1 < (X.tr g).length := by
    by_contra! hLong
    have hEnd : c.pos+1 = (X.tr g).length := Nat.le_antisymm hBound hLong
    have hStarted : X.tr g ≠ [] := by intro h; rw [h,List.length_nil] at hEnd; omega
    have hReady := releasedIfLast (l := l) hFence (by intro h; cases h) hEnd
    rw [List.take_of_length_le hLong] at hPast
    exact hMax.not_grows (Step.bar_counted_extension hMax.1 hg (.inl hStarted) hReady
      (Assumptions.wfStep.quiet hMax.1 le_snoc rfl
        (Execution.noNewRead_snoc rfl)) hPast hLocal hEvent)
  rw [List.drop_eq_getElem_cons hLt] at hTail
  have hNext : Next kernel Assumptions.all l g (next c.ready) v
      (.bar id (next v) (some 128) .sync) := ⟨hLocal,hOut⟩
  obtain ⟨_,⟨hRead,hReturned⟩,hRest⟩ := hNext.continuing_event
    (by rintro ⟨_,h⟩; cases h) hTail
  obtain rfl := Option.some.inj hReturned
  have hCount : c.pos+1+1 = c.pos+2 := by omega
  refine ⟨next v,hFence,?_,hV.next.mono hV.2.2.2.2.2,?_,hCount ▸ hRest,?_⟩
  · change (X.tr g)[c.pos+1]? = _
    rw [List.getElem?_eq_getElem hLt,hRead,hV.1]
  · rw [← hCount,List.take_succ_eq_append_getElem hLt,hRead]
    exact hPast.snoc hLocal hEvent
  · exact biasBarSetupFrame (t := next c.ready) (u := v) repeated
      (c.checkpoint.mono hFrame).next.1 hReplay

/-- The first Bias rendezvous records the proxy fence before the stage arrival,
with all the selected Bias operands still live in the return state. -/
structure OpeningBiasArrivalLane (p : Params) (l : Launch) (X : Execution)
    (g batch : Nat) (stage : Fin 2) (wait : Nat) where
  loaded : OpeningBiasReadLane p l X g batch stage wait
  state : TState
  fence : X.get (g,wait+65) = some ⟨3581,.fenceProxy (.async (some (.shared .cta))) none⟩
  arrival : X.get (g,wait+66) = some ⟨3583,.bar (11+stage.val) (some 128) .sync⟩
  initial : observedBarrierOrdinal X (g,wait+66) (11+stage.val) = 0
  ready : At state 3584 (biasKeep l g loaded.opening.warp false)
  recorded : Run kernel Assumptions.all l g {} ((X.tr g).take (wait+67)) (some state)
  continuation : Run kernel Assumptions.all l g state ((X.tr g).drop (wait+67))
    loaded.opening.ending
  unpacked : ∀ i, BiasUnpacked false i state (openingBiasWord p l g batch stage i)
  scores : OpeningScoreBeforeBias l X g stage state
  frame : ∀ r, r ≠ biasBarReg false → state.regs r = loaded.cursor.ready.regs r

/-- The actual loaded Bias state drives an arrival at the first stage rendezvous. -/
theorem OpeningBiasReadLane.arrivalOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch wait : Nat} {stage : Fin 2} (hg : g < l.threads)
    (loaded : OpeningBiasReadLane p l X g batch stage wait) :
    Nonempty (OpeningBiasArrivalLane p l X g batch stage wait) := by
  let c := loaded.cursor
  let warp := loaded.opening.warp
  have hFrame : Holds c.ready.regs (biasFenceFacts l g warp false) := by
    have hAll := c.checkpoint.2.2.2.2
    simp only [openingScoreReturnedFacts,singleVisitGeometryCarry,holds_append] at hAll
    exact hAll.2.2
  obtain ⟨u,hFence,hArrival,hAt,hRecorded,hCont,hRegs⟩ :=
    biasRendezvousOfMaximal hp hMax hg warp false c hFrame
  have hPos : c.pos = wait+65 := loaded.position
  rw [hPos] at hFence hArrival hRecorded hCont
  have hStage : stageOf warp = stage := loaded.opening.selectedStage
  rw [hStage] at hArrival
  have hInitial := Thread.Scores.firstBiasBarrierOrdinal hp hMax.1 stage hArrival
  refine ⟨⟨loaded,u,hFence,hArrival,hInitial,hAt,hRecorded,hCont,?_,?_,hRegs⟩⟩
  · intro i k hk
    have hLeft : (biasUnpackRegs false i k).1 ≠ biasBarReg false := by
      have hi := i.isLt
      simp only [biasUnpackRegs,biasUnpackTop,biasBarReg,Bool.false_eq_true,ite_false]
      omega
    have hRight : (biasUnpackRegs false i k).2 ≠ biasBarReg false := by
      have hi := i.isLt
      simp only [biasUnpackRegs,biasUnpackTop,biasBarReg,Bool.false_eq_true,ite_false]
      omega
    exact ⟨(hRegs _ hLeft).trans (loaded.unpacked i k hk).1,
      (hRegs _ hRight).trans (loaded.unpacked i k hk).2⟩
  · apply loaded.scores.withFrame
    intro q k _
    apply hRegs
    change 7303 + 16*q.val + k ≠ 3075
    omega

end PTX.Kernels.TmlFa4Fwd.Softmax
