-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.SoftmaxProbabilityReuse
import Kernels.TmlFa4Fwd.Proof.MbarSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.AsyncCopy PTX.MBarrier PTX.MbarRing Prologue Epilogue Thread.Scores

/-- A successful tail probability poll observes the credit of each warp in the
selected stage. Exact notification ordinals apply at every physical generation. -/
theorem tailCreditOfObservedWarpExact {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta phase : Nat} (stage : Fin 2) (warp : Fin 4) {k : Nat} {poll : Record Ref}
    (hRecord : (X.objects (probabilityObject l cta stage 1))[k]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hSeen : observedAt (X.objects (probabilityObject l cta stage 1)) k = some phase) :
    ∃ i, ProbabilityCredit l X i cta stage 1 ∧
      warpIndex l i.1 = 4 * stage.val + warp.val ∧
      probabilityOrdinal l X cta stage 1 i = phase ∧ MbarObserved X (.thread i) poll.id := by
  classical
  let loc := probabilityObject l cta stage 1
  let log := X.objects loc
  let credits := (Finset.range log.length).filter (UnitArrivalIn log phase)
  let label (n : Nat) : Fin 4 := (tailLabel l X cta stage (log[n]?.getD poll).id).1
  have hChecked := X.objects_checked hX loc
  have hInit := probabilityInitialized hp hX stage 1 (List.mem_of_getElem? hRecord)
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hUnit {r : Record Ref} (hr : r ∈ log) (hu : CounterUpdate r.action) :
      r.action = .arrive 1 0 := by
    obtain ⟨_,_,_,_,ha⟩ := probabilityUpdate hp hX stage 1 hr hu
    exact ha
  have hIncr : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro r hr hInc
    have h := hUnit hr (by rw [hInc]; trivial)
    rw [hInc] at h
    cases h
  obtain ⟨st,hSt,hCurrent⟩ := hChecked.observed_phase hRecord hSuccess hSeen
  have hCard : credits.card = 4 := by
    exact hChecked.card_unit_arrivals_phase hNo (q := phase)
      (fun _ r count tx hr _ ha =>
        (Action.arrive.inj (ha.symm.trans (hUnit (List.mem_of_getElem? hr)
          (by rw [ha]; trivial)))).1)
      (fun _ _ _ h => PairTmaRing.expected_of_init hX hInit hNo h) hIncr
      (List.getElem?_eq_some_iff.mp hRecord).1.le hSt (by omega)
  have source {n : Nat} (hn : n ∈ credits) :
      ∃ (r : Record Ref) (i : EvId), log[n]? = some r ∧ r.id = .thread i ∧
        ProbabilityCredit l X i cta stage 1 ∧
        probabilityOrdinal l X cta stage 1 i = phase ∧
        label n = ⟨warpIndex l i.1 % 4,Nat.mod_lt _ (by decide)⟩ ∧
        warpIndex l i.1 / 4 = stage.val ∧
        MbarObserved X (.thread i) poll.id := by
    obtain ⟨_,r,tx,hr,hArrive,hClean,hPhase⟩ := Finset.mem_filter.mp hn
    have hUpdate : CounterUpdate r.action := by rw [hArrive]; trivial
    obtain ⟨i,hId,hCredit,_,_⟩ := probabilityUpdate hp hX stage 1
      (List.mem_of_getElem? hr) hUpdate
    have hExact := (tailProbabilityCreditPhaseExact hp hX stage hr hUpdate hId).2
    have hOrdinal : probabilityOrdinal l X cta stage 1 i = phase :=
      Option.some.inj (hExact.symm.trans hPhase)
    have hLabel : label n = ⟨warpIndex l i.1 % 4,Nat.mod_lt _ (by decide)⟩ := by
      simp only [label,hr,Option.getD_some,hId,tailLabel]
    have hStage : warpIndex l i.1 / 4 = stage.val := by
      rcases (probabilityCreditRole hp hX stage 1 hCredit).2 with h | h
      · exact h.2
      · have hFalse : (1 : Fin 2).val ≠ 0 := by decide
        exact (hFalse h.1).elim
    have hObserved := hX.observed_of_phase hNo hr hClean hUpdate hRecord hSuccess hPhase hSeen
    exact ⟨r,i,hr,hId,hCredit,hOrdinal,hLabel,hStage,hId ▸ hObserved⟩
  have hInject : Set.InjOn label credits := by
    intro a ha b hb hSame
    obtain ⟨r,i,hr,hId,hC,hOrd,hLabel,_,_⟩ := source ha
    obtain ⟨s,j,hs,hJd,hD,hJOrd,hJLabel,_,_⟩ := source hb
    have hPair : tailLabel l X cta stage (.thread i) = tailLabel l X cta stage (.thread j) :=
      Prod.ext (hLabel.symm.trans (hSame.trans hJLabel)) (hOrd.trans hJOrd.symm)
    have hEq := tailLabelInj hp hX hC hD hPair
    exact ObjectInit.checked_record_index_eq hChecked hr hs (by simp only [hId,hJd,hEq])
  have hImage : credits.image label = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_image_of_injOn hInject,hCard,Finset.card_univ,Fintype.card_fin]
  have hMember : warp ∈ credits.image label := hImage ▸ Finset.mem_univ _
  obtain ⟨n,hn,hWarp⟩ := Finset.mem_image.mp hMember
  obtain ⟨_,i,_,_,hCredit,hOrdinal,hLabel,hStage,hObserved⟩ := source hn
  have hMod : warpIndex l i.1 % 4 = warp.val := congrArg Fin.val (hLabel.symm.trans hWarp)
  exact ⟨i,hCredit,by omega,hOrdinal,hObserved⟩

/-- The elected sender in a chosen warp contributed to the completed tail packet. -/
theorem tailCreditOfObservedWarp {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta phase : Nat} (stage : Fin 2) (warp : Fin 4) {k : Nat} {poll : Record Ref}
    (hRecord : (X.objects (probabilityObject l cta stage 1))[k]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hSeen : observedAt (X.objects (probabilityObject l cta stage 1)) k = some phase) :
    ∃ i, ProbabilityCredit l X i cta stage 1 ∧
      warpIndex l i.1 = 4 * stage.val + warp.val ∧ MbarObserved X (.thread i) poll.id := by
  obtain ⟨i,hi,hw,_,hObserved⟩ :=
    tailCreditOfObservedWarpExact hp hX stage warp hRecord hSuccess hSeen
  exact ⟨i,hi,hw,hObserved⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
