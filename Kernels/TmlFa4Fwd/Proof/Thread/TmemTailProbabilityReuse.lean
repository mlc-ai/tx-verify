-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTailRendezvous
public import Lemmas.Order.WarpBarOrdinal
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityReuseTrace
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder
import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Lemmas.Flow.CountWindow

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.MBarrier PTX.AsyncCopy Softmax

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

/-- Each elected tail credit follows its warp rendezvous and election in the
last two events of the same lane. -/
theorem tailCreditImmediateBarrier (hX : Consistent l kernel Assumptions.all m X) {credit : EvId}
    {cta : Nat} (stage : Fin 2) (hCredit : ProbabilityCredit l X credit cta stage 1) :
    ∃ barrier inst, barrier+2 = credit.2 ∧ X.WarpBar (credit.1,barrier) (2^32-1) inst := by
  obtain ⟨round,hPos,inst,hElection⟩ := tailCreditImmediateElectionBefore hp hX stage hCredit
  obtain ⟨j,s,hJ,hBar⟩ := tailBarrierBeforeElection hX round hElection
  exact ⟨j,s,by omega,hBar⟩

private theorem tailCreditOfMarker (hX : Consistent l kernel Assumptions.all m X) {i : EvId}
    {cta : Nat} (stage : Fin 2) {e : Event} (he : X.get i = some e)
    (hMark : arrivesOn (probabilityObject l cta stage 1) e = true) :
    ProbabilityCredit l X i cta stage 1 := by
  obtain ⟨site,kind⟩ := e
  obtain ⟨tx,count,rel,scope,hm⟩ := arrivesOn_form hMark
  change kind = _ at hm
  subst kind
  have hOff : 96+8*stage.val+16*(1 : Fin 2).val ∈ [96,104,112,120] := by
    fin_cases stage <;> decide
  rcases actualProbabilityArrivalSite hp hX he hOff rfl with ⟨k,rfl⟩ | hc
  · obtain ⟨rfl,rfl,rfl,rfl,_,_⟩ := Softmax.probabilityArriveFacts hp hX k he
    exact ⟨_,he⟩
  · have hLoc := Correction.correctionArriveAddressExact hp hX he
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hc ⊢; tauto)
    have hAddr := congrArg Loc.addr hLoc
    have audit : ∀ k ∈ [7752,7754,8223,8442,8759,9055],
        Correction.correctionArriveOffset k = 96 ∨
          Correction.correctionArriveOffset k = 104 := by decide
    have h := audit site hc
    change l.sharedBase+(96+8*stage.val+16*(1 : Fin 2).val) =
      l.sharedBase+Correction.correctionArriveOffset site at hAddr
    have hOne : (1 : Fin 2).val = 1 := rfl
    omega

/-- The number of earlier tail credits cannot exceed the sender's earlier
warp rendezvous count at the current credit's own warp rendezvous. -/
theorem tailCreditOrdinalLeBarrier (hX : Consistent l kernel Assumptions.all m X) {credit : EvId}
    {cta : Nat} (stage : Fin 2) (hCredit : ProbabilityCredit l X credit cta stage 1) :
    ∃ barrier inst, barrier+2 = credit.2 ∧ X.WarpBar (credit.1,barrier) (2^32-1) inst ∧
      probabilityOrdinal l X cta stage 1 credit ≤ warpBars X credit.1 barrier := by
  classical
  obtain ⟨g,j⟩ := credit
  obtain ⟨k,inst,hK,hBar⟩ := tailCreditImmediateBarrier hp hX stage hCredit
  let tr := X.tr g
  let dependsOnCredit := arrivesOn (probabilityObject l cta stage 1)
  let credits := (Finset.range j).filter (fun n => (tr[n]?).any dependsOnCredit = true ∧
    0 ≤ (tr.take n).countP dependsOnCredit)
  let barriers := (Finset.range k).filter (fun n => (tr[n]?).any Execution.isWarpBar = true ∧
    0 ≤ (tr.take n).countP Execution.isWarpBar)
  have hCredits : credits.card = (tr.take j).countP dependsOnCredit := by
    exact (card_window tr dependsOnCredit 0 j).trans (Nat.sub_zero _)
  have hBarriers : barriers.card = (tr.take k).countP Execution.isWarpBar := by
    exact (card_window tr Execution.isWarpBar 0 k).trans (Nat.sub_zero _)
  have hOrigin (n : Nat) (hn : n ∈ credits) : 2 ≤ n ∧ n-2 ∈ barriers := by
    obtain ⟨hRange,hMark,_⟩ := Finset.mem_filter.mp hn
    cases he : tr[n]? with
    | none => simp [he] at hMark
    | some e =>
      have he' : X.get (g,n) = some e := he
      have hm : dependsOnCredit e = true := by simpa [he] using hMark
      have hC : ProbabilityCredit l X (g,n) cta stage 1 := tailCreditOfMarker hp hX stage he' hm
      obtain ⟨prior,bInst,hPrior,hB⟩ := tailCreditImmediateBarrier hp hX stage hC
      have hN : n < j := Finset.mem_range.mp hRange
      have hIndex : prior = n-2 := by dsimp at hPrior; omega
      subst prior
      refine ⟨by dsimp at hPrior; omega,Finset.mem_filter.mpr ⟨?_,?_,Nat.zero_le _⟩⟩
      · apply Finset.mem_range.mpr
        change k+2 = j at hK
        omega
      · obtain ⟨tag,hGet⟩ := hB
        change tr[n-2]? = _ at hGet
        simp [hGet,Execution.isWarpBar]
  have hCard := Finset.card_le_card_of_injOn (fun n => n-2)
    (fun n hn => (hOrigin n hn).2) (fun a ha b hb h => by
      have hA := (hOrigin a ha).1
      have hB := (hOrigin b hb).1
      change a-2 = b-2 at h
      omega)
  refine ⟨k,inst,hK,hBar,?_⟩
  rw [hCredits,hBarriers] at hCard
  exact hCard

/-- The current probability-tail store lies beyond each earlier publication rendezvous
in the lane's real sequence of score uses. -/
theorem tailProbabilityStoreScoreUses (hX : Consistent l kernel Assumptions.all m X) {store : EvId}
    (stage : Fin 2) (hStore : TailProbabilityStore X store)
    (hStage : Prologue.warpIndex l store.1 / 4 = stage.val) :
    let obj := scoreReadyObject l (store.1/l.block) stage
    warpBars X store.1 store.2 + 1 ≤ okPolls obj ((X.tr store.1).take store.2) := by
  obtain ⟨g,j⟩ := store
  obtain ⟨round,address,values,shape,he⟩ := hStore.decoded
  change Prologue.warpIndex l g / 4 = stage.val at hStage
  have hw : Prologue.warpIndex l g < 8 := by have := stage.isLt; omega
  have hBudget := actualTailStoreBarrierBudget hX round he
  let past := (X.tr g).take j
  have hPrior : warpBars X g j ≤
      past.countP (fun e => ([4858,6543,7448] : List Nat).contains e.pc) := by
    apply List.countP_mono_left
    intro e he hm
    obtain ⟨k,hGet⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take he)
    obtain ⟨source,kind⟩ := e
    cases kind <;> cases hm
    rename_i mask inst
    exact List.contains_iff_mem.mpr (warpBarrierSite hX (i := (g,k)) hGet)
  have hCount : past.countP scoreAcquireMark =
      okPolls (scoreReadyObject l (g/l.block) stage) past := by
    rw [show scoreAcquireMark = phaseAcquired true by
      funext event
      rw [scoreReadyMarkKind]
      rfl]
    exact scoreCount hp hX stage hw rfl hStage
  change _ + 1 ≤ past.countP scoreAcquireMark at hBudget
  exact (Nat.add_le_add_right hPrior 1).trans (hCount ▸ hBudget)

omit hp in
private theorem fullTailMask (l : Launch) (g : Nat) :
    electMember (2^32-1) (laneOf l g) := by
  have h (lane : Fin 32) : electMember (2^32-1) lane.val := by fin_cases lane <;> decide
  exact h ⟨_,Nat.mod_lt _ (by decide)⟩

/-- A tail store completes through the matching warp rendezvous before a consumer
following a credit at its generation or later. -/
theorem tailProbabilityDoneThroughWarpCredit (hX : Consistent l kernel Assumptions.all m X)
    {store credit consumer : EvId} (stage : Fin 2) (hStore : TailProbabilityStore X store)
    (hCredit : ProbabilityCredit l X credit (store.1/l.block) stage 1)
    (hSame : SameWarp l store.1 credit.1)
    (hCount : warpBars X store.1 store.2 ≤ probabilityOrdinal l X (store.1/l.block) stage 1 credit)
    (hConsumer : baseCausality l X credit consumer) : TcMma.StoreDoneBefore l X store consumer := by
  obtain ⟨g,index⟩ := store
  obtain ⟨h,finish⟩ := credit
  obtain ⟨k,inst,hK,hSender,hOrd⟩ := tailCreditOrdinalLeBarrier hp hX stage hCredit
  obtain ⟨s,hPartner⟩ := WarpBar.partner hX (sameWarp_symm hSame) hSender (fullTailMask l g)
  have hWarpCount : warpBars X h k = warpBars X g s := WarpBar.ordinal_eq hX (sameWarp_symm hSame)
    (fun _ _ _ he => actualFullWarpBarrier hX he ▸ fullTailMask l g)
    (fun _ _ _ he => actualFullWarpBarrier hX he ▸ fullTailMask l h) hPartner
  have hPair := hPartner
  obtain ⟨mask,bar,_,hOwn⟩ := hPair
  have hSameCount : warpBars X g index ≤ warpBars X g s :=
    hWarpCount ▸ hCount.trans hOrd
  obtain ⟨r,address,values,shape,he⟩ := hStore.decoded
  have hOwnRaw := hOwn
  obtain ⟨source,hGet⟩ := hOwnRaw
  have hBefore : index < s := by
    by_contra! hLE
    rcases Nat.eq_or_lt_of_le hLE with rfl | hLt
    · exact Kind.noConfusion (congrArg Event.kind (Option.some.inj (he.symm.trans hGet)))
    · have hm := countP_take_mono Execution.isWarpBar (X.tr g) (show s+1 ≤ index from hLt)
      change warpBars X g (s+1) ≤ warpBars X g index at hm
      rw [WarpBar.warpBars_succ hOwn] at hm
      exact Nat.not_succ_le_self _ (hm.trans hSameCount)
  have hRound : ∃ round : Softmax.Round, source = probabilityWaitPc round true+1 := by
    have hSite := warpBarrierSite hX hGet
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hSite
    rcases hSite with rfl | rfl | rfl
    · exact ⟨.first,rfl⟩
    · exact ⟨.biased,rfl⟩
    · exact ⟨.unbiased,rfl⟩
  obtain ⟨round,rfl⟩ := hRound
  obtain ⟨wait,hWait,hAfter,hBar⟩ :=
    probabilityTailWaitBeforeWarpBarrier hp hX r round he hGet hBefore
  obtain ⟨_,hCreditGet⟩ := hCredit
  have hLen : finish < (X.tr h).length := len_of_get hCreditGet
  have hCausal := WarpBar.sync hSame hPartner.symm hBar (by omega : k < finish) hLen
  exact ⟨⟨address,values,shape,_,he⟩,.inl ⟨(g,wait),hWait,rfl,hAfter,
    .inl (hCausal.trans hConsumer)⟩⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
