-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningSoftmaxBias
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasBarrierProgress
import Kernels.TmlFa4Fwd.Proof.Thread.FirstBiasRendezvous
import Kernels.TmlFa4Fwd.Proof.Protocol.NamedBarriers
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasCredits
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningBiasGuard
import Kernels.TmlFa4Fwd.Proof.Protocol.BiasEmptyGeneration
import Lemmas.Protocol.MbarPending
import Lemmas.Protocol.GatedFaults

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Proof Prologue Epilogue AsyncCopy MBarrier

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
include hp hMax

/-- Every participant in the selected CTA has recorded the opening Bias synchronization. -/
theorem openingBiasParticipantsArrive (hFrame : OutputFootprint p X) {cta batch : Nat}
    (hc : cta < l.grid) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch+1)*p.heads) (stage : Fin 2) :
    ∀ lane < l.block, lane/32 ∈ Thread.biasParticipants stage →
      ∃ i, Softmax.FirstBiasArrival X (cta*l.block+lane) i stage := by
  intro lane hl hMember
  let g := cta*l.block+lane
  have hg : g < l.threads := NamedBar.cta_thread_lt hc hl
  have hBlock : 0 < l.block := by rw [hp.block]; decide
  have hCta : g/l.block = cta := by
    dsimp [g]
    rw [Nat.mul_comm cta l.block,Nat.mul_add_div hBlock,Nat.div_eq_of_lt hl,Nat.add_zero]
  have hWarp : warpIndex l g = lane/32 := by
    have hMod : g%l.block = lane := by
      simp [g,Nat.add_mod,Nat.mod_eq_of_lt hl]
    simp [warpIndex,hMod]
  have hRole := ((Thread.biasParticipantIff stage (lane/32)).mp hMember).2
  exact openingSoftmaxBiasArrivalOfMaximal hp hMax hFrame hg stage (hWarp.symm ▸ hRole) hb
    (hCta.symm ▸ hLo) (hCta.symm ▸ hHi)

/-- A lane blocked at its opening Bias barrier has a maximal history with the same
lane traces and writes in which its named synchronization is released. -/
theorem openingBiasReleasedHistory (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (stage : Fin 2)
    (hPending : Softmax.FirstBiasArrival X g ((X.tr g).length-1) stage) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧ Step.Released l Y g := by
  apply Thread.releaseSynchronization hMax ?_ hg
    (Thread.biasBarrierShape hp stage) (Thread.biasBarrierSources hp hMax.1 stage) hPending.barrier
  · intro lane hl hMember
    rw [hPending.ordinalZero hp hMax.1]
    obtain ⟨i,hi⟩ := openingBiasParticipantsArrive hp hMax hFrame (NamedBar.cta_lt hg)
      hb hLo hHi stage lane hl hMember
    have hExtent := Thread.barrierArrivalExtent hi.barrier
    exact Nat.zero_lt_of_lt hExtent
  · intro Y hY _ hWrites
    have hOutput : OutputFootprint p Y := by
      intro w a bytes loc hw
      rw [hWrites] at hw
      exact hFrame w a bytes loc hw
    have hCuQ : DrainCuQProtected p Y :=
      hp.cuQ_protected (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hOutput)
    exact Protocol.noActualNamedBarrierFault hp hY hCuQ

/-- Each active softmax warp leader publishes its opening unit Bias-empty credit. -/
theorem openingBiasLeaderCreditOfMaximal (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (stage : Fin 2)
    (hRole : warpIndex l g/4 = stage.val) (hLeader : laneOf l g = 0) :
    ∃ i, Softmax.FirstBiasArrival X g i stage ∧
      X.get (g,i+1) =
        some ⟨3590,.arrive (Thread.Loader.biasEmptyObject l (g/l.block) stage) 0 1 true .cta⟩ := by
  obtain ⟨i,_,⟨cursor⟩⟩ :=
    openingSoftmaxBiasCursorOfMaximal hp hMax hFrame hg stage hRole hb hLo hHi
  have hReturn : i+67 < (X.tr g).length ∨
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g := by
    by_cases hMore : i+67 < (X.tr g).length
    · exact .inl hMore
    · right
      have hBound := cursor.observed.bound
      have hLast : i+66 = (X.tr g).length-1 := by omega
      obtain ⟨Y,hY,hTrace,_,hReady⟩ :=
        openingBiasReleasedHistory hp hMax hFrame hg hb hLo hHi stage (hLast ▸ cursor.observed)
      exact ⟨Y,hY,hTrace,hReady⟩
  obtain ⟨fma⟩ := cursor.firstFmaOfMaximal hp hg hReturn
  exact ⟨i+66,cursor.observed,fma.biasEmptyCredit hLeader⟩

/-- In every active CTA, both opening Bias-empty phases have all four actual return credits. -/
theorem openingBiasEmptyAdvancedOfMaximal (hFrame : OutputFootprint p X) {cta batch : Nat}
    (hc : cta < l.grid) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch+1)*p.heads) (stage : Fin 2) :
    let log := X.objects (Thread.Loader.biasEmptyObject l cta stage)
    ∃ s, MBarrier.stateBefore log log.length = some s ∧ 1 ≤ s.phase := by
  classical
  let addr := Thread.Loader.biasEmptyObject l cta stage
  let log := X.objects addr
  let thread (w : Fin 4) := cta*l.block+(4*stage.val+w.val)*32
  have hCredit (w : Fin 4) : ∃ i, X.Arrive (thread w,i) addr 0 1 true .cta := by
    let lane := (4*stage.val+w.val)*32
    have hStage := stage.isLt
    have hWarp := w.isLt
    have hl : lane < l.block := by rw [hp.block]; dsimp [lane]; omega
    have hBlock : 0 < l.block := by rw [hp.block]; decide
    obtain ⟨hOwner,hLocal⟩ := NamedBar.lane_cta (c := cta) hBlock hl
    change thread w/l.block = cta at hOwner
    change thread w%l.block = lane at hLocal
    have hRole : warpIndex l (thread w)/4 = stage.val := by
      rw [warpIndex,hLocal]
      dsimp [lane]
      omega
    have hLeader : laneOf l (thread w) = 0 := by
      simp [laneOf,hLocal,lane]
    obtain ⟨i,_,hi⟩ := openingBiasLeaderCreditOfMaximal hp hMax hFrame
      (NamedBar.cta_thread_lt hc hl) hb (hOwner.symm ▸ hLo) (hOwner.symm ▸ hHi) stage hRole hLeader
    rw [hOwner] at hi
    exact ⟨i+1,_,hi⟩
  have hRecord (w : Fin 4) : ∃ (i : Nat) (r : Record Ref), r ∈ log ∧
      r.id = .thread (thread w,i) ∧ r.action = .arrive 1 0 := by
    obtain ⟨i,⟨site,he⟩⟩ := hCredit w
    have hObj : objectAction X X.async addr (.thread (thread w,i)) = some (.arrive 1 0) := by
      simp [objectAction,he]
    obtain ⟨r,hr,hi⟩ := (hMax.1.tma.2.2.1 addr).2.2 _ _ hObj
    have ha := ((hMax.1.tma.2.2.1 addr).2.1 r hr).1
    rw [hi,hObj] at ha
    exact ⟨i,r,hr,hi,(Option.some.inj ha).symm⟩
  choose idx record hMem hId hAct using hRecord
  have hShape (r : Record Ref) (hr : r ∈ log) (hu : CounterUpdate r.action) :
      r.action = .arrive 1 0 :=
    (Thread.Softmax.biasEmptyUpdate hp hMax.1 stage hr hu).elim fun _ h => h.2.2.2.2.2
  let rows := log.filter countedArrive
  have hUnits : 4 ≤ arrivalUnits log := by
    rw [arrivalUnits_eq_length]
    · let members := rows.toFinset
      have hIn (w : Fin 4) : record w ∈ members := by
        exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hMem w,countedArrive_iff.mpr
          ⟨Protocol.Bias.biasEmptyHistoryClean hp hMax.1 stage (hMem w),1,0,hAct w⟩⟩)
      let target (w : Fin 4) : {r // r ∈ members} := ⟨record w,hIn w⟩
      have hInj : Function.Injective target := by
        intro a b hab
        have he := congrArg (fun r => Record.id r.val) hab
        change (record a).id = (record b).id at he
        rw [hId,hId] at he
        have ht : thread a = thread b := congrArg Prod.fst (Ref.thread.inj he)
        apply Fin.ext
        dsimp [thread] at ht
        omega
      have hCard := Fintype.card_le_of_injective target hInj
      simp only [Fintype.card_fin,Fintype.card_coe] at hCard
      exact hCard.trans (List.toFinset_card_le rows)
    · intro r hr c tx _ ha
      have hu : CounterUpdate r.action := by rw [ha]; trivial
      exact (Action.arrive.inj (ha.symm.trans (hShape r hr hu))).1
  have hInitial := (Thread.Loader.openingBiasEmptyInitializedAtStage hp hMax hc stage).1
  obtain ⟨init,hInit,hAction,hClean,_⟩ := hInitial (record 0) (hMem 0)
  have hChecked := X.objects_checked hMax.1 addr
  have hNo := objects_noInval hMax.1.tma.2.2.1 (fun i _ => noMbarInval hMax.1 (i := i)) addr
  have hLen : 0 < log.length := (List.getElem?_eq_some_iff.mp hInit).1
  obtain ⟨s,hState,hExpected⟩ := ObjectInit.checked_expected_after_init hChecked hNo
    hInit hAction hClean hLen (Nat.le_refl _)
  refine ⟨s,hState,?_⟩
  have hZeroIncr : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro r hr ha
    have hu : CounterUpdate r.action := by rw [ha]; trivial
    have h := hShape r hr hu
    rw [ha] at h
    cases h
  have hBefore := ((hChecked.accounted hNo (Nat.le_refl _)).2 s hState).2
  change arrivalUnits (log.take log.length) + s.pending =
    s.expected*(s.phase+1) + incrementsBefore log log.length at hBefore
  rw [List.take_length,hExpected,hZeroIncr] at hBefore
  have hNoTx : s.tx = 0 := by
    apply MbarRing.tx_zero_of hMax.1 hNo _ _ (Nat.le_refl _) hState
    · intro r hr n tx ha
      have hu : CounterUpdate r.action := by rw [ha]; trivial
      exact (Action.arrive.inj (ha.symm.trans (hShape r hr hu))).2
    · intro r hr n ha
      have hu : CounterUpdate r.action := by rw [ha]; trivial
      have h := hShape r hr hu
      rw [ha] at h
      cases h
  have hpending := stateBefore_pending_pos hChecked hState hNoTx
  by_contra! hs
  have hzero : s.phase = 0 := by omega
  rw [hzero] at hBefore
  omega

end PTX.Kernels.TmlFa4Fwd.Progress
