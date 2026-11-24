-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasBoxGenerations
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Order.DependencyWitness
import Lemmas.Order.WaitOrderEnables
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Thread.Loader

/-- A completed Bias-empty generation includes the actual return of each of its consumer warps. -/
theorem biasEmptyObservedReturnOfWarp {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta j phase : Nat} (stage : Fin 2) (warp : Fin 4) {poll : Record Ref}
    (hj : (X.objects (biasEmptyObject l cta stage))[j]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hPhase : observedAt (X.objects (biasEmptyObject l cta stage)) j = some phase) :
    ∃ e, X.Arrive e (biasEmptyObject l cta stage) 0 1 true .cta ∧
      e.1 / l.block = cta ∧ Prologue.warpIndex l e.1 = 4 * stage.val + warp.val ∧
      biasArrivalOrdinal X (biasEmptyObject l cta stage) e = phase ∧
      MbarObserved X (.thread e) poll.id := by
  classical
  let loc := biasEmptyObject l cta stage
  let log := X.objects loc
  let returns := (Finset.range log.length).filter (fun i => UnitArrivalIn log phase i)
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hChecked := X.objects_checked hX loc
  have hInit : PairTmaRing.InitFirst X loc 4 := by
    have hMem := List.mem_of_getElem? hj
    fin_cases stage
    · exact (activeObjectHistory hp hX (32 : Fin 34) hMem).1
    · exact (activeObjectHistory hp hX (33 : Fin 34) hMem).1
  obtain ⟨s, hs, hP⟩ := hChecked.observed_phase hj hSuccess hPhase
  have hLt : phase < s.phase := by omega
  have hInc : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro r hr ha
    obtain ⟨_, _, _, _, _, _, hb⟩ :=
      Thread.Softmax.biasEmptyUpdate hp hX stage hr (ha.symm ▸ trivial)
    rw [ha] at hb
    cases hb
  have hUnit (i : Nat) (r : Record Ref) (units bytes : Nat) (hr : log[i]? = some r)
      (_ : r.fault = none) (ha : r.action = .arrive units bytes) : units = 1 := by
    obtain ⟨_, _, _, _, _, _, hb⟩ := Thread.Softmax.biasEmptyUpdate hp hX stage
      (List.mem_of_getElem? hr) (ha.symm ▸ trivial)
    exact (Action.arrive.inj (ha.symm.trans hb)).1
  have hCard : returns.card = 4 :=
    hChecked.card_unit_arrivals_phase hNo hUnit
      (fun _ _ _ hs => PairTmaRing.expected_of_init hX hInit hNo hs) hInc
      (List.getElem?_eq_some_iff.mp hj).1.le hs hLt
  have origin (i : Nat) (hi : i ∈ returns) :
      ∃ r e, log[i]? = some r ∧ r.id = .thread e ∧ X.Arrive e loc 0 1 true .cta ∧
        e.1 / l.block = cta ∧ Prologue.warpIndex l e.1 < 8 ∧
        Prologue.warpIndex l e.1 / 4 = stage.val ∧ biasArrivalOrdinal X loc e = phase ∧
        MbarObserved X (.thread e) poll.id := by
    obtain ⟨_, r, tx, hr, ha, hf, hQ⟩ := Finset.mem_filter.mp hi
    obtain ⟨e, hId, hIssue, hOwner, hWarp, hStage, hb⟩ :=
      Thread.Softmax.biasEmptyUpdate hp hX stage (List.mem_of_getElem? hr) (ha.symm ▸ trivial)
    have hReal := (biasEmptyReleaseGeneration hp hX stage hr hId hb).2
    rw [hQ] at hReal
    have hObs := hX.observed_of_phase hNo hr hf (hb.symm ▸ trivial) hj hSuccess hQ hPhase
    rw [hId] at hObs
    exact ⟨r,e,hr,hId,hIssue,hOwner,hWarp,hStage,(Option.some.inj hReal).symm,hObs⟩
  choose rr ee hGet hId hIssue hOwner hWarp hStage hOrdinal hObs using origin
  let label (i : Nat) : Fin 4 :=
    if hi : i ∈ returns then
      ⟨Prologue.warpIndex l (ee i hi).1 % 4, Nat.mod_lt _ (by decide)⟩
    else 0
  have hFind : ∃ i ∈ returns, label i = warp := by
    by_contra! hAvoid
    let other := (Finset.univ : Finset (Fin 4)).erase warp
    have hCapacity : other.card = 3 := by simp [other]
    have hBounds : returns.card ≤ other.card := by
      apply Finset.card_le_card_of_injOn label
      · intro i hi
        exact Finset.mem_erase.mpr ⟨hAvoid i hi, Finset.mem_univ _⟩
      · intro i hi i' hi' hEq
        have hI : i ∈ returns := hi
        have hI' : i' ∈ returns := hi'
        dsimp only [label] at hEq
        rw [dite_eq_left hI, dite_eq_left hI'] at hEq
        have hMod : Prologue.warpIndex l (ee i hI).1 % 4 =
            Prologue.warpIndex l (ee i' hI').1 % 4 := congrArg Fin.val hEq
        have hDiv := (hStage i hI).trans (hStage i' hI').symm
        have hW : Prologue.warpIndex l (ee i hI).1 = Prologue.warpIndex l (ee i' hI').1 := by omega
        have hSame : SameWarp l (ee i hI).1 (ee i' hI').1 :=
          ⟨⟨Thread.Softmax.arrivalIssuerPresent hX (hIssue i hI),
            Thread.Softmax.arrivalIssuerPresent hX (hIssue i' hI'),
            (hOwner i hI).trans (hOwner i' hI').symm⟩, hW⟩
        have hThread := Thread.Softmax.biasReturnSameWarpIssuer hp hX stage
          (hIssue i hI) (hIssue i' hI') hSame
        have hEvt : ee i hI = ee i' hI' := by
          rcases he : ee i hI with ⟨g,k⟩
          rcases hf : ee i' hI' with ⟨g',k'⟩
          have he' := hIssue i hI
          have hf' := hIssue i' hI'
          have hOrd := (hOrdinal i hI).trans (hOrdinal i' hI').symm
          rw [he, hf] at hThread hOrd
          rw [he] at he'
          rw [hf] at hf'
          change g = g' at hThread
          subst g'
          exact congrArg (fun x => (g,x)) (Thread.Softmax.arrivalOrdinalInjective he' hf' hOrd)
        have hRecord := (hId i hI).trans ((congrArg Ref.thread hEvt).trans (hId i' hI').symm)
        exact ObjectInit.checked_record_index_eq hChecked (hGet i hI) (hGet i' hI') hRecord
    omega
  obtain ⟨i, hi, hw⟩ := hFind
  dsimp only [label] at hw
  rw [dite_eq_left hi] at hw
  have hMod : Prologue.warpIndex l (ee i hi).1 % 4 = warp.val := congrArg Fin.val hw
  have hDiv := hStage i hi
  exact ⟨ee i hi, hIssue i hi, hOwner i hi, by omega, hOrdinal i hi, hObs i hi⟩

/-- A reused Bias half waits for every consumer warp's return of the preceding generation. -/
theorem biasTensorReuseOfConsumerWarp {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {stage half : Fin 2} {spec : TensorCopy.Spec} (warp : Fin 4)
    (hIssue : BiasSubbox p l X (g,j) stage half spec)
    (hReused : 0 < biasTensorOrdinal l X stage half (g,j)) :
    ∃ (release : EvId) (k : Nat),
      X.Arrive release (biasEmptyObject l (g / l.block) stage) 0 1 true .cta ∧
      release.1 / l.block = g / l.block ∧
      Prologue.warpIndex l release.1 = 4 * stage.val + warp.val ∧
      biasArrivalOrdinal X (biasEmptyObject l (g / l.block) stage) release + 1 =
        biasTensorOrdinal l X stage half (g,j) ∧
      MbarObserved X (.thread release) (.thread (g,k)) ∧ Resumes kernel X (g,k) (g,j) := by
  obtain ⟨k, i, r, hr, hid, hReply, hResume, hObs⟩ :=
    biasTensorReuseGuardExact hp hX hIssue hReused
  obtain ⟨e, he, hOwner, hWarp, hOrd, hObserve⟩ :=
    biasEmptyObservedReturnOfWarp hp hX stage warp hr hReply hObs
  rw [hid] at hObserve
  refine ⟨e,k,he,hOwner,hWarp,?_,hObserve,hResume⟩
  change biasArrivalOrdinal X (biasEmptyObject l (g / l.block) stage) e =
    biasTensorOrdinal l X stage half (g,j) - 1 at hOrd
  omega

private theorem arrivalOrdinalIndexLe {X : Execution} {loc : Loc} {g j k : Nat}
    (hLater : X.Arrive (g,k) loc 0 1 true .cta)
    (hOrdinal : biasArrivalOrdinal X loc (g,j) ≤ biasArrivalOrdinal X loc (g,k)) :
    j ≤ k := by
  by_contra! hLt
  obtain ⟨_, hGet⟩ := hLater
  have hCount := countP_take_succ hGet (p := arrivesOn loc) (by simp [sourceArrive])
  have hMono := countP_take_mono (arrivesOn loc) (X.tr g) (show k + 1 ≤ j by omega)
  change ((X.tr g).take j).countP (arrivesOn loc) ≤ ((X.tr g).take k).countP (arrivesOn loc)
    at hOrdinal
  omega

private theorem biasResumesLater {X : Execution} {g k i j : Nat}
    (hOld : Resumes kernel X (g,k) (g,i)) (hOrder : i ≤ j) (hLen : j < (X.tr g).length) :
    Resumes kernel X (g,k) (g,j) := by
  have hBefore : TraceBefore X (g,k) (g,j) := ⟨rfl, lt_of_lt_of_le hOld.1.2.1 hOrder, hLen⟩
  refine ⟨hBefore, ?_⟩
  have hResume := hOld.2
  cases h : (X.get (g,k)).map (fun ev => ev.kind.resume) with
  | none => simp [h] at hResume
  | some res =>
    cases res <;> simp [h] at hResume ⊢
    obtain ⟨site, exit, m, q, acq, sc, hGet, hSpin, _⟩ := hResume
    exact ⟨site, exit, m, q, acq, sc, hGet, hSpin, hBefore⟩

/-- The consumer's real Bias return follows a ready acquire of its exact local generation. -/
theorem biasReturnObservedReadyExact {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 2) {e : EvId}
    (hIssue : X.Arrive e (biasEmptyObject l cta stage) 0 1 true .cta) :
    let log := X.objects (biasReadyObject l cta stage)
    ∃ (k i : Nat) (r : Record Ref), log[i]? = some r ∧
      r.id = .thread (e.1,k) ∧ r.reply.waited = some true ∧
      observedAt log i = some (biasArrivalOrdinal X (biasEmptyObject l cta stage) e) ∧
      Resumes kernel X (e.1,k) e := by
  let empty := biasEmptyObject l cta stage
  let loc := biasReadyObject l cta stage
  let ordinal := biasArrivalOrdinal X empty e
  obtain ⟨k, i, phase, r, hr, hId, hSeen, hObs, hLower, hResume⟩ :=
    Thread.Softmax.biasReadyObservedOfReturn hp hX stage hIssue
  change ordinal ≤ phase at hLower
  have hExact : phase = ordinal := by
    by_contra hNe
    have hGt : ordinal < phase := by omega
    have hAct : objectAction X X.async empty (.thread e) = some (.arrive 1 0) := by
      obtain ⟨_, hGet⟩ := hIssue
      simp [objectAction, hGet, empty]
    obtain ⟨u, hu, hUid⟩ := (hX.tma.2.2.1 empty).2.2 _ _ hAct
    have hU := ((hX.tma.2.2.1 empty).2.1 _ hu).1
    rw [hUid, hAct] at hU
    obtain ⟨f, hf, _, hOwner, hWarp, hStage, _⟩ :=
      Thread.Softmax.biasEmptyUpdate hp hX stage hu ((Option.some.inj hU) ▸ trivial)
    have he : e = f := Ref.thread.inj (hUid.symm.trans hf)
    subst f
    let warp : Fin 4 := ⟨Prologue.warpIndex l e.1 % 4, Nat.mod_lt _ (by decide)⟩
    obtain ⟨box, spec, hBoxOwner, hBox, hOrdinal, hObserve⟩ :=
      biasReadyObservedHalfOwner hp hX stage 0 hr hSeen hObs
    obtain ⟨g,j⟩ := box
    obtain ⟨release, w, hRet, hCta, hW, hRetOrd, hWait, hReuse⟩ :=
      biasTensorReuseOfConsumerWarp hp hX warp hBox (by omega)
    change g / l.block = cta at hBoxOwner
    rw [hBoxOwner] at hRet hCta hRetOrd
    change Prologue.warpIndex l release.1 = 4 * stage.val +
      Prologue.warpIndex l e.1 % 4 at hW
    have hWarpEq : Prologue.warpIndex l e.1 =
        4 * stage.val + Prologue.warpIndex l e.1 % 4 := by
      have hDiv : Prologue.warpIndex l e.1 / 4 = stage.val := hStage
      have hRem := Nat.mod_add_div (Prologue.warpIndex l e.1) 4
      rw [hDiv] at hRem
      omega
    have hSameWarp : SameWarp l e.1 release.1 :=
      ⟨⟨Thread.Softmax.arrivalIssuerPresent hX hIssue,
        Thread.Softmax.arrivalIssuerPresent hX hRet, hOwner.trans hCta.symm⟩, hWarpEq.trans hW.symm⟩
    have hThread := Thread.Softmax.biasReturnSameWarpIssuer hp hX stage hIssue hRet hSameWarp
    obtain ⟨softmax, old⟩ := e
    obtain ⟨softmax', new⟩ := release
    change softmax = softmax' at hThread
    subst softmax'
    have hOrder : old ≤ new := by
      apply arrivalOrdinalIndexLe hRet
      change ordinal ≤ biasArrivalOrdinal X empty (softmax,new)
      change biasArrivalOrdinal X empty (softmax,new) + 1 =
        biasTensorOrdinal l X stage 0 (g,j) at hRetOrd
      omega
    obtain ⟨_, hRetGet⟩ := hRet
    have hTail := biasResumesLater hResume hOrder (List.getElem?_eq_some_iff.mp hRetGet).1
    have hPath := (Relation.TransGen.single (DepStep.of_resumes l hTail)).tail
      (DepStep.of_witness l (Witness.of_mbarObserved hWait))
    have hFromBox := biasNotificationAfterIssue hX hBox hObserve.1
    rw [hId] at hObserve
    have hCycle := ((hPath.tail (DepStep.of_resumes l hReuse)).trans hFromBox).tail
      (DepStep.of_witness l (Witness.of_mbarObserved hObserve))
    exact DepStepAcyclic.of_dependency hX.dependency _ hCycle
  rw [hExact] at hObs
  exact ⟨k,i,r,hr,hId,hSeen,hObs,hResume⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
