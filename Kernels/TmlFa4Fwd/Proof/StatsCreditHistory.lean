-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionCreditBalance
public import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
public import Kernels.TmlFa4Fwd.Proof.LoaderRingMbarAddress
public import Kernels.TmlFa4Fwd.Proof.MbarRecordOwner
public import Kernels.TmlFa4Fwd.Proof.SoftmaxCreditReuse
import Kernels.TmlFa4Fwd.Proof.SoftmaxCreditPhase
import Kernels.TmlFa4Fwd.Proof.PollSafety
public import Lemmas.Protocol.ObjectSource
public import Lemmas.Protocol.PollPhase
import Lemmas.Flow.NthEv
import Lemmas.Protocol.MbarRingRound
import Lemmas.Protocol.PollIndex
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.MmaReadyHistory
import Kernels.TmlFa4Fwd.Proof.Thread.MbarOperands
public import Lemmas.Protocol.UnitObject

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.MBarrier PTX.AsyncCopy Prologue

private def statsCreditSlot (stage : Fin 2) : Fin 34 :=
  ⟨24 + stage.val, by have := stage.isLt; omega⟩

private theorem statsCreditSlot_eq (l : Launch) (cta : Nat) (stage : Fin 2) :
    initObject l cta (statsCreditSlot stage) = statsCreditLoc l cta stage := by
  fin_cases stage <;> rfl

/-- A statistics-buffer credit record is initialization, polling, or a correction lane's unit. -/
inductive StatsCreditSource (l : Launch) (X : Execution) (cta : Nat)
    (stage : Fin 2) (r : Record Ref) : Prop
  | init {count : Nat} : r.action = .init count → StatsCreditSource l X cta stage r
  | poll {phase : Nat} {ok : Bool} :
      r.action = .pollParity phase ok → StatsCreditSource l X cta stage r
  | credit {i : EvId} {e : Event} :
      r.id = .thread i → X.get i = some e → correctionStatsCreditMark stage e = true →
      Thread.correctionAction e = some (.statsCredit stage) →
      i.1 / l.block = cta → 8 ≤ warpIndex l i.1 → warpIndex l i.1 < 12 →
      r.action = .arrive 1 0 → StatsCreditSource l X cta stage r

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The stage counter is initialized with the correction group's size of 128 lanes. -/
theorem statsCreditHistoryInit {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (statsCreditLoc l cta stage)) :
    PairTmaRing.InitFirst X (statsCreditLoc l cta stage) 128 := by
  have hCount : (initSite (statsCreditSlot stage)).count = 128 := by fin_cases stage <;> rfl
  rw [← statsCreditSlot_eq l cta stage] at hr ⊢
  rw [← hCount]
  exact (activeObjectHistory hp hX (statsCreditSlot stage) hr).1

/-- All actual updates that count towards a credit phase are unit correction arrivals. -/
theorem statsCreditHistorySource {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (statsCreditLoc l cta stage)) :
    StatsCreditSource l X cta stage r := by
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ ha => exact .init ha
  | wait _ _ ha => exact .poll ha
  | inval _ hi _ => exact (noMbarInval hX ⟨_, hi⟩).elim
  | @arrive g j pc tx units rel scope hid he ha =>
    have hSite := actualStatsCreditArrivalSite hp hX stage he rfl
    let e : Event := ⟨pc, .arrive (statsCreditLoc l cta stage) tx units rel scope⟩
    have hm := (correctionStatsCreditMark_iff stage e).mpr hSite
    have hSiteAll : pc ∈ [7987, 8224, 8443, 8464, 8468, 8764] := by
      fin_cases stage <;> simp at hSite ⊢ <;> tauto
    obtain ⟨hTx, _, hRel, hScope⟩ := correctionStatsCreditOperands hp hX he hSiteAll
    have hKind : e.kind = .arrive (statsCreditLoc l cta stage) 0 units true .cta := by
      dsimp only [e]
      rw [hTx, hRel, hScope]
    have hAction := (Thread.correctionStatsCreditObservation stage hKind).mpr hSite
    have hPayload := correctionStatsCreditPayload hp hX stage (e := e) he hm rfl
    have hUnits := Kind.arrive.inj hPayload
    rw [hUnits.2.1, hUnits.2.2.1] at ha
    have hOwner : g / l.block = cta := (congrArg Loc.cta hUnits.1).symm
    have hPc : 7752 ≤ pc ∧ pc < 9205 := by fin_cases stage <;> simp at hSite <;> omega
    have hh : pc ∉ registerHintSites := by
      simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    have hRole := roleBodyPcOfEvent hp hX he (show 173 < pc by omega) hh
    change roleBodyPc (warpIndex l g) pc at hRole
    have hW : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
      rcases hRole with h | h
      · omega
      · split_ifs at h <;> omega
    exact .credit hid he hm hAction hOwner hW.1 hW.2 ha
  | increment _ he _ =>
    obtain ⟨_, hNo, _, _⟩ := Loader.actualAsyncArrival hX he
    cases hNo
  | @tensor i pc addr spec _ he hLoc _ =>
    obtain ⟨site, rfl⟩ := Loader.actualInputIssuePc hX he
    obtain ⟨off, hOff, hL⟩ := Loader.loaderTensorAddress hp hX site he
    have hEq := congrArg Loc.addr (hL.symm.trans hLoc)
    change l.sharedBase + off = l.sharedBase + (192 + 8 * stage.val) at hEq
    have hB := stage.isLt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
    omega
  | @arriveOn i pc loc noinc _ he hm _ _ =>
    obtain ⟨⟨site, hPc⟩, hNo, _, _⟩ := Loader.actualAsyncArrival hX he
    subst noinc
    have hSite : pc ∈ [674, 904, 1137, 1342, 1602, 1735] := by
      rw [hPc]
      fin_cases site <;> decide
    rcases i with ⟨g, j⟩
    obtain ⟨off, hOff, hL⟩ := Loader.loaderAsyncAddress hp hX he hSite
    have hEq := congrArg Loc.addr (hL.symm.trans hm)
    change l.sharedBase + off = l.sharedBase + (192 + 8 * stage.val) at hEq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
    omega
  | bulk _ he hm _ _ =>
    rw [(actualCopyShape hX ⟨_, he⟩).completion] at hm
    cases hm
  | commit _ he hTarget _ =>
    exact (commitExcludesStatsCredit hp hX stage he hTarget rfl).elim
  | clc _ he _ _ _ => exact (noClcIssue hX ⟨_, he⟩).elim

private theorem statsCreditNoInval {cta : Nat} (stage : Fin 2)
    : NoInval (X.objects (statsCreditLoc l cta stage)) := by
  intro q hq hi
  cases statsCreditHistorySource hp hX stage hq with
  | init ha => rw [ha] at hi; cases hi
  | poll ha => rw [ha] at hi; cases hi
  | credit _ _ _ _ _ _ _ ha => rw [ha] at hi; cases hi

/-- An ordinary unit arrival at this object yields the correction role's statistics credit. -/
theorem statsCreditArrivalAction (stage : Fin 2) {g i site cta : Nat} {scope : MbarScope}
    (he : X.get (g, i) = some ⟨site, .arrive (statsCreditLoc l cta stage) 0 1 true scope⟩) :
    Thread.correctionAction ⟨site, .arrive (statsCreditLoc l cta stage) 0 1 true scope⟩ =
      some (.statsCredit stage) := by
  let e : Event := ⟨site, .arrive (statsCreditLoc l cta stage) 0 1 true scope⟩
  have hSite := actualStatsCreditArrivalSite hp hX stage he rfl
  have hSites : site ∈ [7987, 8224, 8443, 8464, 8468, 8764] := by
    fin_cases stage <;> simp at hSite ⊢ <;> tauto
  have hScope := (correctionStatsCreditOperands hp hX he hSites).2.2.2
  have hKind : e.kind = .arrive (statsCreditLoc l cta stage) 0 1 true .cta :=
    congrArg (fun sc => Kind.arrive (statsCreditLoc l cta stage) 0 1 true sc) hScope
  exact (Thread.correctionStatsCreditObservation stage hKind).mpr hSite

/-- A reached successful statistics acquire has a successful record on the issuing stage. -/
theorem statsCreditAcquireRecord {i : EvId} (stage : Fin 2)
    (hStage : stage.val = warpIndex l i.1 / 4) (hAcquire : Softmax.StatsCreditAcquired X i) :
    let loc := statsCreditLoc l (i.1 / l.block) stage
    ∃ (j : Nat) (r : Record Ref), (X.objects loc)[j]? = some r ∧
      r.id = .thread i ∧ r.reply.waited = some true := by
  dsimp only
  obtain ⟨e, parity, acq, scope, he, hk⟩ := Softmax.creditAcquireObject hp hX hAcquire
  rw [← hStage] at hk
  have ee : e = ⟨e.pc, .wait (statsCreditLoc l (i.1 / l.block) stage) parity true acq scope⟩ := by
    cases e
    exact congrArg (Event.mk _) hk
  obtain ⟨j, r, hj, hId, _, _, hSuccess⟩ :=
    actualPollRecordClean hp hX (he.trans (congrArg some ee))
  exact ⟨j, r, hj, hId, hSuccess⟩

/-- The phase found by a poll with alternating use parity contains at least as many complete
credit groups as the number of the lane's earlier successful acquires. -/
theorem statsCreditUnitsBefore {cta : Nat} (stage : Fin 2) (sel : Ref → Bool) {j : Nat}
    {r : Record Ref} (hj : (X.objects (statsCreditLoc l cta stage))[j]? = some r)
    (hSel : sel r.id = true) (hSuccess : r.reply.waited = some true)
    (hAlt : SelectedAlternates sel (X.objects (statsCreditLoc l cta stage)) 1) :
    128 * selectedBefore sel (X.objects (statsCreditLoc l cta stage)) j ≤
      unitsBefore (X.objects (statsCreditLoc l cta stage)) j := by
  let loc := statsCreditLoc l cta stage
  have hInit := statsCreditHistoryInit hp hX stage (List.mem_of_getElem? hj)
  have hNo := statsCreditNoInval hp hX (cta := cta) stage
  have hChecked := X.objects_checked hX loc
  obtain ⟨st, hst, hPhase, _⟩ :=
    hChecked.selected_poll_phase_ge hNo sel (by decide) hAlt hj hSel hSuccess
  have hExpected := PairTmaRing.expected_of_init hX hInit hNo hst
  have hLen : j ≤ (X.objects loc).length := (List.getElem?_eq_some_iff.mp hj).1.le
  obtain ⟨hPend, hUnits⟩ := (hChecked.accounted hNo hLen).2 st hst
  have hU : 128 * st.phase ≤ unitsBefore (X.objects loc) j := by
    rw [hExpected] at hPend hUnits
    omega
  have hEnough : selectedBefore sel (X.objects loc) j ≤ st.phase := by omega
  exact (Nat.mul_le_mul_left 128 hEnough).trans hU

private theorem softmaxPollOfRole {g j pc q : Nat} {target : Loc} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g,j) = some ⟨pc, .wait target q ok acq scope⟩)
    (hw : warpIndex l g < 8) :
    pc ∈ [3420,3425,3498,4874,5109,5181,6558,6676,7463,7738] := by
  let check := fun pc => decide (173 < pc ∧ pc ∉ registerHintSites ∧ pc ≠ 9205 ∧
    (3103 ≤ pc ∧ pc ≤ 7742 → pc ∈ [3420,3425,3498,4874,5109,5181,6558,6676,7463,7738]))
  have hAll : Flow.mbarWait.toList.all check = true := by decide
  obtain ⟨hLo, hHint, hEnd, hShape⟩ :=
    of_decide_eq_true (List.all_eq_true.mp hAll pc (actualMbarPollSite hX he))
  apply hShape
  have hR := roleBodyPcOfEvent hp hX (g := g) he hLo hHint
  change roleBodyPc (warpIndex l g) pc at hR
  rcases hR with hExit | hRole
  · exact (hEnd hExit).elim
  · split_ifs at hRole <;> first | exact hRole | omega

private theorem creditPollAtObject {g j pc q : Nat} {target : Loc} {acq : Bool} {scope : MbarScope}
    (he : X.get (g,j) = some ⟨pc, .wait target q true acq scope⟩) (stage : Fin 2)
    (hStage : stage.val = warpIndex l g / 4) :
    pc ∈ [3420,4874,6558,7463,7738] ↔ target = statsCreditLoc l (g/l.block) stage := by
  constructor
  · intro hSite
    have hLoc := Softmax.softmaxStatsCreditWaitAddress hp hX he hSite
    simpa only [statsCreditLoc, hStage] using hLoc
  · rintro rfl
    have hw : warpIndex l g < 8 := by have := stage.isLt; omega
    obtain ⟨o, ho, hLoc⟩ :=
      Softmax.softmaxWaitAddressClass hp hX he (softmaxPollOfRole hp hX he hw)
    by_contra hSite
    rw [ite_eq_right hSite] at ho
    have hEq := congrArg Loc.addr hLoc
    simp only [statsCreditLoc] at hEq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    omega

/-- Successful waits on the statistics object are exactly the softmax credit observations. -/
theorem statsCreditPollCursor {g j : Nat} (stage : Fin 2) (hStage : stage.val = warpIndex l g / 4) :
    okPolls (statsCreditLoc l (g/l.block) stage) ((X.tr g).take j) =
      (Thread.Scores.before X (g,j)).credits := by
  rw [Thread.Scores.beforeCredits, Flow.okPolls]
  apply List.countP_congr
  intro f hf
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hf
  have hK := (List.getElem?_eq_some_iff.mp hk).1
  simp only [List.length_take] at hK
  rw [List.getElem?_take_of_lt (by omega)] at hk
  obtain ⟨pc,kind⟩ := f
  cases kind <;> try rfl
  rename_i loc q ok acq scope
  cases ok
  · rfl
  · simp only [sourceWaitSuccess, decide_eq_true_eq, Thread.Scores.creditAcquired,
      List.contains_iff_mem]
    exact (creditPollAtObject hp hX (g := g) (j := k) hk stage hStage).symm

private theorem statsCreditPollsAlternate {g : Nat} (stage : Fin 2)
    (hStage : stage.val = warpIndex l g / 4) {r : Record Ref}
    (hr : r ∈ X.objects (statsCreditLoc l (g/l.block) stage)) :
    SelectedAlternates (objectThreadSelected g)
      (X.objects (statsCreditLoc l (g/l.block) stage)) 1 := by
  have hInit := statsCreditHistoryInit hp hX stage hr
  have hClean := PairTmaRing.poll_clean hX hInit (statsCreditNoInval hp hX stage)
  apply MbarRing.Poll.alternates hX hClean
  intro j pc phase acq scope he
  have hSite := (creditPollAtObject hp hX he stage hStage).mpr rfl
  rw [Softmax.creditPollParity hp hX he hSite, Nat.mod_mod,
    statsCreditPollCursor hp hX stage hStage]

/-- An actual statistics acquire implies one complete credit group for each earlier use. -/
theorem statsCreditUnitsOfAcquire {i : EvId} (stage : Fin 2)
    (hStage : stage.val = warpIndex l i.1 / 4) (hAcquire : Softmax.StatsCreditAcquired X i) :
    let loc := statsCreditLoc l (i.1/l.block) stage
    ∃ cursor r, (X.objects loc)[cursor]? = some r ∧ r.id = .thread i ∧
      r.reply.waited = some true ∧
      128 * (Thread.Scores.before X i).credits ≤ unitsBefore (X.objects loc) cursor := by
  obtain ⟨cursor,r,hr,hId,hSuccess⟩ := statsCreditAcquireRecord hp hX stage hStage hAcquire
  have hm := List.mem_of_getElem? hr
  have hAlt := statsCreditPollsAlternate hp hX stage hStage hm
  have hInit := statsCreditHistoryInit hp hX stage hm
  have hClean := PairTmaRing.poll_clean hX hInit (statsCreditNoInval hp hX stage)
  have hUnits := statsCreditUnitsBefore hp hX stage (objectThreadSelected i.1) hr
    (objectThreadSelected_iff.mpr ⟨i.2, hId⟩) hSuccess hAlt
  rw [MbarRing.Poll.count_before hX hr hId hClean,
    statsCreditPollCursor hp hX stage hStage] at hUnits
  exact ⟨cursor,r,hr,hId,hSuccess,hUnits⟩

omit hp hX in
/-- The same 128 correction lanes return credits for both statistics stages. -/
def statsCreditLane (l : Launch) (cta : Nat) (lane : Fin 128) : Nat :=
  cta * l.block + 256 + lane.val

omit hp hX in
/-- Every physical correction lane is a participant in the statistics credit object. -/
theorem statsCreditLaneOf {l : Launch} {g cta : Nat}
    (hCta : g / l.block = cta) (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12) :
    ∃ lane : Fin 128, g = statsCreditLane l cta lane := by
  unfold warpIndex at hLo hHi
  have hLane : 256 ≤ g % l.block ∧ g % l.block < 384 := by omega
  refine ⟨⟨g % l.block - 256, by omega⟩, ?_⟩
  have hG := Nat.div_add_mod g l.block
  rw [hCta, Nat.mul_comm] at hG
  unfold statsCreditLane
  dsimp only
  omega

/-- The object arrival count agrees with the correction lane's statistics credit cursor. -/
theorem statsCreditArrivalCursor (stage : Fin 2) {i : EvId} {e : Event} (he : X.get i = some e) :
    arrivals (statsCreditLoc l (i.1 / l.block) stage) ((X.tr i.1).take i.2) =
      (Thread.correctionBefore X i).count (.statsCredit stage) := by
  have hLen := len_of_get he
  rw [correctionCreditCursor hp hX stage he, arrivals]
  apply List.countP_congr
  intro f hf
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hf
  have hK := (List.getElem?_eq_some_iff.mp hk).1
  simp only [List.length_take] at hK
  rw [List.getElem?_take_of_lt (by omega)] at hk
  have hGet : X.get (i.1, k) = some f := hk
  constructor
  · intro ha
    obtain ⟨site, kind⟩ := f
    cases kind <;> simp [arrivesOn, sourceArrive] at ha
    case arrive target tx count rel scope =>
      exact (correctionStatsCreditMark_iff stage _).mpr
        (actualStatsCreditArrivalSite hp hX stage hGet (congrArg Loc.addr ha))
  · intro hMark
    have hObs := creditObservationOfMark hp hX stage hGet (by omega) hMark
    obtain ⟨target, units, hKind⟩ := Thread.correctionStatsCreditKind hObs
    have hPayload := correctionStatsCreditPayload hp hX stage hGet hMark hKind
    simp [arrivesOn, sourceArrive, hPayload]

/-- The stage credit counter is a unit object of the CTA's physical correction lanes. -/
theorem statsCreditObject (cta : Nat) (stage : Fin 2) :
    MbarRing.Unit.Obj X (statsCreditLoc l cta stage) 128 (statsCreditLane l cta) 1 where
  pos := by decide
  inj := by
    intro a b he
    exact Fin.ext (by unfold statsCreditLane at he; omega)
  src r hr := by
    cases statsCreditHistorySource hp hX stage hr with
    | init ha => exact .init ha
    | poll ha =>
      cases record_source hX.tma.2.2.1 hr
      case wait hId he ha' => exact .poll hId he ha'
      all_goals grind
    | @credit i e hId hGet hMark hObs hCta hLo hHi ha =>
      obtain ⟨target, units, hk⟩ := Thread.correctionStatsCreditKind hObs
      have hPayload := correctionStatsCreditPayload hp hX stage hGet hMark hk
      rw [hCta] at hPayload
      obtain ⟨lane, hLane⟩ := statsCreditLaneOf hCta hLo hHi
      obtain ⟨pc, kind⟩ := e
      change kind = _ at hPayload
      subst kind
      exact .arrive hId ⟨lane, hLane⟩ hGet ha
  init r hr := statsCreditHistoryInit hp hX stage hr r hr
  noInval := statsCreditNoInval hp hX stage
  parity {g k pc parity acq scope} he := by
    obtain ⟨hCta, hStage, hSite⟩ := statsCreditWaitStage hp hX stage he
    rw [hCta, statsCreditPollCursor hp hX stage hStage]
    rw [Softmax.creditPollParity hp hX he hSite, Nat.mod_mod]
  δ_le := le_rfl

/-- If a prefix has enough arrival units and all its credited uses are below the cutoff, then
it has the unit of every participating lane for every use below that cutoff. -/
theorem statsCreditCoverage {cta j n : Nat} (stage : Fin 2)
    (hUnits : 128*n ≤ unitsBefore (X.objects (statsCreditLoc l cta stage)) j)
    (hCap : ∀ k < j, ∀ (r : Record Ref) i e,
      (X.objects (statsCreditLoc l cta stage))[k]? = some r → r.fault = none →
      r.action = .arrive 1 0 → r.id = .thread i → X.get i = some e →
      correctionStatsCreditMark stage e = true →
      (Thread.correctionBefore X i).count (.statsCredit stage) < n) (lane : Fin 128) {use : Nat}
    (hUse : use < n) :
    ∃ k < j, ∃ (r : Record Ref),
      (X.objects (statsCreditLoc l cta stage))[k]? = some r ∧ r.fault = none ∧
      r.action = .arrive 1 0 ∧
      r.id = .thread (statsCreditLane l cta lane,
        nthEv X (correctionStatsCreditMark stage) (statsCreditLane l cta lane) use) := by
  classical
  let loc := statsCreditLoc l cta stage
  let log := X.objects loc
  let update : Fin 128 × Nat → Ref := fun item =>
    .thread (statsCreditLane l cta item.1,
      nthEv X (correctionStatsCreditMark stage) (statsCreditLane l cta item.1) item.2)
  let hasRecord := fun item => ∃ k < j, ∃ (r : Record Ref), log[k]? = some r ∧
    r.fault = none ∧ r.action = .arrive 1 0 ∧ r.id = update item
  generalize hPairs : ((Finset.univ : Finset (Fin 128)) ×ˢ Finset.range n).filter hasRecord = seen
  have hFilter (v : Fin 128 × Nat) : v ∈ seen ↔ v.2 < n ∧ hasRecord v := by
    rw [← hPairs]
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]
  have hSeen (k : Nat) (r : Record Ref) (c tx : Nat) (hr : log[k]? = some r)
      (ha : r.action = .arrive c tx) : c = 1 ∧ tx = 0 ∧
        ∃ i e, r.id = .thread i ∧ X.get i = some e ∧ correctionStatsCreditMark stage e = true ∧
          i.1 / l.block = cta ∧ 8 ≤ warpIndex l i.1 ∧ warpIndex l i.1 < 12 := by
    cases statsCreditHistorySource hp hX stage (List.mem_of_getElem? hr) with
    | init hi => rw [ha] at hi; cases hi
    | poll hi => rw [ha] at hi; cases hi
    | credit hid he hm _ hOwn hlo hhi hAct =>
      rw [ha] at hAct
      exact ⟨(Action.arrive.inj hAct).1, (Action.arrive.inj hAct).2,
        _, _, hid, he, hm, hOwn, hlo, hhi⟩
  have hUpper := PTX.MbarRing.Round.units_le_of_uses (X.objects_checked hX loc) update seen (i := j)
    (fun k r c tx hr _ ha => (hSeen k r c tx hr ha).1) (by
      intro k hk r c tx hr hClean ha
      obtain ⟨rfl, rfl, i, e, hid, he, hm, hOwner, hLo, hHi⟩ := hSeen k r c tx hr ha
      obtain ⟨a, hA⟩ := statsCreditLaneOf hOwner hLo hHi
      let u := (Thread.correctionBefore X i).count (.statsCredit stage)
      have hu : u < n := hCap k hk r i e hr hClean ha hid he hm
      have hIdx : nthEv X (correctionStatsCreditMark stage) i.1 u = i.2 := by
        unfold u
        rw [correctionCreditCursor hp hX stage he]
        exact nthEv_eq he hm
      have href : r.id = update (a,u) := by
        rw [hid]
        change Ref.thread i = .thread (statsCreditLane l cta a, _)
        rw [← hA, hIdx]
      exact ⟨(a,u), (hFilter (a,u)).mpr ⟨hu, k, hk, r, hr, hClean, ha, href⟩, href⟩)
  have hGoal : (lane,use) ∈ seen := by
    by_contra hMissing
    have hLess := PTX.MbarRing.Round.card_lt_of_uses seen (Q := n)
      (fun v hv => ((hFilter v).mp hv).1) (z := (lane,use)) hUse hMissing
    rw [Fintype.card_fin] at hLess
    change 128*n ≤ unitsBefore (X.objects loc) j at hUnits
    omega
  exact ((hFilter (lane,use)).mp hGoal).2

end PTX.Kernels.TmlFa4Fwd.Correction
