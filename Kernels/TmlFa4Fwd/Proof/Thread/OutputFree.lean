-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.Epilogue
public import Kernels.TmlFa4Fwd.Proof.Thread.ObservationMachine
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
public import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Lemmas.Flow.NotClc
public import Lemmas.Step.CtaBar
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
public import Kernels.TmlFa4Fwd.Proof.RoleDispatch
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
public import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
public import Lemmas.Protocol.PairTmaRing.Hyp
import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
import Kernels.TmlFa4Fwd.Proof.LoaderArrivalSites
import Kernels.TmlFa4Fwd.Proof.MbarSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Output
open PTX Epilogue Prologue AsyncCopy MBarrier

/-- The object released by all output lanes after the stage's bulk read drain. -/
def freeObject (l : Launch) (cta : Nat) (stage : Fin 2) : Loc :=
  ⟨.shared, cta, l.sharedBase + (224 + 8 * stage.val)⟩

/-- The output role uses warp 13 of the CTA and one lane per free credit. -/
def outputLane (l : Launch) (cta : Nat) (lane : Fin 32) : Nat :=
  cta * l.block + 416 + lane.val

/-- The output state has reached the stage's release, contributing one unit with no bytes. -/
def FreeCredit (l : Launch) (X : Execution) (cta : Nat) (stage : Fin 2) (i : EvId) : Prop :=
  ∃ e, X.get i = some e ∧ e.pc = freePc stage ∧
    e.kind = .arrive (freeObject l cta stage) 0 1 true .cta

private theorem FreeCredit.decoded {l : Launch} {X : Execution} {cta : Nat} {stage : Fin 2}
    {i : EvId} (h : FreeCredit l X cta stage i) :
    X.get i = some ⟨freePc stage, .arrive (freeObject l cta stage) 0 1 true .cta⟩ := by
  obtain ⟨⟨site, kind⟩, he, hSite, hKind⟩ := h
  change site = _ at hSite
  change kind = _ at hKind
  simpa only [hSite, hKind] using he

/-- Two release observations by one lane for the same stage point to the same event. -/
theorem FreeCredit.indexUnique {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta g i j : Nat} {stage : Fin 2} (hi : FreeCredit l X cta stage (g, i))
    (hj : FreeCredit l X cta stage (g, j)) : i = j :=
  OutputWarp.freeIndexUnique hp hX stage hi.decoded hj.decoded

/-- Every actual output-free record follows an initializer with 32 expected arrival units. -/
theorem freeInitialized {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 2) {r : Record Ref} (hr : r ∈ X.objects (freeObject l cta stage)) :
    PairTmaRing.InitFirst X (freeObject l cta stage) 32 := by
  fin_cases stage
  · exact (activeObjectHistory hp hX (28 : Fin 34) hr).1
  · exact (activeObjectHistory hp hX (29 : Fin 34) hr).1

/-- Every counter update has the identity of one of the output lanes' stage releases. -/
theorem freeUpdate {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 2) {r : Record Ref} (hr : r ∈ X.objects (freeObject l cta stage))
    (hUpdate : CounterUpdate r.action) :
    ∃ lane : Fin 32, ∃ j, r.id = .thread (outputLane l cta lane, j) ∧
      FreeCredit l X cta stage (outputLane l cta lane, j) ∧ r.action = .arrive 1 0 := by
  have offset {off owner : Nat}
      (h : freeObject l cta stage = ⟨.shared, owner, l.sharedBase + off⟩) :
      off = 224 + 8 * stage.val := by
    have hAddress := congrArg Loc.addr h
    change l.sharedBase + (224 + 8 * stage.val) = l.sharedBase + off at hAddress
    omega
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ ha | wait _ _ ha | inval _ _ ha => rw [ha] at hUpdate; exact hUpdate.elim
  | @arrive g index site tx count rel scope hId he hAct =>
    have hAddr : (freeObject l cta stage).addr = l.sharedBase + 224 ∨
        (freeObject l cta stage).addr = l.sharedBase + 232 := by
      fin_cases stage
      · exact .inl rfl
      · exact .inr rfl
    have hs := actualOutputFreeArrivalSite hp hX he hAddr
    obtain ⟨actualStage, hSite⟩ : ∃ actualStage : Fin 2, site = freePc actualStage := by
      rcases hs with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    subst site
    obtain ⟨hLoc, rfl, rfl, rfl, rfl⟩ := OutputWarp.freeOperands hp hX actualStage he
    have hOff := offset hLoc
    have hStage : actualStage = stage := Fin.ext (by omega)
    subst actualStage
    have hCta : g / l.block = cta := congrArg Loc.cta hLoc.symm
    have hSite : 2768 ≤ freePc stage ∧ freePc stage < 3099 :=
      (by decide : ∀ s : Fin 2, 2768 ≤ freePc s ∧ freePc s < 3099) stage
    have hWarp := issuerWarpOfEpiloguePc hp hX he hSite.1 hSite.2
    let lane : Fin 32 := ⟨laneOf l g, by unfold laneOf; omega⟩
    have hLane : outputLane l cta lane = g := by
      have hParts := Nat.div_add_mod g l.block
      have hLaneParts := Nat.div_add_mod (g % l.block) 32
      change g % l.block / 32 = 13 at hWarp
      change cta * l.block + 416 + g % l.block % 32 = g
      rw [hp.block] at hWarp hParts hLaneParts hCta ⊢
      omega
    have hEvent : X.get (outputLane l cta lane, index) =
        some ⟨freePc stage, .arrive (freeObject l cta stage) 0 1 true .cta⟩ := by
      simpa only [hLane] using he
    exact ⟨lane, index, by simpa only [hLane] using hId,
      ⟨_, hEvent, rfl, rfl⟩, hAct⟩
  | increment _ he _ => exact (Loader.noIncrementingCopyArrival hX ⟨_, he⟩).elim
  | tensor _ he hl _ =>
    obtain ⟨site, rfl⟩ := Loader.actualInputIssuePc hX he
    have hLoc := Loader.loaderTensorOffset hp hX site he
    have audit : ∀ (j : Fin 14) (s : Fin 2),
        Loader.inputBarrierBase j + (Loader.inputSite j).barrierOffset ≠ 224 + 8 * s.val := by
      decide
    exact (audit site stage (offset (hl.symm.trans hLoc))).elim
  | arriveOn _ he hl _ _ =>
    obtain ⟨⟨site, rfl⟩, rfl, _, _⟩ := Loader.actualAsyncArrival hX he
    have hs := (by decide : ∀ q : Fin 6,
      Loader.copyCommitPc q + 1 ∈ [674, 904, 1137, 1342, 1602, 1735]) site
    obtain ⟨off, hh, ha⟩ := Loader.loaderAsyncAddress hp hX he hs
    have hOff := offset (hl.symm.trans ha)
    have hBound := (by decide : ∀ n ∈ [32, 40, 48], n ≤ 48) off hh
    omega
  | bulk _ he hCompletion _ _ =>
    rw [(actualCopyShape hX ⟨_, he⟩).completion] at hCompletion
    cases hCompletion
  | commit _ he hTarget _ =>
    rcases inCommitSites hX he with hFixed | hRing
    · obtain ⟨off, hOff, hLoc⟩ := Mma.mmaFixedCommitAddress hp hX he hFixed hTarget
      have hEq := offset hLoc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
      rcases hOff with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · obtain ⟨slot, hLoc⟩ := Mma.mmaRingCommitAddress hp hX he hRing hTarget
      have := offset hLoc
      have := slot.isLt
      omega
  | clc _ he _ _ _ => exact (noClcIssue hX ⟨_, he⟩).elim

end PTX.Kernels.TmlFa4Fwd.Thread.Output
