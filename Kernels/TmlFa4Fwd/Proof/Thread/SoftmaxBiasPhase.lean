-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasConsume
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyPhase
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
import Lemmas.Protocol.PollIndex

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Softmax
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Thread.Loader
open PTX.Kernels.TmlFa4Fwd.Softmax

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem softmaxBiasReadyPollSite {g i pc q cta : Nat} {ok acq : Bool} {scope : MbarScope}
    (stage : Fin 2) (hw : Prologue.warpIndex l g < 8)
    (he : X.get (g,i) = some ⟨pc, .wait (biasReadyObject l cta stage) q ok acq scope⟩) :
    pc = 3498 ∨ pc = 5181 := by
  let poll := Flow.mbarWait.toList
  have hSource := actualMbarPollSite hX he
  have hAudit : poll.all (fun s =>
    decide (173 < s ∧ s < 9205 ∧ s ∉ registerHintSites)) = true := by decide
  obtain ⟨hLo, hHi, hHint⟩ := of_decide_eq_true (List.all_eq_true.mp hAudit _ hSource)
  have hRole := roleBodyPcOfEvent hp hX he hLo hHint
  change roleBodyPc (Prologue.warpIndex l g) pc at hRole
  have hRoleRange : 3103 ≤ pc ∧ pc ≤ 7742 := by
    rcases hRole with h | h
    · omega
    · have hA : ¬ 14 ≤ Prologue.warpIndex l g := by omega
      have hB : Prologue.warpIndex l g ≠ 13 := by omega
      have hC : Prologue.warpIndex l g ≠ 12 := by omega
      simpa only [hA, hB, hC, hw, ↓reduceIte] using h
  let score := [3425, 5109, 6676]
  let stats := [3420, 4874, 6558, 7463, 7738]
  have hCases : poll.all (fun s => decide
      (3103 ≤ s ∧ s ≤ 7742 → s = 3498 ∨ s = 5181 ∨ s ∈ score ∨ s ∈ stats)) = true :=
    by decide
  have hSite := (of_decide_eq_true (List.all_eq_true.mp hCases _ hSource)) hRoleRange
  rcases hSite with h | h | h | h
  · exact .inl h
  · exact .inr h
  · obtain ⟨offset, hOff, hLoc⟩ := scoreReadyWaitOffset hp hX (g := g) (index := i) he h
    have hAddr := congrArg Loc.addr hLoc
    change l.sharedBase + (320 + 8 * stage.val) = l.sharedBase + offset at hAddr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
    omega
  · have hs : pc ∈ [3420, 3425, 3498, 4874, 5109, 5181, 6558, 6676, 7463, 7738] := by
      simp only [stats, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      tauto
    obtain ⟨offset, hOff, hLoc⟩ := softmaxWaitAddressClass hp hX (g := g) (index := i) he hs
    rw [ite_eq_left h] at hOff
    have hAddr := congrArg Loc.addr hLoc
    change l.sharedBase + (320 + 8 * stage.val) = l.sharedBase + offset at hAddr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
    omega

/-- Counts the actual successful waits on this stage within the lane prefix. -/
theorem softmaxBiasSourceCount {g j cta : Nat} (stage : Fin 2) (hw : Prologue.warpIndex l g < 8)
    (hCta : g / l.block = cta) (hStage : Prologue.warpIndex l g / 4 = stage.val) :
    ((X.tr g).take j).countP readSuccess =
      okPolls (biasReadyObject l cta stage) ((X.tr g).take j) := by
  apply List.countP_congr
  intro e hMem
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hMem)
  obtain ⟨site, kind⟩ := e
  cases kind <;> try rfl
  rename_i target q ok acq scope
  cases ok
  · rfl
  change (site == 3498 || site == 5181) = true ↔
    decide (target = biasReadyObject l cta stage) = true
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have hSite : site ∈ [3498, 5181] := by simpa using h
    have hLoc := biasReadyWaitAddress hp hX (g := g) (index := i) hi hSite
    rw [hLoc, hCta, hStage]
    rfl
  · intro h
    subst target
    exact softmaxBiasReadyPollSite hp hX (g := g) (i := i) stage hw hi

/-- Each Bias stage's ready observations alternate in the physical softmax consumer's
object history, starting with parity zero. -/
theorem biasReadySelectedAlternates {cta : Nat} (stage : Fin 2) {g : Nat}
    (hw : Prologue.warpIndex l g < 8) (hCta : g / l.block = cta)
    (hStage : Prologue.warpIndex l g / 4 = stage.val)
    (hClean : ∀ r ∈ X.objects (biasReadyObject l cta stage),
      (∃ q ok, r.action = .pollParity q ok) → r.fault = none) :
    SelectedAlternates (objectThreadSelected g) (X.objects (biasReadyObject l cta stage)) 0 := by
  apply MbarRing.Poll.alternates hX hClean
  intro j site q acq scope he
  have hSite := softmaxBiasReadyPollSite hp hX stage hw he
  rw [biasReadySourceParity hp hX he hSite,
    softmaxBiasSourceCount hp hX stage hw hCta hStage, Nat.add_zero, Nat.mod_mod]


/-- A real Bias return follows a successful ready observation of at least its local ordinal. -/
theorem biasReadyObservedOfReturn {cta : Nat} (stage : Fin 2) {e : EvId}
    (hIssue : X.Arrive e (biasEmptyObject l cta stage) 0 1 true .cta) :
    let log := X.objects (biasReadyObject l cta stage)
    ∃ (k i phase : Nat) (r : Record Ref), log[i]? = some r ∧
      r.id = .thread (e.1,k) ∧ r.reply.waited = some true ∧ observedAt log i = some phase ∧
      arrivals (biasEmptyObject l cta stage) ((X.tr e.1).take e.2) ≤ phase ∧
      Resumes kernel X (e.1,k) e := by
  obtain ⟨g,j⟩ := e
  obtain ⟨site, hGet⟩ := hIssue
  have hIssue : X.Arrive (g,j) (biasEmptyObject l cta stage) 0 1 true .cta := ⟨site,hGet⟩
  have hSite := actualBiasEmptyArrivalSite hp hX stage hGet rfl
  obtain ⟨_, _, _, _, hWarp, hLoc⟩ := biasEmptyArriveFacts hp hX hGet hSite
  have hCta : g / l.block = cta := (congrArg Loc.cta hLoc).symm
  have hAddress := congrArg Loc.addr hLoc
  change l.sharedBase + (336 + 8 * stage.val) =
    l.sharedBase + (336 + 8 * (Prologue.warpIndex l g / 4)) at hAddress
  have hStage : Prologue.warpIndex l g / 4 = stage.val := by omega
  let loc := biasReadyObject l cta stage
  let log := X.objects loc
  let ordinal := arrivals (biasEmptyObject l cta stage) ((X.tr g).take j)
  have hClean : ∀ r ∈ log, (∃ q ok, r.action = .pollParity q ok) → r.fault = none := by
    intro r hr hq
    exact actualInitOrPollClean hp hX hr (.inr hq)
  have hAlt := biasReadySelectedAlternates hp hX stage hWarp hCta hStage hClean
  obtain ⟨k, w, q, acquire, scope, hW, hK, hOrdinal, hTail⟩ :=
    biasReadyAcquireOfReturn hp hX stage hIssue
  obtain ⟨source, kind⟩ := w
  change kind = _ at hK
  subst kind
  have hNth := MbarRing.Poll.nth_eq hW
  rw [hOrdinal] at hNth
  have hBound : ordinal < okPolls loc (X.tr g) := by
    apply MbarRing.Poll.nth_present.mp
    rw [hNth]
    exact ⟨_,hW⟩
  obtain ⟨i, r, _, hAt, hId, _, hReply, _, hCount⟩ := MbarRing.Poll.record hX hClean hBound
  rw [hNth] at hId
  have hChecked := X.objects_checked hX loc
  have hNo := objects_noInval hX.tma.2.2.1 (fun i _ => noMbarInval hX (i := i)) loc
  have hSel : objectThreadSelected g r.id = true := objectThreadSelected_iff.mpr ⟨k,hId⟩
  obtain ⟨s, hs, hLower, _⟩ := hChecked.selected_poll_phase_ge hNo
    (objectThreadSelected g) (by decide : 0 ≤ 1) hAlt hAt hSel hReply
  have hPos : 0 < s.phase := by omega
  obtain ⟨u, _, hu, _, _, hCompleted⟩ := hChecked.okPoll hAt hReply
  rw [hs] at hu
  obtain rfl := Option.some.inj hu
  have hPhase : observedAt log i = some (s.phase - 1) := by
    change ((X.objects loc)[i]?.bind (·.reply.completed)) = _
    rw [hAt, Option.bind_some, hCompleted, ite_eq_left hPos]
  refine ⟨k, i, s.phase - 1, r, hAt, hId, hReply, hPhase, ?_, hTail⟩
  change ordinal ≤ s.phase - 1
  omega
end

/-- A physical lane issues at most one arrival with a particular local object ordinal. -/
theorem arrivalOrdinalInjective {X : Execution} {loc : Loc} {g j k tx n : Nat}
    {rel : Bool} {scope : MbarScope}
    (hFirst : X.Arrive (g,j) loc tx n rel scope)
    (hSecond : X.Arrive (g,k) loc tx n rel scope)
    (hOrdinal : arrivals loc ((X.tr g).take j) = arrivals loc ((X.tr g).take k)) :
    j = k := by
  obtain ⟨_, he⟩ := hFirst
  obtain ⟨_, hf⟩ := hSecond
  have ha := nthEv_eq he (p := arrivesOn loc) (by simp [sourceArrive])
  have hb := nthEv_eq hf (p := arrivesOn loc) (by simp [sourceArrive])
  change ((X.tr g).take j).countP _ = ((X.tr g).take k).countP _ at hOrdinal
  rw [hOrdinal, hb] at ha
  exact ha.symm

/-- A recorded ordinary arrival is issued by a launched thread. -/
theorem arrivalIssuerPresent {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {e : EvId} {loc : Loc} {tx n : Nat}
    {rel : Bool} {scope : MbarScope} (hIssue : X.Arrive e loc tx n rel scope) :
    e.1 < l.threads := by
  obtain ⟨_, he⟩ := hIssue
  exact PTX.Proof.event_thread_lt hX he
end PTX.Kernels.TmlFa4Fwd.Thread.Softmax
