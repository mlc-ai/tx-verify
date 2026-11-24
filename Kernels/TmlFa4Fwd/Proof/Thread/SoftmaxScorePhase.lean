-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxProbabilityGate
public import Lemmas.Protocol.PollIndex
public import Kernels.TmlFa4Fwd.Proof.SoftmaxCreditPhase
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Kernels.TmlFa4Fwd.Proof.CtaMemoryOrder
import Kernels.TmlFa4Fwd.Flow.Code.Part053
import Kernels.TmlFa4Fwd.Flow.Code.Part079
import Kernels.TmlFa4Fwd.Flow.Code.Part104

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Prologue
open PTX.Kernels.TmlFa4Fwd.Softmax

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem scoreSite {g i pc q cta : Nat} {ok acq : Bool} {scope : MbarScope} (stage : Fin 2)
    (hw : warpIndex l g < 8)
    (he : X.get (g,i) = some ⟨pc, .wait (scoreReadyObject l cta stage) q ok acq scope⟩) :
    pc ∈ [3425, 5109, 6676] := by
  let poll := Flow.mbarWait.toList
  have hSource := actualMbarPollSite hX he
  have hAudit : poll.all (fun s => decide (173 < s ∧ s < 9205 ∧ s ∉ registerHintSites)) = true :=
    by decide
  obtain ⟨hLo, _, hHint⟩ := of_decide_eq_true (List.all_eq_true.mp hAudit _ hSource)
  have hRole := roleBodyPcOfEvent hp hX he hLo hHint
  change roleBodyPc (warpIndex l g) pc at hRole
  have hRange : 3103 ≤ pc ∧ pc ≤ 7742 := by
    rcases hRole with h | h
    · omega
    · have hA : ¬ 14 ≤ warpIndex l g := by omega
      have hB : warpIndex l g ≠ 13 := by omega
      have hC : warpIndex l g ≠ 12 := by omega
      simpa only [hA, hB, hC, hw, ↓reduceIte] using h
  have hCases : poll.all (fun s => decide ((3103 ≤ s ∧ s ≤ 7742) →
      s ∈ [3425, 5109, 6676] ∨ s ∈ [3498, 5181] ∨ s ∈ [3420,4874,6558,7463,7738])) = true :=
    by decide
  rcases (of_decide_eq_true (List.all_eq_true.mp hCases _ hSource)) hRange with h | h | h
  · exact h
  · have hAddress := congrArg Loc.addr (biasReadyWaitAddress hp hX (g := g) (index := i) he h)
    change l.sharedBase + (80 + 8 * stage.val) =
      l.sharedBase + (320 + 8 * (warpIndex l g / 4)) at hAddress
    have hStage := stage.isLt
    omega
  · have hs : pc ∈ [3420, 3425, 3498, 4874, 5109, 5181, 6558, 6676, 7463, 7738] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      tauto
    obtain ⟨offset, hOff, hLoc⟩ := softmaxWaitAddressClass hp hX (g := g) (index := i) he hs
    rw [ite_eq_left h] at hOff
    have hAddress := congrArg Loc.addr hLoc
    change l.sharedBase + (80 + 8 * stage.val) = l.sharedBase + offset at hAddress
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
    have hStage := stage.isLt
    omega

/-- Successful softmax score observations use an acquire at CTA scope. -/
theorem successfulScoreWaitIsAcquire {g i source q cta : Nat} {acq : Bool} {scope : MbarScope}
    (stage : Fin 2) (hw : warpIndex l g < 8)
    (he : X.get (g,i) = some ⟨source,.wait (scoreReadyObject l cta stage) q true acq scope⟩) :
    acq = true ∧ scope = .cta := by
  have hScope := actualPollScope hX he
  have hSite := scoreSite hp hX stage hw he
  have audit {pc : Nat} (h : pc ∈ [3425,5109,6676]) :
      ∃ pred base phase, kernel.code[pc]? =
        some ⟨none,.mbarWait pred base 0 (.reg phase) true .cta⟩ := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨_,_,_,Flow.code_3425⟩
    · exact ⟨_,_,_,Flow.code_5109⟩
    · exact ⟨_,_,_,Flow.code_6676⟩
  obtain ⟨pred,base,phase,hCode⟩ := audit hSite
  rcases get_source hX he with ⟨_,hBad⟩ | ⟨s,ins,u,_,hGet,hFire⟩
  · cases hBad
  change kernel.code[source]? = some ins at hGet
  rw [hCode] at hGet
  obtain rfl := Option.some.inj hGet.symm
  obtain ⟨_,_,_,_,_,hFlags,_⟩ := fires_wait_flags hFire
    (show (⟨source,.wait (scoreReadyObject l cta stage) q true acq scope⟩ : Event).kind =
      .wait (scoreReadyObject l cta stage) q true acq scope from rfl)
  exact ⟨(Op.mbarWait.inj hFlags).2.2.2.2.1.symm,hScope⟩

/-- The decoded score wait marker counts the physical successful acquisitions of this stage. -/
theorem scoreCount {g j cta : Nat} (stage : Fin 2) (hw : warpIndex l g < 8)
    (hCta : g / l.block = cta) (hStage : warpIndex l g / 4 = stage.val) :
    ((X.tr g).take j).countP (phaseAcquired true) =
      okPolls (scoreReadyObject l cta stage) ((X.tr g).take j) := by
  apply List.countP_congr
  intro e hMem
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hMem)
  rw [scoreReadyMarkKind]
  obtain ⟨source, kind⟩ := e
  cases kind <;> try rfl
  case wait loc q ok acq scope =>
    cases ok
    · rfl
    change ([3425, 5109, 6676] : List Nat).contains source = true ↔
      decide (loc = scoreReadyObject l cta stage) = true
    rw [List.contains_iff_mem, decide_eq_true_eq]
    constructor
    · intro h
      have hLoc := (scoreReadyWaitStage hp hX (g := g) (index := i) hi h).2
      rw [hCta, hStage] at hLoc
      exact hLoc
    · rintro rfl
      exact scoreSite hp hX stage hw hi

/-- The role-local score cursor agrees with alternating successful object-history observations. -/
theorem scoreReadySelectedAlternates {cta g : Nat} (stage : Fin 2) (hw : warpIndex l g < 8)
    (hCta : g / l.block = cta) (hStage : warpIndex l g / 4 = stage.val) :
    SelectedAlternates (objectThreadSelected g) (X.objects (scoreReadyObject l cta stage)) 0 := by
  apply MbarRing.Poll.alternates hX (fun _ hr hPoll => actualInitOrPollClean hp hX hr (.inr hPoll))
  intro j source q acq scope hPoll
  have hSite := scoreSite hp hX stage hw hPoll
  rw [scoreReadySourceParity hp hX hPoll hSite, scoreCount hp hX stage hw hCta hStage,
    Nat.add_zero, Nat.mod_mod]

/-- The actual probability and score-ready objects agree exactly at every score load. -/
theorem scoreLoadExactCursor {g j address : Nat} {values : List Value} {shape : TcShape}
    (stage : Fin 2) (hw : warpIndex l g < 8) (hs : warpIndex l g/4 = stage.val)
    (round : Softmax.Round) (quarter : Fin 4)
    (he : X.get (g,j) = some ⟨Softmax.scorePc round quarter,.tc (.ld address values shape)⟩) :
    okPolls (scoreReadyObject l (g/l.block) stage) ((X.tr g).take j) =
      probabilityOrdinal l X (g/l.block) stage 0 (g,j)+1 := by
  have hLedger := Softmax.actualScoreLoadEarlyLedger hX round quarter he
  have hScore := scoreCount (j := j) hp hX stage hw rfl hs
  have hEarly := earlyProbabilityCount hp hX stage hw hs (len_of_get he)
  have hMark : Softmax.phaseAcquired true = Softmax.scoreAcquireMark := by
    funext e
    rw [Softmax.scoreReadyMarkKind]
    rfl
  rw [hMark] at hScore
  rw [← hScore,hLedger,hEarly]

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
