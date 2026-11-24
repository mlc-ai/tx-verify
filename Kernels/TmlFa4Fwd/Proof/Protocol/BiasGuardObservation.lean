-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasWaitHistory
import Kernels.TmlFa4Fwd.Proof.MbarSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Thread.Loader

/-- Every reused Bias buffer was returned through at least its preceding generation before
the loader's expectation. The selected poll uses only that buffer's successful history. -/
theorem biasReuseGuardObserved {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta g j : Nat} (stage : Fin 2)
    (hIssue : X.Arrive (g,j) (biasReadyObject l cta stage) 32768 1 true .cta)
    (hReused : 0 < arrivals (biasReadyObject l cta stage) ((X.tr g).take j)) :
    let ordinal := arrivals (biasReadyObject l cta stage) ((X.tr g).take j)
    let log := X.objects (biasEmptyObject l cta stage)
    ∃ (k i phase : Nat) (r : Record Ref), log[i]? = some r ∧ r.id = .thread (g,k) ∧
      r.fault = none ∧ r.reply.waited = some true ∧
      Resumes kernel X (g,k) (g,j) ∧ observedAt log i = some phase ∧ ordinal ≤ phase + 1 := by
  let ordinal := arrivals (biasReadyObject l cta stage) ((X.tr g).take j)
  let obj := biasEmptyObject l cta stage
  let log := X.objects obj
  obtain ⟨k, e, hGet, hKind, hOrdinal, hResume⟩ :=
    biasExpectationGenerationGuard hp hX stage hIssue
  have hClean : ∀ r ∈ log, (∃ p ok, r.action = .pollParity p ok) → r.fault = none := by
    intro r hr hPoll
    exact actualInitOrPollClean hp hX hr (.inr hPoll)
  have hNo := objects_noInval hX.tma.2.2.1 (fun i _ => noMbarInval hX (i := i)) obj
  have hAlt := biasEmptySelectedAlternates hp hX stage hIssue hClean
  obtain ⟨source, kind⟩ := e
  change kind = _ at hKind
  subst kind
  have hOrdinal' := MbarRing.Poll.nth_eq hGet
  rw [hOrdinal] at hOrdinal'
  have hBound : ordinal < okPolls obj (X.tr g) := by
    apply MbarRing.Poll.nth_present.mp
    rw [hOrdinal']
    exact ⟨_, hGet⟩
  obtain ⟨i, r, _, hIndex, hI, _, hSuccess, hF, hCount⟩ :=
    MbarRing.Poll.record hX hClean hBound
  have hId : r.id = .thread (g,k) := by rw [hI, hOrdinal']
  have hSel : objectThreadSelected g r.id = true := objectThreadSelected_iff.mpr ⟨k, hId⟩
  have hChecked := X.objects_checked hX obj
  obtain ⟨st, hSt, hLower, _⟩ := hChecked.selected_poll_phase_ge hNo
    (objectThreadSelected g) (by decide : 1 ≤ 1) hAlt hIndex hSel hSuccess
  have hPos : 0 < st.phase := by omega
  obtain ⟨s, q, hs, _, _, hComplete⟩ := hChecked.okPoll hIndex hSuccess
  rw [hSt] at hs
  obtain rfl := Option.some.inj hs
  have hObs : observedAt log i = some (st.phase - 1) := by
    change ((X.objects obj)[i]?.bind (·.reply.completed)) = _
    rw [hIndex, Option.bind_some, hComplete, ite_eq_left hPos]
  exact ⟨k, i, st.phase - 1, r, hIndex, hId, hF, hSuccess, hResume, hObs, by omega⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
