-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderTasks
public import Kernels.Fp16Gemm8192.Proof.Interface
public import Kernels.Fp16Gemm8192.Proof.Thread.RankCounts

@[expose] public section

/-! # The loader's exact counts on a trace without undefined behaviour

`LoaderTasks.Counts` carries, on a trace with no `ub` event, the exact counts of the loader outside
its exit stage: its tensor issues and loads to issue on each slot, and its arrivals and pending
batch
on the leader CTA, against its successful empty polls, less the drain's polls (`loader_exact`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A thread's trace with no `ub` event is `LoaderTasks.NoUb`. -/
theorem noUb_of_no_ub {g : Nat} (hub : ∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) :
    LoaderTasks.NoUb (X.tr g) := by
  intro e he f hf
  obtain ⟨i, hlt, hi⟩ := List.getElem_of_mem he
  obtain ⟨pc, k⟩ := e
  have hk : k = .ub f := hf
  subst hk
  exact hub i pc f (by show (X.tr g)[i]? = _; rw [List.getElem?_eq_getElem hlt, hi])

set_option maxHeartbeats 4000000 in
/-- The elected loader's counts are exact on a trace without undefined behaviour, outside its exit
stage. -/
theorem loader_exact_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ∀ {g : Nat} {l : Loader.D}, g < L.threads →
    (∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) → l.site.done =
      false →
    (∀ s : Fin 4, (X.tr g).countP (issuesTo (Loader.fullOf L g s)) + Loader.remaining l s +
      3 * Loader.drained l s = 3 * okPolls (Loader.emptyOf L g s) (X.tr g)) ∧
    (Loader.leader L g = true → ∀ s : Fin 4, arrivals (Loader.fullOf L g s) (X.tr g) +
      (if Loader.pending l s then 1 else 0) + Loader.drained l s =
        okPolls (Loader.emptyOf L g s) (X.tr g)) := by
  intro g l hg hub hσ hd
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have c : LoaderTasks.Counts L g l (X.tr g) := by
    have h := LoaderTasks.run hpre hg htr (X.tr g).length (.inr (.loader l)) hσ
    rw [List.take_length] at h
    exact h
  obtain ⟨c1, c2⟩ := c.exact hd (noUb_of_no_ub hub)
  exact ⟨c1, c2⟩

/-- The elected loader's exit-stage counts on a trace without undefined behaviour, once it has
polled
the response (`0 < loaderCount`): the drain's polls are the one extra successful poll per slot. -/
theorem loader_exit_exact_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ∀ {g : Nat} {l : Loader.D}, g < L.threads →
    (∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) → l.site.done =
      true →
    0 < loaderCount L g (X.tr g) →
    (∀ s : Fin 4, (X.tr g).countP (issuesTo (Loader.fullOf L g s)) + 3 =
      3 * okPolls (Loader.emptyOf L g s) (X.tr g)) ∧
    (Loader.leader L g = true → ∀ s : Fin 4, arrivals (Loader.fullOf L g s) (X.tr g) + 1 =
      okPolls (Loader.emptyOf L g s) (X.tr g)) := by
  intro g l hg hub hσ hd hpos
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have c : LoaderTasks.Counts L g l (X.tr g) := by
    have h := LoaderTasks.run hpre hg htr (X.tr g).length (.inr (.loader l)) hσ
    rw [List.take_length] at h
    exact h
  rw [loaderCount_eq] at hpos
  obtain ⟨c1, c2⟩ := c.exitExact hd hpos (noUb_of_no_ub hub)
  exact ⟨c1, c2⟩

/-- The elected loader's exit-stage empty polls once it has polled the response: 128 per response
poll,
plus the drain's four polls. -/
theorem loader_exit_tasks_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ∀ {g : Nat} {l : Loader.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) → l.site.done =
      true →
    0 < loaderCount L g (X.tr g) →
    loaderCount L g (X.tr g) = 128 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) +
      4 := by
  intro g l hg hσ hd hpos
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have c : LoaderTasks.Counts L g l (X.tr g) := by
    have h := LoaderTasks.run hpre hg htr (X.tr g).length (.inr (.loader l)) hσ
    rw [List.take_length] at h
    exact h
  rw [loaderCount_eq] at hpos ⊢
  exact c.exitTasks hd hpos

/-- An elected loader that has left its task loop after a response (`0 < okPolls`): its latest
successful response poll is followed by a read of a response that names no first CTA. -/
theorem loader_exit_claim_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ∀ {g : Nat} {l : Loader.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) →
    ((∃ i : Fin 4, l.site = .drain i) ∨ l.site = .exitArrive ∨ l.site = .exitWait ∨ l.site =
    .exit) →
    0 < okPolls (clcResp L g) (X.tr g) →
    ∃ j pc p acq sc pcr a bs rr, (X.tr g)[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ ∧
      (X.tr g)[j + 1]? = some ⟨pcr, .rd a bs⟩ ∧ a.loc = respLoc L g ∧ a.size = 16 ∧
      Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr ∧
      okPolls (clcResp L g) ((X.tr g).take j) + 1 = okPolls (clcResp L g) (X.tr g) := by
  intro g l hg hσ hd hpos
  have hleave : l.site.leaving = true := by
    rcases hd with ⟨i, hi⟩ | hi | hi | hi <;> simp [hi, Loader.Site.leaving]
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have c : LoaderTasks.Counts L g l (X.tr g) := by
    have h := LoaderTasks.run hpre hg htr (X.tr g).length (.inr (.loader l)) hσ
    rw [List.take_length] at h
    exact h
  obtain ⟨rr, hrr, hx⟩ := c.heldX (Or.inr (Or.inr hleave)) hpos
  have hnone := c.leaveX hleave hpos
  obtain ⟨j, pc, p, acq, sc, pcr, a, bs, h1, h2, ha, hs, hr, hcnt⟩ := hrr
  refine ⟨j, pc, p, acq, sc, pcr, a, bs, rr, h1, h2, ha, hs, hr, ?_, hcnt⟩
  intro hcl
  have hfo : LoaderTasks.firstOfL rr = Loader.none32 := by rw [← hx]; exact hnone
  unfold LoaderTasks.firstOfL at hfo
  exact hcl hfo

/-- Every loader state's block count is a multiple of eight. -/
theorem loader_q8_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ∀ {g : Nat} {l : Loader.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) → l.q % 8 = 0 := by
  intro g l hg hσ
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have c : LoaderTasks.Counts L g l (X.tr g) := by
    have h := LoaderTasks.run hpre hg htr (X.tr g).length (.inr (.loader l)) hσ
    rw [List.take_length] at h
    exact h
  exact c.q8

end
end PTX.Kernels.Fp16Gemm8192.Proof
