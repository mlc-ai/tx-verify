-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.FactsA
public import Kernels.RmsNorm.Proof.Thread.FactsB
public import Kernels.RmsNorm.Proof.Thread.FactsC
public import Lemmas.Flow.RunInv

@[expose] public section

/-! # The thread facts

Each event of a followed thread is its state's site event (`site_event`). Along a thread's run
the invariant `RunFacts` holds (`run_facts`, from the steps of each site). `thread_facts` proves
the interface's `ThreadFacts` from it. -/

namespace PTX.Kernels.RmsNorm.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- **The event of a site.** -/
theorem site_event (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hat : (code P L g).AtD d t) (hi : Inv P g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) : SiteEvent P g d e := by
  rw [tmpl_site hpre hi hat hc] at hf
  exact ⟨t, o, hf⟩

/-- One step of the run invariant. -/
theorem runFacts_step (hpre : Pre P L mem0) {d d' : D} {pre : List Event} {e : Event}
    {t : TState} {ins : Instr} {o : Option TState} (hJ : RunFacts P g d pre)
    (hat : (code P L g).AtD d t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o)
    (hn : next P g d e = some (some d')) : RunFacts P g d' (pre ++ [e]) := by
  have hev : Fires d.site.pc (siteTmpl P g d t) e o := by
    rw [← tmpl_site hpre hJ.1 hat hc]; exact hf
  rcases hs : d.site with _ | _ | _ | _ | _ | _ | _ | k | _ | _ | _ | k | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _
  · exact rf_shfl0 hJ hs hev hn
  · exact rf_ldxa hJ hs hev hn
  · exact rf_stxa0 hJ hs hev hn
  · exact rf_stxa1 hJ hs hev hn
  · exact rf_ldxb hJ hs hev hn
  · exact rf_stxb0 hJ hs hev hn
  · exact rf_stxb1 hJ hs hev hn
  · exact rf_bfa hJ hs hev hn
  · exact rf_stws hJ hs hev hn
  · exact rf_bar0 hJ hs hev hn
  · exact rf_ldws hJ hs hev hn
  · exact rf_bfb hJ hs hev hn
  · exact rf_stts hJ hs hev hn
  · exact rf_bar1 hJ hs hev hn
  · exact rf_ldts hJ hs hev hn
  · exact rf_ldwa hJ hs hev hn
  · exact rf_ldsa0 hJ hs hev hn
  · exact rf_ldsa1 hJ hs hev hn
  · exact rf_stoa hJ hs hev hn
  · exact rf_ldwb hJ hs hev hn
  · exact rf_ldsb0 hJ hs hev hn
  · exact rf_ldsb1 hJ hs hev hn
  · exact rf_stob hJ hs hev hn
  · exact rf_bar2 hJ hs hev hn
  · simp [next, hs] at hn

theorem runFacts_init : RunFacts P g ({ site := .shfl0 } : D) [] := by
  refine ⟨?_, rfl, rfl, rfl, rfl, ?_, fun _ => rfl⟩
  · show Inv P g ({ site := .shfl0 } : D)
    inv_tac
  · constructor <;> intro h <;> simp [Site.inRow, Site.vload] at h

variable {X : Execution}

/-- **The run invariant holds at every followed state.** -/
theorem run_facts (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {d : D} (hσ : stateAt P L X g k = some (some d)) :
    RunFacts P g d ((X.tr g).take k) := by
  have htr := (sound hpre hg).machine.produces (hX.thr g hg)
  refine Code.run_inv (sound hpre hg) htr (RunFacts P g) runFacts_init ?_ k d hσ
  intro d d' pre e t ins o hJ hat _ hc hf hn
  exact runFacts_step hpre hJ hat hc hf hn

theorem loadNext_ne {d : D} {e : Event} {k : List Value → Option D} : loadNext d e k ≠ some none :=
    by
  unfold loadNext
  repeat' split
  all_goals simp

/-- The machine never gives up a thread: a step continues in a state or stops. -/
theorem next_ne (g : Nat) (d : D) (e : Event) : next P g d e ≠ some none := by
  unfold next
  split
  all_goals first
    | exact loadNext_ne
    | (unfold storeNext; split <;> simp)
    | (repeat' split) <;> simp

/-- **The thread facts of a consistent execution.** -/
theorem thread_facts (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ThreadFacts P L X := by
  have hC : ∀ g < L.threads, (codes P L g).Sound := fun g hg => sound hpre hg
  have ht : Frame.Tracked (codes P L) X := Frame.tracked_of_next fun g d e => next_ne g d e
  refine ⟨ht, fun hg hσ => (run_facts hpre hX hg hσ).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g k e d hg he hσ
    obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hC hX he hσ
    exact site_event hpre hat hinv hc hf
  · intro g k d hg hk hσ
    have h := (run_facts hpre hX hg hσ).2.1
    rwa [List.length_take, Nat.min_eq_left hk] at h
  · intro g k d hg hσ
    obtain ⟨-, -, h0, h1, hs, -, -⟩ := run_facts hpre hX hg hσ
    exact ⟨h0, h1, hs⟩
  · intro g k d hg hσ
    exact (run_facts hpre hX hg hσ).2.2.2.2.2.1
  · intro g k hg hk hσ
    obtain ⟨j, d, hj, hσj, hσj'⟩ := Frame.first_stop ht hg hσ
    obtain ⟨e, he⟩ : ∃ e, X.get (g, j) = some e :=
      ⟨_, List.getElem?_eq_getElem (show j < (X.tr g).length by omega)⟩
    refine ⟨j, d, e, hj, hσj, he, ?_⟩
    rw [Frame.stateAt_succ he, hσj] at hσj'
    exact hσj'
  · intro g k pc f hg he
    rcases Code.ub_stopped (hC g hg) (tmplOk hpre) (hX.thr g hg) he with h | h
    · exact h
    · exact absurd h (ht g k hg)
  · intro g t d hg hr hσ
    obtain ⟨t1, ins, hl, hat, hinv, hc, hout⟩ := Frame.end_at hC hg hr hσ
    refine ⟨t1, hl, hat.1, ?_⟩
    rw [hout, tmpl_site hpre hinv hat hc]

end
end PTX.Kernels.RmsNorm.Proof
