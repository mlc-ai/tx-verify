-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

public import Kernels.InklingRelDecode.Proof.Lib.WindowFwd
public import Lemmas.Kernel.FrameEnd
public import Lemmas.Step.ExitLast
public import Lemmas.Flow.ReturningPrefix

@[expose] public section

/-! # The event after a state at pc 2562

The code at 2562 to 2564 is local without jumps and a wait follows at 2565, so a state of a
lane at pc 2562 of a complete execution is followed by an event of pc 2565, or by undefined
behaviour. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

variable {L : Launch} {g : Nat}

theorem win2562 : fwdWin 2562 2565 = true := by decide +kernel

theorem code_len : 2565 ≤ kernel.code.length := by decide +kernel

/-- An event fired from a local instruction is undefined behaviour. -/
theorem estep_local_ub {t : TState} {e : Event} {o : Option TState}
    (hes : EStep kernel Assumptions.all L g t e o) {ins : Instr}
    (hc : kernel.code[t.pc]? = some ins) (hl : ins.op.isLocal = true) : ∃ f, e.kind = .ub f := by
  obtain ⟨m, ho, hf⟩ := hes
  have ub : ∀ f, m = .ub f → ∃ f, e.kind = .ub f := fun f h => by
    subst h
    exact ⟨f, by simp only [Fires] at hf; rw [hf.1]⟩
  unfold out at ho
  split at ho
  · cases ho
    exact ub _ rfl
  · split at ho
    · cases ho
      exact ub _ rfl
    · rename_i ins' hc'
      obtain rfl : ins' = ins := Option.some.inj (hc'.symm.trans hc)
      split at ho
      · cases ho
        exact ub _ rfl
      · cases ho
      · simp only [hl, ↓reduceIte] at ho
        split at ho
        · cases ho
        · cases ho
          exact ub _ rfl

/-- **The state about to perform the next event** of a lane is reached by local steps. -/
theorem next_state {X : Execution} {m : Mem0} (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) {k : Nat} {t0 : TState} {ev : Event}
    (hr : Run kernel Assumptions.all L g {} ((X.tr g).take k) (some t0))
    (nxt : X.get (g, k) = some ev) : ∃ s o, Relation.ReflTransGen (Tau kernel Assumptions.all L g)
      t0 s ∧ EStep kernel Assumptions.all L g s ev o := by
  obtain ⟨o, hrun⟩ := hX.thr g hg
  have hs := List.take_append_drop k (X.tr g)
  rw [← hs] at hrun
  have tail := hr.after_returned_prefix hrun
  have hd : (X.tr g).drop k = ev :: ((X.tr g).drop (k + 1)) := by
    rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp nxt).1]
    rw [(List.getElem?_eq_some_iff.mp nxt).2]
  rw [hd] at tail
  generalize (X.tr g).drop (k + 1) = rest at tail
  cases tail with
  | step h1 hes _ => exact ⟨_, _, h1, hes⟩
  | last h1 hes => exact ⟨_, _, h1, hes⟩

/-- **The next event after a state at 2562** is at pc 2565 or undefined behaviour. -/
theorem next_2562 {X : Execution} {m : Mem0} (hX : Consistent L kernel Assumptions.all m X)
    (hc : Complete L X) (hg : g < L.threads) (hcl : ¬ ClcCanceled L X g) {k : Nat}
    {t0 t : TState} (hr : Run kernel Assumptions.all L g {} ((X.tr g).take k) (some t0))
    (ht : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t0 t) (hpc : t.pc = 2562) :
    ∃ e, (X.tr g)[k]? = some e ∧ (e.pc = 2565 ∨ ∃ f, e.kind = .ub f) := by
  obtain ⟨o, hrun⟩ := hX.thr g hg
  have hs := List.take_append_drop k (X.tr g)
  rw [← hs] at hrun
  have tail := hr.after_returned_prefix hrun
  have go : ∀ {t1 : TState} {e : Event} {o' : Option TState},
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) t0 t1 → EStep kernel Assumptions.all
        L g t1 e o' → e.pc = 2565 ∨ ∃ f, e.kind = .ub f := by
    intro t1 e o' h1 hes
    have e1 := EventFrame.estep_source_pc hes
    have ord : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t t1 := by
      rcases rtg_tau_total ht h1 with h | h
      · exact h
      · rcases Relation.ReflTransGen.cases_head h with rfl | ⟨_, hTau, _⟩
        · exact .refl
        · exact (not_tau_of_stops (stops_of_estep hes) hTau).elim
    obtain ⟨a1, a2⟩ := rtg_fwd win2562 ord (by omega) (by omega)
    by_cases h5 : t1.pc = 2565
    · exact .inl (by omega)
    · obtain ⟨ins, hci⟩ : ∃ ins, kernel.code[t1.pc]? = some ins :=
        ⟨_, List.getElem?_eq_getElem (lt_of_lt_of_le (by omega : t1.pc < 2565) code_len)⟩
      exact .inr (estep_local_ub hes hci (fwdWin_at win2562 (by omega) (by omega) hci).2)
  cases hd : (X.tr g).drop k with
  | nil =>
    rw [hd] at tail
    exfalso
    obtain ⟨j, pc, hj, he⟩ := Frame.Complete.exit_last hc hg hcl
    have hk : (X.tr g).length ≤ k := by simpa using hd
    have := Run.no_exit hr (j := j) (pc := pc)
    rw [List.getElem?_take_of_lt (by omega)] at this
    exact this he
  | cons e rest =>
    rw [hd] at tail
    refine ⟨e, ?_, ?_⟩
    · have := List.getElem?_drop (xs := X.tr g) (i := k) (j := 0)
      rw [hd] at this
      simpa using this.symm
    · cases tail with
      | step h1 hes _ => exact go h1 hes
      | last h1 hes => exact go h1 hes

end PTX.Kernels.InklingRelDecode.Proof.Lib
