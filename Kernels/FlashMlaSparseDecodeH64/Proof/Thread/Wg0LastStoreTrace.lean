-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GlobalWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingGateEvents

public section

/-! # Softmax prefixes before publication of the last store -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0LastStoreTrace

open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The pre-loop sites before or at the last-store arrival. -/
@[expose] def Initial : Wg0.Site → Prop
  | .sink | .lenOrig | .lenExtra | .bulkWait | .lastStore => True
  | _ => False

/-- A lane may publish before it enters the first softmax loop iteration. -/
inductive Early : Machine.ThreadD → Prop
  | prologue (s : Machine.PSite) : Early (.prologue s)
  | softmax (d : Wg0.D) (h : Initial d.site) : Early (.wg0 d)

/-- The thread has no arrival on its CTA's last-store barrier in the execution. -/
@[expose] def Missing (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ∀ i tag, X.get (g, i) ≠ some ⟨tag, .arrive
    ⟨.shared, ctaOf L g, L.sharedBase + 222768⟩ 0 1 true .cta⟩

private theorem first_initial : Initial (Wg0.firstSite P) := by
  simp only [Wg0.firstSite, Wg0.afterSink, Wg0.afterLen]
  split_ifs <;> trivial

private theorem early_step {d q : Machine.ThreadD} {e : Event}
    (hWg : wgOf L g = 0) (hEarly : Early d)
    (hNot : ∀ v : Wg0.D, d = .wg0 v → v.site ≠ .lastStore)
    (hn : Machine.next P L g d e = some (some q)) : Early q := by
  cases hEarly with
  | prologue s =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
      exact .prologue _
    · split at hn
      · rename_i w _
        fin_cases w <;> simp [hWg] at hn
        subst q
        exact .softmax _ first_initial
      · cases hn
    · cases hn
  | softmax v h =>
    have hStop := hNot v rfl
    simp only [Machine.next] at hn
    split at hn
    · rename_i u hn'
      obtain rfl := Option.some.inj (Option.some.inj hn)
      have hNext : Wg0.nextSite P L g v e = some (some u) := hn'
      cases hSite : v.site <;> simp only [Initial, hSite] at h
      case lastStore => exact (hStop hSite).elim
      all_goals
        simp only [Wg0.nextSite, hSite] at hNext
        repeat' split at hNext
      all_goals cases hNext
      all_goals
        exact .softmax _ (by
          simp only [Wg0.afterSink, Wg0.afterLen]
          (try split_ifs) <;> trivial)
    · split at hn
      · rename_i hEnd
        rcases hEnd with hEnd | hEnd <;> rw [hEnd] at h <;> cases h
      · cases hn
    · cases hn

/-- A represented softmax lane which has not published the last-store arrival is still in the
prologue or the opening softmax states. -/
theorem early_of_missing (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hg : g < L.threads) (hWg : wgOf L g = 0) (hm : Missing L X g)
    {n : Nat} {d : Machine.ThreadD} (hn : n ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g n = some (some d)) : Early d := by
  induction n generalizing d with
  | zero =>
    rw [Frame.stateAt_zero] at hd
    obtain rfl := (Option.some.inj (Option.some.inj hd)).symm
    exact .prologue _
  | succ n ih =>
    obtain ⟨q, hq⟩ := Frame.stateAt_live ht hg hd (Nat.le_succ n)
    have hLt : n < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, n) = some e := ⟨_, List.getElem?_eq_getElem hLt⟩
    have hNext := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hq, hd] at hNext
    refine early_step hWg (ih hLt.le hq) (fun v hEq hSite => ?_) hNext.symm
    subst q
    obtain ⟨o, hf⟩ := RingEvents.fired_of_trace hX (hs g hg).machine he hq
    have hKind := RingEvents.lastStore_arrive hpre hSite hf
    obtain ⟨tag, kind⟩ := e
    change kind = _ at hKind
    subst kind
    exact hm n tag he

private theorem early_not_exit (hpre : Pre P L mem0)
    {d : Machine.ThreadD} {e : Event} {o : Option TState}
    (hEarly : Early d) (hf : (Machine.machine P L g).Fired (some d) e o) :
    e.kind ≠ .exit := by
  intro hExit
  cases hEarly with
  | prologue s => exact RingGateEvents.exit_after_prologue hf hExit s rfl
  | softmax q hi =>
    cases hSite : q.site <;> simp only [hSite, Initial] at hi
    case lastStore =>
      rw [RingEvents.lastStore_arrive hpre hSite hf] at hExit
      cases hExit
    all_goals
      have hCode : ∃ ins, kernel.code[q.site.pc]? = some ins ∧
          ins.op ≠ .ret ∧ ins.op ≠ .exit := by
        rw [hSite]
        first
        | exact ⟨_, Flow.code_156, by nofun, by nofun⟩
        | exact ⟨_, Flow.code_168, by nofun, by nofun⟩
        | exact ⟨_, Flow.code_181, by nofun, by nofun⟩
        | exact ⟨_, Flow.code_198, by nofun, by nofun⟩
      obtain ⟨ins, hc, hRet, hEnd⟩ := hCode
      obtain ⟨_, _, hf'⟩ := RingGateEvents.fired_at_code hf hc
      exact (fires_exit_op hf' hExit).elim hRet hEnd

/-- A softmax lane with a missing last-store arrival has not exited. -/
theorem not_exited_of_missing (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hWg : wgOf L g = 0) (hm : Missing L X g) {tag : Nat} :
    (X.tr g).getLast? ≠ some ⟨tag, .exit⟩ := by
  intro hLast
  have he : X.get (g, (X.tr g).length - 1) = some ⟨tag, .exit⟩ := by
    change (X.tr g)[(X.tr g).length - 1]? = _
    rwa [← List.getLast?_eq_getElem?]
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hd⟩ := Frame.event_state hs hX ht he (by simp)
  have hEarly := early_of_missing hpre hX hs ht hg hWg hm (len_of_get he).le hd
  obtain ⟨o, hf⟩ := RingEvents.fired_of_trace hX (hs g hg).machine he hd
  exact early_not_exit hpre hEarly hf rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0LastStoreTrace
