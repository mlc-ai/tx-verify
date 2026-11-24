-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantSignals

@[expose] public section

/-! # Actual dequantizer acquires and returns in block order -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- A prefix of the producer-consumer loop, with the block and whether its slot is held.
Failed polls and instructions on other objects leave this sequence unchanged. -/
inductive RawTurns : Nat → Bool → List RawSignal → Prop where
  | nil (block : Nat) (held : Bool) : RawTurns block held []
  | acquire {block : Nat} {es : List RawSignal} : RawTurns block true es →
      RawTurns block false (.acquire (block % 2) (block / 2 % 2) :: es)
  | release {block : Nat} {es : List RawSignal} : RawTurns (block + 1) false es →
      RawTurns block true (.release (block % 2) :: es)

private theorem raw_body_silent {t : TState} {before tail : List Event} {o : Option TState}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hPc : t.pc = 2680) (hRun : Run kernel Assumptions.all L g t (before ++ tail) o)
    (hBefore : ∀ f ∈ before, f.pc ≠ 3599)
    (hEvents : ∀ f ∈ before, ∃ i, X.get (g, i) = some f) :
    before.filterMap (rawSignal L g) = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro f hf
  obtain ⟨i, he⟩ := hEvents f hf
  have hNot := hBefore f hf
  obtain ⟨prior, later, hList⟩ := List.mem_iff_append.mp hf
  have hPrior : ∀ e ∈ prior, e.pc ≠ 3599 := by
    rw [hList] at hBefore
    intro e he
    exact hBefore e (List.mem_append_left _ he)
  rw [hList, List.append_assoc, List.cons_append] at hRun
  exact raw_signal_silent hpre hX he (dequant_body_event_bound hPc hPrior hRun) hNot

set_option maxHeartbeats 1000000 in
/-- Starting at an actual raw wait, the entire continuing raw trace follows the two-slot
acquire and release sequence, including partial blocks and the final epilogue. -/
theorem dequant_turns_of_poll {block : Nat} {t : TState} {events : List Event}
    {o : Option TState}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hAt : AtVector t 2677 (dequantPollFacts L g block) t.sub t.acc)
    (hRun : Run kernel Assumptions.all L g t events o)
    (hEvents : ∀ f ∈ events, ∃ i, X.get (g, i) = some f) :
    RawTurns block false (events.filterMap (rawSignal L g)) := by
  generalize hLength : events.length = n
  induction n using Nat.strong_induction_on generalizing events block t with
  | h n ih =>
    cases events with
    | nil => exact .nil _ _
    | cons e tail =>
      obtain ⟨ok, he, hContinue⟩ := dequant_raw_poll_of_run hpre hAt hRun
      have hSig := congrArg (rawSignal L g) he
      rw [raw_signal_wait] at hSig
      have hTail (f : Event) (hf : f ∈ tail) := hEvents f (List.mem_cons_of_mem _ hf)
      cases ok with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hSig hContinue
        simp only [List.filterMap_cons, hSig]
        cases tail with
        | nil => exact .nil _ _
        | cons hd tl =>
          obtain ⟨u, hu, hRun'⟩ := hContinue (by simp)
          have hLt : (hd :: tl).length < n := by rw [← hLength]; simp
          exact ih _ hLt hu hRun' hTail rfl
      | true =>
        simp only [↓reduceIte] at hSig hContinue
        simp only [List.filterMap_cons, hSig]
        apply RawTurns.acquire
        cases tail with
        | nil => exact .nil _ _
        | cons hd tl =>
          obtain ⟨v, hv, hBody⟩ := hContinue (by simp)
          let before := (hd :: tl).takeWhile (fun f => f.pc != 3599)
          let later := (hd :: tl).dropWhile (fun f => f.pc != 3599)
          have hSplit : hd :: tl = before ++ later := List.takeWhile_append_dropWhile.symm
          have hBefore : ∀ f ∈ before, f.pc ≠ 3599 := by
            intro f hf
            simpa using List.all_eq_true.mp List.all_takeWhile f hf
          have hBeforeMem : ∀ f ∈ before, ∃ i, X.get (g, i) = some f := by
            intro f hf
            apply hTail
            rw [hSplit]
            exact List.mem_append_left _ hf
          have hBody' : Run kernel Assumptions.all L g v (before ++ later) o := hSplit ▸ hBody
          have hSilent := raw_body_silent hpre hX hv.1 hBody' hBefore hBeforeMem
          rw [hSplit, List.filterMap_append, hSilent, List.nil_append]
          cases hLater : later with
          | nil => exact .nil _ _
          | cons release remaining =>
            have hTag : release.pc = 3599 := by
              have h := List.head?_dropWhile_not (fun f : Event => f.pc != 3599) (hd :: tl)
              change (hd :: tl).dropWhile (fun f : Event => f.pc != 3599) = _ at hLater
              simpa [hLater] using h
            rw [hLater] at hBody' hSplit
            rw [List.filterMap_cons,
              raw_signal_release (dequant_body_release hpre hv hTag hBefore hBody')]
            apply RawTurns.release
            cases remaining with
            | nil => exact .nil _ _
            | cons next rest =>
              obtain ⟨after, hAfter, hRun'⟩ := dequant_body_advance hv hTag hBefore hBody'
              rcases dequant_route_after_advance hpre hAfter hRun' with ⟨u, hu, hNext⟩ | hEpi
              · have hEvents' (f : Event) (hf : f ∈ next :: rest) := hTail f
                  (hSplit ▸ List.mem_append_right before (List.mem_cons_of_mem _ hf))
                have hLt : (next :: rest).length < n := by
                  have hLen := congrArg List.length hSplit
                  simp only [List.length_cons, List.length_append] at hLength hLen ⊢
                  omega
                exact ih _ hLt hu hNext hEvents' rfl
              · suffices (next :: rest).filterMap (rawSignal L g) = [] by rw [this]; exact .nil _ _
                apply List.filterMap_eq_nil_iff.mpr
                intro f hf
                have hBound := hEpi f hf
                have hf' : f ∈ hd :: tl := by
                  rw [hSplit]
                  exact List.mem_append_right before (List.mem_cons_of_mem _ hf)
                obtain ⟨i, he⟩ := hTail f hf'
                exact raw_signal_silent hpre hX he (by omega) (by omega)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
