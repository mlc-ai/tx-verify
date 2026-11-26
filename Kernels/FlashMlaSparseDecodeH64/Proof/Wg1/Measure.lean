-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Time

@[expose] public section

/-! # Warpgroup 1's termination measures

The head's and the idle code's sites in program order: the local times (`Wg1/Time.lean`). Every
transition raises them (`measure_step`, `imeasure_step`), so a lane makes at most two head events
and four idle events. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
open PTX

/-- **The head's measure.** -/
def measure (s : Site) : Nat := time s

/-- **The idle code's measure.** -/
def imeasure (s : IdleSite) : Nat := itime s

/-- **Every head transition raises the measure.** -/
theorem measure_step {s s' : Site} {e : Event} (h : succ s e = some (some s')) :
    measure s < measure s' := by
  cases s with
  | smr =>
    simp only [succ, Option.some.injEq] at h
    subst h
    decide
  | hsh =>
    simp only [succ] at h
    split at h
    · simp only [dispatch] at h
      split at h
      · split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
          decide
      · cases h
    · cases h
  | _ => simp [succ] at h

/-- **Every idle transition raises the measure.** -/
theorem imeasure_step {P : Params} {s s' : IdleSite} {e : Event}
    (h : isucc P s e = some (some s')) : imeasure s < imeasure s' := by
  cases s with
  | ldA =>
    simp only [isucc, afterNc] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp only [imeasure, idleAfterA]
        split <;> decide
      · cases h
    · cases h
  | ldB =>
    simp only [isucc, afterNc] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        decide
      · cases h
    · cases h
  | bar =>
    simp only [isucc, Option.some.injEq] at h
    subst h
    decide
  | ret => simp [isucc] at h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
