-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.SubWon
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Machine

@[expose] public section

/-! # The idle code's length loads have their pointers set

The idle code is at its top-k length load only when the top-k pointer is set and at its extra
length load only when the extra pointer is set (`idleOk`, kept along the thread by `idle_ok`):
the first state `idleFirst` and the step after the top-k load (`idleAfterA`) test the pointers,
and no other step goes to a length load. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The pointer a length load of the idle code reads through is set.** -/
def idleOk (P : Params) : IdleSite → Prop
  | .ldA => eqz64 (pw8 (P.topkLenBase.getD 0)) = false
  | .ldB => eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = false
  | _ => True

private theorem ok_after (P : Params) : idleOk P (idleAfterA P) := by
  unfold idleAfterA
  cases h : eqz64 (pw8 (P.extraTopkLenBase.getD 0)) <;> simp [idleOk, h]

/-- The idle code's first state has its pointer set. -/
theorem idleOk_first (P : Params) (L : Launch) (g : Nat) : idleOk P (idleFirst P L g) := by
  unfold idleFirst
  split
  · trivial
  · split
    · exact ok_after P
    · rename_i h
      simpa [idleOk] using h

/-- A step of the idle code keeps `idleOk`. -/
theorem idleOk_step {s s' : IdleSite} {e : Event} (h : Wg1.isucc P s e = some (some s')) :
    idleOk P s' := by
  cases s <;> simp only [Wg1.isucc, Wg1.afterNc] at h
  · split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact ok_after P
      · cases h
    · cases h
  · split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        trivial
      · cases h
    · cases h
  · simp only [Option.some.injEq] at h
    subst h
    trivial
  · cases h

/-- The idle states with `idleOk`. -/
def IdleOkR (P : Params) (L : Launch) (g : Nat) (σ : (thread P L g).D) : Prop :=
  ∀ s n, σ = (.inr ⟨.inl .wg1, .inr ⟨.inl .idle, s⟩⟩, n) → idleOk P s

/-- Warpgroup 1's head enters the idle code at its first state. -/
private theorem enter_sub {p : (wg1HeadCode P L g).D} {d : IdleSite}
    (h : Code.enter (wg1HeadCode P L g) (Code.withStubsAt (subFrag P L g) (SubEntry.pc P L g))
      (Code.gatedExit (wg1Enter P L g) (subSel P L g)) p = .inr ⟨.inl .idle, d⟩) :
    idleOk P d := by
  unfold Code.enter at h
  split at h
  · rename_i i _
    simp only [Sum.inr.injEq] at h
    cases i with
    | inl e =>
      cases e <;> simp only [Sigma.mk.inj_iff, Sum.inl.injEq, reduceCtorEq, false_and] at h
      obtain ⟨-, h2⟩ := h
      cases eq_of_heq h2
      exact idleOk_first P L g
    | inr r => simp at h
  · simp at h

/-- The startup enters warpgroup 1 at its first state. -/
private theorem enter_top {s : (startupCode P L g).D} {d : IdleSite} {n n' : Cls → Nat}
    (h : (Code.enter (startupCode P L g) (Code.withStubs (frag P L g) Entry.pc)
      (Code.gatedExit (startupEnter P L g) (sel P L g)) s, n) =
      (.inr ⟨.inl .wg1, .inr ⟨.inl .idle, d⟩⟩, n')) : idleOk P d := by
  unfold Code.enter at h
  split at h
  · simp only [Prod.mk.injEq, Sum.inr.injEq] at h
    obtain ⟨h1, -⟩ := h
    rename_i i _
    cases i with
    | inl e =>
      cases e <;> simp only [Sigma.mk.inj_iff, Sum.inl.injEq, reduceCtorEq, false_and] at h1
      obtain ⟨-, h2⟩ := h1
      exact enter_sub (eq_of_heq h2)
    | inr r => simp at h1
  · simp at h

/-- **The idle code's states have `idleOk`.** -/
theorem idle_ok {k : Nat} {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g k = some (some σ)) : IdleOkR P L g σ := by
  refine region_stays_ev (IdleOkR P L g) (j := 0) ?_ (Frame.stateAt_zero ..) ?_ k
    (Nat.zero_le k) σ hσ
  · rintro i ⟨s | ⟨r, x⟩, n⟩ σ' f - hσi hR hf hn d' n' rfl
    · simp only [Code.toMachine, Code.glue] at hn
      cases hs : Startup.succ L g s f with
      | none => simp [hs] at hn
      | some o =>
        cases o with
        | none => simp [hs] at hn
        | some s' =>
          simp only [hs, Option.map_some, Option.some.injEq] at hn
          exact enter_top hn
    · simp only [Code.toMachine, Code.glue] at hn
      rcases hs : (Code.withStubs (frag P L g) Entry.pc r).next x f with _ | _ | a <;>
        rw [hs] at hn <;>
        simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq,
          Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff] at hn
      obtain ⟨⟨rfl, ha⟩, -⟩ := hn
      cases eq_of_heq ha
      rcases x with h0 | ⟨j, d⟩
      · simp only [Code.withStubs, frag, wg1Code, Code.roleLoop, Code.loopGlue,
          Option.map_eq_some_iff] at hs
        obtain ⟨a, -, a1, rfl, ha⟩ := hs
        exact enter_sub ha
      · simp only [Code.withStubs, frag, wg1Code, Code.roleLoop, Code.loopGlue,
          Option.map_eq_some_iff] at hs
        obtain ⟨a, hj, a1, rfl, ha⟩ := hs
        unfold Code.backEnter at ha
        split at ha
        · exact enter_sub ha
        · obtain ⟨rfl, h2⟩ := Sigma.mk.inj (Sum.inr.inj ha)
          cases eq_of_heq h2
          exact idleOk_step hj
  · rintro d n h
    exact enter_top (s := (startupCode P L g).init) (n := fun _ => 0) h

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
