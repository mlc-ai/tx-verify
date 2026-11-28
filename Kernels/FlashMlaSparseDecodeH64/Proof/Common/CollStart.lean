-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Table
public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Coll
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View

@[expose] public section

/-! # The collectives of a startup state

`startup_count`: at a startup state the thread's prefix count of warp collectives is `ncS` of the
state (`Startup/Coll.lean`), by induction along the trace: every earlier state is a startup state
(a role or a stub is never left), and a step adds a collective exactly when its event is one. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {x : Nat}

/-- A startup state at an election site has the warp word of warp 0. -/
theorem startup_warp0 {d : Startup.D} {n : Cls → Nat} {j : Fin 2} (hJ : (table P L).J x (.inl d, n))
    (hs : d.site = .elect j) : Startup.notWarp0 d.x2 = false := by
  obtain ⟨-, hW, -⟩ := hJ
  obtain ⟨site, x1, x2⟩ := d
  simp only at hs
  subst hs
  obtain ⟨-, -, h2, h0⟩ := hW
  simp only at h2 ⊢
  rw [h2]
  simp [Startup.notWarp0, warpW, h0]
  decide

/-- The step of the thread machine from a startup state to a startup state. -/
theorem startup_next_inl {d0 d : Startup.D} {n0 n : Cls → Nat} {e : Event}
    (h : (thread P L x).toMachine.next (some (.inl d0, n0)) e = some (some (.inl d, n))) :
    Startup.succ L x d0 e = some (some d) := by
  have h1 : (thread P L x).next (.inl d0, n0) e = some (some (.inl d, n)) := h
  rw [next_startup] at h1
  cases hs : Startup.succ L x d0 e with
  | none => rw [hs] at h1; cases h1
  | some o =>
    cases o with
    | none => rw [hs] at h1; cases h1
    | some d' =>
      rw [hs] at h1
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨h2, -⟩ := h1
      unfold Code.enter at h2
      split at h2
      · cases h2
      · cases h2; rfl

/-- A fragment's step never returns to the startup. -/
theorem frag_next_not_inl {i : Entry} {d1 : (frag P L x i).D} {n0 n : Cls → Nat} {e : Event}
    {d : Startup.D}
    (h : (thread P L x).toMachine.next (some (.inr ⟨.inl i, d1⟩, n0)) e =
      some (some (.inl d, n))) : False := by
  have h1 : (thread P L x).next (.inr ⟨.inl i, d1⟩, n0) e = some (some (.inl d, n)) := h
  rw [next_frag] at h1
  cases hs : (frag P L x i).next d1 e with
  | none => rw [hs] at h1; cases h1
  | some o => cases o <;> rw [hs] at h1 <;> simp at h1

/-- A stub's step stops. -/
theorem stub_next_not_inl {r : Entry} {u : Unit} {n0 n : Cls → Nat} {e : Event} {d : Startup.D}
    (h : (thread P L x).toMachine.next (some (.inr ⟨.inr r, u⟩, n0)) e =
      some (some (.inl d, n))) : False := by
  have h1 : (thread P L x).next (.inr ⟨.inr r, u⟩, n0) e = some (some (.inl d, n)) := h
  rw [Code.roleThread_stub] at h1
  cases h1

/-- **At a startup state the prefix count of collectives is `ncS`.** -/
theorem startup_count (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) :
    ∀ k {d : Startup.D} {n : Cls → Nat},
      Frame.stateAt (thread P L) X x k = some (some (.inl d, n)) →
      ((X.tr x).take k).countP Sched.isWarpColl = Startup.ncS d := by
  intro k
  induction k with
  | zero =>
    intro d n h
    rw [Frame.stateAt_zero] at h
    have h' := Option.some.inj (Option.some.inj h)
    rw [thread_init] at h'
    obtain ⟨h1, -⟩ := Prod.mk.inj h'
    cases h1
    simp [Startup.ncS]
  | succ k ih =>
    intro d n h
    by_cases hk : k < (X.tr x).length
    · obtain ⟨e, he⟩ : ∃ e, X.get (x, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
      have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(x, k), e.pc, f, by
        rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
      obtain ⟨⟨s, n0⟩, hσ, hJ, hi, hev⟩ := ev_state hp hX hFw he hne
      have hnext := Frame.stateAt_succ (C := thread P L) (X := X) (g := x) (k := k) he
      rw [hσ] at hnext
      rw [hnext] at h
      rcases s with d0 | ⟨i | r, d1⟩
      · have hs := startup_next_inl h
        have hst := Startup.ncS_step hev hne (fun j hj => startup_warp0 hJ hj) hs
        rw [List.take_add_one, List.countP_append, ih hσ, hst]
        have : (X.tr x)[k]? = some e := he
        simp [this, Option.toList]
      · exact (frag_next_not_inl h).elim
      · exact (stub_next_not_inl h).elim
    · have h1 : (X.tr x).take (k + 1) = (X.tr x).take k := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      have h2 : Frame.stateAt (thread P L) X x (k + 1) = Frame.stateAt (thread P L) X x k := by
        unfold Frame.stateAt; rw [h1]
      rw [h1]
      rw [h2] at h
      exact ih h

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
