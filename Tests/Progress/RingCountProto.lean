-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.WaitOrderEnables

/-! Prototype: round attribution for one slot of a GEMM input ring under `DepStepAcyclic`.

Slot `s` has a full barrier `F` and an empty barrier `E`, both of count 1. Uses of the slot
are numbered `0, 1, …, N - 1` (use `t` is round `t * S + s`). The producer, for use `n ≥ 1`,
waits on `E` (`wE n`), and for every use `t` arrives on `F` with expect-tx (`aF t`) and
issues the tensor copy (`tma t`). The MMA thread, for use `j`, waits on `F` (`wF j`) and
issues `tcgen05.commit` on `E` (`cm j`), whose arrive-on is `note j`.

Hypotheses, in three groups.
* Per object, replay and counting (no other object, no causality): `wE (p + 1)` observes
  phase `p` of `E`, whose single counted update is the notification of commit `σ p`
  (count 1; every update of `E` is a commit notification); `wF j` observes phase `j` of `F`,
  whose single counted arrival is `aF (π j)` (count 1; only the producer arrives on `F`). An
  observed update is a witness of the successful poll (`Witness`, DEP-ORDER).
  `σ` and `π` are injective: one record per notification or arrival, counted in one phase.
* Thread-local (from the site machines): the waits are canonical spins and the later
  instructions follow them in program order (`Resumes`, DEP-CANONICAL-SPIN, and the code order):
  `wE n` guards `aF t` and `tma t` for `t ≥ n`; `wF j` guards `cm t` for `t ≥ j`.
* Existence: each commit instruction is present and its notification is present.

Results. `empty_attribution`: `σ p = p`, so the producer's wait for use `n` observed the
commit of use `n - 1` (round `k - S`), and every phase `p < n` of `E` was completed by the
commit of use `p`. `full_attribution`: `π j = j`. `full_tx_attribution`: a copy's
complete-tx counted in the phase the MMA thread's wait for use `j` observes comes from a use
`t ≤ j`, not from a later round. Only `DepStepAcyclic` is used: no `ObjectCoherent`, no
`stageCausality`, no `WaitAcyclic`.

Not derived here: that the parity polled by a round's wait selects that round's phase
(`wE (p + 1)` observes phase `p`, not `p + 2`); §9.7.15.16.19 makes a parity wait valid only
for the current incomplete or the immediately preceding phase, so this needs a replay fact
of the object that the phase has not advanced twice. -/

namespace PTX.Tests.RingCountProto

/-- Pigeonhole: an injective map on `0, …, m` takes some value `≥ n` there when `n ≤ m`. -/
theorem exists_ge_of_injOn (π : Nat → Nat) {m n : Nat} (hnm : n ≤ m)
    (hinj : ∀ j ≤ m, ∀ j' ≤ m, π j = π j' → j = j') : ∃ j ≤ m, n ≤ π j := by
  by_contra h
  push Not at h
  have hsub : (Finset.range (m + 1)).image π ⊆ Finset.range n := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (h j (by simp at hj; omega))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn (fun a ha b hb hab => hinj a (by simp at ha; omega) b
    (by simp at hb; omega) hab)] at hcard
  simp at hcard
  omega

/-- An injective map below `N` that never increases is the identity there. -/
theorem eq_of_le_injOn (σ : Nat → Nat) (N : Nat) (hle : ∀ p < N, σ p ≤ p)
    (hinj : ∀ p < N, ∀ p' < N, σ p = σ p' → p = p') : ∀ p < N, σ p = p := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp
    rcases Nat.lt_or_eq_of_le (hle p hp) with hlt | heq
    · have := ih (σ p) hlt (by omega)
      exact absurd (hinj _ (by omega) _ hp this) (by omega)
    · exact heq

section
variable {L : Launch} {K : Kernel} {X : Execution}

/-- The setting of one ring slot. -/
structure Slot (L : Launch) (K : Kernel) (X : Execution) where
  N : Nat
  wE : Nat → EvId
  aF : Nat → EvId
  tma : Nat → EvId
  wF : Nat → EvId
  cm : Nat → EvId
  rank : Fin 16
  σ : Nat → Nat
  π : Nat → Nat
  -- per object: replay and counting
  obsE : ∀ p, p + 1 < N → σ p < N ∧
    Witness L X (.async (cm (σ p)) (.tcNotify rank)) (wE (p + 1))
  injE : ∀ p, p + 1 < N → ∀ p', p' + 1 < N → σ p = σ p' → p = p'
  obsF : ∀ j < N, π j < N ∧ Witness L X (.thread (aF (π j))) (wF j)
  injF : ∀ j < N, ∀ j' < N, π j = π j' → j = j'
  -- thread-local
  guardP : ∀ n t, 1 ≤ n → n ≤ t → t < N →
    Resumes K X (wE n) (aF t) ∧ Resumes K X (wE n) (tma t)
  guardM : ∀ j t, j ≤ t → t < N → Resumes K X (wF j) (cm t)
  -- existence
  commit : ∀ t < N, X.RefPresent (.thread (cm t)) ∧ X.AsyncPresent (cm t) (.tcNotify rank)

namespace Slot
variable (R : Slot L K X)

/-- Use `t`'s commit precedes its notification (its issue). -/
theorem note_edge {t : Nat} (ht : t < R.N) :
    DepStep L K X (.thread (R.cm t), false) (.async (R.cm t) (.tcNotify R.rank), false) :=
  .inr (.inl ⟨rfl, rfl, _, _, rfl, rfl, (R.commit t ht).1, (R.commit t ht).2, trivial⟩)

/-- The commit counted in phase `p` of `E` belongs to a use `≤ p`. -/
theorem empty_le (hacyc : DepStepAcyclic L K X) : ∀ p, p + 1 < R.N → R.σ p ≤ p := by
  intro p hp
  by_contra hgt
  obtain ⟨hσN, hobs⟩ := R.obsE p hp
  -- among the full phases `0, …, σ p`, one counts an arrival of a use `≥ p + 1`
  obtain ⟨j, hj, hπj⟩ := exists_ge_of_injOn R.π (m := R.σ p) (n := p + 1) (by omega)
    (fun a ha b hb => R.injF a (by omega) b (by omega))
  obtain ⟨hπN, hobsF⟩ := R.obsF j (by omega)
  -- wE (p+1) → aF (π j) → wF j → cm (σ p) → note → wE (p+1)
  exact hacyc (.thread (R.wE (p + 1)), true)
    (.tail (.tail (.tail (.tail (.single
      (DepStep.of_resumes L (R.guardP (p + 1) (R.π j) (by omega) hπj hπN).1))
      (DepStep.of_witness L hobsF)) (DepStep.of_resumes L (R.guardM j (R.σ p) hj hσN)))
      (R.note_edge hσN)) (DepStep.of_witness L hobs))

/-- The arrival counted in phase `j` of `F` belongs to a use `≤ j`. -/
theorem full_le (hacyc : DepStepAcyclic L K X) : ∀ j < R.N, R.π j ≤ j := by
  intro j hj
  by_contra hgt
  obtain ⟨hπN, hobsF⟩ := R.obsF j hj
  -- among the empty phases `0, …, π j - 1`, one counts a commit of a use `≥ j`
  obtain ⟨p, hp, hσp⟩ := exists_ge_of_injOn R.σ (m := R.π j - 1) (n := j) (by omega)
    (fun a ha b hb => R.injE a (by omega) b (by omega))
  obtain ⟨hσN, hobs⟩ := R.obsE p (by omega)
  -- wF j → cm (σ p) → note → wE (p+1) → aF (π j) → wF j
  exact hacyc (.thread (R.wF j), true)
    (.tail (.tail (.tail (.tail (.single (DepStep.of_resumes L (R.guardM j (R.σ p) hσp hσN)))
      (R.note_edge hσN)) (DepStep.of_witness L hobs))
      (DepStep.of_resumes L (R.guardP (p + 1) (R.π j) (by omega) (by omega) hπN).1))
      (DepStep.of_witness L hobsF))

/-- Empty barrier: phase `p` is completed by the commit of use `p`. So the producer's wait for
use `n` observed the commit of use `n - 1`, and the commits of all uses `< n` completed the
phases before it. -/
theorem empty_attribution (hacyc : DepStepAcyclic L K X) :
    ∀ p, p + 1 < R.N → R.σ p = p ∧
      Witness L X (.async (R.cm p) (.tcNotify R.rank)) (R.wE (p + 1)) := by
  have hid := eq_of_le_injOn R.σ (R.N - 1) (fun p hp => R.empty_le hacyc p (by omega))
    (fun p hp p' hp' => R.injE p (by omega) p' (by omega))
  intro p hp
  have h := hid p (by omega)
  refine ⟨h, ?_⟩
  have := (R.obsE p hp).2
  rwa [h] at this

/-- Full barrier: phase `j` counts the producer's arrival of use `j`. -/
theorem full_attribution (hacyc : DepStepAcyclic L K X) :
    ∀ j < R.N, R.π j = j ∧ Witness L X (.thread (R.aF j)) (R.wF j) := by
  have hid := eq_of_le_injOn R.π R.N (R.full_le hacyc) R.injF
  intro j hj
  refine ⟨hid j hj, ?_⟩
  have := (R.obsF j hj).2
  rwa [hid j hj] at this

/-- Full barrier, transaction side: a copy's complete-tx counted in the phase the MMA
thread's wait for use `j` observes comes from a use `t ≤ j`. Needs, for that copy, its issue
and one of its writes to be present. -/
theorem full_tx_attribution (hacyc : DepStepAcyclic L K X) {j t x y k : Nat}
    (hj : j < R.N) (ht : t < R.N)
    (hobs : Witness L X (.async (R.tma t) (.notify .load)) (R.wF j))
    (hcopy : X.RefPresent (.thread (R.tma t)))
    (hwrite : X.AsyncPresent (R.tma t) (.write (.load x y k)))
    (hnote : X.AsyncPresent (R.tma t) (.notify .load)) : t ≤ j := by
  by_contra hgt
  have hE := (R.empty_attribution hacyc j (by omega)).2
  -- wF j → cm j → note → wE (j+1) → tma t → write → complete-tx → wF j
  exact hacyc (.thread (R.wF j), true)
    (.tail (.tail (.tail (.tail (.tail (.tail (.tail
      (.single (DepStep.of_resumes L (R.guardM j j le_rfl hj)))
      (R.note_edge hj)) (DepStep.of_witness L hE))
      (DepStep.of_resumes L (R.guardP (j + 1) t (by omega) (by omega) ht).2))
      (.inr (.inl ⟨rfl, rfl, _, .write (.load x y k), rfl, rfl, hcopy, hwrite, trivial⟩)))
      (show DepStep L K X (.async (R.tma t) (.write (.load x y k)), false)
        (.async (R.tma t) (.write (.load x y k)), true) from .inl (.inl ⟨rfl, rfl, rfl, hwrite⟩)))
      (show DepStep L K X (.async (R.tma t) (.write (.load x y k)), true)
        (.async (R.tma t) (.notify .load), false) from
        .inl (.inr ⟨rfl, rfl, rfl, rfl, hwrite, hnote⟩)))
      (DepStep.of_witness L hobs))

end Slot
end

end PTX.Tests.RingCountProto
