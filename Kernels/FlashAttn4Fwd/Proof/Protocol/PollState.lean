-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.InitFirst
public import Lemmas.Protocol.MbarPending

@[expose] public section

/-! # A polled table barrier has a state, and a safe execution's histories do not fault

Two facts the progress of the mbarrier polls uses for every wait class.

* **The polled barrier has a final state** (`state_of_reg`). A thread that has made its role's
  register request (`setmaxnreg`, an event after the start that is not of the prologue's kinds)
  is past the start cluster barrier, so every table barrier of its cluster is initialized
  (`init_exists`). The initialization is recorded in the barrier's history with a valid count
  (`count_valid`), so the checked history ends in a state (`MBarrier.stateBefore_length_some`).
* **No record faults** (`fault_free`): a record with a fault makes the execution unsafe
  (`TmaUnsafe`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.InitFirst
open PTX PTX.Flow PTX.Proof AsyncCopy MBarrier

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A table barrier of the cluster of a thread past its register request has a final
state.** -/
theorem state_of_reg (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (htm : TmemFacts L X) (hi : InitFacts L X) (b : FBar)
    {cta g j pc n inst : Nat} {inc : Bool}
    (he : X.get (g, j) = some ⟨pc, .setMaxReg inc n inst⟩) (hcl : ctaOf L g / 2 = cta / 2) :
    ∃ s, stateBefore (X.objects (b.loc L cta)) (X.objects (b.loc L cta)).length = some s := by
  obtain ⟨⟨g0, k0⟩, pc0, n0, hinit⟩ :=
    init_exists hpre hX hc hi b he (by simp [PreKind]) (by simp) hcl
  have hact : objectAction X X.async (b.loc L cta) (.thread (g0, k0)) = some (.init n0) := by
    simp [objectAction, hinit]
  obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 _).2.2 _ _ hact
  have hra : r.action = .init n0 := by
    have h := ((hX.tma.2.2.1 _).2.1 r hr).1
    rw [hid, hact] at h
    exact (Option.some.inj h).symm
  obtain ⟨-, -, rfl⟩ := init_of_site hc (Frame.lt_of_get hX hinit) hinit
  exact stateBefore_length_some (hX.tma.2.2.1 _).1
    (objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, h⟩ => htm.no_inval h) _) hr hra (count_valid b)

/-- **No record of a safe execution's object histories faults.** -/
theorem fault_free (hsafe : ¬ Unsafe L kernel asms mem0 X) {m : Loc} {r : Record Ref}
    (hr : r ∈ X.objects m) : r.fault = none := by
  cases hf : r.fault with
  | none => rfl
  | some f =>
    exact absurd (by
      unfold Unsafe
      exact .inr (.inr (.inr (.inr (.inr (.inl (.inl ⟨m, r, hr, by simp [hf]⟩))))))) hsafe

end

end PTX.Kernels.FlashAttn4Fwd.Proof.InitFirst
