-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Common.Sound
public import Kernels.InklingRelDecode.Proof.Thread.EvWComp

@[expose] public section

/-! # The worker fragment's reference

**Reference** (`WRef`): a worker state is at the dispatch loop's head, its barrier, the role
byte's load or the bad-byte barriers (the worker machine's own copy of the startup is not
reached), and the base word every state carries (`%r2`, register 463 of the inherited record) is
the base word 0, and the record holds the tensor map's pointer in the register the K/V copies
read (`EvW.MapReg`, which the loader's shape needs). A role carries the record the dispatch
handed it (`Worker.handoff`), which keeps both, and returns to the loop's head with it
(`Worker.bumpPro`).

**Step** (`wnext_ne`, `wnext_ref`): under `WRef` the worker machine does not stop and every
successor holds `WRef`. The machine follows every role byte, loop bound, block-table word and
received word (`WComp.ldRole_next_follows`, `loader_next_follows`, `mma_next_follows`); its one
content stop, the MMA role's entry on a base word without room for 512 columns (`WComp.baseOk`),
is excluded by the base word 0. So no source is needed for any returned value of the workers. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode

noncomputable section

variable {L : Launch} {g : Nat}

/-- The reached sites of the worker states and the base word `b` they carry. -/
def WSite (b : Value) : Proof.WComp.WSt → Prop
  | .worker w => (w.site = .loop ∨ w.site = .bar2 ∨ w.site = .ldRole ∨ w.site = .bad0 ∨
      w.site = .bad1) ∧ w.P.rest 463 = b
  | .idle d => d.P.rest 463 = b
  | .loader _ P => P.rest 463 = b
  | .mma _ P => P.rest 463 = b
  | .exit _ => True

/-- **The worker states' reference**: a reached site with the base word `b`, and the tensor map's
pointer in its register. -/
def WRef (b : Value) (σ : Proof.WComp.WSt) : Prop :=
  WSite b σ ∧ Proof.EvW.MapReg (Proof.EvW.stPro σ)

theorem baseOk_zero {P : Proof.Loader.Pro} (h : P.rest 463 = b32 0) : Proof.WComp.baseOk P :=
  ⟨0, by simp [Proof.WComp.tmOf, h, b32], by norm_num⟩

theorem handoff_463 (P : Proof.Loader.Pro) :
    (Proof.WComp.handoffPro L g P).rest 463 = P.rest 463 := by
  simp [Proof.WComp.handoffPro, Proof.Worker.handoff, Proof.Worker.valueOf, Proof.Worker.own,
    Proof.Loader.Pro.val, Proof.Loader.Pro.table, List.lookup]

theorem bump_463 (P : Proof.Loader.Pro) : (Proof.Worker.bumpPro P).rest 463 = P.rest 463 := by
  simp [Proof.Worker.bumpPro, Proof.Worker.roundReg]

/-- **The worker machine does not stop under its reference**, at a dispatch whose base word has
room for the MMA role's 512 columns (`WComp.baseOk`). -/
theorem wnext_ne_of {b : Value} {σ : Proof.WComp.WSt} {e : Event} (hR : WSite b σ)
    (hok : ∀ w, σ = .worker w → w.site = .ldRole → Proof.WComp.baseOk w.P) :
    Proof.WComp.next L g σ e ≠ some none := by
  cases σ with
  | worker w =>
    obtain ⟨hs, h0⟩ := hR
    rcases hs with hs | hs | hs | hs | hs
    · exact Proof.WComp.worker_next_follows (.inr (.inr (.inr (.inl hs))))
    · exact Proof.WComp.worker_next_follows (.inr (.inr (.inr (.inr (.inl hs)))))
    · obtain ⟨s, P⟩ := w
      simp only at hs
      subst hs
      exact Proof.WComp.ldRole_next_follows (hok _ rfl rfl)
    · exact Proof.WComp.worker_next_follows (.inr (.inr (.inr (.inr (.inr (.inl hs))))))
    · exact Proof.WComp.worker_next_follows (.inr (.inr (.inr (.inr (.inr (.inr hs))))))
  | idle d => exact Proof.WComp.idle_next_follows d
  | loader d P => exact Proof.WComp.loader_next_follows P
  | mma d P => exact Proof.WComp.mma_next_follows P
  | exit x => exact Proof.WComp.exit_next_follows x

/-- **The worker machine does not stop under its reference with the base word 0.** -/
theorem wnext_ne {σ : Proof.WComp.WSt} {e : Event} (hR : WRef (b32 0) σ) :
    Proof.WComp.next L g σ e ≠ some none :=
  wnext_ne_of hR.1 fun w hw _ => by subst hw; exact baseOk_zero hR.1.2

/-- **Every successor of the worker machine holds its reference.** -/
theorem wsite_next {b : Value} {σ σ' : Proof.WComp.WSt} {e : Event} (hR : WSite b σ)
    (h : Proof.WComp.next L g σ e = some (some σ')) : WSite b σ' := by
  cases σ with
  | worker w =>
    obtain ⟨s, P⟩ := w
    obtain ⟨hs, h0⟩ := hR
    simp only at hs h0
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · simp only [Proof.WComp.next, Proof.Worker.next, Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨by simp, h0⟩
    · simp only [Proof.WComp.next, Proof.Worker.next, Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨by simp, h0⟩
    · simp only [Proof.WComp.next, Proof.WComp.dispatch] at h
      split at h
      · rename_i d' hd'
        obtain ⟨-, hs'⟩ := Proof.WComp.ldRole_some hd'
        rcases hs' with hs' | hs' | hs' | hs' | hs' <;>
          simp only [hs', Proof.WComp.roleStart] at h
        · simp only [Option.some.injEq] at h
          subst h
          show (Proof.WComp.handoffPro L g P).rest 463 = b
          rw [handoff_463, h0]
        · repeat' split at h
          all_goals simp only [Option.some.injEq, reduceCtorEq] at h
          subst h
          show (Proof.WComp.handoffPro L g P).rest 463 = b
          rw [handoff_463, h0]
        · simp only [Option.some.injEq] at h
          subst h
          exact h0
        · simp only [Option.some.injEq] at h
          subst h
          trivial
        · simp only [Option.some.injEq] at h
          subst h
          exact ⟨by simp, h0⟩
      · cases h
      · cases h
    · simp only [Proof.WComp.next, Proof.Worker.next, Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨by simp, h0⟩
    · simp only [Proof.WComp.next, Proof.Worker.next, Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨by simp, h0⟩
  | idle d =>
    obtain ⟨s, P⟩ := d
    cases s <;> simp only [Proof.WComp.next, Proof.Worker.Idle.next, Option.map_some,
      Option.some.injEq] at h
    all_goals first
      | (subst h; exact hR)
      | (subst h; exact ⟨by simp, by rw [bump_463]; exact hR⟩)
  | loader d P =>
    obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
    cases s
    all_goals simp only [Proof.WComp.next] at h
    all_goals first
      | (simp only [Option.some.injEq] at h; subst h; exact ⟨by simp, by rw [bump_463]; exact hR⟩)
      | (cases hn : Proof.Loader.next L g _ e with
          | none => rw [hn] at h; cases h
          | some o =>
            cases o with
            | none => rw [hn] at h; cases h
            | some d' =>
              rw [hn] at h
              simp only [Option.map_some, Option.some.injEq] at h
              subst h
              exact hR)
  | mma d P =>
    obtain ⟨s, i, n, tm, pro⟩ := d
    cases s
    all_goals simp only [Proof.WComp.next] at h
    all_goals first
      | (simp only [Option.some.injEq] at h; subst h; exact ⟨by simp, by rw [bump_463]; exact hR⟩)
      | (cases hn : Proof.Mma.next L g _ e with
          | none => rw [hn] at h; cases h
          | some o =>
            cases o with
            | none => rw [hn] at h; cases h
            | some d' =>
              rw [hn] at h
              simp only [Option.map_some, Option.some.injEq] at h
              subst h
              exact hR)
  | exit x =>
    obtain ⟨s, P⟩ := x
    cases s <;> simp only [Proof.WComp.next, Option.some.injEq, reduceCtorEq] at h
    subst h
    trivial

/-- **Every successor holds the reference** (`wsite_next`; the map register by
`EvW.next_keep`). -/
theorem wnext_ref {b : Value} {σ σ' : Proof.WComp.WSt} {e : Event} (hR : WRef b σ)
    (h : Proof.WComp.next L g σ e = some (some σ')) : WRef b σ' := by
  refine ⟨wsite_next hR.1 h, ?_⟩
  have hk := Proof.EvW.next_keep h
  unfold Proof.EvW.MapReg
  rw [hk.2.2.2.2.2.2]
  exact hR.2

end
end PTX.Kernels.InklingRelDecode.Proof2
