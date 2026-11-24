-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Code
public import Lemmas.Kernel.Frame
public import Lemmas.Flow.Counted
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.Loader.Ledger
public import Kernels.TmlFa4Fwd.Proof.Loader.Ref
public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
public import Kernels.TmlFa4Fwd.Proof.Loader.Move
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Std.Tactic.BVDecide.Normalize.Prop
import Lemmas.Flow.GlueStep
import Kernels.TmlFa4Fwd.Proof.Loader.RefNext

@[expose] public section

/-! # A fact of the positions of a loader lane

`pos_at`: a predicate of the position and the loader state that holds at the role's first state and
is kept by every step, from its truth at all earlier positions, holds at every state before any
undefined behaviour. A step gives the event, the reference invariant and values, the event's shape,
the successor and the step spec. It is `fact_at` with the trace position. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Loader

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **A fact of the positions holds at every loader state of a lane of warp 14 or 15** without
undefined behaviour so far. -/
theorem pos_at {I : Nat → D → Prop} (h0 : ∀ k b, I k (Loader.F p L g b).init)
    (hstep : ∀ k b d n e d', X.get (g, k) = some e →
      Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)) → n .ub = 0 →
      Loader.Ref p L g (wOf b) (d, lcn n) →
      LFits p L g d (n .shfl) (n .vote) (n (.load .commit)) → Ev p L g (wOf b) d e →
      (∀ f, e.kind ≠ .ub f) → succ p L g (wOf b) d e = some (some d') →
      Move L g (wOf b) (d, lcn n) e d' →
      (∀ j ≤ k, ∀ b d n, Frame.stateAt (thread p L) X g j = some (some (linj p L g b d n)) →
        n .ub = 0 → I j d) → I (k + 1) d')
    (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) :
    ∀ k, k ≤ (X.tr g).length → ∀ b d n,
      Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)) →
      n .ub = 0 → I k d := by
  have hG := good hp hX hw hg rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  cases k with
  | zero =>
    intro _ b d n hσ
    rw [Frame.stateAt_zero] at hσ
    cases hσ
  | succ k =>
    intro hkl b d n hσ hub
    have hk : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
    have hs := Frame.stateAt_succ (C := thread p L) he
    rw [hσ] at hs
    cases h0' : Frame.stateAt (thread p L) X g k with
    | none => rw [h0'] at hs; simp at hs
    | some o =>
      cases o with
      | none => exact absurd h0' (hG k).1
      | some σ0 =>
        rw [h0'] at hs
        have hn : (thread p L g).next σ0 e = some (some (linj p L g b d n)) := hs.symm
        have hR := (hG k).2 σ0 h0'
        obtain ⟨σ1, n0⟩ := σ0
        obtain ⟨h1, hn2⟩ := Code.counted_next_some hn
        simp only at hn2
        rcases σ1 with s | ⟨i, d0⟩
        · -- the startup enters the role
          obtain ⟨s', -, hent⟩ := Code.glue_inl_some h1
          simp only [Code.enter] at hent
          split at hent
          · cases hent
            exact h0 _ b
          · cases hent
        · -- a step of the role
          cases i with
          | loader b0 =>
            obtain ⟨hb, hR⟩ := hR
            rw [next_linj] at hn
            cases hF : (Loader.F p L g b0).next d0 e with
            | none => rw [hF] at hn; cases hn
            | some o =>
              cases o with
              | none => rw [hF] at hn; cases hn
              | some d' =>
                rw [hF] at hn
                simp only [Option.map_some, Option.some.injEq] at hn
                cases hn
                have hub0 : n0 .ub = 0 := ub_zero hX he h0'
                have hnu : ∀ f, e.kind ≠ .ub f := fun f hf => by
                  have h := hub
                  simp [Code.bump, Proof.cls, hf] at h
                have hw' : wOf b = 14 ∨ wOf b = 15 := by cases b <;> simp [wOf]
                obtain ⟨hJ, hF'⟩ := hR hub0
                rw [← hb] at hJ
                have hev := (lfired hp hX he h0').1
                exact hstep k b d0 n0 e d he h0' hub0 hJ hF' hev hnu hF
                  (step_spec hp hw' hJ hev hnu hF)
                  (fun j hj b1 d1 n1 hs1 hu1 => ih j (by omega) (by omega) b1 d1 n1 hs1 hu1)
          | _ => exact hR.elim

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
