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
public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Std.Tactic.BVDecide.Normalize.Prop
import Lemmas.Flow.GlueStep
import Kernels.TmlFa4Fwd.Proof.Loader.RefNext

@[expose] public section

/-! # A loader fact holds at every state of a loader lane

`fact_at`: a predicate of the warp and the counted loader state that holds at the role's first
state and is kept by every step from a state with the reference invariant (`Loader.Ref`), given
the step spec (`Loader.Move`), holds at every state of a lane of warp 14 or 15 before any
undefined behaviour. The loader's standalone facts (`Loader/Facts/`) are proved with it, so a
fact is one file that states its predicate and its step obligation; it never walks a run. This
is the loader's instance of the role-lifting lemma (`RoleTable.roleInv`, lane 1b), proved on the
loader warps' following (`good`), which needs no open premise. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Loader

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **A loader fact holds at every loader state of a lane of warp 14 or 15** without undefined
behaviour so far. -/
theorem fact_at {I : Nat → D × (Cnt → Nat) → Prop}
    (h0 : ∀ b, I (wOf b) ((Loader.F p L g b).init, fun _ => 0))
    (hstep : ∀ w (dn : D × (Cnt → Nat)) e d', (w = 14 ∨ w = 15) → Loader.Ref p L g w dn →
      Move L g w dn e d' → I w dn → I w (d', Code.bump (Loader.cls L g) dn.2 e))
    (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) :
    ∀ k b d n, Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)) →
      n .ub = 0 → I (wOf b) (d, lcn n) := by
  have hG := good hp hX hw hg rfl
  intro k
  induction k with
  | zero =>
    intro b d n hσ
    rw [Frame.stateAt_zero] at hσ
    cases hσ
  | succ k ih =>
    intro b d n hσ hub
    by_cases hk : k < (X.tr g).length
    swap
    · rw [Frame.stateAt_of_le (by omega)] at hσ
      exact ih b d n (by rw [Frame.stateAt_of_le (by omega)]; exact hσ) hub
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
          obtain ⟨hS, -, hZ⟩ := hR
          have hE := (start_fired hp hX he h0').1
          obtain ⟨s', -, hent⟩ := Code.glue_inl_some h1
          simp only [Code.enter] at hent
          split at hent
          · cases hent
            have hz : lcn n = fun _ => 0 := funext fun c => by
              rw [hn2]
              exact (start_bump hS hE (.load c) (by simp [StartCls])).trans (hZ c)
            rw [hz]
            exact h0 b
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
                obtain ⟨hJ, -⟩ := hR hub0
                rw [← hb] at hJ
                have hev := (lfired hp hX he h0').1
                exact hstep _ _ e d hw' hJ (step_spec hp hw' hJ hev hnu hF)
                  (ih b d0 n0 h0' hub0)
          | _ => exact hR.elim

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
