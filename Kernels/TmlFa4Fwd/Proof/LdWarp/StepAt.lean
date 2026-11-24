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
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Fact
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.Startup.Shape
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Loader.RefNext

@[expose] public section

/-! # A loader fact with everything known at a step

`step_at`: as `hist_at` (`LdWarp/Hist.lean`), with the state's ledger, the reference values
(`LFits`) before and after the step, and the step itself (`Loader.succ`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Loader

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **A loader fact about the earlier events holds at every loader state of a lane of warp 14 or
15** without undefined behaviour so far. -/
theorem step_at {w : Nat} {I : Nat → D × (Cnt → Nat) → Prop}
    (h0 : ∀ b k n, Frame.stateAt (thread p L) X g k =
      some (some (linj p L g b (Loader.F p L g b).init n)) → (lcn n = fun _ => 0) →
      (∀ c : Event → Bool, (∀ s e, Startup.Ev L g s e → (∀ r, s.site ≠ .enter r) → c e = false) →
        ((X.tr g).take k).countP c = 0) →
      I k ((Loader.F p L g b).init, fun _ => 0))
    (hstep : ∀ k b n d e d', X.get (g, k) = some e →
      Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)) → n .ub = 0 →
      Loader.Ref p L g w (d, lcn n) →
      LFits p L g d (n .shfl) (n .vote) (n (.load .commit)) →
      (∃ ns nv, LFits p L g d' ns nv (n (.load .commit) + cm e)) →
      Loader.Ev p L g w d e → (∀ f, e.kind ≠ .ub f) →
      Loader.succ p L g w d e = some (some d') →
      Move L g w (d, lcn n) e d' → I k (d, lcn n) →
      I (k + 1) (d', Code.bump (Loader.cls L g) (lcn n) e))
    (hmono : ∀ k dn, (X.tr g).length ≤ k → I k dn → I (k + 1) dn)
    (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (hw : w = 14 ∨ w = 15) (hgw : Prologue.warpIndex L g = w) :
    ∀ k b d n, Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)) →
      n .ub = 0 → I k (d, lcn n) := by
  have hG := good hp hX hw hg hgw
  have hen : ∀ {s : Startup.D}, exit L g s = none →
      ∀ r, s.site ≠ .enter r := by
    intro s h r hr
    obtain ⟨site, x1, x2, x3⟩ := s
    simp only at hr
    subst hr
    simp [exit] at h
  -- no event of a class the startup does not make
  have hst : ∀ c : Event → Bool,
      (∀ s e, Startup.Ev L g s e → (∀ r, s.site ≠ .enter r) → c e = false) → ∀ {k : Nat} {s n},
      Frame.stateAt (thread p L) X g k = some (some (.inl s, n)) →
      ((X.tr g).take k).countP c = 0 := by
    intro c hc k
    induction k with
    | zero => intro s n _; simp
    | succ k ih =>
      intro s n hσ
      by_cases hk : k < (X.tr g).length
      swap
      · have h := ih (by rw [Frame.stateAt_of_le (by omega)] at hσ ⊢; exact hσ)
        rw [List.take_of_length_le (by omega)] at h ⊢
        exact h
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
          have hn : (thread p L g).next σ0 e = some (some (.inl s, n)) := hs.symm
          obtain ⟨σ1, n0⟩ := σ0
          obtain ⟨h1, -⟩ := Code.counted_next_some hn
          rcases σ1 with s0 | ⟨i, d0⟩
          · rw [List.take_add_one, he, List.countP_append, ih h0']
            simp [hc _ _ (start_fired hp hX he h0').1 (hen (start_fired hp hX he h0').2.1)]
          · exfalso
            simp only [glued, Code.glue] at h1
            cases hr : (frag p L g i).next d0 e with
            | none => rw [hr] at h1; simp at h1
            | some o => cases o <;> rw [hr] at h1 <;> simp at h1
  intro k
  induction k with
  | zero =>
    intro b d n hσ
    rw [Frame.stateAt_zero] at hσ
    cases hσ
  | succ k ih =>
    intro b d n hσ hub
    have hσ0 := hσ
    by_cases hk : k < (X.tr g).length
    swap
    · rw [Frame.stateAt_of_le (by omega)] at hσ
      exact hmono k _ (by omega) (ih b d n (by rw [Frame.stateAt_of_le (by omega)]; exact hσ) hub)
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
          simp only [glued, Code.glue, Startup.code] at h1
          cases hsu : Startup.succ L g s e with
          | none => rw [hsu] at h1; simp at h1
          | some o =>
            cases o with
            | none => rw [hsu] at h1; simp at h1
            | some s' =>
              rw [hsu] at h1
              simp only [Option.map_some, Option.some.injEq, Code.enter] at h1
              split at h1
              · cases h1
                have hz : lcn n = fun _ => 0 := funext fun c => by
                  rw [hn2]
                  exact (start_bump hS hE (.load c) (by simp [StartCls])).trans (hZ c)
                rw [hz]
                refine h0 b _ _ hσ0 hz fun c hc => ?_
                rw [List.take_add_one, he, List.countP_append, hst c hc h0']
                simp [hc _ _ hE (hen (start_fired hp hX he h0').2.1)]
              · cases h1
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
                obtain ⟨hJ, hF0⟩ := hR hub0
                obtain ⟨-, hF1⟩ := ((hG (k + 1)).2 _ hσ0).2 hub
                have hev := (lfired hp hX he h0').1
                subst hb
                have hcm : Code.bump (Proof.cls L g) n0 e (.load .commit) =
                    n0 (.load .commit) + cm e := by
                  obtain ⟨pc, kd⟩ := e
                  cases kd <;> simp [Code.bump, Proof.cls, Loader.cls, cm]
                rw [hcm] at hF1
                exact hstep _ _ n0 d0 e d he h0' hub0 hJ hF0 ⟨_, _, hF1⟩ hev hnu hF
                  (step_spec hp hw hJ hev hnu hF) (ih b d0 n0 h0' hub0)
          | _ => exact hR.elim

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
