-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
public import Kernels.TmlFa4Fwd.Proof.Loader.Move
public import Kernels.TmlFa4Fwd.Proof.Loader.Ref
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.Loader.RefNext
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A loader fact with a count of the trace

`LdWarp.count_at`: a predicate of the counted loader state and of the number of the lane's earlier
events of a class, which need not be one of the ledger's, kept by every step (`Loader.Move`, with
the step itself), holds at every state of a lane of warp 14 or 15 (`LdWarp.fact_at` with a
counter). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Loader

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A startup event is neither copy. -/
private theorem start_no {s s' : Startup.D} {e : Event} (hEv : Startup.Ev L g s e)
    (hsu : Startup.succ L g s e = some (some s'))
    (h : (∃ s, e.kind = .copy s) ∨ ∃ a s, e.kind = .tensorIssue a s) : False := by
  obtain ⟨site, x1, x2, x3⟩ := s
  rcases h with ⟨_, hk⟩ | ⟨_, _, hk⟩ <;>
  · cases site with
    | enter r => simp [Startup.succ] at hsu
    | sh j =>
      fin_cases j <;> simp only [Startup.Ev] at hEv <;> obtain ⟨_, _, hk'⟩ := hEv <;>
        rw [hk] at hk' <;> cases hk'
    | fence => simp only [Startup.Ev] at hEv; rw [hk] at hEv; cases hEv
    | bar => simp only [Startup.Ev] at hEv; rw [hk] at hEv; cases hEv
    | elect j =>
      simp only [Startup.Ev] at hEv
      rcases hEv with ⟨_, _, -, hk'⟩ | ⟨_, hk'⟩ <;> rw [hk] at hk' <;> cases hk'
    | init q =>
      simp only [Startup.Ev] at hEv
      rcases hEv with ⟨_, _, hk'⟩ | ⟨_, hk'⟩ <;> rw [hk] at hk' <;> cases hk'

set_option maxHeartbeats 1000000 in
/-- **A loader fact with a count holds at every loader state**, the steps at the trace's events. -/
theorem count_on {I : Nat → D × (Cnt → Nat) → Nat → Prop} {c : Event → Bool}
    (hc : ∀ e, c e = true → (∃ s, e.kind = .copy s) ∨ ∃ a s, e.kind = .tensorIssue a s)
    (h0 : ∀ b, I (wOf b) ((Loader.F p L g b).init, fun _ => 0) 0)
    (hstep : ∀ w (dn : D × (Cnt → Nat)) e d' N, (w = 14 ∨ w = 15) → Loader.Ref p L g w dn →
      Loader.Ev p L g w dn.1 e → (∀ f, e.kind ≠ .ub f) →
      Loader.succ p L g w dn.1 e = some (some d') → Move L g w dn e d' →
      (∃ k, X.get (g, k) = some e) → I w dn N →
      I w (d', Code.bump (Loader.cls L g) dn.2 e) (N + if c e then 1 else 0))
    (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) :
    ∀ k b d n, Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)) →
      n .ub = 0 → I (wOf b) (d, lcn n) (((X.tr g).take k).countP c) := by
  have hG := good hp hX hw hg rfl
  -- no such event in the startup
  have hst : ∀ {k : Nat} {s n}, Frame.stateAt (thread p L) X g k = some (some (.inl s, n)) →
      ((X.tr g).take k).countP c = 0 := by
    intro k
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
          · have hE := (start_fired hp hX he h0').1
            have hce : c e = false := by
              rw [Bool.eq_false_iff]
              intro h
              simp only [glued, Code.glue, Startup.code] at h1
              cases hsu : Startup.succ L g s0 e with
              | none => rw [hsu] at h1; simp at h1
              | some o =>
                cases o with
                | none => rw [hsu] at h1; simp at h1
                | some s' => exact start_no hE hsu (hc e h)
            rw [List.take_add_one, he, List.countP_append, ih h0']
            simp [hce]
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
    by_cases hk : k < (X.tr g).length
    swap
    · rw [Frame.stateAt_of_le (by omega)] at hσ
      have h := ih b d n (by rw [Frame.stateAt_of_le (by omega)]; exact hσ) hub
      rw [List.take_of_length_le (by omega)] at h ⊢
      exact h
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
    have hcnt : ((X.tr g).take (k + 1)).countP c =
        ((X.tr g).take k).countP c + if c e then 1 else 0 := by
      rw [List.take_add_one, he, List.countP_append]
      simp [List.countP_cons]
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
                have hce : c e = false := by
                  rw [Bool.eq_false_iff]
                  intro h
                  exact start_no hE hsu (hc e h)
                rw [hz, hcnt, hce, hst h0']
                exact h0 b
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
                have hw' : wOf b = 14 ∨ wOf b = 15 := by cases b <;> simp [wOf]
                obtain ⟨hJ, -⟩ := hR hub0
                rw [← hb] at hJ
                have hev := (lfired hp hX he h0').1
                rw [hcnt]
                exact hstep _ _ e d _ hw' hJ hev hnu hF (step_spec hp hw' hJ hev hnu hF)
                  ⟨k, he⟩ (ih b d0 n0 h0' hub0)
          | _ => exact hR.elim

/-- **A loader fact with a count holds at every loader state.** -/
theorem count_at {I : Nat → D × (Cnt → Nat) → Nat → Prop} {c : Event → Bool}
    (hc : ∀ e, c e = true → (∃ s, e.kind = .copy s) ∨ ∃ a s, e.kind = .tensorIssue a s)
    (h0 : ∀ b, I (wOf b) ((Loader.F p L g b).init, fun _ => 0) 0)
    (hstep : ∀ w (dn : D × (Cnt → Nat)) e d' N, (w = 14 ∨ w = 15) → Loader.Ref p L g w dn →
      Loader.Ev p L g w dn.1 e → (∀ f, e.kind ≠ .ub f) →
      Loader.succ p L g w dn.1 e = some (some d') → Move L g w dn e d' → I w dn N →
      I w (d', Code.bump (Loader.cls L g) dn.2 e) (N + if c e then 1 else 0))
    (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) :
    ∀ k b d n, Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)) →
      n .ub = 0 → I (wOf b) (d, lcn n) (((X.tr g).take k).countP c) :=
  count_on hc h0 (fun w dn e d' N hw' hJ hev hub hn hm _ h =>
    hstep w dn e d' N hw' hJ hev hub hn hm h) hp hX hg hw

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
