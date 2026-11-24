-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.TcCount
import Kernels.TmlFa4Fwd.Proof.Common.Coll
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Representative
import Kernels.TmlFa4Fwd.Proof.Correction.RefCases
import Kernels.TmlFa4Fwd.Proof.Correction.RefEv
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Src
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The rescale ballots and the collective `tcgen05` events at a correction lane's states

`corr_tcC`: the relation `TcC` holds at every role state of a correction lane. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (ptsOf passed before allSites mem_allSites nexts)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

open Correction (tw pend finPts rvPts finc brv bnb vv)

/-- **The relation at every role state of a correction lane.** -/
theorem corr_tcC (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hub : ¬ HasUb X) (hg : g < L.threads)
    (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11) :
    ∀ k, k ≤ (X.tr g).length → ∀ σ, Frame.stateAt (thread p L) X g k = some (some σ) →
      (∃ s n, σ = (.inl s, n) ∧ ((X.tr g).take k).countP isTcColl = 0 ∧
        ((X.tr g).take k).countP isRb = 0 ∧ n .vote = 0 ∧ n (.corr (.nb 0)) = 0) ∨
      ∃ d n, σ = CorrWarp.cinj p L g d n ∧ TcC X g k d.site n := by
  intro k
  induction k with
  | zero =>
    intro _ σ hσ
    rw [Frame.stateAt_zero] at hσ
    cases hσ
    exact .inl ⟨_, _, rfl, by simp, by simp, rfl, rfl⟩
  | succ k ih =>
    intro hk σ hσ
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e :=
      ⟨_, List.getElem?_eq_getElem (show k < (X.tr g).length by omega)⟩
    have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(g, k), e.pc, f, by
      rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
    have hstep := Frame.stateAt_succ (C := thread p L) (show (X.tr g)[k]? = some e from he)
    rw [hσ] at hstep
    cases hσ0 : Frame.stateAt (thread p L) X g k with
    | none => rw [hσ0] at hstep; simp at hstep
    | some o =>
      cases o with
      | none => rw [hσ0] at hstep; simp [Code.toMachine] at hstep
      | some σ0 =>
        rw [hσ0] at hstep
        have hn : (thread p L g).next σ0 e = some (some σ) := hstep.symm
        have hpc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hσ0 hne
        rcases ih (by omega) σ0 hσ0 with ⟨s, n, rfl, h1, h2, h3, h4⟩ | ⟨d, n, rfl, hT⟩
        · have hex := CorrWarp.open_ev hp hX hFw hw hw1 he hne
          rcases hex with ⟨s', n', hσ', -, -, hi, hev⟩ | ⟨d', n', hσ', -⟩
          swap
          · rw [hσ0] at hσ'; cases hσ'
          rw [hσ0] at hσ'
          cases hσ'
          have hq : isTcColl e = false ∧ isRb e = false ∧ isFullVote e = false ∧
              cls L g (.corr (.nb 0)) e = false := by
            have hx : exit L g s = none := hi.2
            obtain ⟨site, x1, x2, x3⟩ := s
            obtain ⟨pc, kd⟩ := e
            cases site with
            | sh j =>
              fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk⟩ := hev <;>
                subst hk <;>
                exact ⟨rfl, by simp [isRb, isBallot], rfl, by simp [cls, Correction.cls]⟩
            | elect j =>
              simp only [Startup.Ev] at hev
              rcases hev with ⟨_, _, -, hk⟩ | ⟨f, hk⟩ <;> subst hk <;>
                exact ⟨rfl, by simp [isRb, isBallot], rfl, by simp [cls, Correction.cls]⟩
            | init q =>
              simp only [Startup.Ev] at hev
              rcases hev with ⟨_, _, hk⟩ | ⟨f, hk⟩ <;> subst hk <;>
                exact ⟨rfl, by simp [isRb, isBallot], rfl, by simp [cls, Correction.cls]⟩
            | fence =>
              simp only [Startup.Ev] at hev
              subst hev
              exact ⟨rfl, by simp [isRb, isBallot], rfl, by simp [cls, Correction.cls]⟩
            | bar =>
              simp only [Startup.Ev] at hev
              subst hev
              have := (corr_nb_range L g).1
              refine ⟨rfl, by simp [isRb, isBallot], rfl, ?_⟩
              simp only [cls, Correction.cls, decide_eq_false_iff_not]
              exact fun h => by
                have h' : 0 = (Correction.nb0W L g).toNat := h
                omega
            | enter r => simp [exit] at hx
          obtain ⟨q1, q2, q3, q4⟩ := hq
          have hv : Code.bump (cls L g) n e .vote = 0 := by simp [Code.bump, cls, q3, h3]
          have hnb : Code.bump (cls L g) n e (.corr (.nb 0)) = 0 := by simp [Code.bump, q4, h4]
          have k1 : ((X.tr g).take (k + 1)).countP isTcColl = 0 := by
            rw [corr_take_snoc he, h1, q1]; rfl
          have k2 : ((X.tr g).take (k + 1)).countP isRb = 0 := by
            rw [corr_take_snoc he, h2, q2]; rfl
          have k3 : ((X.tr g).take (k + 1)).countP isRv = 0 := by
            have := List.countP_mono_left (l := (X.tr g).take (k + 1)) fun e _ => isRb_of_isRv e
            omega
          have hpl := (CorrWarp.good hp hX ⟨hw, hw1⟩ hg rfl (k + 1)).2 _ hσ
          obtain ⟨σ1, n1⟩ := σ
          obtain ⟨hn1, rfl⟩ := Code.counted_next_some (C := glued p L g) hn
          rcases σ1 with s' | ⟨_ | _ | _ | _ | r | _, d'⟩ <;> try exact hpl.elim
          · exact .inl ⟨s', _, rfl, k1, k2, hv, hnb⟩
          · right
            refine ⟨d', _, rfl, ?_⟩
            have hd' : d' = (frag p L g .correction).init := by
              simp only [glued, Code.glue, Startup.code] at hn1
              cases hsu : Startup.succ L g s e with
              | none => rw [hsu] at hn1; simp at hn1
              | some o =>
                cases o with
                | none => rw [hsu] at hn1; simp at hn1
                | some s1 =>
                  rw [hsu] at hn1
                  simp only [Option.map_some, Option.some.injEq] at hn1
                  unfold Code.enter at hn1
                  split at hn1
                  · cases hn1; rfl
                  · cases hn1
            subst hd'
            have hi : finc .setmax = 0 ∧ brv .setmax = 0 ∧ bnb .setmax = 0 ∧ vv .setmax = 0 ∧
                pend .setmax = 0 := by decide
            obtain ⟨i1, i2, i3, i4, i5⟩ := hi
            constructor
            · rw [k1, k3]
              show ((0 : Nat) : Int) + (pend .setmax : Int) = 25 * ((0 : Nat) : Int) + finc .setmax
              rw [i5, i1]; rfl
            · rw [k2, hnb]
              show ((0 : Nat) : Int) = brv .setmax + 2 * (((0 : Nat) : Int) - bnb .setmax)
              rw [i2, i3]; rfl
            · intro _ _
              rw [k2, hv]
              show ((0 : Nat) : Int) = ((0 : Nat) : Int) + vv .setmax
              rw [i4]; rfl
            · intro h
              exact absurd h (by
                rw [show pend (frag p L g .correction).init.site = 0 from i5]; omega)
        · right
          obtain ⟨hJ, hev⟩ : Correction.Control.Ref p L g (d, CorrWarp.rc n) ∧
              Correction.Control.Ev p L g d e := by
            rcases CorrWarp.open_ev hp hX hFw hw hw1 he hne with ⟨s, n', hσ', -⟩ |
              ⟨d', n', hσ', h0, hR, -, hev, -⟩
            · rw [hσ0] at hσ'; cases hσ'
            · rw [hσ0] at hσ'; cases hσ'; exact ⟨(hR h0).1.counts, hev⟩
          have hn' := (CorrWarp.next_cinj d n e).symm.trans hn
          cases hs : Correction.Control.succ p L g d e with
          | none => rw [hs] at hn'; cases hn'
          | some o =>
            cases o with
            | none => rw [hs] at hn'; simp at hn'
            | some d' =>
              rw [hs] at hn'
              simp only [Option.map_some, Option.some.injEq] at hn'
              subst hn'
              exact ⟨d', _, rfl, tcC_step hJ he hev hne hpc hs hT⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof
