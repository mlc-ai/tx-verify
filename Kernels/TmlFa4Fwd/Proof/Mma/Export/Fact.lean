-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Flow.GlueStep
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Recv

@[expose] public section

/-! # A fact of the MMA warp's states along its trace

`Mma.fact_at`: a predicate of the role's state that holds at the role's first state and is kept by
every step of a lane of warp 12 holds at each of the lane's role states. The step is given with the
event's position in the trace, so a fact can read a broadcast's received word
(`Mma.recv_word`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **Every state of a lane of warp 12 is followed with its reference invariant.** -/
theorem good_at (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (h12 : Prologue.warpIndex L g = 12) (k : Nat) : Good p L X g k :=
  good hp hX (cuQReadsFromLaunch hp hX) hg h12 k

/-- A state of the thread machine has the fact `I` if it is a state of the role. -/
def FactAt (p : Params) (L : Launch) (g : Nat) (I : D → Prop) : (thread p L g).D → Prop
  | (.inr ⟨.mma, .inr ⟨_, d⟩⟩, _) => I d
  | _ => True

theorem factAt_enter {I : D → Prop} (s : Startup.D) (n : Cls → Nat) :
    FactAt p L g I (Code.enter (Startup.code p L g) (frag p L g) (exit L g) s, n) := by
  unfold Code.enter
  split
  · rename_i i _
    cases i <;> trivial
  · trivial

set_option maxHeartbeats 8000000 in
/-- **A fact kept by the role's steps holds at every role state of a lane of warp 12.** -/
theorem fact_at (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (h12 : Prologue.warpIndex L g = 12) {I : D → Prop} (h0 : I ⟨.bar1, {}⟩)
    (hstep : ∀ k d n e d', X.get (g, k) = some e →
      Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)) →
      RefCounts p L g (d, rc n) → MFits p L g d (n .shfl) (n .vote) →
      GoodUpTo p L X (n .shfl + n .vote) → succ p L g d e = some (some d') → I d → I d') :
    ∀ k d n, Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)) → I d := by
  have hReads := cuQReadsFromLaunch hp hX
  have IH : ∀ n, GoodUpTo p L X n := fun _ h j hin _ => good hp hX hReads hin.1 hin.2 j
  have key : ∀ k σ, Frame.stateAt (thread p L) X g k = some (some σ) → FactAt p L g I σ := by
    intro k
    induction k with
    | zero =>
      intro σ hσ
      rw [Frame.stateAt_zero] at hσ
      cases hσ
      exact factAt_enter (Startup.code p L g).init (fun _ => 0)
    | succ k ih =>
      intro σ hσ
      by_cases hk : k < (X.tr g).length
      swap
      · rw [Frame.stateAt_of_le (by omega)] at hσ
        exact ih σ (by rw [Frame.stateAt_of_le (by omega)]; exact hσ)
      obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
      have hst := Frame.stateAt_succ (C := thread p L) (show (X.tr g)[k]? = some e from he)
      rw [hσ] at hst
      cases hσ0 : Frame.stateAt (thread p L) X g k with
      | none => rw [hσ0] at hst; simp at hst
      | some o =>
        cases o with
        | none => rw [hσ0] at hst; simp [Code.toMachine] at hst
        | some σ0 =>
          rw [hσ0] at hst
          have hn : (thread p L g).next σ0 e = some (some σ) := hst.symm
          have hI := ih σ0 hσ0
          have hJ := (good hp hX hReads hg h12 k).2 σ0 hσ0
          obtain ⟨σ1, n0⟩ := σ0
          obtain ⟨σ', n'⟩ := σ
          obtain ⟨h1, -⟩ := Code.counted_next_some (C := glued p L g) hn
          rcases σ1 with s | ⟨i, d⟩
          · obtain ⟨s', -, rfl⟩ := Code.glue_inl_some h1
            exact factAt_enter s' n'
          cases i with
          | mma =>
            rcases d with s0 | ⟨⟨⟩, d⟩
            · simp only [glued, Code.glue, frag, Mma.M, Mma.G, Mma.S] at h1
              cases s0
              all_goals simp only [Option.map_some, Option.map_none, Option.some.injEq,
                reduceCtorEq] at h1
              all_goals subst h1
              all_goals (try split)
              all_goals simp only [Code.enter, Mma.Start.exit]
              all_goals trivial
            · simp only [glued, Code.glue, frag, Mma.M, Mma.G] at h1
              cases hs : Mma.succ p L g d e with
              | none => simp [Mma.code, hs] at h1
              | some o' =>
                cases o' with
                | none => simp [Mma.code, hs] at h1
                | some d' =>
                  simp only [Mma.code, hs, Option.map_some, Option.some.injEq] at h1
                  subst h1
                  obtain ⟨hRC, hMF⟩ := hJ (ub_zero hX he hσ0)
                  exact hstep k d n0 e d' he hσ0 hRC hMF (IH _) hs hI
          | _ =>
            exfalso
            simp [Mma.Ref] at hJ
  exact fun k d n h => key k _ h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
