-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Flow.GlueStep
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Recv

@[expose] public section

/-! # The MMA warp's descriptor words along its trace

Every role state of a lane of warp 12 keeps its descriptor words (`Mma.DOk`): the broadcast words
it recorded have the pattern `BW` and, past the broadcast before the scan, its Q descriptors are
`qv` of its site (`mma_desc`, by induction along the trace: the role's first state records no
word, and each step keeps them by `Mma.succ_desc` with the received words of `Mma.recv_word`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The descriptor words of a state of the thread machine: those of a role state of the MMA
warp. -/
def MDesc (p : Params) (L : Launch) (g : Nat) : (thread p L g).D → Prop
  | (.inr ⟨.mma, .inr ⟨_, d⟩⟩, _) => Mma.DOk L d
  | _ => True

theorem dok_init : Mma.DOk L ⟨.bar1, {}⟩ :=
  ⟨fun k => by fin_cases k <;> exact Mma.bw_i32 0 (by decide), fun h => by cases h⟩

theorem mdesc_enter (s : Startup.D) (n : Cls → Nat) :
    MDesc p L g (Code.enter (Startup.code p L g) (frag p L g) (exit L g) s, n) := by
  unfold Code.enter
  split
  · rename_i i _
    cases i <;> trivial
  · trivial

set_option maxHeartbeats 8000000 in
/-- **Every state of a lane of warp 12 keeps its descriptor words.** -/
theorem mma_desc (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (h12 : Prologue.warpIndex L g = 12) :
    ∀ k, k ≤ (X.tr g).length → ∀ σ, Frame.stateAt (thread p L) X g k = some (some σ) →
      MDesc p L g σ := by
  have hReads := cuQReadsFromLaunch hp hX
  have IH : ∀ n, Mma.GoodUpTo p L X n := fun _ h j hin _ =>
    Mma.good hp hX hReads hin.1 hin.2 j
  intro k
  induction k with
  | zero =>
    intro _ σ hσ
    rw [Frame.stateAt_zero] at hσ
    cases hσ
    exact mdesc_enter (Startup.code p L g).init (fun _ => 0)
  | succ k ih =>
    intro hk σ hσ
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e :=
      ⟨_, List.getElem?_eq_getElem (show k < (X.tr g).length by omega)⟩
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
        have hI := ih (by omega) σ0 hσ0
        have hJ := (Mma.good hp hX hReads hg h12 k).2 σ0 hσ0
        obtain ⟨σ1, n0⟩ := σ0
        obtain ⟨σ', n'⟩ := σ
        obtain ⟨h1, -⟩ := Code.counted_next_some (C := glued p L g) hn
        rcases σ1 with s | ⟨i, d⟩
        · obtain ⟨s', -, rfl⟩ := Code.glue_inl_some h1
          exact mdesc_enter s' n'
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
            all_goals first | trivial | exact dok_init
          · simp only [glued, Code.glue, frag, Mma.M, Mma.G] at h1
            cases hs : Mma.succ p L g d e with
            | none => simp [Mma.code, hs] at h1
            | some o' =>
              cases o' with
              | none => simp [Mma.code, hs] at h1
              | some d' =>
                simp only [Mma.code, hs, Option.map_some, Option.some.injEq] at h1
                subst h1
                have hub0 : n0 .ub = 0 := ub_zero hX he hσ0
                obtain ⟨hRC, hMF⟩ := hJ hub0
                refine Mma.succ_desc hI (fun hsite md a b c r o hk => ?_) hs
                obtain ⟨pc, kind⟩ := e
                simp only at hk
                subst hk
                obtain ⟨x, hx, h2, h3⟩ := Mma.recv_word hp hX hg h12 he hσ0 hRC hMF (IH _) hsite
                exact ⟨x, hx, h2, h3⟩
        | _ =>
          exfalso
          simp [Mma.Ref] at hJ

end
end PTX.Kernels.TmlFa4Fwd.Proof
