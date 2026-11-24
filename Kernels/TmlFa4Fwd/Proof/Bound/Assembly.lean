-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.JR
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Bound
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Bound
public import Kernels.TmlFa4Fwd.Proof.Loader.Export.Bound
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Bound
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Bound
public import Kernels.TmlFa4Fwd.Proof.Bound.Startup
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Code
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Lib.GlobalWrites
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.FollowView
import Kernels.TmlFa4Fwd.Proof.Top.JRView
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Kernels.TmlFa4Fwd.Proof.Correction.Export.ControlBound
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.ControlBound
import Lemmas.Flow.GlueStep
import Lemmas.Kernel.BoundU

@[expose] public section

/-! # Every execution is bounded (G1)

The thread machine's states are measured role by role: the startup's measure below `9181`, and a
role state's measure (`roleμ`, from the role's bound file) above it; the MMA warp's four startup
states below its code states. A state after undefined behaviour (its ledger counts one) has the
largest measure, `top`. Along a followed thread every transition keeps the measure and every
counted event raises it (`μ_step`, from the roles' `measure_step` with the room of their round
counters, which the reference invariant gives), and the measure of a state that holds its role's
reference invariant is at most `top` (`μ_le`, from the roles' `measure_le`). So `top` less the
measure is a rank that every counted event lowers (`Frame.count_le`), and every thread's counted
events are at most `top + 2` (`terminates`). The copies' widths are the old tree's code check
(`actualCopyShape`, a static check that moves with the switch). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Bound
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The MMA warp's startup states, in their order. -/
def startRank : Mma.Start → Nat
  | .set => 0 | .alloc => 1 | .wr => 2 | .enter => 3

/-- **The measure of a role state**, with the thread's ledger. -/
def roleμ (p : Params) (L : Launch) (g : Nat) : (i : Role) → (frag p L g i).D → (Cls → Nat) → Nat
  | .epilogue, d, n => Epilogue.measure d (n .shfl)
  | .mma, .inl s, _ => startRank s
  | .mma, .inr ⟨_, d⟩, n => 4 + Mma.measure d (n .shfl)
  | .correction, d, n => Correction.measure d (n .shfl)
  | .loader _, d, n => Loader.measure p d (n .shfl)
  | .softmax, d, n => Softmax.measure d (n .shfl)
  | .stub _, _, _ => 0

/-- The bound of the roles' measures. -/
def RB (p : Params) : Nat :=
  4 + ((14 * p.batch + 27) * 64 + 63) + (14 * p.batch + 29) * Mma.W +
    (14 * p.batch + 28) * Correction.W + (Loader.base p 3 + 64) + (14 * p.batch + 28) * Softmax.W

/-- The largest measure. -/
def top (p : Params) : Nat := 9182 + RB p

/-- The measure of a state that has not seen undefined behaviour. -/
def μ0 (p : Params) (L : Launch) (g : Nat) : (thread p L g).D → Nat
  | (.inl s, _) => Startup.measure s
  | (.inr ⟨i, d⟩, n) => 9181 + roleμ p L g i d n

/-- **The measure of a thread machine state.** -/
def μ (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Nat :=
  if σ.2 .ub = 0 then μ0 p L g σ else top p

/-- **A state that holds its role's reference invariant and has seen no undefined behaviour has
a measure below `top`.** -/
theorem μ0_le (hp : Pre p L m) {σ : (glued p L g).D} {n : Cls → Nat} (hJ : JR p L g (σ, n))
    (hub : n .ub = 0) : μ0 p L g (σ, n) + 1 ≤ top p := by
  have hR : ∀ x, x ≤ RB p → 9181 + x + 1 ≤ top p := fun x hx => by unfold top; omega
  rcases σ with s | ⟨i, d⟩
  · have := Startup.measure_le s
    simp only [μ0, top]
    omega
  simp only [μ0]
  refine hR _ ?_
  unfold RB
  rw [JR_eq] at hJ; unfold RefAll at hJ
  cases i with
  | softmax =>
    split_ifs at hJ
    · obtain ⟨-, h⟩ := hJ
      have := Softmax.measure_le hp (h hub).2
      simp only [roleμ]
      omega
    all_goals simp [Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref] at hJ
  | epilogue =>
    split_ifs at hJ <;> simp only [SmWarp.Ref, Mma.Ref, LdWarp.Ref, CorrWarp.Ref] at hJ
    have := Epilogue.measure_le hp hJ.1
    simp only [roleμ]
    omega
  | mma =>
    split_ifs at hJ <;> simp only [SmWarp.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref] at hJ
    rcases d with s | ⟨_, d⟩
    · have : startRank s ≤ 3 := by cases s <;> simp [startRank]
      simp only [roleμ]
      omega
    · have := Mma.measure_le hp (hJ hub).2
      simp only [roleμ]
      omega
  | correction =>
    split_ifs at hJ <;> simp only [SmWarp.Ref, Epilogue.Ref, LdWarp.Ref, Mma.Ref] at hJ
    have := Correction.measure_le hp (hJ hub).2
    simp only [roleμ]
    omega
  | loader b =>
    split_ifs at hJ <;> simp only [SmWarp.Ref, Epilogue.Ref, CorrWarp.Ref, Mma.Ref] at hJ
    have := Loader.measure_le hp (hJ.2 hub).2
    simp only [roleμ]
    omega
  | stub r =>
    split_ifs at hJ <;> simp [SmWarp.Ref, Epilogue.Ref, CorrWarp.Ref, Mma.Ref, LdWarp.Ref] at hJ

/-- **Every transition from a state that holds its role's reference invariant keeps the measure,
and every counted event raises it.** -/
theorem μ0_step (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat} {σ σ' :
    (glued p L g).D} {n : Cls → Nat} {e : Event}
    (he : X.get (g,k) = some e) (hσ : Frame.stateAt (thread p L) X g k = some (some (σ,n)))
    (hu : ∀ f, e.kind ≠ .ub f) (hJ : JR p L g (σ, n)) (hub : n .ub = 0)
    (hn : (glued p L g).next σ e = some (some σ')) :
    μ0 p L g (σ, n) + (if e.counts then 1 else 0) ≤
      μ0 p L g (σ', Code.bump (cls L g) n e) := by
  have hsh : Code.bump (cls L g) n e .shfl = n .shfl + if Execution.isShfl e then 1 else 0 := rfl
  have hc : ∀ {a b : Nat}, a ≤ b → (e.counts = true → a < b) →
      a + (if e.counts then 1 else 0) ≤ b := fun h1 h2 => by
    cases hct : e.counts
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; exact h1
    · have := h2 hct; simp only [↓reduceIte]; omega
  rcases σ with s | ⟨i, d⟩
  · obtain ⟨s', hs', rfl⟩ := Code.glue_inl_some hn
    have hlt := Startup.measure_lt (show Startup.succ L g s e = some (some s') from hs')
    have hle := Startup.measure_le s
    cases hx : exit L g s' with
    | none =>
      rw [Code.enter_none hx]
      simp only [μ0]
      split <;> omega
    | some i =>
      rw [Code.enter_some hx]
      simp only [μ0]
      split <;> omega
  obtain ⟨d', hd', rfl⟩ := Code.glue_inr_some hn
  suffices h : roleμ p L g i d n + (if e.counts then 1 else 0) ≤
      roleμ p L g i d' (Code.bump (cls L g) n e) by
    simp only [μ0]; omega
  rw [JR_eq] at hJ; unfold RefAll at hJ
  cases i with
  | epilogue =>
    split_ifs at hJ <;> simp only [SmWarp.Ref, Mma.Ref, LdWarp.Ref, CorrWarp.Ref] at hJ
    obtain ⟨h1, h2⟩ := Epilogue.measure_step (p := p) (L := L) (g := g) hd' hsh
    exact hc h1 h2
  | mma =>
    split_ifs at hJ <;> simp only [SmWarp.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref] at hJ
    rcases d with s | ⟨u, d⟩
    · obtain ⟨s', hs', rfl⟩ := Code.glue_inl_some hd'
      unfold Code.enter
      cases s <;> simp only [Mma.S, Option.some.injEq, reduceCtorEq] at hs'
      all_goals subst hs'
      all_goals (split_ifs <;> simp [roleμ, startRank, Mma.Start.exit] <;> omega)
    · obtain ⟨d'', hd'', rfl⟩ := Code.glue_inr_some hd'
      obtain ⟨hRC, hF⟩ := hJ hub
      have hps : d.v.ps ≤ n .shfl := by
        unfold Mma.MFits at hF
        split at hF <;> omega
      obtain ⟨h1, h2⟩ := Mma.measure_step (p := p) (L := L) (g := g) hd''
        (Mma.trip_room hRC) hps hsh
      simp only [roleμ]
      exact hc (by omega) (fun h => by have := h2 h; omega)
  | correction =>
    split_ifs at hJ <;> simp only [SmWarp.Ref, Epilogue.Ref, LdWarp.Ref, Mma.Ref] at hJ
    obtain ⟨hRef, hF⟩ := hJ hub
    have hev := (CorrWarp.fired_both hp hX he hσ hu).1
    have rep := Correction.Control.represents hRef.counts hev hu hd'
    obtain ⟨h1, h2⟩ := Correction.Control.measure_step rep
      (Correction.trip_room hF) hsh
    exact hc h1 h2
  | loader b =>
    split_ifs at hJ <;> simp only [SmWarp.Ref, Epilogue.Ref, CorrWarp.Ref, Mma.Ref] at hJ
    obtain ⟨-, hF⟩ := hJ.2 hub
    obtain ⟨h1, h2⟩ := Loader.measure_step (p := p) (L := L) (g := g) hd'
      (Loader.rnd_room hF) (Loader.pass_bounds hp hF).1 (Loader.pass_bounds hp hF).2 hsh
    exact hc h1 h2
  | softmax =>
    by_cases h8 : Prologue.warpIndex L g < 8
    swap
    · simp only [h8, ↓reduceIte] at hJ
      split_ifs at hJ <;> simp [Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref] at hJ
    simp only [h8, ↓reduceIte] at hJ
    obtain ⟨-, h⟩ := hJ
    obtain ⟨⟨c, hRef, -⟩, -⟩ := h hub
    have hev := (SmWarp.fired_soft hp hX he hσ hu).1.1
    have rep := Softmax.Control.represents hp hRef hev hu hd'
    obtain ⟨h1, h2⟩ := Softmax.Control.measure_step rep
      (fun hs' => Softmax.nb_room (dn := (d.scheduler, c)) hRef.counts hs') hsh
    exact hc h1 h2
  | stub r =>
    split_ifs at hJ <;> simp [SmWarp.Ref, Epilogue.Ref, CorrWarp.Ref, Mma.Ref, LdWarp.Ref] at hJ

/-- **A followed thread's counted events are bounded**: `top - μ` is a rank that every
transition from a followed state lowers by the event's count. -/
theorem counts_le (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hg : g < L.threads) :
    (X.tr g).countP Event.counts ≤ top p + 2 := by
  have hC : ∀ g < L.threads, (thread p L g).SoundU := fun g hg => thread_sound hp hg
  have ht : Frame.Tracked (thread p L) X := fun h k hh => (goodR hp hX hFw hh k).1
  have h := Frame.count_leU hC hX hg ht (fun σ => top p - μ p L g σ) (fun _ => false) 0
    fun k ⟨s, n⟩ ⟨s', n'⟩ e he hσ _ hu hn => by
      obtain ⟨hn1, rfl⟩ := Code.counted_next_some (C := glued p L g) hn
      have hJ := (goodR hp hX hFw hg k).2 _ hσ
      have hub := ub_zero hX (show X.get (g, k) = some e from he) hσ
      have hlt := μ0_le hp hJ hub
      have hst := μ0_step hp hX he hσ hu hJ hub hn1
      dsimp only at hst
      simp only [μ, hub, ↓reduceIte, Bool.false_eq_true, Nat.add_zero]
      split
      · have hσ' : Frame.stateAt (thread p L) X g (k + 1) =
            some (some (s', Code.bump (cls L g) n e)) := by
          rw [Frame.stateAt_succ he, hσ]; exact hn
        have hJ' := (goodR hp hX hFw hg (k + 1)).2 _ hσ'
        rename_i hub'
        have := μ0_le hp hJ' hub'
        omega
      · split <;> omega
  have h0 : μ p L g (thread p L g).init = 0 := rfl
  simpa only [h0, Nat.sub_zero, Nat.zero_mul, Nat.add_zero] using h

/-- **Every consistent execution is bounded.** -/
theorem terminates (hp : Pre p L m) :
    ∃ n, ∀ X, Consistent L kernel Assumptions.all m X → X.size L ≤ n :=
  terminates_of_count (top p + 2)
    (fun X hX g hg => counts_le hp hX (follow hp hX) hg)
    (fun X hX i s hi => by
      rw [(actualCopyShape hX hi).widthEq]
      decide)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Bound
