-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Mma.Machine
public import Lemmas.Kernel.Frame
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Entry
import Std.Tactic.BVDecide.Normalize.Prop
set_option linter.unnecessarySeqFocus false

@[expose] public section

/-! # The state of the MMA warp's code before a state of it -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **A state of the MMA warp's code other than its initial state was reached from a state of the
code.** -/
theorem mma_pred {k : Nat} {d : Mma.D} {n : Cls → Nat} {e : Event}
    (hk : (X.tr g)[k]? = some e)
    (h : Frame.stateAt (thread p L) X g (k + 1) = some (some (Mma.minj p L g d n)))
    (hne : d ≠ (Mma.code p L g (Mma.ent p L)).init) :
    ∃ d0 n0, Frame.stateAt (thread p L) X g k = some (some (Mma.minj p L g d0 n0)) ∧
      Mma.succ p L g d0 e = some (some d) := by
  rw [Frame.stateAt_succ hk] at h
  rcases hs : Frame.stateAt (thread p L) X g k with _ | _ | ⟨σ1, n'⟩
  · rw [hs] at h; cases h
  · rw [hs] at h; cases h
  rw [hs] at h
  obtain ⟨h1, -⟩ := Code.counted_next_some (C := glued p L g) h
  rcases σ1 with s | ⟨i, d'⟩
  · exfalso
    simp only [glued, Code.glue] at h1
    rcases hn : Startup.succ L g s e with _ | _ | s' <;> rw [hn] at h1 <;>
      simp only [Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq] at h1
    exact hne (enter_mma h1)
  · cases i with
    | mma =>
      rcases d' with s | ⟨⟨⟩, d'⟩
      · exfalso
        apply hne
        cases s <;> simp [glued, Code.glue, frag, Mma.M, Mma.G, Code.enter, Mma.S,
          Mma.Start.exit] at h1 <;> (try split at h1) <;> simp_all
      · refine ⟨d', n', rfl, ?_⟩
        have h' : (thread p L g).next (Mma.minj p L g d' n') e = some (some (Mma.minj p L g d n)) :=
          h
        rw [Mma.next_minj] at h'
        obtain ⟨o, ho1, ho⟩ := Option.map_eq_some_iff.mp h'
        cases o with
        | none => cases ho
        | some x =>
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq,
            Sigma.mk.injEq, heq_eq_eq, true_and] at ho
          obtain ⟨rfl, -⟩ := ho
          exact ho1
    | _ =>
      exfalso
      simp only [glued, Code.glue] at h1
      obtain ⟨o, -, ho⟩ := Option.map_eq_some_iff.mp h1
      cases o <;> simp at ho

end
end PTX.Kernels.TmlFa4Fwd.Proof
