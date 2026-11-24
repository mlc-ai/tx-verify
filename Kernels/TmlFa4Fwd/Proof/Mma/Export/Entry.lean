-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Core.Data.Types
public import Core.Data.Value
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Mma.Machine
public import Kernels.TmlFa4Fwd.Proof.Startup.Machine
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.Code
public import Lemmas.Kernel.Frame
import Kernels.TmlFa4Fwd.Proof.Mma.Places
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Every state of the MMA warp's code follows its first barrier-2 rendezvous

The thread machine enters the MMA warp's code (`Mma.code`) only at its initial state, the
rendezvous `bar1`, and the code's states step to the code's states (`next_minj`). So a state of
the code before position `k` was preceded by its initial state at some position `k1 ≤ k`
(`mma_entered`); when the state is at another site, the lane's event at `k1` is that
rendezvous, a `bar.sync 2, 416` (`mma_bar1_before`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (minj)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- Entering a glued fragment's role of one index at a state: the role's initial state. -/
theorem enter_unit {P : Code kernel Assumptions.all L g}
    {R : Unit → Code kernel Assumptions.all L g}
    {ex : P.D → Option Unit} {s : P.D} {d : (R ()).D}
    (h : Code.enter P R ex s = .inr ⟨(), d⟩) : d = (R ()).init := by
  unfold Code.enter at h
  split at h
  · cases h; rfl
  · cases h

/-- The MMA warp's fragment entered at a state of its code: the code's initial state. -/
theorem frag_mma_init {d : Mma.D} (h : (frag p L g .mma).init = .inr ⟨(), d⟩) :
    d = (Mma.code p L g (Mma.ent p L)).init :=
  enter_unit (P := Mma.S p L g (Mma.ent p L)) (R := fun _ => Mma.code p L g (Mma.ent p L))
    (ex := Mma.Start.exit) (s := (Mma.S p L g (Mma.ent p L)).init) h

/-- The thread machine enters a state of the MMA warp's code from the startup only at the code's
initial state. -/
theorem enter_mma {s : Startup.D} {d : Mma.D}
    (h : Code.enter (Startup.code p L g) (frag p L g) (exit L g) s =
      .inr ⟨.mma, .inr ⟨(), d⟩⟩) : d = (Mma.code p L g (Mma.ent p L)).init := by
  unfold Code.enter at h
  split at h
  · cases h
  · cases h

set_option maxHeartbeats 4000000 in
/-- **A state of the MMA warp's code was preceded by the code's initial state.** -/
theorem mma_entered : ∀ (k : Nat) (d : Mma.D) (n : Cls → Nat),
    Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)) →
    ∃ k1 ≤ k, ∃ n1, Frame.stateAt (thread p L) X g k1 =
      some (some (minj p L g (Mma.code p L g (Mma.ent p L)).init n1)) := by
  intro k
  induction k with
  | zero =>
    intro d n h
    rw [Frame.stateAt_zero] at h
    simp [thread, glued, Code.counted, Code.glue, Code.enter, exit, Startup.code] at h
  | succ k ih =>
    intro d n h
    rcases hk : (X.tr g)[k]? with _ | e
    · have hle : (X.tr g).length ≤ k := by
        by_contra hc; rw [List.getElem?_eq_getElem (by omega)] at hk; cases hk
      rw [Frame.stateAt_of_le (by omega), ← Frame.stateAt_of_le hle] at h
      obtain ⟨k1, hk1, n1, h1⟩ := ih d n h
      exact ⟨k1, by omega, n1, h1⟩
    · have h0 := h
      rw [Frame.stateAt_succ hk] at h
      rcases hs : Frame.stateAt (thread p L) X g k with _ | _ | ⟨σ1, n'⟩
      · rw [hs] at h; cases h
      · rw [hs] at h; cases h
      rw [hs] at h
      obtain ⟨h1, -⟩ := Code.counted_next_some (C := glued p L g) h
      have fin : d = (Mma.code p L g (Mma.ent p L)).init → ∃ k1 ≤ k + 1, ∃ n1,
          Frame.stateAt (thread p L) X g k1 =
            some (some (minj p L g (Mma.code p L g (Mma.ent p L)).init n1)) := by
        rintro rfl; exact ⟨k + 1, le_refl _, n, h0⟩
      rcases σ1 with s | ⟨i, d'⟩
      · apply fin
        simp only [glued, Code.glue] at h1
        rcases hn : Startup.succ L g s e with _ | _ | s' <;> rw [hn] at h1 <;>
          simp only [Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq] at h1
        exact enter_mma h1
      · cases i with
        | mma =>
          rcases d' with s | ⟨⟨⟩, d'⟩
          · apply fin
            cases s <;> simp [glued, Code.glue, frag, Mma.M, Mma.G, Code.enter, Mma.S,
              Mma.Start.exit] at h1 <;> (try split at h1) <;> simp_all
          · obtain ⟨k1, hk1, n1, h1'⟩ := ih d' n' hs
            exact ⟨k1, by omega, n1, h1'⟩
        | _ =>
          simp only [glued, Code.glue] at h1
          obtain ⟨o, -, ho⟩ := Option.map_eq_some_iff.mp h1
          cases o <;> simp at ho

/-- **A state of the MMA warp's code at a site other than `bar1` follows the lane's
`bar.sync 2, 416`.** -/
theorem mma_bar1_before (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {k : Nat} {d : Mma.D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)))
    (hs : d.site ≠ .bar1) :
    ∃ j < k, ∃ pc, X.get (g, j) = some ⟨pc, .bar 2 (some 416) .sync⟩ := by
  obtain ⟨k1, hk1, n1, h1⟩ := mma_entered k d n hσ
  have hne : k1 ≠ k := by
    rintro rfl
    rw [hσ] at h1
    simp only [Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq] at h1
    obtain ⟨h1, -⟩ := h1
    cases h1
    exact hs rfl
  have hlt : k1 < (X.tr g).length := by
    have := (List.getElem?_eq_some_iff.mp (show (X.tr g)[k]? = _ from he)).1
    omega
  obtain ⟨e1, he1⟩ : ∃ e1, X.get (g, k1) = some e1 :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  have hev := (Mma.mfired hp hX he1 h1).1
  obtain ⟨pc, kd⟩ := e1
  simp only [Mma.Ev] at hev
  subst hev
  exact ⟨k1, by omega, pc, he1⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof
