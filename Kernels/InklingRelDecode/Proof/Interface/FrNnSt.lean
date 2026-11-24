-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk3Exch
public import Kernels.InklingRelDecode.Proof.Interface.Lk5VChain
public import Kernels.InklingRelDecode.Proof.Interface.Lk3Upd
public import Kernels.InklingRelDecode.Proof.Thread.FrExit

@[expose] public section

/-!
# The numbers of the running maximum and sum at every softmax state

`Sm.NnInv` (the running sum is a number at least `0`, the running maximum reads as an extended real
that is not `+inf`, `alpha` and the row sum are numbers at least `0`) holds at every softmax state
of a thread: by induction along the trace from the region's first state, with the step
`Sm.nnInv_next`. Its one premise on another lane, that the sum of probabilities received at
`shfl6` is non-negative, is the partner's own sum: the source lane of the shuffle is at the same
site and iteration (`sm_shfl_peer_d`), and every probability of a lane is non-negative
(`Sm.PfNn`, by its own induction).

`exit_noFault`: the bridge to the epilogue (`DComp.exitNext`) does not fault at any softmax state
of a launched thread. No premise on the scores, the scale (positive: `Ent.Ok.scalePos`) or the
launch beyond `Pre` and `ThreadFacts`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Sm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The invariant of a softmax state before an event. -/
theorem smInv_ev (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X) {x j : Nat}
    {d : Sm.D} {e : Event} (he : X.get (x, j) = some e)
    (hσ : St Q L X x j = some (some (.d (.sm d)))) : Sm.Inv L x d := by
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
  exact hinv.2

/-- **The probabilities of a softmax state are non-negative.** -/
theorem pfNn_at {k : Nat} {d : Sm.D} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) : PfNn d := by
  induction k using Nat.strong_induction_on generalizing d with
  | _ k ih =>
    rcases Sv.pred_sm hk hσ with ⟨dt, rfl⟩ | ⟨k0, d0, e, rfl, he, hσ0, hn⟩
    · intro j
      exact le_rfl
    · exact pfNn_next (ih k0 (by omega) (by omega) hσ0) hn

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

/-- **The word received at the exchange of the half sums is the partner's sum of probabilities**,
a non-negative `.f32` number: the source lane is at the same site and iteration
(`sm_shfl_peer_d`) and its probabilities are non-negative (`pfNn_at`). -/
theorem shfl6_recv (hre : SmReal Q L X) (hg : g < L.threads) {k : Nat} {d : Sm.D} {e : Event}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hs6 : d.site = .shfl6) {md : ShflMode} {a : Value} {b c : Nat} {recv : Value} {ok : Bool}
    (hk6 : e.kind = .shfl md a b c recv ok) : ∃ y : ℝ, recv = .float .f32 y ∧ 0 ≤ y := by
  obtain ⟨recv', ok', x, j, d2, he', -, -, hσ2, -, -, hrecv, -, hj, r2, o2, he2⟩ :=
    sm_shfl_peer_d hpre hX hf hpre.block (fld := fun d => d.stg.sw) (k := 16)
      (by rw [hs6]; exact shflShape_6 L) hg he hσ
  rw [he'] at hk6
  simp only [Kind.shfl.injEq] at hk6
  obtain ⟨-, -, -, -, hr, -⟩ := hk6
  have hsw := ((smInv_ev hX hf he2 hσ2).re (hre hσ2)).sw
  exact ⟨d2.sumP, by rw [← hr, hrecv]; exact hsw, sumP_nonneg (pfNn_at hj hσ2)⟩

/-- **The numbers of a softmax state**: the running sum and maximum, `alpha` and the row sum. -/
theorem nnInv_at (hre : SmReal Q L X) (hg : g < L.threads) {k : Nat} {d : Sm.D}
    (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some (.d (.sm d)))) : NnInv d := by
  induction k using Nat.strong_induction_on generalizing d with
  | _ k ih =>
    rcases Sv.pred_sm hk hσ with ⟨dt, rfl⟩ | ⟨k0, d0, e, rfl, he, hσ0, hn⟩
    · exact nnInv_init _
    · refine nnInv_next (ih k0 (by omega) (by omega) hσ0) (pfNn_at (by omega) hσ0)
        (fun _ => ((smInv_ev hX hf he hσ0).re (hre hσ0)).sw) ?_ hn (hre hσ)
      intro md a b c recv ok hs6 hk6
      exact shfl6_recv hpre hX hf hre hg he hσ0 hs6 hk6

/-- **The numbers of a softmax state**, at any event index. -/
theorem nnInv_state (hre : SmReal Q L X) (hg : g < L.threads) {k : Nat} {d : Sm.D}
    (hσ : St Q L X g k = some (some (.d (.sm d)))) : NnInv d := by
  by_cases hk : k ≤ (X.tr g).length
  · exact nnInv_at hpre hX hf hre hg hk hσ
  · have h1 : Frame.stateAt (code L Q) X g k =
        Frame.stateAt (code L Q) X g (X.tr g).length :=
      Frame.stateAt_of_le (by omega)
    have h2 : St Q L X g (X.tr g).length = some (some (.d (.sm d))) := h1.symm.trans hσ
    exact nnInv_at hpre hX hf hre hg le_rfl h2

/-- **The loop's exit does not fault** at a softmax state of a launched thread. -/
theorem exit_noFault (hre : SmReal Q L X) (hg : g < L.threads) {k : Nat} {d : Sm.D} {e : Event}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d (.sm d)))) :
    (DComp.exitIn L g d).NoFault := by
  have hI : Sm.Inv L g d := by
    obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
    exact hinv.2
  exact DComp.exitIn_noFault hI (nnInv_state hpre hX hf hre hg hσ)

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
