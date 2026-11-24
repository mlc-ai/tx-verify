-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.RrArrive
public import Kernels.InklingRelDecode.Proof.Interface.WvAnchor

@[expose] public section

/-!
# Thread 0's arrivals on `p_ready` at an epilogue state, and the MMA lane at `pWait`

* `arr_epi`: at an epilogue state, thread 0 of the CTA has made at least `below2 b num_iters`
  arrivals on `p_ready b` when `num_iters ≥ 1`. The epilogue follows the softmax state at the
  event that leaves the loop (`epi_back`); for thread 0 that is the arrival of the last iteration
  `num_iters - 1` (the site `bar21` leaves only for the other threads), and before it the arrivals
  are `below2 b (num_iters - 1)` (`Rr.arr_cnt`).
* `next_pWait`: the state before `pWait` is `pvBar` of the same iteration and bound, so a state at
  `pWait` other than the initial one has `1 ≤ i ≤ n` (`mma_pWait_iter`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wv
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Sm PTX.Kernels.InklingRelDecode.Proof.Sv
open PTX.Kernels.InklingRelDecode.Proof.EvW (pReady)
open PTX.Kernels.InklingRelDecode.Proof.SO (below2)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **Thread 0's arrivals at an epilogue state.** -/
theorem arr_epi (hpre : Pre Q L mem0) (hX : Consistent L kernel Interface.asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) (hlead : g % L.block = 0)
    (hn1 : 1 ≤ Q.numIters (ProA.cta L g .z) (ProA.cta L g .x)) {k : Nat}
    (hk : k ≤ (X.tr g).length) {d : Epi.D} (hσ : St Q L X g k = some (some (.d (.epi d)))) :
    ∀ b < 2, below2 b (Q.numIters (ProA.cta L g .z) (ProA.cta L g .x)) ≤
      arrivals (pReady L (g / L.block) b) ((X.tr g).take k) := by
  obtain ⟨k0, e0, d0, hk0, he0, hσ0, hl⟩ := epi_back k hk hσ
  have hge0 : X.get (g, k0) = some e0 := he0
  have hI := Sv.sm_inv_at hX hf hge0 hσ0
  have hm := ((hf.reach hg hσ0).2 : SmMeans Q L g d0.e)
  have hr25 := hm.ent.r25
  obtain ⟨-, -, hz⟩ := ProA.cta_lt hpre hg
  have hn31 := numIters_lt31 hpre hz (ProA.cta L g .x)
  have hr26 : d0.e.r26 = Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
    have h1 := hI.ok.r26
    rw [hr25] at h1
    rw [h1]
    simp only [hn31, ↓reduceIte]
  have hleave := leaveSite_of_leaves hl
  have hlast : d0.i + 1 = Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) ∧
      d0.site = .arrive := by
    rcases hleave with ⟨hs, he⟩ | ⟨j, hs, he⟩ | ⟨hs, he⟩
    · exfalso
      have := (hI.loop.2 hs).1
      omega
    · exfalso
      have := (hI.loop.1 j hs).1
      omega
    · refine ⟨by omega, ?_⟩
      rcases hs with hs | hs
      · exfalso
        unfold DComp.leaves at hl
        rw [hs] at hl
        exact hl.1 hlead
      · exact hs
  intro b hb
  have hc := (Rr.arr_cnt hpre hX hf hg hlead k0 (by omega) _ hσ0).2 d0 rfl b hb
  obtain ⟨u, hF⟩ := fired_cont hX hf hg hge0 hσ0 (by simp [ExitState])
  have ha := SO.sm_arrivesOn_p (Sm.sharedOk_of_pre hpre) (fired_sm hF) (b := b)
  have h1 := Rr.arrivals_take_succ (pReady L (g / L.block) b) he0
  have h2 : arrivals (pReady L (g / L.block) b) ((X.tr g).take (k0 + 1)) ≤
      arrivals (pReady L (g / L.block) b) ((X.tr g).take k) :=
    (List.take_sublist_take_left (by omega)).countP_le
  rw [hc, ha, hlast.2] at h1
  rw [← hlast.1, SO.below2_succ hb]
  by_cases hm : d0.i % 2 = b
  · simp [hm] at h1
    simp only [hm, ↓reduceIte]
    omega
  · simp [hm] at h1
    simp only [hm, ↓reduceIte]
    omega

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The step into `pWait` is from `pvBar` or `pWait` (a failed poll) of the same iteration and
bound. -/
theorem next_pWait {d0 d : Mma.D} {e : Event} (hn : Mma.next L g d0 e = some (some d))
    (hs : d.site = .pWait) :
    (d0.site = .pvBar ∨ d0.site = .pWait) ∧ d.i = d0.i ∧ d.n = d0.n := by
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp at hs; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)

/-- **The iteration of an MMA state at `pWait`** is between 1 and the loop bound. -/
theorem mma_pWait_iter (hX : Consistent L kernel Interface.asms mem0 X)
    (hf : ThreadFacts Q L mem0 X)
    {k : Nat} {d : Mma.D} {P : Loader.Pro} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) (hs : d.site = .pWait) :
    1 ≤ d.i ∧ d.i ≤ d.n := by
  obtain ⟨k1, e, d1, rfl, -, -, hσ1, hn⟩ := mma_pred_le hX hk hσ (by rw [hs]; nofun)
  obtain ⟨hs1, hi, hnn⟩ := next_pWait hn hs
  have hI := mma_inv_at hX hf (by omega) hσ1
  have := hI.pv (by rcases hs1 with h | h <;> rw [h] <;> trivial)
  omega

end
end PTX.Kernels.InklingRelDecode.Proof.Wv
