-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.RdSmProg
public import Kernels.InklingRelDecode.Proof.Interface.Lk5BAlign
public import Kernels.InklingRelDecode.Proof.Interface.Lk5VCount

@[expose] public section

/-!
# The site `bar20` of an iteration and the counts that order a thread's states

The rendezvous of a softmax thread's Tensor Memory access with another default thread goes
through named barrier 0 at the site `bar20` of the iteration. This file gives the thread-side
facts:

* `next_tmemSt`, `bar20_before`: the state before a state at `tmemSt` is the state at `bar20` of
  the same iteration, and its event is a `bar.sync 0, 128`;
* `sm_reaches_bar20`: in a complete execution every default thread has that state for every
  iteration below `num_iters`;
* `cnt_val`: when the decisions of every iteration agree in the CTA, the number of barrier-0
  events before a softmax state is `2 + C0 + phi site i + RD`, a function of the site, the
  iteration and the CTA (`B0N.rinv_all`); `cnt_same`: two default threads of a CTA at states of
  one site and one iteration have made the same number of barrier-0 events;
* `shfl_val`: the number of shuffles before a softmax state (`Lk.cnt_inv`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Kk
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Lk5B PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Interface.B0N
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk (DecAgree)

noncomputable section
set_option maxRecDepth 100000
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The step into `tmemSt` comes from `bar20`** of the same iteration. -/
theorem next_tmemSt {d0 d : Sm.D} {e : Event} (hn : Sm.next L g d0 e = some (some d))
    (hs : d.site = .tmemSt) : d0.site = .bar20 ∧ d.i = d0.i := by
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (have := Sv.afterSetup_site hn; rcases this with h | h <;> simp_all)
    | (have := Sv.toBar20_site hn; simp_all)
    | (simp only [Option.some.injEq] at hn; subst hn; simp [Sm.D.afterSum] at hs)

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

/-- **The state before a state at `tmemSt`** is at `bar20` of the same iteration, at a
`bar.sync 0, 128`. -/
theorem bar20_before (hg : g < L.threads) {kT : Nat} {ds : Sm.D}
    (hk : kT ≤ (X.tr g).length) (hσ : St Q L X g kT = some (some (.d (.sm ds))))
    (hs : ds.site = .tmemSt) :
    ∃ (kB : Nat) (dB : Sm.D) (pc : Nat), kT = kB + 1 ∧
      St Q L X g kB = some (some (.d (.sm dB))) ∧ dB.site = .bar20 ∧ dB.i = ds.i ∧
      X.get (g, kB) = some ⟨pc, .bar 0 (some 128) .sync⟩ := by
  rcases Sv.pred_sm hk hσ with ⟨dt, rfl⟩ | ⟨k1, d1, e1, rfl, he1, hσ1, hn1⟩
  · simp [SmEntry.d0] at hs
  obtain ⟨hs1, hi1⟩ := next_tmemSt hn1 hs
  have hge : X.get (g, k1) = some e1 := he1
  obtain ⟨u, hF⟩ := fired_cont hX hf hg hge hσ1 (by simp [ExitState])
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  have hev := Sm.shape_bar20 hb (fired_sm hF) hs1
  refine ⟨k1, d1, Sm.evPc d1.site, rfl, hσ1, hs1, hi1.symm, ?_⟩
  rw [hge, hev]

/-- **Every default thread reaches `bar20` of every iteration** in a complete execution, followed
by its state at `tmemSt` of the iteration. -/
theorem sm_reaches_bar20 (hc : Complete L X) (hg : g < L.threads) (hdef : g % L.block < 128)
    {i0 : Nat} (hi : i0 < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x)) :
    ∃ (kB : Nat) (dB ds : Sm.D) (pc : Nat), St Q L X g kB = some (some (.d (.sm dB))) ∧
      dB.site = .bar20 ∧ dB.i = i0 ∧ X.get (g, kB) = some ⟨pc, .bar 0 (some 128) .sync⟩ ∧
      St Q L X g (kB + 1) = some (some (.d (.sm ds))) ∧ ds.site = .tmemSt ∧ ds.i = i0 ∧
      kB + 1 < (X.tr g).length := by
  obtain ⟨kT, ds, pcT, aT, valsT, hσT, hsT, hiT, heT, -⟩ :=
    sm_reaches_tmemSt hpre hX hf hc hg hdef hi
  have hkT : kT < (X.tr g).length := len_of_get heT
  obtain ⟨kB, dB, pc, rfl, hσB, hsB, hiB, heB⟩ := bar20_before hpre hX hf hg hkT.le hσT hsT
  exact ⟨kB, dB, ds, pc, hσB, hsB, by omega, heB, hσT, hsT, hiT, hkT⟩

/-- **The barrier-0 count of a softmax state**, when every decision of the CTA agrees. -/
theorem cnt_val (hg : g < L.threads) (hD : ∀ j, DecAgree Q L X (g / L.block) j) {k : Nat}
    {d : Sm.D} (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some (.d (.sm d)))) :
    JS (Dc Q L X (g / L.block)) d ∧
      (cnt0 X g k : Int) = 2 + C0 Q L g + phi d.site d.i + RD (Dc Q L X (g / L.block)) d := by
  have h1 := cnt_eq hpre hX hf hg hk hσ
  obtain ⟨hJ, hv⟩ := rinv_all hpre hX hf hg (default_of hk hσ) hD k hk _ hσ
  simp only [JSx] at hJ
  simp only [Rval] at hv
  rw [hv] at h1
  simp only [dN0, p128] at h1
  refine ⟨hJ, ?_⟩
  rw [h1]
  push_cast
  ring

/-- **Two default threads of a CTA at one site and iteration have made the same number of
barrier-0 events**, when every decision of the CTA agrees. -/
theorem cnt_same {g' k k' : Nat} {d d' : Sm.D} (hg : g < L.threads) (hg' : g' < L.threads)
    (hc : g / L.block = g' / L.block) (hD : ∀ j, DecAgree Q L X (g / L.block) j)
    (hk : k ≤ (X.tr g).length) (hk' : k' ≤ (X.tr g').length)
    (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hσ' : St Q L X g' k' = some (some (.d (.sm d')))) (hs : d.site = d'.site) (hi : d.i = d'.i) :
    cnt0 X g k = cnt0 X g' k' := by
  have h1 := (cnt_val hpre hX hf hg hD hk hσ).2
  have h2 := (cnt_val hpre hX hf hg' (hc ▸ hD) hk' hσ').2
  have hq : C0 Q L g = C0 Q L g' := by
    simp only [C0, nbQ_cta (Q := Q) hc]
  have hR : RD (Dc Q L X (g / L.block)) d = RD (Dc Q L X (g' / L.block)) d' := by
    rw [← hc]
    unfold RD
    rw [hs, hi]
  rw [hs, hi, hq, hR, ← h2] at h1
  exact_mod_cast h1

/-- **The number of shuffles before a softmax state.** -/
theorem shfl_val (hg : g < L.threads) {k : Nat} {d : Sm.D} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) :
    Lk.cnt Execution.isShfl X g k = 1 + Lk.NP Q L g + Sm.smW d :=
  (Lk.cnt_inv hpre hX hf hg k hk hσ).1

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Kk
