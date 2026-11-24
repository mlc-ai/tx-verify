-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxScheduler
public import Kernels.TmlFa4Fwd.Proof.PrologueFenceProgress
import Kernels.TmlFa4Fwd.Proof.Thread.AllocationReadProgress
import Kernels.TmlFa4Fwd.Proof.PrologueNonzeroTrace
public import Kernels.TmlFa4Fwd.Proof.SoftmaxWarpZero

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue
open PTX.Kernels.TmlFa4Fwd.Mma (allocationEntrySites allocationGenerationZeroMember)

noncomputable section

private theorem advanceEntryPrefix {l : Launch} {X : Execution} {g i : Nat}
    {s t u : TState} {e : Event} (he : X.get (g,i) = some e)
    (hr : Run kernel Assumptions.all l g {} ((X.tr g).take i) (some s))
    (hl : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (hs : EStep kernel Assumptions.all l g t e (some u)) :
    Run kernel Assumptions.all l g {} ((X.tr g).take (i+1)) (some u) := by
  have hi : i < (X.tr g).length := len_of_get he
  rw [List.take_succ_eq_append_getElem hi, (List.getElem?_eq_some_iff.mp he).2]
  exact hr.snoc hl hs

private theorem softmaxArrival {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hSoft : warpIndex l g < 8) :
    ∃ i, (0 < warpIndex l g → i = 6) ∧ X.IsBarrier (g,i) 2 (some 416) 3103 := by
  obtain ⟨pos, u, _, e, inc, n, inst, he, hk, hPos, hu, hPrefix, hTail⟩ :=
    Thread.Register.requestReturn hp hMax hg
  have hSite : u.pc = 3103 := by
    rw [hu.1]
    simp [registerHintPc, dispatchParamPc, hSoft, show ¬ 14 ≤ warpIndex l g by omega,
      show warpIndex l g ≠ 13 by omega, show warpIndex l g ≠ 12 by omega]
  have hArr := Thread.Allocation.requireArrival hp hMax hg (by change 0 < pos + 1; omega)
    (len_of_get he) (by rw [hSite]; decide) hu.2.2.2.1 hPrefix hTail
    (Thread.Register.releasedAfterRequest hp hMax he hk)
  rw [hSite] at hArr
  exact ⟨pos+1, fun h => by rw [hPos h], hArr⟩

private theorem softmaxRendezvousReplay {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g i j : Nat} (hg : g < l.threads) (hRole : warpIndex l g < 8)
    {warp : Fin 8} {s u : TState} {o : Option TState}
    (hu : At u 3101 (dispatchOutput p l g warp))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u)
    (hPast : Run kernel Assumptions.all l g {} ((X.tr g).take i) (some s))
    (hRest : Run kernel Assumptions.all l g u ((X.tr g).drop i) o)
    (hEarly : EarlierEvents X g i 174) (hCount : beforeFirstScan X g i) (hIndex : i ≤ j)
    (hArr : X.IsBarrier (g,j) 2 (some 416) 3103) :
    ∃ t, X.IsBarrier (g,i+1) 2 (some 416) 3103 ∧ At t 3104 (schedulerEntry p l g warp) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (i+2)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (i+2)) o ∧
      beforeFirstScan X g (i+2) ∧
      (i+2 = (X.tr g).length → Step.Released l X g) := by
  have hLen : j < (X.tr g).length := len_of_get hArr
  obtain ⟨b, hBatch, hb⟩ := batchRun hp g warp u hu
  have hNext : Next kernel Assumptions.all l g u b (.setMaxReg true 184 (next b)) :=
    ⟨run_rtg hBatch, firstHint hb⟩
  obtain ⟨e0, _, hGet, ⟨inst, rfl, hRet⟩, hAfter⟩ := hNext.continuing_at_nonempty
    (by rintro _ ⟨_, _, hBad⟩; cases hBad) hRest
    (fun hNil => by have := List.drop_eq_nil_iff.mp hNil; omega)
  obtain rfl := Option.some.inj hRet
  have hPast' := advanceEntryPrefix hGet hPast (hLocal.trans hNext.steps)
    ⟨_, hNext.stop, inst, rfl, rfl⟩
  have hStrict : i < j := by
    apply Nat.lt_of_le_of_ne hIndex
    rintro rfl
    unfold Execution.IsBarrier at hArr
    rw [hGet] at hArr
    cases congrArg Event.kind (Option.some.inj hArr)
  have hOut := entryBarrier (g := g) hp.block hb.next
  have hBarNext : Next kernel Assumptions.all l g (next b) (next b)
      (.bar 2 (next (next b)) (some 416) .sync) := ⟨.refl, hOut⟩
  obtain ⟨e1, _, hBar, ⟨rfl, hRet⟩, hEnd⟩ := hBarNext.continuing_at_nonempty
    (by rintro _ ⟨_, hBad⟩; cases hBad) hAfter
    (fun hNil => by have := List.drop_eq_nil_iff.mp hNil; omega)
  obtain rfl := Option.some.inj hRet
  have hPast'' := advanceEntryPrefix hBar hPast' .refl ⟨_, hOut, rfl, rfl⟩
  have hFirst : X.IsBarrier (g,i+1) 2 (some 416) 3103 := by
    change X.get (g,i+1) = _
    rwa [hb.next.1] at hBar
  have hCount' := beforeFirstScan_advance (beforeFirstScan_advance hCount hGet rfl rfl)
    hBar rfl rfl
  refine ⟨_, hFirst, hb.next.next, hPast'', hEnd, hCount', ?_⟩
  intro hLast
  have hDone := Thread.Allocation.initialBarrierReleased hp hMax hg
  obtain ⟨k, site, hS, hObserved, hKey⟩ :=
    allocationGenerationZeroMember hp hMax.1 hg (by omega) hDone
  have hEq : k = i + 1 := by
    have hk : k < (X.tr g).length := len_of_get hObserved
    by_contra hNe
    have hLe : k ≤ i := by omega
    unfold Execution.IsBarrier at hObserved
    rcases Nat.lt_or_eq_of_le hLe with hLt | rfl
    · have hSite : site < 174 := hEarly k hLt _ hObserved
      simp [allocationEntrySites] at hS
      omega
    · rw [hGet] at hObserved
      cases congrArg Event.kind (Option.some.inj hObserved)
  subst k
  have hIdx : (X.tr g).length - 1 = i+1 := by omega
  exact NamedBar.released_of_key hMax.1.ctaBar rfl (hIdx.symm ▸ hObserved)
    (hIdx.symm ▸ hKey) hDone

/-- A softmax warp in a maximal execution reaches the first scheduler with its actual ABI
state and the initial allocation rendezvous has released. -/
theorem schedulerEntryOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hSoft : warpIndex l g < 8) :
    let warp : Fin 8 := ⟨warpIndex l g, hSoft⟩
    ∃ i t o, X.IsBarrier (g,i+1) 2 (some 416) 3103 ∧ At t 3104 (schedulerEntry p l g warp) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (i+2)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (i+2)) o ∧
      beforeFirstScan X g (i+2) ∧
      (i+2 = (X.tr g).length → Step.Released l X g) := by
  dsimp only
  obtain ⟨j, hJ, hArr⟩ := softmaxArrival hp hMax hg hSoft
  rcases Nat.eq_zero_or_pos (warpIndex l g) with hZero | hNonzero
  · obtain ⟨i, u, o, hI, hCount, hu, hRest, hEarly, a, hPast, hLocal⟩ :=
      zeroDispatchPrefixOfEvent hp hMax.1 hArr (by decide) hZero
    obtain ⟨t, hBar, ht, hPrefix, hTail, hCount, hRelease⟩ :=
      softmaxRendezvousReplay hp hMax hg hSoft hu hLocal hPast hRest hEarly hCount hI hArr
    have hWarp : (⟨warpIndex l g, hSoft⟩ : Fin 8) = 0 := Fin.ext hZero
    exact ⟨i, t, o, hBar, hWarp.symm ▸ ht, hPrefix, hTail, hCount, hRelease⟩
  · obtain rfl := hJ hNonzero
    have hLen : 6 < (X.tr g).length := len_of_get hArr
    obtain ⟨s, o, hs, _, hPast, hRest⟩ := nonzeroCommonPrefix hp hMax.1 hg hNonzero (by omega)
    let warp : Fin 8 := ⟨warpIndex l g, hSoft⟩
    have hS : At s 174 (dispatchInput p l warp) := by
      apply hs.mono
      have hRegs := hs.2.2.2.2
      refine ⟨hRegs.1, hRegs.2.1, holds_mem hRegs ?_, holds_mem hRegs ?_, holds_mem hRegs ?_,
        trivial⟩ <;> simp [nonzeroBarrierFacts, abiFacts]
    obtain ⟨u, hLocal, hu⟩ := dispatchRun hp g hg warp s hS
    obtain ⟨hFence, hCTA⟩ := nonzeroBarrierArrives hp hMax hg hNonzero
    have hPrefix : EarlierEvents X g 5 174 := by
      intro k hk e he
      interval_cases k
      · rw [firstSharedValue hp hMax.1 g hg he]
        change 25 < 174
        decide
      · rw [secondWarpValue hp hMax.1 g hg he]
        change 34 < 174
        decide
      · rw [thirdWarpValue hp hMax.1 g hg he]
        change 35 < 174
        decide
      · cases Option.some.inj (he.symm.trans hFence); decide
      · cases Option.some.inj (he.symm.trans hCTA); decide
    have hCount := beforeFirstScan_advance
      (beforeFirstScan_advance (beforeFirstScan_three hp hMax.1 hg (by omega)) hFence rfl rfl)
      hCTA rfl rfl
    obtain ⟨t, hBar, ht, hPrefix, hTail, hCount, hRelease⟩ :=
      softmaxRendezvousReplay hp hMax hg hSoft hu (run_rtg hLocal) hPast
        (hRest.after_local_nonempty (run_rtg hLocal)
          (fun hNil => by have := List.drop_eq_nil_iff.mp hNil; omega))
        hPrefix hCount (by decide) hArr
    exact ⟨5, t, o, hBar, ht, hPrefix, hTail, hCount, hRelease⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
