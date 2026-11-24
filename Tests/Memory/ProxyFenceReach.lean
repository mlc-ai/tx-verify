-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness

/-!
# Litmus tests of the reach of an async proxy fence (MEM-MODEL-CAUSALITY, `ProxyFenceReach`)

A cluster of two CTAs of one thread each; `g` is a global word.

```
// CTA0, thread 0
st.global.u32 [g], 1;
fence.proxy.async.global{.sem}.scope;    // or without a scope
cp.async.bulk.shared::cta.global ...;    // async-proxy read of g in the fence's CTA
barrier.cluster.arrive;
barrier.cluster.wait;

// CTA1, thread 1
barrier.cluster.arrive;
barrier.cluster.wait;
cp.async.bulk.shared::cta.global ...;    // async-proxy read of g in the peer CTA
```

* With the scope `.cta` the fence does not reach the peer CTA's copy: the store is not ordered
  before the copy's read of `g`, so the read may return the launch content of `g` (§9.7.15.4: "The
  scope qualifier specifies the set of threads that may observe the ordering effect of this
  operation.").
* With the scope `.cta` the fence still orders the store before the copy of its own thread.
* With the scopes `.cluster` and `.gpu`, and without a scope, the cluster barrier carries the
  fence's order to the peer CTA's copy.
-/

namespace PTX.Tests.ProxyFenceReach
noncomputable section

private def L : Launch := { grid := 2, block := 1, clusterSize := 2, params := fun _ => none }
private def g : Loc := ⟨.global, 0, 0⟩
private def gA : Acc := { loc := g, size := 4 }
private def bytes1 : List Byte := (Value.bits 32 (BitVec.ofNat 64 1)).toBytes
/-- `cp.async.bulk` of `g` into the shared memory of CTA `cta`, completed on an mbarrier there. -/
private def copyOf (cta : Nat) : AsyncCopy.Spec :=
  { src := gA, dst := { loc := ⟨.shared, cta, 16⟩, size := 4 },
    completion := .mbarrier ⟨.shared, cta, 0⟩ }

private def history : List (ClusterBarrier.Record EvId) := [
  .arrival 0 0 true [(0, (0, 3))], .arrival 1 0 true [(1, (1, 0))],
  .wait 0 0 [(0, (0, 4))], .wait 1 0 [(1, (1, 1))]]

/-- The execution of the program with a fence of scope `sc` (`none`: no scope). -/
private def X (sc : Option MbarScope) : Execution := {
  tr := fun t => if t = 0 then
    [⟨0, .wr gA bytes1⟩, ⟨1, .fenceProxy (.async (some .global)) sc⟩, ⟨2, .copy (copyOf 0)⟩,
      ⟨3, .cluster (.arrive true true)⟩, ⟨4, .cluster (.wait true)⟩, ⟨5, .exit⟩]
    else if t = 1 then
      [⟨0, .cluster (.arrive true true)⟩, ⟨1, .cluster (.wait true)⟩, ⟨2, .copy (copyOf 1)⟩,
        ⟨3, .exit⟩]
    else []
  rf := fun _ _ => none
  clusters := fun c => if c = 0 then history else []
}

private def stateOf : ClusterBarrier.Outcome → ClusterBarrier.State
  | .done s => s
  | _ => {}
private def phaseOf : ClusterBarrier.Outcome → Option Nat
  | .done s => some s.phase
  | _ => none
private theorem done_of_phase {o : ClusterBarrier.Outcome} {p : Nat} (h : phaseOf o = some p) :
    o = .done (stateOf o) := by
  cases o <;> simp_all [phaseOf, stateOf]

private theorem arrival : ClusterBarrier.ArrivalOf 1 2 history (0, 3) 0 true := by
  refine ⟨0, {}, stateOf (ClusterBarrier.run 1 2 {} (history.take 1)),
    0, 0, [(0, (0, 3))], 0, rfl, rfl, by simp, rfl, ?_⟩
  exact done_of_phase (p := 0) (by decide)

private theorem waited : ClusterBarrier.WaitOf 1 2 history (1, 1) 0 := by
  let s := stateOf (ClusterBarrier.run 1 2 {} (history.take 3))
  let r : ClusterBarrier.Record EvId := .wait 1 0 [(1, (1, 1))]
  refine ⟨3, s, stateOf (r.perform 1 2 s), 1, 0, [(1, (1, 1))], 1,
    rfl, ?_, by simp, ?_, ?_⟩
  · exact done_of_phase (p := 1) (by decide)
  · rfl
  · exact done_of_phase (p := 1) (by decide)

private theorem sameCluster : SameCluster L 0 1 := by unfold SameCluster; decide

/-- The store precedes the fence in program order. -/
private theorem store_fence (sc : Option MbarScope) : baseCausality L (X sc) (0, 0) (0, 1) :=
  .single (.inl ⟨rfl, by decide, by simp [X], by simp [SameAccess, Execution.get, X, Event.acc]⟩)

/-- The fence precedes the copy of its own thread in program order. -/
private theorem fence_own (sc : Option MbarScope) : baseCausality L (X sc) (0, 1) (0, 2) :=
  .single (.inl ⟨rfl, by decide, by simp [X], by simp [SameAccess, Execution.get, X, Event.acc]⟩)

/-- The cluster barrier orders the fence before the peer CTA's copy. -/
private theorem fence_peer (sc : Option MbarScope) : baseCausality L (X sc) (0, 1) (1, 2) := by
  refine .single (.inr (.inr (.inr (.inl ⟨sameCluster, 3, 1, ?_, by simp [X], by decide,
    by decide, by simp [X]⟩))))
  exact ⟨0, arrival, waited⟩

private theorem fence_get (sc : Option MbarScope) :
    (X sc).IsProxyFence (0, 1) (.async (some .global)) sc := ⟨1, rfl⟩

/-- The only proxy fence of `X sc` is `(0, 1)`, of scope `sc`. -/
private theorem fence_only {sc sc' : Option MbarScope} {f : EvId} {sp : Option StateSpace}
    (h : (X sc).IsProxyFence f (.async sp) sc') : f = (0, 1) ∧ sc' = sc := by
  obtain ⟨t, i⟩ := f
  obtain ⟨pc, hf⟩ := h
  rcases t with _ | _ | t
  · rcases i with _ | _ | _ | _ | _ | _ | i <;> simp [Execution.get, X] at hf
    exact ⟨rfl, hf.2.2.symm⟩
  · rcases i with _ | _ | _ | _ | i <;> simp [Execution.get, X] at hf
  · simp [Execution.get, X] at hf

/-! ## The witness: a `.cta` fence does not reach the peer CTA -/

/-- With `fence.proxy.async.global.cta`, the store is not ordered before the peer CTA's copy. -/
theorem cta_not_peer : ¬ ProxyBefore L (X (some .cta)) (0, 0) (1, 2) g := by
  rintro ⟨f, sp, sc', hf, -, -, hr, -⟩
  obtain ⟨rfl, rfl⟩ := fence_only hf
  obtain ⟨-, -, -, hc⟩ := hr
  simp [L] at hc

private theorem copy_not_generic (sc : Option MbarScope) (t i : Nat) :
    ¬ GenericCopy (X sc) (t, i) := by
  rintro ⟨s, ⟨pc, h⟩, hs⟩
  rcases t with _ | _ | t
  · rcases i with _ | _ | _ | _ | _ | _ | i <;> simp [Execution.get, X] at h
    obtain ⟨-, rfl⟩ := h; simp [copyOf] at hs
  · rcases i with _ | _ | _ | _ | i <;> simp [Execution.get, X] at h
    obtain ⟨-, rfl⟩ := h; simp [copyOf] at hs
  · simp [Execution.get, X] at h

/-- Hence no access of the peer CTA's copy at `g` is ordered after the store: `NoFuture` and
`Hidden` do not force the copy to read the stored value, and its read of the launch content of `g`
is not excluded. -/
theorem cta_peer_unordered (p : AsyncCopy.Part) :
    ¬ modelCausality L (X (some .cta)) g (.thread (0, 0)) (.async (1, 2) p) := by
  rw [modelCausality_thread_async_of_not_generic L (copy_not_generic _ 1 2)]
  exact fun h => cta_not_peer h.2

/-! ## Fences that reach the copy -/

/-- A `.cta` fence orders the store before the copy of its own thread. -/
theorem cta_own : ProxyBefore L (X (some .cta)) (0, 0) (0, 2) g :=
  ⟨(0, 1), _, _, fence_get _, by decide, rfl, ⟨by unfold SameCluster; decide,
    by simp [MbarScopeIncludes, SameCta, L, Launch.threads]⟩, store_fence _, fence_own _⟩

/-- A `.cluster` fence orders the store before the peer CTA's copy. -/
theorem cluster_peer : ProxyBefore L (X (some .cluster)) (0, 0) (1, 2) g :=
  ⟨(0, 1), _, _, fence_get _, by decide, rfl, ⟨sameCluster, sameCluster⟩, store_fence _,
    fence_peer _⟩

/-- A `.gpu` fence orders the store before the peer CTA's copy. -/
theorem gpu_peer : ProxyBefore L (X (some .gpu)) (0, 0) (1, 2) g :=
  ⟨(0, 1), _, _, fence_get _, by decide, rfl, ⟨sameCluster, by decide, by decide⟩,
    store_fence _, fence_peer _⟩

/-- A fence without a scope (`fence.proxy.async.global`) orders the store before the peer CTA's
copy. -/
theorem none_peer : ProxyBefore L (X none) (0, 0) (1, 2) g :=
  ⟨(0, 1), _, _, fence_get _, by decide, rfl, sameCluster, store_fence _, fence_peer _⟩

end

end PTX.Tests.ProxyFenceReach
