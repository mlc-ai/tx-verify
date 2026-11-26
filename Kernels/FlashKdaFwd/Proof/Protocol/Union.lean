-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Protocol.StateBar
public import Kernels.FlashKdaFwd.Proof.Protocol.LoadRing
public import Kernels.FlashKdaFwd.Proof.Protocol.StoreRing
public import Kernels.FlashKdaFwd.Proof.Protocol.Regions
public import Lemmas.Protocol.LoadObserved

@[expose] public section

/-! # The union region: every ordered pair of access classes

The second part of the region argument of `Regions.lean`. The union region
(`InUnion`, offsets 32768 to 98304 of a CTA's shared memory) is the FP32 state buffer; its bytes
are also the three input buffers and the two output buffers.

## The classes

Its accesses fall into nine classes, each with an *epoch*. `T` is the number of tiles; tile `t`
uses load stage `s = t % 3` for the `u = t / 3`-th time and store stage `o = t % 2` for the
`u = t / 2`-th time. For each class: its accesses, then what the thread layer has to say of one
of them (its classification).

* `A0`, epoch 0: the byte writes of the 16 loads of the initial state. A load of the load
  leader that completes on the state barrier.
* `R1`, epoch 1: the generic reads of the conversion loop and of the carry loads. A thread
  access with at most 5 `bar.sync 0` before it, followed in its thread by a proxy fence that
  also has at most 5 before it (the fence 1401).
* `WL t`, epoch `2 + 2t`: the byte writes of the 70 loads of tile `t`, into input buffer `s`.
  A load of the load leader that completes on `loadFull s`, with `q` earlier ones, `q / 70 = u`.
* `WO t`, epoch `2 + 2t`: the compute threads' `stmatrix` writes of output buffer `o`. A thread
  access with `u` arrivals on `storeFull o`, `u + 1` successful polls of `storeEmpty o` and 6
  `bar.sync 0` before it; the thread's later proxy fences are `StoreFacts.out_fence` (2914,
  before its next arrival on `storeFull o`) and the fence 3774 (with 7 `bar.sync 0` before it).
* `RI t`, epoch `3 + 2t`: the compute threads' reads of input buffer `s`. A thread access with
  `u + 1` successful polls of `loadFull s` and `u` arrivals on `loadEmpty s` before it.
* `RS t`, epoch `3 + 2t`: the source reads of the store leader's 16 stores of output buffer `o`.
  A store of the store leader issued after `u + 1` successful polls of `storeFull o` and `u`
  arrivals on `storeEmpty o`; the leader's later `.read` group wait is `StoreFacts.store_wait`
  (3093, before its next arrival on `storeEmpty o`, with 6 `bar.sync 0` up to it).
* `RG t`, epoch `3 + 2t`: the store leader's generic reads of output buffer `o` (the partial
  last tile). A thread access with the same counts.
* `WF`, epoch `2 + 2T`: the compute threads' writes of the final state. A thread access with 7
  `bar.sync 0` before it, followed in its thread by a proxy fence that also has 7 before it
  (the fence 3774).
* `RF`, epoch `3 + 2T`: the source reads of the 16 final-state stores. A store of the store
  leader issued with 8 `bar.sync 0` before it.

Two accesses of one epoch do not conflict (two readers) or touch different bytes (two writers:
different loads of a tile, different compute threads; the input buffers and the output buffers
are apart, `input_output_apart`). This is part of the classification.

## The pairs

For two conflicting accesses of different epochs the earlier is visible to the later
(`modelCausality`). Earlier class, later class, lemma:

* `A0`, a thread access (`R1`, `WO`, `RI`, `RG`, `WF`): `init_before_thread`, by the thread's
  own poll of the state barrier.
* `A0`, a stage of an asynchronous operation (`WL`, `RS`, `RF`): `init_before_async`, by the
  issuer's own poll of the state barrier.
* `R1`, `WL`: `publish_of_bar` (`Fences.lean`; the fence 1401; counts `≤ 5 < 6`).
* `R1`, `WO`, `RI` or `RG`, a thread access behind a later `bar.sync 0` (`WO`, `WF`):
  `bar_before`.
* `WL t`, a thread access behind its thread's poll of `loadFull s` for the use (`RI t'` with
  `t ≤ t'`, `WF`): `load_before_thread`.
* `WL t`, `WL t'` with `t < t'` and the same stage: `load_before_load`.
* `WL t`, `RF`: `load_before_async` (a compute thread's poll, then the CTA barrier).
* `WO t`, `RS t'` with `t ≤ t'` and the same stage: `StoreFacts.publish_output`.
* `WO t`, `RG t'` with `t ≤ t'`: `output_before_leader`.
* `WO t`, `WO t'` of the same thread: `same_thread`.
* `WO`, `RF`: `publish_of_bar` (the fence 3774; `7 < 8`).
* `RI t`, `WL t'` with `t < t'` and the same stage: `LoadFacts.publish_input`.
* `RS t`, `WO t'` with `t < t'` and the same stage: `StoreFacts.release_output`.
* `RG t`, `WO t'` with `t < t'`: `leader_before_output`.
* `RS`, `WF`: `release_of_bar` (`Fences.lean`; the wait 3093; `6 < 7`).
* `WF`, `RF`: `publish_of_bar` (the fence 3774; `7 < 8`).

Every lemma takes the thread-fact structures and count premises about the two accesses; none
needs the classification of the other accesses of the region. What is not written is the
classification structure and the case split that applies these lemmas to obtain
`Frame.ItemOrder L X (InUnion L c) epoch` (then `Regions.unionOrdered`). -/

namespace PTX.Kernels.FlashKdaFwd.Protocol
open PTX PTX.Flow PTX.Frame AsyncCopy MBarrier

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {T : Nat → Nat}

/-- **Two overlapping accesses of one thread are ordered by program order.** -/
theorem same_thread {g i k : Nat} {a b : Acc} {w w' : Bool} {l : Loc}
    (hi : X.Access (g, i) a w) (hk : X.Access (g, k) b w') (hik : i < k) (ha : a.Covers l)
    (hb' : b.Covers l) : modelCausality L X l (.thread (g, i)) (.thread (g, k)) :=
  .inl (.single (.inl (po_of_overlap hi hk rfl hik ⟨l, ha, hb'⟩)))

/-- **Thread events on the two sides of a `bar.sync 0`.** In one CTA, an event with at most `q`
`bar.sync 0` up to and including it is visible to an event with more than `q` before it. -/
theorem bar_before (hB : BarFacts L X T) (hX : Consistent L K A mem0 X) (hb : L.block = 192)
    {g i h k : Nat} {l : Loc} (hsame : SameCta L g h) (hk : k < (X.tr h).length)
    (hlt : bar0UpTo X (g, i) < bar0Before X (h, k)) :
    modelCausality L X l (.thread (g, i)) (.thread (h, k)) :=
  .inl (hB.handoff0 hX hb g h i k hsame hk hlt)

section state
variable (hS : StateFacts L X) (hI : InitFacts L X) (hB : BarFacts L X T) (hN : NoEvents K X)
  (hX : Consistent L K A mem0 X) (hb : L.block = 192)
include hS hI hB hN hX hb

/-- A thread's successful poll of the state barrier observed a given load of the initial
state. -/
theorem init_observed {c : Nat} (hc : c < L.grid) {i pc al : Nat} {sp : TensorCopy.Spec}
    (hi : X.get (loadLeader L c, i) = some ⟨pc, .tensorIssue al sp⟩)
    (hm : sp.mbar = Bar.state.loc L c) {h j pcw p : Nat} {acq : Bool} {sc : MbarScope}
    (hw : X.get (h, j) = some ⟨pcw, .wait (Bar.state.loc L c) p true acq sc⟩) :
    WaitObserves X (.async (loadLeader L c, i) (.notify .load)) (h, j) (Bar.state.loc L c)
      true sc ∧ SameCta L (loadLeader L c) h := by
  have hy : loadLeader L c < L.threads := thr_lt hb hc (by decide)
  obtain ⟨-, -, hlt⟩ := hS.issue hy hi hm
  have hh := Frame.lt_of_get hX hw
  obtain ⟨hcta, -, hok⟩ := hS.poll hh hw
  have hacq := (hok rfl).1
  subst hacq
  have hp : issuesTo (Bar.state.loc L c) ⟨pc, .tensorIssue al sp⟩ = true := by
    simp [issuesTo, hm]
  have hobs : WaitObserves X (.async (loadLeader L c,
      nthEv X (issuesTo (Bar.state.loc L c)) (loadLeader L c)
        (((X.tr (loadLeader L c)).take i).countP (issuesTo (Bar.state.loc L c))))
      (.notify .load)) (h, j) (Bar.state.loc L c) true sc :=
    hS.observes_load hI hB hN hX hb hc hw ⟨_, hlt⟩
  rw [nthEv_eq hi hp] at hobs
  have hdiv : loadLeader L c / L.block = c := thr_div hb (by decide)
  exact ⟨hobs, hy, hh, hdiv.trans hcta⟩

/-- **A write of an initial-state load is visible to every later access of a thread that has
polled the state barrier** (class `A0` before `R1`, `WO`, `RI`, `RG`, `WF`). -/
theorem init_before_thread {c : Nat} (hc : c < L.grid) {i pc al : Nat} {sp : TensorCopy.Spec}
    (hi : X.get (loadLeader L c, i) = some ⟨pc, .tensorIssue al sp⟩)
    (hm : sp.mbar = Bar.state.loc L c) {h j pcw p : Nat} {acq : Bool} {sc : MbarScope}
    (hw : X.get (h, j) = some ⟨pcw, .wait (Bar.state.loc L c) p true acq sc⟩) {k : Nat}
    (hjk : j < k) (hk : k < (X.tr h).length) {x y z : Nat} {l : Loc}
    (hcov : AsyncCovers X (loadLeader L c, i) (.write (.load x y z)) l) :
    modelCausality L X l (.async (loadLeader L c, i) (.write (.load x y z)))
      (.thread (h, k)) := by
  obtain ⟨hobs, hsame⟩ := init_observed hS hI hB hN hX hb hc hi hm hw
  exact hobs.write_before_later hX hsame hcov hjk hk

/-- **A write of an initial-state load is visible to every asynchronous operation issued later
by a thread that has polled the state barrier** (class `A0` before `WL`, `RS`, `RF`). -/
theorem init_before_async {c : Nat} (hc : c < L.grid) {i pc al : Nat} {sp : TensorCopy.Spec}
    (hi : X.get (loadLeader L c, i) = some ⟨pc, .tensorIssue al sp⟩)
    (hm : sp.mbar = Bar.state.loc L c) {h j pcw p : Nat} {acq : Bool} {sc : MbarScope}
    (hw : X.get (h, j) = some ⟨pcw, .wait (Bar.state.loc L c) p true acq sc⟩) {k : Nat}
    (hjk : j < k) (hk : k < (X.tr h).length) {x y z : Nat} {l : Loc} {q : Part}
    (hcov : AsyncCovers X (loadLeader L c, i) (.write (.load x y z)) l)
    (hcov' : AsyncCovers X (h, k) q l) :
    modelCausality L X l (.async (loadLeader L c, i) (.write (.load x y z)))
      (.async (h, k) q) := by
  obtain ⟨hobs, hsame⟩ := init_observed hS hI hB hN hX hb hc hi hm hw
  exact hobs.write_before_later_async hX hsame hcov hcov' hjk hk

end state

section load
variable (hLd : LoadFacts L X) (hI : InitFacts L X) (hB : BarFacts L X T) (hN : NoEvents K X)
  (hX : Consistent L K A mem0 X) (hb : L.block = 192)
include hLd hI hB hN hX hb

/-- A compute thread's successful poll of `loadFull s` for the use of a given tile load
observed that load. -/
theorem load_observed {c : Nat} (hc : c < L.grid) (s : Fin 3) {i pc al : Nat}
    {sp : TensorCopy.Spec} (hi : X.get (loadLeader L c, i) = some ⟨pc, .tensorIssue al sp⟩)
    (hm : sp.mbar = (Bar.loadFull s).loc L c) (ga : Fin 128) {j pcw p : Nat} {acq : Bool}
    {sc : MbarScope}
    (hw : X.get (computeThread L c ga, j) =
      some ⟨pcw, .wait ((Bar.loadFull s).loc L c) p true acq sc⟩)
    (hu : okPolls ((Bar.loadFull s).loc L c) ((X.tr (computeThread L c ga)).take j) =
      ((X.tr (loadLeader L c)).take i).countP (issuesTo ((Bar.loadFull s).loc L c)) / 70) :
    WaitObserves X (.async (loadLeader L c, i) (.notify .load)) (computeThread L c ga, j)
      ((Bar.loadFull s).loc L c) true sc ∧
      SameCta L (loadLeader L c) (computeThread L c ga) := by
  have hacq := (hLd.full_poll (Frame.lt_of_get hX hw) hw).2.2.2 rfl
  subst hacq
  have hp : issuesTo ((Bar.loadFull s).loc L c) ⟨pc, .tensorIssue al sp⟩ = true := by
    simp [issuesTo, hm]
  have hobs := hLd.full_observes_copy hI hB hN hX hb hc s ga hw hu
    ⟨((X.tr (loadLeader L c)).take i).countP (issuesTo ((Bar.loadFull s).loc L c)) % 70,
      Nat.mod_lt _ (by decide)⟩
  simp only [Nat.div_add_mod] at hobs
  rw [nthEv_eq hi hp] at hobs
  exact ⟨hobs, sameCta_thr hb hc (by decide) (by have := ga.isLt; omega)⟩

/-- **A write of a tile load is visible to every access of a compute thread that has polled
`loadFull s` for the load's use** (class `WL t` before `RI t'` with `t ≤ t'`, and before
`WF`). -/
theorem load_before_thread {c : Nat} (hc : c < L.grid) (s : Fin 3) {i pc al : Nat}
    {sp : TensorCopy.Spec} (hi : X.get (loadLeader L c, i) = some ⟨pc, .tensorIssue al sp⟩)
    (hm : sp.mbar = (Bar.loadFull s).loc L c) (ga : Fin 128) {k : Nat}
    (hk : k < (X.tr (computeThread L c ga)).length)
    (hpolls : ((X.tr (loadLeader L c)).take i).countP (issuesTo ((Bar.loadFull s).loc L c)) / 70
        + 1 ≤ okPolls ((Bar.loadFull s).loc L c) ((X.tr (computeThread L c ga)).take k))
    {x y z : Nat} {l : Loc}
    (hcov : AsyncCovers X (loadLeader L c, i) (.write (.load x y z)) l) :
    modelCausality L X l (.async (loadLeader L c, i) (.write (.load x y z)))
      (.thread (computeThread L c ga, k)) := by
  obtain ⟨j, pcw, par, acq, sc, hjk, hw, hu⟩ := MbarRing.UnitHandoff.exists_poll hpolls
  obtain ⟨hobs, hsame⟩ := load_observed hLd hI hB hN hX hb hc s hi hm ga hw hu
  exact hobs.write_before_later hX hsame hcov hjk hk

/-- **A write of a tile load is visible to every asynchronous operation whose issue a compute
thread's observing poll happens before** (class `WL` before `RF`: the poll, then the CTA
barrier, then the final-state store). -/
theorem load_before_async {c : Nat} (hc : c < L.grid) (s : Fin 3) {i pc al : Nat}
    {sp : TensorCopy.Spec} (hi : X.get (loadLeader L c, i) = some ⟨pc, .tensorIssue al sp⟩)
    (hm : sp.mbar = (Bar.loadFull s).loc L c) (ga : Fin 128) {j pcw p : Nat} {acq : Bool}
    {sc : MbarScope}
    (hw : X.get (computeThread L c ga, j) =
      some ⟨pcw, .wait ((Bar.loadFull s).loc L c) p true acq sc⟩)
    (hu : okPolls ((Bar.loadFull s).loc L c) ((X.tr (computeThread L c ga)).take j) =
      ((X.tr (loadLeader L c)).take i).countP (issuesTo ((Bar.loadFull s).loc L c)) / 70)
    {e : EvId} (hsame : SameCta L (loadLeader L c) e.1)
    (hbc : baseCausality L X (computeThread L c ga, j) e) {x y z : Nat} {l : Loc} {q : Part}
    (hcov : AsyncCovers X (loadLeader L c, i) (.write (.load x y z)) l)
    (hcov' : AsyncCovers X e q l) :
    modelCausality L X l (.async (loadLeader L c, i) (.write (.load x y z))) (.async e q) := by
  obtain ⟨hobs, hsame'⟩ := load_observed hLd hI hB hN hX hb hc s hi hm ga hw hu
  exact hobs.write_before_async hX hsame' hsame hcov hcov' hbc

/-- **A write of a tile load is visible to the loads of every later use of its stage** (class
`WL t` before `WL t'`, `t < t'`, same stage; more generally to every asynchronous operation the
load leader issues after one more successful poll of `loadEmpty s` than the load's use needs).
A compute thread polled `loadFull s` for the use, then arrived on `loadEmpty s`, and the load
leader's next poll of `loadEmpty s` observed that arrival. -/
theorem load_before_load {c : Nat} (hc : c < L.grid) (s : Fin 3) {i pc al : Nat}
    {sp : TensorCopy.Spec} (hi : X.get (loadLeader L c, i) = some ⟨pc, .tensorIssue al sp⟩)
    (hm : sp.mbar = (Bar.loadFull s).loc L c) {k : Nat}
    (hk : k < (X.tr (loadLeader L c)).length)
    (hpolls : ((X.tr (loadLeader L c)).take i).countP (issuesTo ((Bar.loadFull s).loc L c)) / 70
        + 1 + 1 ≤ okPolls ((Bar.loadEmpty s).loc L c) ((X.tr (loadLeader L c)).take k))
    {x y z : Nat} {l : Loc} {q : Part}
    (hcov : AsyncCovers X (loadLeader L c, i) (.write (.load x y z)) l)
    (hcov' : AsyncCovers X (loadLeader L c, k) q l) :
    modelCausality L X l (.async (loadLeader L c, i) (.write (.load x y z)))
      (.async (loadLeader L c, k) q) := by
  have hH := hLd.empty_handoff hI hB hN hX hb hc s
  -- the load leader's poll of the empty barrier that follows the use
  obtain ⟨w0, pcw, par, acq, sc, hw0, hwget, hwq⟩ := MbarRing.UnitHandoff.exists_poll hpolls
  -- a compute thread's arrival of the use, which that poll observed
  obtain ⟨xa, hxa, hs⟩ := hH (loadLeader L c) w0 pcw par acq sc _ rfl hwget hwq
    (computeThread L c 0) ⟨0, rfl⟩
  obtain ⟨rs, ⟨tx, cnt, pcx, hxget⟩, -⟩ := id hs
  have hg := (hLd.empty_arrive (Frame.lt_of_get hX hxget) hxget).2.2.2.2.2
  rw [hxa] at hg
  -- and that thread's poll of the full barrier for the use
  obtain ⟨j, pcj, pj, acqj, scj, hjx, hjget, hjq⟩ := MbarRing.UnitHandoff.exists_poll hg
  have hje : arrivals ((Bar.loadEmpty s).loc L c) ((X.tr (computeThread L c 0)).take j) ≤
      ((X.tr (loadLeader L c)).take i).countP (issuesTo ((Bar.loadFull s).loc L c)) / 70 := by
    have := (List.take_sublist_take_left (l := X.tr (computeThread L c 0)) hjx.le).countP_le
      (p := arrivesOn ((Bar.loadEmpty s).loc L c))
    unfold arrivals at hxa ⊢
    omega
  have hbc : baseCausality L X (computeThread L c 0, j) (loadLeader L c, k) :=
    hH.baseCausality_of_counts rfl ⟨0, rfl⟩ hje hpolls hk
  have hsame : SameCta L (loadLeader L c) (loadLeader L c, k).1 :=
    sameCta_thr hb hc (s := 128) (t := 128) (by decide) (by decide)
  exact load_before_async hLd hI hB hN hX hb hc s hi hm 0 hjget hjq hsame hbc hcov hcov'

end load

section store
variable (hS : StoreFacts L X) (hI : InitFacts L X) (hB : BarFacts L X T) (hN : NoEvents K X)
  (hX : Consistent L K A mem0 X) (hb : L.block = 192)
include hS hI hB hN hX hb

/-- **A compute thread's event is visible to the store leader's events after the poll of
`storeFull o` that follows it** (class `WO t` before `RG t'`, `t ≤ t'`: the leader's generic
reads of the partial tile). -/
theorem output_before_leader {c : Nat} (hc : c < L.grid) (o : Fin 2) (ga : Fin 128)
    {i k j : Nat} {l : Loc}
    (hj : arrivals ((Bar.storeFull o).loc L c) ((X.tr (computeThread L c ga)).take i) ≤ j)
    (hk : k < (X.tr (storeLeader L c)).length)
    (hpolls : j + 1 ≤ okPolls ((Bar.storeFull o).loc L c) ((X.tr (storeLeader L c)).take k)) :
    modelCausality L X l (.thread (computeThread L c ga, i)) (.thread (storeLeader L c, k)) :=
  .inl ((hS.full_handoff hI hB hN hX hb hc o).baseCausality_of_counts ⟨0, rfl⟩ ⟨ga, rfl⟩ hj
    hpolls hk)

/-- **The store leader's event is visible to a compute thread's events after the poll of
`storeEmpty o` that follows it** (class `RG t` before `WO t'`, `t < t'`). -/
theorem leader_before_output {c : Nat} (hc : c < L.grid) (o : Fin 2) (ga : Fin 128)
    {i k j : Nat} {l : Loc}
    (hj : arrivals ((Bar.storeEmpty o).loc L c) ((X.tr (storeLeader L c)).take k) ≤ j)
    (hi : i < (X.tr (computeThread L c ga)).length)
    (hpolls : j + 1 + 1 ≤
      okPolls ((Bar.storeEmpty o).loc L c) ((X.tr (computeThread L c ga)).take i)) :
    modelCausality L X l (.thread (storeLeader L c, k)) (.thread (computeThread L c ga, i)) :=
  .inl ((hS.empty_handoff hI hB hN hX hb hc o).baseCausality_of_counts ⟨ga, rfl⟩ ⟨0, rfl⟩ hj
    hpolls hi)

end store

end PTX.Kernels.FlashKdaFwd.Protocol
