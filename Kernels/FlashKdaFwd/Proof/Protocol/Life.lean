-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Protocol.Union
public import Lemmas.Kernel.Safety.Lifetime
public import Lemmas.Kernel.ExitChain
public import Lemmas.Step.BulkWaitReady
public import Lemmas.Kernel.Frame
public import Lemmas.Protocol.ObjectSource
public import Lemmas.Protocol.Region

@[expose] public section

/-! # Asynchronous uses of shared memory end before the CTA exits

The rule
(`SharedLifetimeUnsafe`, one class of `Unsafe`): once every thread of a CTA has exited, each use
of the CTA's shared memory must have completed before an exit of one of its threads. A thread
instruction completes before its own thread's exit (the library's `noSharedLifetime_of_own`
does that part). The asynchronous uses of this kernel are

* the source reads of an asynchronous store (stage `.readsDone`): completed before the store
  leader's exit because the leader executes `cp.async.bulk.wait_group.read 0` after every
  `commit_group` (3093 in the tile loop, 3833 after the final-state stores); `store_finished`,
  by the library's `Step.BulkWait.stages_of_returned`, `witness_of_waitsFor` and
  `SharedFinished.of_observer_exit`;
* the byte writes and the completion notification of an asynchronous load: completed before
  the exit of a thread whose successful poll observed the load. For one of the 16 loads of the
  initial state that thread is the load leader itself, which like every thread polls the state
  barrier before it can exit. For one of the 70 loads of a tile it is a compute thread, which
  polls `loadFull s` once for each use of stage `s`. `loads_finished`, by
  `AsyncCopy.WaitObserves.notify_finished` and `AsyncCopy.load_write_finished`
  (`Lemmas/Protocol/LoadObserved.lean`).

`asyncFinished` is the case split over the kinds of asynchronous use (`SharedUse`); every other
kind needs an instruction the kernel does not have (`NoEvents`). Its conclusion has the shape of
the field `asyncFinished` of `Top.SafetyFacts`. It takes as a hypothesis that every use is of
the issuer's own CTA (the field `sharedOwn`; `Export.lean` derives it from the memory frames).

Model: `Kernels/TmlFa4Fwd/Proof/Protocol/Life/Use.lean` and `Life/Q.lean`. -/

namespace PTX.Kernels.FlashKdaFwd.Protocol
open PTX PTX.Flow PTX.Frame AsyncCopy MBarrier

/-- **Every asynchronous load of an exited CTA has completed**: each of its writes and its
notification completed before an exit of a thread of the CTA. -/
def LoadsFinished (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ i a (s : TensorCopy.Spec), X.TensorIssue i a s → CtaExited L X (i.1 / L.block) →
    (∀ x y k, (TensorTransfer.slotAt s.descriptor x y k).isSome →
      SharedFinished L K A X (.async i (.write (.load x y k))) (i.1 / L.block)) ∧
    SharedFinished L K A X (.async i (.notify .load)) (i.1 / L.block)

/-- **Thread-layer facts for the lifetime rule.** `T c` is the number of tiles of CTA `c`, as
in `BarFacts`; `uses 3 (T c) s` is the number of tiles that use load stage `s`. -/
structure LifeFacts (L : Launch) (X : Execution) (T : Nat → Nat) : Prop where
  /-- A thread that issues an asynchronous store and exits has executed, between the two, a
  `.read` bulk-group wait that covers the store. -/
  store_wait : ∀ {g k j pc a pcx : Nat} {s : TensorStore.Spec},
    X.get (g, k) = some ⟨pc, .tensorStore a s⟩ → X.get (g, j) = some ⟨pcx, .exit⟩ →
      ∃ w, k < w ∧ w < j ∧ BulkWaitsFor X .read (g, k) (g, w)
  /-- A thread that exits has polled the state barrier of its CTA successfully (384). -/
  state_polled : ∀ {g j pcx : Nat}, g < L.threads → X.get (g, j) = some ⟨pcx, .exit⟩ →
    1 ≤ okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take j)
  /-- The load leader issues at most 70 loads on `loadFull s` for each use of stage `s`. -/
  full_issues : ∀ {c : Nat} (s : Fin 3), c < L.grid →
    (X.tr (loadLeader L c)).countP (issuesTo ((Bar.loadFull s).loc L c)) ≤
      70 * uses 3 (T c) s
  /-- A compute thread that exits has polled `loadFull s` successfully once for each use of
  stage `s`. -/
  full_polled : ∀ {c j pcx : Nat} (s : Fin 3) (a : Fin 128), c < L.grid →
    X.get (computeThread L c a, j) = some ⟨pcx, .exit⟩ →
      uses 3 (T c) s ≤
        okPolls ((Bar.loadFull s).loc L c) ((X.tr (computeThread L c a)).take j)

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {T : Nat → Nat}

/-- A thread of an exited CTA ends with an exit. -/
theorem exit_of_exited {c g : Nat} (hx : CtaExited L X c) (hg : g < L.threads)
    (hc : g / L.block = c) : ∃ pc, X.get (g, (X.tr g).length - 1) = some ⟨pc, .exit⟩ := by
  obtain ⟨pc, hl⟩ := hx g hg hc
  rw [List.getLast?_eq_getElem?] at hl
  exact ⟨pc, hl⟩

namespace LifeFacts

/-- **A store's source reads complete before its thread's exit.** -/
theorem store_finished (hF : LifeFacts L X T) (hX : Consistent L K A mem0 X) {i : EvId}
    {a : Nat} {s : TensorStore.Spec} (hi : X.TensorStoreIssue i a s)
    (hx : CtaExited L X (i.1 / L.block)) :
    SharedFinished L K A X (.async i .readsDone) (i.1 / L.block) := by
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, he⟩ := hi
  have hg : g < L.threads := Frame.lt_of_get hX he
  obtain ⟨pcx, hxg⟩ := exit_of_exited hx hg rfl
  have hlen : (X.tr g).length - 1 < (X.tr g).length := (List.getElem?_eq_some_iff.mp hxg).1
  obtain ⟨w, hkw, hwl, hwait⟩ := hF.store_wait he hxg
  have hq : Part.readsDone ∈ GroupWaitStages X (g, k) (.bulk .read) := by
    simp [GroupWaitStages, he]
  have hpres : X.AsyncPresent (g, k) .readsDone :=
    Step.BulkWait.stages_of_returned hX hwait (by simp only; omega) _ hq
  obtain ⟨pcw, rem, hwt, -⟩ := id hwait
  exact SharedFinished.of_observer_exit (finish := (g, (X.tr g).length - 1)) hpres
    (Step.BulkWait.witness_of_waitsFor hwait hq hpres)
    (Resumes.of_blocking hwt (b := false) rfl ⟨rfl, hwl, hlen⟩) ⟨hg, rfl, _, hxg⟩

/-- **Every asynchronous load completes before an exit of a thread of its CTA.** A load of the
initial state was observed by the load leader's own poll of the state barrier; a load of a tile
by compute thread 0's poll of `loadFull s` for the load's use. -/
theorem loads_finished (hF : LifeFacts L X T) (hLd : LoadFacts L X) (hS : StateFacts L X)
    (hSt : StoreFacts L X) (hI : InitFacts L X) (hB : BarFacts L X T) (hN : NoEvents K X)
    (hX : Consistent L K A mem0 X) (hb : L.block = 192) : LoadsFinished L K A X := by
  rintro ⟨g, k⟩ a sp ⟨pc, he⟩ hx
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hc : g / L.block < L.grid := cta_lt hb hg
  suffices hfin : SharedFinished L K A X (.async (g, k) (.notify .load)) (g / L.block) from
    ⟨fun x y z hsl => load_write_finished hX ⟨pc, he⟩ hfin hsl, hfin⟩
  obtain ⟨b, hm, -⟩ := hI.use_ev hg he (m := sp.mbar) rfl (fun n h => by cases h)
  simp only at hx ⊢
  generalize hcc : g / L.block = c at hm hx hc ⊢
  have hspin : ∀ (w : EvId) (m : Loc) (acq : Bool) (sc : MbarScope) (pc par : Nat),
      X.get w = some ⟨pc, .wait m par true acq sc⟩ → ∃ ex, K.CanonicalSpin pc ex :=
    fun w m acq sc pc par h => hN.spins w pc m par acq sc h
  cases b with
  | loadFull s =>
    obtain ⟨rfl, -, -, -⟩ := hLd.full_issue hg he hm
    have hh := computeThread_lt hb hc 0
    obtain ⟨pcx, hexit⟩ := exit_of_exited hx hh (computeThread_div hb 0)
    have hpolled := hF.full_polled s 0 hc hexit
    have hiss := hF.full_issues s hc
    have hq : ((X.tr (loadLeader L c)).take k).countP (issuesTo ((Bar.loadFull s).loc L c)) + 1
        ≤ (X.tr (loadLeader L c)).countP (issuesTo ((Bar.loadFull s).loc L c)) := by
      have h1 := countP_take_succ (p := issuesTo ((Bar.loadFull s).loc L c)) he
        (by simp [issuesTo, hm])
      have h2 := (List.take_sublist (k + 1) (X.tr (loadLeader L c))).countP_le
        (p := issuesTo ((Bar.loadFull s).loc L c))
      omega
    obtain ⟨j, pcw, par, acq, sc, -, hw, hu⟩ := MbarRing.UnitHandoff.exists_poll
      (c := ((X.tr (loadLeader L c)).take k).countP (issuesTo ((Bar.loadFull s).loc L c)) / 70)
      (X := X) (m := (Bar.loadFull s).loc L c) (h := computeThread L c 0)
      (f := (X.tr (computeThread L c 0)).length - 1) (by omega)
    obtain ⟨hobs, -⟩ := load_observed hLd hI hB hN hX hb hc s he hm 0 hw hu
    exact hobs.notify_finished hX (hspin _ _ _ _) hh (computeThread_div hb 0) hexit
  | state =>
    obtain ⟨rfl, -, -⟩ := hS.issue hg he hm
    obtain ⟨pcx, hexit⟩ := exit_of_exited hx hg hcc
    have hpolled := hF.state_polled hg hexit
    rw [hcc] at hpolled
    obtain ⟨j, pcw, par, acq, sc, -, hw, -⟩ :=
      MbarRing.UnitHandoff.exists_poll (X := X) (c := 0) hpolled
    obtain ⟨hobs, -⟩ := init_observed hS hI hB hN hX hb hc he hm hw
    exact hobs.notify_finished hX (hspin _ _ _ _) hg hcc hexit
  | loadEmpty s => exact (hLd.no_tensor_empty he hm).elim
  | storeFull o => exact ((hSt.no_tensor he).1 hm).elim
  | storeEmpty o => exact ((hSt.no_tensor he).2 hm).elim

/-- **Every asynchronous use of a CTA's shared memory is finished once the CTA has exited.**
`hown`: every use is of the issuer's own CTA. The uses are the byte writes and the notification
of a load (`hload`) and the source reads of a store (`store_finished`); every other kind of use
needs an instruction the kernel does not have. -/
theorem asyncFinished (hF : LifeFacts L X T) (hN : NoEvents K X)
    (hX : Consistent L K A mem0 X)
    (hown : ∀ e c, SharedUse L X e c → c = e.issuer.1 / L.block)
    (hload : LoadsFinished L K A X) :
    ∀ i p c, SharedUse L X (.async i p) c → CtaExited L X c →
      SharedFinished L K A X (.async i p) c := by
  intro i p c huse hx
  obtain rfl : c = i.1 / L.block := hown _ _ huse
  have hstore : ∀ {a : Nat} {s : TensorStore.Spec}, X.TensorStoreIssue i a s →
      SharedFinished L K A X (.async i .readsDone) (i.1 / L.block) :=
    fun hi => hF.store_finished hX hi hx
  rcases huse with ⟨hpres, ⟨a, w, hint, hsp, -⟩ | ⟨addr, act, hact⟩⟩ |
      ⟨i', s, heq, -⟩ | ⟨i', address, s, x, y, k, heq, hi, hsl, -⟩ |
      ⟨i', address, s, heq, hi, -⟩ | ⟨i', q, heq, hfin, hsu⟩
  · -- a stage that accesses shared memory
    cases p with
    | mmaRead isB idx =>
      obtain ⟨-, -, hfp⟩ := hint
      rcases hfp with ⟨d, sp, acc, mask, ⟨pc, he⟩, -⟩ | ⟨c', k', cta, ⟨pc, he⟩, -⟩
      · exact (hN.tc _ _ _ he).elim
      · exact (hN.tc _ _ _ he).elim
    | readStore x y k =>
      obtain ⟨-, sp, addr, hti, -⟩ := hint
      have hf := hstore hti
      exact SharedFinished.of_stage (j := i) (q := .readsDone) hpres
        (.inr ⟨rfl, rfl, rfl, hpres, hf.1⟩) hf
    | readLoad x y k =>
      obtain ⟨-, sp, addr, -, hl, -⟩ := hint
      rw [Execution.tensor_readLoc_global hl] at hsp
      cases hsp
    | readPrefetch x y k =>
      obtain ⟨-, sp, addr, -, hl, -⟩ := hint
      rw [TensorTransfer.sourceLoc_global hl] at hsp
      cases hsp
    | readCopy =>
      obtain ⟨-, ⟨s, hcopy, -⟩ | hb⟩ := hint
      · exact (hN.copy _ _ hcopy).elim
      · exact (hN.prefetch _ _ hb).elim
    | writeStore x y k =>
      obtain ⟨-, sp, addr, -, hl, -⟩ := hint
      rw [Execution.store_writeLoc_global hl] at hsp
      cases hsp
    | oldStore x y k =>
      obtain ⟨-, sp, addr, -, -, hl, -⟩ := hint
      rw [Execution.store_writeLoc_global hl] at hsp
      cases hsp
    | writeLoad x y k =>
      obtain ⟨-, sp, addr, hti, hl, -⟩ := hint
      simp only [TensorCopy.writeLoc, Option.map_eq_some_iff] at hl
      obtain ⟨slot, hslot, -⟩ := hl
      exact (hload _ _ _ hti hx).1 x y k (by simp [hslot])
    | writeCta c' =>
      obtain ⟨-, s, tg, hcl, -⟩ := hint
      exact (hN.clc _ _ _ hcl).elim
    | writeCopy =>
      obtain ⟨-, s, hcopy, -⟩ := hint
      exact (hN.copy _ _ hcopy).elim
    | writeElem j =>
      obtain ⟨-, s, hcopy, -⟩ := hint
      exact (hN.copy _ _ hcopy).elim
    | oldElem j =>
      obtain ⟨-, s, r, hcopy, -⟩ := hint
      exact (hN.copy _ _ hcopy).elim
    | _ => exact hint.2.elim
  · -- a stage that acts on an mbarrier object
    have hsrc := objectAction_source
      (r := (⟨.async i p, act, { state := none }, none⟩ : Record Ref)) hact
    cases hsrc with
    | init hid _ _ | inval hid _ _ | arrive hid _ _ | wait hid _ _ | increment hid _ _ =>
      cases hid
    | tensor hid he _ _ =>
      cases hid
      exact (hload _ _ _ ⟨_, he⟩ hx).2
    | arriveOn _ he _ _ _ => exact (hN.asyncArrive _ _ _ ⟨_, he⟩).elim
    | bulk _ he _ _ _ => exact (hN.copy _ _ ⟨_, he⟩).elim
    | commit _ he _ _ => exact (hN.commit _ _ ⟨_, he⟩).elim
    | clc _ he _ _ _ => exact (hN.clc _ _ _ ⟨_, he⟩).elim
  · cases heq
  · -- a byte write of a load, performed or not
    cases heq
    exact (hload _ _ _ hi hx).1 x y k hsl
  · -- the source reads of a store
    cases heq
    exact hstore hi
  · -- the final stage of an operation
    cases heq
    rcases hfin with ⟨s, l, hcopy, -⟩ | ⟨s, hcopy, -⟩ | ⟨l, noinc, harr, -⟩ | ⟨-, rfl⟩ |
        ⟨s, tg, c', hcl, -⟩ | ⟨a, s, hti, rfl⟩ | ⟨a, s, -, rfl⟩ | ⟨s, rank, l, hcm, -⟩
    · exact (hN.copy _ _ hcopy).elim
    · exact (hN.copy _ _ hcopy).elim
    · exact (hN.asyncArrive _ _ _ harr).elim
    · rcases hsu with ⟨d, s, acc, mask, ⟨pc, he⟩, -⟩ | ⟨cp, ⟨pc, he⟩, -⟩
      · exact (hN.tc _ _ _ he).elim
      · exact (hN.tc _ _ _ he).elim
    · exact (hN.clc _ _ _ hcl).elim
    · exact (hload _ _ _ hti hx).2
    · exact hsu.elim
    · exact (hN.commit _ _ hcm).elim

end LifeFacts

end PTX.Kernels.FlashKdaFwd.Protocol
