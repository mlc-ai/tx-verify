-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.All
public import Kernels.InklingRelDecode.Proof.Progress.Static
public import Kernels.InklingRelDecode.Proof.Safety.Tensor
public import Kernels.InklingRelDecode.Proof.Safety.Barriers
public import Lemmas.Kernel.ExitChain
public import Lemmas.Protocol.Region
public import Lemmas.Protocol.RegionOrder
public import Lemmas.Protocol.ObjectSource
public import Lemmas.TensorStore.TensorStore

@[expose] public section

/-!
# `SharedLifetimeUnsafe`: the table of the kernel's shared uses

ERR-SHARED-LIFETIME (`Core/Assembly/SharedLifetime.lean`) asks of every use of a CTA's shared
memory (`SharedUse`) that the CTA started before a use from another CTA (`PeerSharedStarted`), and
that the use completes before an exit of the CTA once every thread of the CTA exited
(`SharedFinished`). This file proves the assembly: **every use is of the issuer's own CTA** (so
the first alternative of `SharedLifetimeUnsafe` is empty), a thread instruction of the CTA
completes before the exit of its own thread, and the uses that complete asynchronously are
finished by three premises, one per kind of operation:

* a thread access (`ld`/`st.shared`, the allocation's store), a thread's `mbarrier.init`,
  `arrive`, `try_wait`, and the issue of a `tcgen05.commit` in its CTA group: of the thread's CTA,
  complete before the thread's own exit (`SharedFinished.of_thread`);
* a tensor load, its data write (`.write (.load ..)`) and its notification (`.notify .load`):
  of the loader's CTA, `CopyFinished`;
* an MMA operand read (`.mmaRead`) and the MMA's completion (`.mmaDone`): of the MMA thread's CTA,
  `MmaFinished`;
* a commit's arrive-on (`.tcNotify r`): of the target barrier's CTA (its own), `CommitFinished`;
* a linear copy, `cp.async.mbarrier.arrive`, a CLC request, a tensor store, `tcgen05.cp`: the
  kernel issues none.

`Own` is the placement premise (a statement about the events of the threads, proved from the
thread layer in `IpLifeOwn.lean`); `CopyFinished`, `MmaFinished`, `CommitFinished` are proved in
`IpLifeMma.lean`, `IpLifeCommit.lean`, `IpLifeCopy.lean`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Life
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Safety

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Placement**: every shared use of the kernel is of its issuer's CTA. -/
structure Own (L : Launch) (X : Execution) : Prop where
  /-- Every mbarrier an instruction names is in the instruction's CTA. -/
  mbar : ∀ {e : EvId} {m : Loc}, X.UsesMbar e m → m.cta = e.1 / L.block
  /-- A thread's shared accesses are of its own CTA. -/
  access : ∀ {g k : Nat} {a : Acc} {w : Bool}, X.Access (g, k) a w → a.loc.space = .shared →
    a.loc.cta = g / L.block
  /-- A tensor load writes the shared memory of its own CTA. -/
  tensor : ∀ {i : EvId} {pc a : Nat} {sp : TensorCopy.Spec},
    X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.sharedBase.cta = i.1 / L.block
  /-- An MMA's operands are in its own CTA. -/
  mma : ∀ {i : EvId} {d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat},
    X.MmaIssue i d s acc mask → s.lowCta = i.1 / L.block ∧ s.highCta = i.1 / L.block
  /-- The CTA group of a commit is its own CTA. -/
  group : ∀ {i : EvId} {s : TcCommit.Spec} {c : Nat},
    (∃ pc, X.get i = some ⟨pc, .tc (.commit s)⟩) →
      SameCtaGroup L s.group (i.1 / L.block) c → c = i.1 / L.block

/-- A tensor load's data write completes before an exit of the destination CTA, and its
notification before an exit of the mbarrier's CTA (observed by the MMA warp's `kv_ready` waits). -/
def CopyFinished (L : Launch) (X : Execution) : Prop :=
  ∀ i a (s : TensorCopy.Spec), X.TensorIssue i a s →
    (∀ x y k, (TensorTransfer.slotAt s.descriptor x y k).isSome →
      CtaExited L X s.sharedBase.cta →
        SharedFinished L kernel asms X (.async i (.write (.load x y k))) s.sharedBase.cta) ∧
    (CtaExited L X s.mbar.cta →
      SharedFinished L kernel asms X (.async i (.notify .load)) s.mbar.cta)

/-- An MMA's completion precedes an exit of each CTA holding its operands. -/
def MmaFinished (L : Launch) (X : Execution) : Prop :=
  ∀ i d (s : TcMma.OperandSpec) acc mask (c : Nat), X.MmaIssue i d s acc mask →
    (c = s.lowCta ∨ c = s.highCta) → CtaExited L X c →
      SharedFinished L kernel asms X (.async i .mmaDone) c

/-- A commit's arrive-on completes before an exit of the target barrier's CTA. -/
def CommitFinished (L : Launch) (X : Execution) : Prop :=
  ∀ i (s : TcCommit.Spec) rank (m : Loc), X.Commit i s → TcCommit.target s rank = some m →
    CtaExited L X m.cta → SharedFinished L kernel asms X (.async i (.tcNotify rank)) m.cta

/-- A thread instruction other than an exit is finished once its own CTA exited. -/
theorem thread_finished (hX : Consistent L kernel asms mem0 X) {i : EvId} {ev : Event}
    (he : X.get i = some ev) (hne : ∀ pc, ev ≠ ⟨pc, .exit⟩) {c : Nat}
    (hc : c = i.1 / L.block) (hx : CtaExited L X c) :
    SharedFinished L kernel asms X (.thread i) c :=
  SharedFinished.of_thread hX.outside he hne hc.symm hx

/-- The record an object action describes. -/
def actionRecord (e : Ref) (act : Action) : Record Ref :=
  { id := e, action := act, reply := { state := none }, fault := none }

/-- **Every use of a CTA's shared memory is safe**: it is of the issuer's CTA, and finished once
that CTA exited. -/
theorem use_ok (hX : Consistent L kernel asms mem0 X) (own : Own L X) (hcopy : CopyFinished L X)
    (hmma : MmaFinished L X) (hcommit : CommitFinished L X) {e : Ref} {c : Nat}
    (huse : SharedUse L X e c) :
    c = e.issuer.1 / L.block ∧ (CtaExited L X c → SharedFinished L kernel asms X e c) := by
  have hu0 := huse
  rcases huse with ⟨hpres, ⟨a, w, hint, hsp, hcta⟩ | ⟨addr, act, hact⟩⟩ |
      ⟨i, s, rfl, hc, hgrp⟩ | ⟨i, address, s, x, y, k, rfl, hi, hsl, hcta⟩ |
      ⟨i, address, s, rfl, hi, hcta⟩ | ⟨i, p, rfl, hfin, hsu⟩
  · -- an access of the owner's shared memory
    rcases e with ⟨g, k⟩ | ⟨i, p⟩
    · have hown : c = g / L.block := hcta ▸ own.access hint hsp
      exact ⟨hown, fun hx => SharedFinished.of_access hX.outside hint hown.symm hx⟩
    · cases p with
      | mmaRead isB idx =>
        obtain ⟨-, -, hfp⟩ := hint
        rcases hfp with ⟨d, sp, acc, mask, hmi, hbl⟩ | ⟨c', k', cta, hcpi, -⟩
        · have hlh := TcMma.OperandSpec.byteLoc_cta hbl
          rw [hcta] at hlh
          obtain ⟨pc, hget⟩ := hmi
          obtain ⟨h1, h2⟩ := own.mma ⟨pc, hget⟩
          have hown : c = i.1 / L.block := by rcases hlh with rfl | rfl <;> assumption
          refine ⟨hown, fun hx => ?_⟩
          have hf := hmma i d sp acc mask c ⟨pc, hget⟩ hlh hx
          exact SharedFinished.of_stage (j := i) (q := .mmaDone) hpres
            (.inr ⟨rfl, rfl, rfl, hpres, hf.1⟩) hf
        · exact (Progress.no_tcCp hX _ _ hcpi).elim
      | readStore x y k =>
        obtain ⟨-, sp, addr, hti, hl, -⟩ := hint
        exact (no_tensorStore hX hti.choose_spec).elim
      | readLoad x y k =>
        obtain ⟨-, sp, addr, -, hl, -⟩ := hint
        rw [Execution.tensor_readLoc_global hl] at hsp
        cases hsp
      | readPrefetch x y k =>
        obtain ⟨-, sp, addr, -, hl, -⟩ := hint
        rw [TensorTransfer.sourceLoc_global hl] at hsp
        cases hsp
      | readCopy =>
        obtain ⟨-, ⟨s, ⟨pc, hget⟩, -⟩ | ⟨pc, hget⟩⟩ := hint
        · exact (no_copy hX hget).elim
        · exact (Progress.no_bulkPrefetch hX hget).elim
      | writeStore x y k =>
        obtain ⟨-, sp, addr, hti, hl, -⟩ := hint
        exact (no_tensorStore hX hti.choose_spec).elim
      | oldStore x y k =>
        obtain ⟨-, sp, addr, hti, -, hl, -⟩ := hint
        exact (no_tensorStore hX hti.choose_spec).elim
      | writeLoad x y k =>
        obtain ⟨-, sp, addr, hti, hl, -⟩ := hint
        obtain ⟨pc, hget⟩ := hti
        simp only [TensorCopy.writeLoc, Option.map_eq_some_iff] at hl
        obtain ⟨slot, hslot, hl⟩ := hl
        have hloc : (sp.sharedLoc slot).cta = sp.sharedBase.cta := rfl
        have hb : sp.sharedBase.cta = i.1 / L.block := own.tensor hget
        have hown : c = i.1 / L.block := by rw [← hcta, ← hl, hloc, hb]
        refine ⟨hown, fun hx => ?_⟩
        have hbc : sp.sharedBase.cta = c := by rw [hb, hown]
        rw [← hbc] at hx ⊢
        exact (hcopy _ _ _ ⟨pc, hget⟩).1 x y k (by simp [hslot]) hx
      | writeCta c' =>
        obtain ⟨-, s, tg, ⟨pc, hget⟩, -⟩ := hint
        exact (no_clc hX hget).elim
      | writeCopy =>
        obtain ⟨-, s, ⟨pc, hget⟩, -⟩ := hint
        exact (no_copy hX hget).elim
      | writeElem j =>
        obtain ⟨-, s, ⟨pc, hget⟩, -⟩ := hint
        exact (no_copy hX hget).elim
      | oldElem j =>
        obtain ⟨-, s, r, ⟨pc, hget⟩, -⟩ := hint
        exact (no_copy hX hget).elim
      | _ => exact hint.2.elim
  · -- an action on a barrier of the owner
    have hsrc := objectAction_source (r := actionRecord e act) hact
    simp only [actionRecord] at hsrc
    cases hsrc with
    | @init g j pc n hid he ha' =>
      subst hid
      have hown : c = g / L.block := own.mbar (Execution.UsesMbar.of_init ⟨pc, he⟩)
      exact ⟨hown, fun hx => thread_finished hX he (fun _ h => by cases h) hown hx⟩
    | inval hid he _ => exact (no_inval hX he).elim
    | @arrive g j pc tx n rel sc hid he ha' =>
      subst hid
      have hown : c = g / L.block := own.mbar (.inl ⟨tx, n, rel, sc, pc, he⟩)
      exact ⟨hown, fun hx => thread_finished hX he (fun _ h => by cases h) hown hx⟩
    | @wait g j pc q ok acq sc hid he ha' =>
      subst hid
      have hown : c = g / L.block :=
        own.mbar (.inr (.inr (.inr (.inr (.inl ⟨pc, q, ok, acq, sc, he⟩)))))
      exact ⟨hown, fun hx => thread_finished hX he (fun _ h => by cases h) hown hx⟩
    | @tensor i pc a sp hid he hm ha' =>
      subst hid
      have hown : c = i.1 / L.block := by
        have := own.mbar (Execution.UsesMbar.of_tensor (X := X) ⟨pc, he⟩)
        rw [hm] at this
        exact this
      refine ⟨hown, fun hx => ?_⟩
      have hcm : sp.mbar.cta = c := by rw [hm]
      rw [← hcm] at hx ⊢
      exact (hcopy _ _ _ ⟨pc, he⟩).2 hx
    | increment hid he _ => exact (no_asyncArrive hX he).elim
    | arriveOn hid he _ _ _ => exact (no_asyncArrive hX he).elim
    | bulk hid he _ _ _ => exact (no_copy hX he).elim
    | @commit i pc sp rank hid he htg ha' =>
      subst hid
      have hown : c = i.1 / L.block :=
        own.mbar (.inr (.inr (.inr (.inl ⟨sp, rank, ⟨pc, he⟩, htg⟩))))
      refine ⟨hown, fun hx => ?_⟩
      exact hcommit i sp rank _ ⟨pc, he⟩ htg hx
    | clc hid he _ _ _ => exact (no_clc hX he).elim
  · -- a commit's issue, in each CTA of its group
    obtain ⟨pc, he⟩ := hc
    have hown : c = i.1 / L.block := own.group ⟨pc, he⟩ hgrp
    exact ⟨hown, fun hx => thread_finished hX he (fun _ h => by cases h) hown hx⟩
  · -- a tensor load's write, in its loader's CTA
    obtain ⟨pc, he⟩ := hi
    have hown : c = i.1 / L.block := by rw [← hcta]; exact own.tensor he
    refine ⟨hown, fun hx => ?_⟩
    rw [← hcta] at hx ⊢
    exact (hcopy _ _ _ ⟨pc, he⟩).1 x y k hsl hx
  · -- a tensor store's source reads
    obtain ⟨pc, he⟩ := hi
    exact (no_tensorStore hX he).elim
  · -- the final stage of an operation
    rcases hfin with ⟨s, m, ⟨pc, hget⟩, -, rfl⟩ | ⟨s, ⟨pc, hget⟩, -, rfl⟩ |
        ⟨m, noinc, ⟨pc, hget⟩, rfl⟩ | ⟨-, rfl⟩ |
        ⟨s, tg, c', ⟨pc, hget⟩, -, rfl⟩ | ⟨a, s, -, rfl⟩ | ⟨a, s, -, rfl⟩ |
        ⟨s, rank, m, -, -, rfl⟩
    · exact (no_copy hX hget).elim
    · exact (no_copy hX hget).elim
    · exact (no_asyncArrive hX hget).elim
    · -- an MMA's completion, in each CTA of its operands
      rcases hsu with ⟨d, s, acc, mask, ⟨pc, he⟩, hlh⟩ | ⟨cp, hcpi, -⟩
      · obtain ⟨h1, h2⟩ := own.mma ⟨pc, he⟩
        have hown : c = i.1 / L.block := by rcases hlh with rfl | rfl <;> assumption
        exact ⟨hown, fun hx => hmma i d s acc mask c ⟨pc, he⟩ hlh hx⟩
      · exact (Progress.no_tcCp hX _ _ hcpi).elim
    · exact (no_clc hX hget).elim
    · -- a tensor load's completion, in the mbarrier's CTA
      obtain ⟨address, s, ⟨pc, he⟩, -, hcta⟩ := hsu
      have hown : c = i.1 / L.block := by
        rw [← hcta]
        exact own.mbar (Execution.UsesMbar.of_tensor (X := X) ⟨pc, he⟩)
      refine ⟨hown, fun hx => ?_⟩
      rw [← hcta] at hx ⊢
      exact (hcopy _ _ _ ⟨pc, he⟩).2 hx
    · exact hsu.elim
    · -- a commit's arrive-on, at its target's CTA
      obtain ⟨s, m, ⟨pc, he⟩, htg, hcta⟩ := hsu
      have hown : c = i.1 / L.block := by
        rw [← hcta]
        exact own.mbar (.inr (.inr (.inr (.inl ⟨s, rank, ⟨pc, he⟩, htg⟩))))
      refine ⟨hown, fun hx => ?_⟩
      rw [← hcta] at hx ⊢
      exact hcommit i s rank m ⟨pc, he⟩ htg hx

/-- **No use of a CTA's shared memory is unsafe** (`Safety.Protocol.lifetime`). -/
theorem no_sharedLifetimeUnsafe (hX : Consistent L kernel asms mem0 X) (own : Own L X)
    (hcopy : CopyFinished L X) (hmma : MmaFinished L X) (hcommit : CommitFinished L X) :
    ¬ SharedLifetimeUnsafe L kernel asms X := by
  rintro ⟨e, owner, huse, ⟨h1, h2⟩ | ⟨h3, h4⟩⟩
  · exact h1 (use_ok hX own hcopy hmma hcommit huse).1
  · exact h4 ((use_ok hX own hcopy hmma hcommit huse).2 h3)

end
end PTX.Kernels.InklingRelDecode.Proof.Life
