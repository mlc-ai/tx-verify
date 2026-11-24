-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution

/-! # Coverage of the shared-memory lifetime rule

ERR-SHARED-LIFETIME (`Core/Assembly/SharedLifetime.lean`) states PTX §2.2.2 / §5.1.7 once, for
every use of a CTA's shared memory (`SharedUse`). This file states the per-kind formulations of
the same requirement, one per instruction kind (prefix `Kind`), and proves that every execution
a per-kind formulation judges unsafe is judged unsafe by the current Core: by the remaining
kind-specific check (`TmaUnsafe`, `ClcUnsafe`, `TensorUnsafe`, `TensorStoreUnsafe`,
`TcMma.InstructionUnsafe`, `TcCommitUnsafe`), by the checks that now state a former kind-specific
part once (`MbarUninit`, `Unalloc`, `AlignedMismatch`) or by `SharedLifetimeUnsafe`.

The per-kind formulations, in brief:

* `KindPeerUnsafe`: a use of another CTA's shared memory (thread access, planned or performed
  asynchronous footprint, mbarrier action, tensor-load notification, commit arrival) without a
  start witness, or not completed before an owner exit (`KindPeerSharedFinished`, which does
  not require that the use occurred);
* `KindPendingAtExit` (in `KindTmaUnsafe`): a linear bulk copy whose notification is missing
  when its issuer's CTA has exited;
* `KindClcUnsafe`, `KindTensorUnsafe`, `KindTensorStoreUnsafe`, `KindInstructionUnsafe`
  (`KindPeerAlive`, `KindCopySafe`), `KindTcCommitUnsafe`: the completing stage of a CLC
  response, tensor load, tensor store, MMA / `tcgen05.cp` and commit must have occurred and
  precede an exit of each exited CTA it uses; the commit issue needs every peer of its CTA group
  started and, if exited, exited after the issue.

Side hypotheses are stated where a per-kind formulation names a location whose space or CTA the
current table takes from the issue rule; each one is documented at its theorem.
-/

namespace PTX.Tests.SharedLifetimeCoverage
noncomputable section

/-! ## Per-kind formulations -/

def KindPeerSharedUse (L : Launch) (X : Execution) (e : AsyncCopy.Ref) (owner : Nat) : Prop :=
  owner ≠ e.issuer.1 / L.block ∧
  ((∃ a write, X.Intent e a write ∧ a.loc.space = .shared ∧ a.loc.cta = owner) ∨
   (∃ addr action, AsyncCopy.objectAction X X.async ⟨.shared, owner, addr⟩ e = some action) ∨
   (∃ i address s, e = .async i (.notify .load) ∧ X.TensorIssue i address s ∧
     s.mbar.space = .shared ∧ s.mbar.cta = owner) ∨
   ∃ i s rank m, e = .async i (.tcNotify rank) ∧ X.Commit i s ∧
     TcCommit.target s rank = some m ∧ m.cta = owner)

/-- The actual effect completes before an owner's exit, not merely before issuer exit. -/
def KindPeerSharedFinished (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution)
    (e : AsyncCopy.Ref) (owner : Nat) : Prop :=
  ∃ finish pc, finish.1 < L.threads ∧ finish.1 / L.block = owner ∧
    X.get finish = some ⟨pc, .exit⟩ ∧ CompletedBefore L K A X e (.thread finish, false)

def KindPeerUnsafe (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∃ e owner, KindPeerSharedUse L X e owner ∧
    (¬ PeerSharedStarted L K A X e owner ∨
      (CtaExited L X owner ∧ ¬ KindPeerSharedFinished L K A X e owner))

/-- A bulk copy (`cp.async.bulk`, `cp.reduce.async.bulk`): a linear operation of the async proxy
completed on mbarrier `m`. -/
def KindBulk (X : Execution) (i : EvId) (s : AsyncCopy.Spec) (m : Loc) : Prop :=
  X.Copy i s ∧ s.completion = .mbarrier m ∧ s.generic = false

def KindPendingAtExit (L : Launch) (X : Execution) : Prop :=
  ∃ c,
    (∀ g < L.threads, g / L.block = c → ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩) ∧
    ∃ i s m, KindBulk X i s m ∧ i.1 / L.block = c ∧
      (X.async.copies i).notified = false

/-- The `.aligned` part of the former TMA check, frozen as it was stated before
ERR-ALIGNED-MISMATCH: two lanes of a warp disagree on the source position or the static operands
of their `k`-th warp-collective `tcgen05` instruction, or a lane exits with at most `k` of them
while another lane of its warp executes its `k`-th. -/
def KindTcUnsafe (L : Launch) (X : Execution) : Prop :=
  (∃ e f k pc pc' ke kf, SameWarp L e.1 f.1 ∧ X.TcK e k ∧ X.TcK f k ∧
    X.get e = some ⟨pc, .tc ke⟩ ∧ X.get f = some ⟨pc', .tc kf⟩ ∧
    (pc ≠ pc' ∨ tcStatic ke ≠ tcStatic kf)) ∨
  (∃ e f k, SameWarp L e.1 f.1 ∧ X.TcK e k ∧ X.ExitedShort isTcColl f k)

def KindTmaUnsafe (L : Launch) (mem0 : Mem0) (X : Execution) : Prop :=
  (∃ m r, r ∈ X.objects m ∧ r.fault.isSome) ∨
  (∃ m r, r ∈ X.objects m ∧ ¬ ObjectPublished L X m r) ∨
  (∃ b s m, KindBulk X b s m ∧
    ¬ ∃ i c, X.MbInit i m c ∧ InitPublished L X i b m) ∨
  (∃ e a w i m c l, X.Intent e a w ∧ X.MbInit i m c ∧ a.Covers l ∧
    Acc.Covers { loc := m, size := 8 } l ∧ ¬ modelCausality L X l e (.thread i) ∧
    ¬ ∃ v, X.MbInval v m ∧ MBarrier.InitBefore (X.objects m) (.thread i) (.thread v) ∧
      modelCausality L X l (.thread v) e) ∨
  (∃ e m l, (X.UsesMbar e m ∨ ∃ c, X.MbInit e m c) ∧ Acc.Covers { loc := m, size := 8 } l ∧ mem0 l =
    none) ∨
  KindPendingAtExit L X ∨ KindTcUnsafe L X

def KindClcUnsafe (L : Launch) (K : Kernel) (A : List Assumption) (mem0 : Mem0) (X : Execution) :
    Prop :=
  (∃ i s targets q pc r, X.ClcIssue i s targets ∧
    X.get q = some ⟨pc, .clcQuery .isCanceled r⟩ ∧ r.firstCta = none ∧
    SameCta L i.1 q.1 ∧ ¬ baseCausality L X i q) ∨
  (∃ i s targets c l, X.ClcIssue i s targets ∧ c ∈ targets ∧
    ({ loc := { s.mbar with cta := c }, size := 8 } : Acc).Covers l ∧ mem0 l = none) ∨
  (∃ i s targets c, X.ClcIssue i s targets ∧ c ∈ targets ∧
    ¬ ∃ init count, X.MbInit init { s.mbar with cta := c } count ∧
      InitPublished L X init i { s.mbar with cta := c }) ∨
  (∃ i s targets c, X.ClcIssue i s targets ∧ c ∈ targets ∧ CtaExited L X c ∧
    ¬ (c ∈ (X.clc i).notified ∧
      KindPeerSharedFinished L K A X (.async i (.notify (.cta c))) c))

def KindTensorUnsafe (L : Launch) (K : Kernel) (A : List Assumption) (mem0 : Mem0) (X : Execution) :
    Prop :=
  (∃ i address s l, X.TensorIssue i address s ∧
    ({ loc := s.mbar, size := 8 } : Acc).Covers l ∧ mem0 l = none) ∨
  (∃ i address s, X.TensorIssue i address s ∧
    ¬ ∃ init count, X.MbInit init s.mbar count ∧ InitPublished L X init i s.mbar) ∨
  (∃ i observation slot content, X.tensor i = some observation ∧
    observation.effects.write slot = some content ∧ content.byte = none) ∨
  (∃ i address s, X.TensorIssue i address s ∧ CtaExited L X s.sharedBase.cta ∧
    ¬ ∃ observation, X.tensor i = some observation ∧ observation.spec = s ∧
      ∀ slot : TensorTransfer.Slot s.descriptor,
        X.AsyncPresent i (.write (.load slot.1.val slot.2.1.val slot.2.2.val)) ∧
        KindPeerSharedFinished L K A X
          (.async i (.write (.load slot.1.val slot.2.1.val slot.2.2.val))) s.sharedBase.cta) ∨
  (∃ i address s, X.TensorIssue i address s ∧ CtaExited L X s.mbar.cta ∧
    ¬ (X.AsyncPresent i (.notify .load) ∧
      KindPeerSharedFinished L K A X (.async i (.notify .load)) s.mbar.cta))

def KindTensorStoreUnsafe (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  (∃ i address s, X.TensorStoreIssue i address s ∧ CtaExited L X s.sharedBase.cta ∧
    ¬ (X.AsyncPresent i .readsDone ∧
      KindPeerSharedFinished L K A X (.async i .readsDone) s.sharedBase.cta)) ∨
  TensorStore.ReduceNoRule A X

def KindPeerAlive (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) (i : EvId)
    (s : TcMma.OperandSpec) : Prop :=
  ∀ owner, owner = s.lowCta ∨ owner = s.highCta →
    (owner ≠ i.1 / L.block → PeerSharedStarted L K A X (.async i .mmaDone) owner) ∧
    (CtaExited L X owner →
      X.async.mmaDone i = true ∧ KindPeerSharedFinished L K A X (.async i .mmaDone) owner)

/-- A copy reads only represented, encoded shared locations of a live CTA. -/
def KindCopySafe (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) (i : EvId)
    (c : TcCopy.Spec) : Prop :=
  TcMma.CopySafe c ∧ ∀ cta ∈ c.ctas, CtaExited L X cta →
    X.async.mmaDone i = true ∧ KindPeerSharedFinished L K A X (.async i .mmaDone) cta

def KindInstructionSafe (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  (∀ i d s accum mask, X.MmaIssue i d s accum mask →
    TcMma.IssueShape L i d s mask ∧ KindPeerAlive L K A X i s ∧ TcMma.CompletedValues L A X i) ∧
  (∀ i c, X.CpIssue i c → KindCopySafe L K A X i c) ∧ TcMma.CollectorSafe X

def KindInstructionUnsafe (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ¬ KindInstructionSafe L K A X

def KindTcCommitTargetSafe (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution)
    (issue : EvId) (rank : Fin 16) (m : Loc) : Prop :=
  (∃ init count, X.MbInit init m count ∧ InitPublished L X init issue m) ∧
  (CtaExited L X m.cta → rank ∈ X.tcNotified issue ∧
    KindPeerSharedFinished L K A X (.async issue (.tcNotify rank)) m.cta)

/-- The issuing CTA group is independent of the target set: even an empty mask or a
mask targeting another group must satisfy the cta_group issue granularity. The CTA group of the
issuing CTA exists in its cluster (`Launch.ctaGroup`, which `Launch.ctaGroup_ne_none_iff` states
as the rank bound `(rank / size + 1) * size ≤ clusterSize` on a well-formed launch). -/
def KindTcCommitIssueSafe (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution)
    (issue : EvId) (s : TcCommit.Spec) : Prop :=
  issue.1 < L.threads ∧ TcCommit.resolve L s.group (issue.1 / L.block) s.mbar s.mask = some s ∧
    L.ctaGroup (issue.1 / L.block) s.group ≠ none ∧
    ∀ peer, SameCtaGroup L s.group (issue.1 / L.block) peer → peer ≠ issue.1 / L.block →
      PeerSharedStarted L K A X (.thread issue) peer ∧
      (CtaExited L X peer → KindPeerSharedFinished L K A X (.thread issue) peer)

def KindTcCommitUnsafe (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  (∃ i s rank m, X.Commit i s ∧ TcCommit.target s rank = some m ∧
    ¬ KindTcCommitTargetSafe L K A X i rank m) ∨
  (∃ i s, X.Commit i s ∧ ¬ KindTcCommitIssueSafe L K A X i s)

/-! ## Helper facts -/

variable {L : Launch} {K : Kernel} {A : List Assumption} {X : Execution}

/-- `SharedFinished` contains the per-kind completion order. -/
theorem kindFinished_of_finished {e : AsyncCopy.Ref} {owner : Nat}
    (h : SharedFinished L K A X e owner) : KindPeerSharedFinished L K A X e owner :=
  h.2

/-- In an execution the rule accepts, every use of a CTA other than the issuer's has a start
witness, and every use of an exited CTA is finished. -/
theorem not_unsafe_use (hu : ¬ SharedLifetimeUnsafe L K A X) {e : AsyncCopy.Ref} {owner : Nat}
    (h : SharedUse L X e owner) :
    (owner ≠ e.issuer.1 / L.block → PeerSharedStarted L K A X e owner) ∧
    (CtaExited L X owner → SharedFinished L K A X e owner) := by
  constructor
  · intro hne
    by_contra hs
    exact hu ⟨e, owner, h, .inl ⟨hne, hs⟩⟩
  · intro hx
    by_contra hf
    exact hu ⟨e, owner, h, .inr ⟨hx, hf⟩⟩

/-- The start witness depends on the issuing instruction only. -/
theorem started_of_issuer {e e' : AsyncCopy.Ref} {owner : Nat} (hi : e'.issuer = e.issuer)
    (h : PeerSharedStarted L K A X e' owner) : PeerSharedStarted L K A X e owner := by
  unfold PeerSharedStarted at h ⊢
  rw [← hi]
  exact h

theorem slotAt_self {outer : Nat} {d : TensorDescriptor.Descriptor outer}
    (slot : TensorTransfer.Slot d) :
    TensorTransfer.slotAt d slot.1.val slot.2.1.val slot.2.2.val = some slot := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨k, hk⟩⟩ := slot
  simp [TensorTransfer.slotAt, hx, hy, hk]

theorem tensorIssue_spec {i : EvId} {a a' : Nat} {s s' : TensorCopy.Spec}
    (h : X.TensorIssue i a s) (h' : X.TensorIssue i a' s') : s = s' := by
  obtain ⟨pc, h⟩ := h
  obtain ⟨pc', h'⟩ := h'
  rw [h] at h'
  simp at h'
  exact h'.2.2

/-- An MMA operand byte is in the shared memory of the low or the high CTA. -/
theorem mma_byteLoc_cta {s : TcMma.OperandSpec} {op : TcMma.Operand} {index : Nat} {l : Loc}
    (h : s.byteLoc op index = some l) : l.cta = s.lowCta ∨ l.cta = s.highCta := by
  unfold TcMma.OperandSpec.byteLoc at h
  simp only [bind, Option.bind] at h
  split_ifs at h
  all_goals
    split at h
    · cases h
    · simp only [pure, Option.some.injEq] at h
      subst h
      simp

/-- A `tcgen05.cp` source byte is in the shared memory of the copy's CTA. -/
theorem copy_byteLoc_cta {shape : TcCpShape} {src : TcShared.Descriptor} {cta index : Nat}
    {l : Loc} (h : TcCopy.byteLoc shape src cta index = some l) : l.cta = cta := by
  unfold TcCopy.byteLoc at h
  split_ifs at h
  cases hb : TcShared.byteAddress 1 .k src (index / shape.rowBytes) (index % shape.rowBytes) 0 <;>
    simp [hb] at h
  subst h
  rfl

/-- A tensor load writes the shared memory of its destination CTA, at a selected slot. -/
theorem load_writeLoc {s : TensorCopy.Spec} {x y k : Nat} {l : Loc}
    (h : TensorCopy.writeLoc s x y k = some l) :
    (TensorTransfer.slotAt s.descriptor x y k).isSome ∧ l.cta = s.sharedBase.cta := by
  unfold TensorCopy.writeLoc at h
  cases hs : TensorTransfer.slotAt s.descriptor x y k <;> simp [hs] at h
  subst h
  exact ⟨rfl, rfl⟩

/-- A tensor store reads the shared memory of its source CTA. -/
theorem store_readLoc {s : TensorStore.Spec} {x y k : Nat} {l : Loc}
    (h : TensorStore.readLoc s x y k = some l) : l.cta = s.sharedBase.cta := by
  unfold TensorStore.readLoc at h
  cases hs : TensorTransfer.slotAt s.descriptor x y k <;> simp [hs] at h
  subst h
  rfl

/-- A tensor store or reduction writes global memory. -/
theorem store_writeLoc {s : TensorStore.Spec} {x y k : Nat} {l : Loc}
    (h : TensorStore.writeLoc s x y k = some l) : l.space = .global := by
  unfold TensorStore.writeLoc at h
  cases hs : TensorTransfer.slotAt s.descriptor x y k <;> simp [hs] at h
  unfold TensorStore.destination at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨_, -, rfl⟩ := h
  rfl

/-- A tensor load or prefetch reads global memory. -/
theorem sourceLoc_global {outer : Nat} {d : TensorDescriptor.Descriptor outer}
    {origin : Fin (outer + 1) → Int} {rows : Option (Fin 4 → Int)} {x y k : Nat} {l : Loc}
    (h : TensorTransfer.sourceLoc d origin rows x y k = some l) : l.space = .global := by
  unfold TensorTransfer.sourceLoc at h
  cases hs : TensorTransfer.slotAt d x y k <;> simp [hs] at h
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨_, -, rfl⟩ := h
  rfl

/-- An mbarrier action is performed by an instruction or stage that occurred. -/
theorem present_of_objectAction {m : Loc} {e : AsyncCopy.Ref} {action : MBarrier.Action}
    (h : AsyncCopy.objectAction X X.async m e = some action) : X.RefPresent e := by
  cases e with
  | thread j =>
    cases hg : X.get j with
    | none => simp [AsyncCopy.objectAction, hg] at h
    | some ev => exact ⟨ev, hg⟩
  | async i p =>
    cases p with
    | notify t =>
      cases t with
      | copy =>
        simp only [AsyncCopy.objectAction] at h
        cases hs : AsyncCopy.issuedBy X i <;> simp [hs] at h
        exact h.1.2
      | load =>
        simp only [AsyncCopy.objectAction] at h
        split at h
        · cases ho : X.tensor i <;> simp [ho] at h
          exact ⟨_, ho, h.1.2⟩
        · cases h
      | cta c =>
        simp only [AsyncCopy.objectAction] at h
        split at h
        · split_ifs at h with hc
          exact hc.2.1
        · cases h
    | tcNotify rank =>
      simp only [AsyncCopy.objectAction] at h
      split at h
      · split_ifs at h with hc
        exact hc.2
      · cases h
    | arriveOn =>
      simp only [AsyncCopy.objectAction] at h
      split at h
      · split_ifs at h with hc
        exact hc.2
      · cases h
    | _ => simp [AsyncCopy.objectAction] at h

/-- The completing stage of an operation is a use of each CTA it lists (`StageUses`). -/
theorem use_stage {i : EvId} {p : AsyncCopy.Part} {c : Nat} (hf : AsyncCopy.FinalStage X i p)
    (hs : StageUses X i p c) : SharedUse L X (.async i p) c :=
  .inr (.inr (.inr (.inr ⟨i, p, rfl, hf, hs⟩)))

/-- An element of an element-wise linear operation lies in the space and CTA of its destination. -/
theorem elem_loc {s : AsyncCopy.Spec} {j : Nat} {a : Acc} (h : s.elems[j]? = some a) :
    a.loc.space = s.dst.loc.space ∧ a.loc.cta = s.dst.loc.cta := by
  unfold AsyncCopy.Spec.elems at h
  rw [List.getElem?_map] at h
  cases hk : s.elemOffsets[j]? <;> simp [hk] at h
  subst h
  exact ⟨rfl, rfl⟩

/-- A shared source or destination of a linear operation with an observable completion is a use,
by the operation's completing stage, of the CTA it lies in. -/
theorem copy_use (hunobs : ∀ i s, X.Copy i s → s.completion = .unobserved →
      s.src.loc.space = .global ∧ s.dst.loc.space = .global)
    {i : EvId} {s : AsyncCopy.Spec} (hc : X.Copy i s) {l : Loc}
    (hl : l = s.src.loc ∨ l = s.dst.loc) (hs : l.space = .shared) :
    ∃ e', e'.issuer = i ∧ SharedUse L X e' l.cta := by
  cases hcomp : s.completion with
  | mbarrier m =>
    refine ⟨.async i (.notify .copy), rfl, use_stage (.inl ⟨s, m, hc, hcomp, rfl⟩)
      ⟨s, m, hc, hcomp, ?_⟩⟩
    rcases hl with rfl | rfl
    · exact .inr (.inl ⟨hs, rfl⟩)
    · exact .inl ⟨hs, rfl⟩
  | bulkGroup =>
    have hn : ∀ m, s.completion ≠ .mbarrier m := fun m h => by rw [hcomp] at h; cases h
    refine ⟨.async i (.write .copy), rfl, use_stage (.inr (.inl ⟨s, hc, hn, rfl⟩))
      ⟨s, hc, .inl hcomp, ?_⟩⟩
    rcases hl with rfl | rfl
    · exact .inr ⟨hs, rfl⟩
    · exact .inl ⟨hs, rfl⟩
  | asyncGroup =>
    have hn : ∀ m, s.completion ≠ .mbarrier m := fun m h => by rw [hcomp] at h; cases h
    refine ⟨.async i (.write .copy), rfl, use_stage (.inr (.inl ⟨s, hc, hn, rfl⟩))
      ⟨s, hc, .inr hcomp, ?_⟩⟩
    rcases hl with rfl | rfl
    · exact .inr ⟨hs, rfl⟩
    · exact .inl ⟨hs, rfl⟩
  | unobserved =>
    obtain ⟨h1, h2⟩ := hunobs i s hc hcomp
    rcases hl with rfl | rfl
    · rw [h1] at hs; cases hs
    · rw [h2] at hs; cases hs

/-- A planned asynchronous footprint in CTA `c`'s shared memory has, in the table, a use of
CTA `c` by the same issuing instruction: the completing stage of its operation (the MMA or copy
completion, the tensor store's read completion, the bulk copy's or CLC response's notification)
or, for a tensor load write, the stage itself. A bulk prefetch reads global memory (`hpre`),
and a linear operation without an observable completion accesses global memory (`hunobs`). -/
theorem footprint_use (hpre : ∀ i a, X.BulkPrefetch i a → a.loc.space = .global)
    (hunobs : ∀ i s, X.Copy i s → s.completion = .unobserved →
      s.src.loc.space = .global ∧ s.dst.loc.space = .global)
    {i : EvId} {p : AsyncCopy.Part} {a : Acc} (hf : X.AsyncFootprint i p a)
    (hs : a.loc.space = .shared) : ∃ e', e'.issuer = i ∧ SharedUse L X e' a.loc.cta := by
  cases p with
  | mmaRead isB index =>
    obtain ⟨-, ⟨d, s, accum, mask, hi, hl⟩ | ⟨c, k, cta, hi, -, hk, -, hl⟩⟩ := hf
    · exact ⟨.async i .mmaDone, rfl, use_stage (.inr (.inr (.inr (.inl
        ⟨.inl ⟨d, s, accum, mask, hi⟩, rfl⟩)))) (.inl ⟨d, s, accum, mask, hi, mma_byteLoc_cta hl⟩)⟩
    · refine ⟨.async i .mmaDone, rfl, use_stage (.inr (.inr (.inr (.inl
        ⟨.inr (.inl ⟨c, hi⟩), rfl⟩)))) (.inr ⟨c, hi, ?_⟩)⟩
      rw [copy_byteLoc_cta hl]
      exact List.mem_of_getElem? hk
  | read slot =>
    cases slot with
    | copy =>
      rcases hf with ⟨s, hc, rfl⟩ | hb
      · exact copy_use hunobs hc (.inl rfl) hs
      · rw [hpre _ _ hb] at hs
        cases hs
    | load x y k =>
      obtain ⟨s, addr, -, hl, -⟩ := hf
      rw [sourceLoc_global hl] at hs
      cases hs
    | store x y k =>
      obtain ⟨s, addr, hi, hl, -⟩ := hf
      exact ⟨.async i .readsDone, rfl, .inr (.inr (.inr (.inl
        ⟨i, addr, s, rfl, hi, (store_readLoc hl).symm⟩)))⟩
    | cta c => exact hf.elim
    | prefetch x y k =>
      obtain ⟨s, addr, -, hl, -⟩ := hf
      rw [sourceLoc_global hl] at hs
      cases hs
    | elem j => exact hf.elim
  | write slot =>
    cases slot with
    | copy =>
      obtain ⟨s, hc, -, rfl⟩ := hf
      exact copy_use hunobs hc (.inr rfl) hs
    | load x y k =>
      obtain ⟨s, addr, hi, hl, -⟩ := hf
      obtain ⟨hsome, hc⟩ := load_writeLoc hl
      exact ⟨.async i (.write (.load x y k)), rfl, .inr (.inr (.inl
        ⟨i, addr, s, x, y, k, rfl, hi, hsome, hc.symm⟩))⟩
    | store x y k =>
      obtain ⟨s, addr, -, hl, -⟩ := hf
      rw [store_writeLoc hl] at hs
      cases hs
    | cta c =>
      obtain ⟨s, targets, hi, hc, rfl⟩ := hf
      exact ⟨.async i (.notify (.cta c)), rfl, use_stage
        (.inr (.inr (.inr (.inr (.inl ⟨s, targets, c, hi, hc, rfl⟩))))) rfl⟩
    | prefetch x y k => exact hf.elim
    | elem j =>
      obtain ⟨s, hc, he⟩ := hf
      obtain ⟨h1, h2⟩ := elem_loc he
      rw [h2]
      exact copy_use hunobs hc (.inr rfl) (h1 ▸ hs)
  | old slot =>
    cases slot with
    | store x y k =>
      obtain ⟨s, addr, -, -, hl, -⟩ := hf
      rw [store_writeLoc hl] at hs
      cases hs
    | elem j =>
      obtain ⟨s, r, hc, -, he⟩ := hf
      obtain ⟨h1, h2⟩ := elem_loc he
      rw [h2]
      exact copy_use hunobs hc (.inr rfl) (h1 ▸ hs)
    | _ => exact hf.elim
  | _ => exact hf.elim

/-- Every per-kind peer use is a use of the table, except a planned footprint of an
asynchronous stage that has not occurred; that stage's issuing instruction then has a use of
the same CTA in the table (`footprint_use`). -/
theorem peer_use (hpre : ∀ i a, X.BulkPrefetch i a → a.loc.space = .global)
    (hunobs : ∀ i s, X.Copy i s → s.completion = .unobserved →
      s.src.loc.space = .global ∧ s.dst.loc.space = .global)
    {e : AsyncCopy.Ref} {owner : Nat} (h : KindPeerSharedUse L X e owner) :
    SharedUse L X e owner ∨
    ∃ i p a, e = .async i p ∧ ¬ X.AsyncPresent i p ∧ X.AsyncFootprint i p a ∧
      a.loc.space = .shared ∧ a.loc.cta = owner ∧
      ∃ e', e'.issuer = i ∧ SharedUse L X e' owner := by
  obtain ⟨-, ⟨a, w, hint, hs, hc⟩ | ⟨addr, action, hact⟩ | ⟨i, address, s, rfl, hi, hms, hmc⟩ |
    ⟨i, s, rank, m, rfl, hi, ht, hmc⟩⟩ := h
  · cases e with
    | thread j =>
      left
      refine .inl ⟨?_, .inl ⟨a, w, hint, hs, hc⟩⟩
      rcases hint with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨old, new, pc, he⟩
      · exact ⟨_, he⟩
      · exact ⟨_, he⟩
      · exact ⟨_, he⟩
    | async i p =>
      by_cases hp : X.AsyncPresent i p
      · exact .inl (.inl ⟨hp, .inl ⟨a, w, hint, hs, hc⟩⟩)
      · right
        obtain ⟨-, hf⟩ := hint
        obtain ⟨e', hi, hu⟩ := footprint_use (L := L) hpre hunobs hf hs
        exact ⟨i, p, a, rfl, hp, hf, hs, hc, e', hi, hc ▸ hu⟩
  · exact .inl (.inl ⟨present_of_objectAction hact, .inr ⟨addr, action, hact⟩⟩)
  · exact .inl (use_stage (.inr (.inr (.inr (.inr (.inr (.inl ⟨address, s, hi, rfl⟩))))))
      ⟨address, s, hi, hms, hmc⟩)
  · exact .inl (use_stage (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨s, rank, m, hi, ht, rfl⟩)))))))
      ⟨s, m, hi, ht, hmc⟩)

/-! ## Coverage -/

/-- **Bulk copies.** `KindPendingAtExit` is a use of the mbarrier's CTA by the copy's
notification (`SharedUse`, the `.notify .copy` row of `StageUses`) that has not occurred while
that CTA has exited. The initialization of a bulk copy's mbarrier is checked for every event that
names an mbarrier (`MbarUninit`, ERR-MBAR-UNINITIALIZED), the storage of an mbarrier by `Unalloc`,
and the agreement of the `tcgen05` collectives (`KindTcUnsafe`) by the `tcgen05` class of
`AlignedMismatch` (ERR-ALIGNED-MISMATCH), through `divergent_tc_iff` and `exited_tc_iff`.

Side hypothesis `hmbar`: the mbarrier of every bulk copy is in the issuer's CTA. The
`cp.async.bulk` issue rule (`tmaTmpl`, `.cpBulk`, Core/Async/Tma.lean) takes it from `mbarLoc`,
which yields a location of the issuing thread's CTA (`Flow.mbarLoc_local`). It excludes only
executions with a bulk-issue event that no thread rule emits; the per-kind formulation speaks of
the issuer's CTA and the table of the mbarrier's CTA, which are the same CTA in every execution
the thread rules produce. -/
theorem tma_covered {mem0 : Mem0}
    (hmbar : ∀ i s m, KindBulk X i s m → m.cta = i.1 / L.block)
    (h : KindTmaUnsafe L mem0 X) :
    TmaUnsafe L mem0 X ∨ MbarUninit L X ∨ Unalloc mem0 X ∨ AlignedMismatch L K X ∨
      SharedLifetimeUnsafe L K A X := by
  rcases h with h | h | ⟨b, s, m, hb, hn⟩ | h | ⟨e, m, l, hu, hl, hn⟩ | h | h
  · exact .inl (.inl h)
  · exact .inl (.inr (.inl h))
  · refine .inr (.inl ⟨b, m, .inr (.inl ⟨s, hb.1, hb.2.1⟩), fun count hi => ?_, hn⟩)
    obtain ⟨pc, h1⟩ := hb.1
    obtain ⟨pc', h2⟩ := hi
    rw [h1] at h2
    cases h2
  · exact .inl (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inl (.inr ⟨e, m, l, hu.elim id fun ⟨_, hi⟩ => .of_init hi, hl, hn⟩)))
  · right; right; right; right
    obtain ⟨c, hx, i, s, m, hb, hc, hn⟩ := h
    refine ⟨.async i (.notify .copy), c, use_stage (.inl ⟨s, m, hb.1, hb.2.1, rfl⟩)
      ⟨s, m, hb.1, hb.2.1, .inr (.inr ((hmbar _ _ _ hb).trans hc))⟩, .inr ⟨hx, ?_⟩⟩
    rintro ⟨hp, -⟩
    change (X.async.copies i).notified = true at hp
    rw [hn] at hp
    cases hp
  · refine .inr (.inr (.inr (.inl (alignedMismatch_iff L |>.mpr (.inl ?_)))))
    rcases h with h | h
    · exact .inl ((AlignedClass.divergent_tc_iff L).mpr h)
    · exact .inr ((AlignedClass.exited_tc_iff L).mpr h)

/-- An event of another kind is no initialization. -/
theorem not_mbInit_of_get {e : EvId} {pc : Nat} {k : Kind} (hk : ∀ m c, k ≠ .mbInit m c)
    (h : X.get e = some ⟨pc, k⟩) {m : Loc} {c : Nat} : ¬ X.MbInit e m c := by
  rintro ⟨pc', h'⟩
  rw [h] at h'
  cases h'
  exact hk m c rfl

/-- **CLC responses.** The per-kind lifetime case is the use of each target CTA by the
notification at that CTA; the response mbarrier's storage is `Unalloc` and its initialization
`MbarUninit`. -/
theorem clc_covered {mem0 : Mem0} (h : KindClcUnsafe L K A mem0 X) :
    ClcUnsafe L X ∨ MbarUninit L X ∨ Unalloc mem0 X ∨ SharedLifetimeUnsafe L K A X := by
  rcases h with h | ⟨i, s, targets, c, l, hi, hc, hl, hn⟩ | ⟨i, s, targets, c, hi, hc, hn⟩ |
    ⟨i, s, targets, c, hi, hc, hx, hn⟩
  · exact .inl h
  · exact .inr (.inr (.inl (.inr ⟨i, _, l, .of_clc hi hc, hl, hn⟩)))
  · obtain ⟨pc, hg⟩ := hi
    exact .inr (.inl ⟨i, _, .of_clc ⟨pc, hg⟩ hc,
      fun _ => not_mbInit_of_get (fun _ _ h => by cases h) hg, hn⟩)
  · exact .inr (.inr (.inr ⟨.async i (.notify (.cta c)), c, use_stage
      (.inr (.inr (.inr (.inr (.inl ⟨s, targets, c, hi, hc, rfl⟩))))) rfl,
      .inr ⟨hx, fun hf => hn ⟨hf.1, hf.2⟩⟩⟩))

/-- **Tensor loads.** The per-kind lifetime cases are the uses of the destination CTA by each
data write and of the mbarrier's CTA by the notification; the mbarrier's storage is `Unalloc`
and its initialization `MbarUninit`.

Side hypotheses, each excluding only executions with a tensor-load issue event that no thread
rule emits, or whose recorded effects do not belong to their issue:

* `htensor` (`TensorOk`, the `Consistent.tensor` field): a recorded observation has its issue's
  specification. The per-kind formulation asks for an observation with spec `s`; the table
  reads the writes of the observation, so both name the same copy.
* `hmbar`: the issued mbarrier is in shared memory. The tensor issue rule (`tensorTmpl`,
  Core/Async/Tensor/TensorThread.lean) emits an issue only after `TensorRoute`, whose second
  conjunct is `mbar.space = .shared`. The table names the mbarrier's CTA only for a shared
  mbarrier, as the per-kind peer use does.
* `hslot`: the box of an issued load has at least one slot. With no slot, the per-kind
  formulation rejects an exited destination CTA only because the observation is missing, that
  is, because the copy has not been performed; such a copy writes no byte of the destination,
  so it is no use of the destination's shared memory, and its notification remains a use of
  the mbarrier's CTA. -/
theorem tensor_covered {mem0 : Mem0} (htensor : TensorOk L X)
    (hmbar : ∀ i address s, X.TensorIssue i address s → s.mbar.space = .shared)
    (hslot : ∀ i address s, X.TensorIssue i address s → Nonempty (TensorTransfer.Slot s.descriptor))
    (h : KindTensorUnsafe L K A mem0 X) :
    TensorUnsafe X ∨ MbarUninit L X ∨ Unalloc mem0 X ∨ SharedLifetimeUnsafe L K A X := by
  by_cases hu : SharedLifetimeUnsafe L K A X
  · exact .inr (.inr (.inr hu))
  rcases h with ⟨i, address, s, l, hi, hl, hn⟩ | ⟨i, address, s, hi, hn⟩ | h |
    ⟨i, address, s, hi, hx, hn⟩ | ⟨i, address, s, hi, hx, hn⟩
  · exact .inr (.inr (.inl (.inr ⟨i, _, l, .of_tensor hi, hl, hn⟩)))
  · obtain ⟨pc, hg⟩ := hi
    exact .inr (.inl ⟨i, _, .of_tensor ⟨pc, hg⟩,
      fun _ => not_mbInit_of_get (fun _ _ h => by cases h) hg, hn⟩)
  · exact .inl h
  · exfalso
    have huse : ∀ slot : TensorTransfer.Slot s.descriptor,
        SharedUse L X (.async i (.write (.load slot.1.val slot.2.1.val slot.2.2.val)))
          s.sharedBase.cta := fun slot =>
      .inr (.inr (.inl ⟨i, address, s, _, _, _, rfl, hi, by rw [slotAt_self]; rfl, rfl⟩))
    have hfin := fun slot => (not_unsafe_use hu (huse slot)).2 hx
    cases ho : X.tensor i with
    | none =>
      obtain ⟨slot⟩ := hslot i address s hi
      obtain ⟨o, -, -, ho', -⟩ := (hfin slot).1
      rw [ho] at ho'
      cases ho'
    | some o =>
      obtain ⟨⟨address', hi'⟩, -⟩ := htensor i o ho
      have hspec : o.spec = s := tensorIssue_spec hi' hi
      exact hn ⟨o, ho, hspec, fun slot => ⟨(hfin slot).1, (hfin slot).2⟩⟩
  · exfalso
    have huse : SharedUse L X (.async i (.notify .load)) s.mbar.cta :=
      use_stage (.inr (.inr (.inr (.inr (.inr (.inl ⟨address, s, hi, rfl⟩))))))
        ⟨address, s, hi, hmbar i address s hi, rfl⟩
    have hf := (not_unsafe_use hu huse).2 hx
    exact hn ⟨hf.1, hf.2⟩

/-- **Tensor stores.** The per-kind lifetime case is the use of the source CTA by the read
completion. -/
theorem tensorStore_covered (h : KindTensorStoreUnsafe L K A X) :
    TensorStoreUnsafe A X ∨ SharedLifetimeUnsafe L K A X := by
  rcases h with ⟨i, address, s, hi, hx, hn⟩ | h
  · exact .inr ⟨.async i .readsDone, s.sharedBase.cta, .inr (.inr (.inr (.inl
      ⟨i, address, s, rfl, hi, rfl⟩))), .inr ⟨hx, fun hf => hn ⟨hf.1, hf.2⟩⟩⟩
  · exact .inl (.inl h)

/-- **MMA and `tcgen05.cp`.** `KindPeerAlive` and the lifetime part of `KindCopySafe` are the
uses of the operand CTAs by the completion of the MMA or copy. -/
theorem instruction_covered (h : KindInstructionUnsafe L K A X) :
    TcMma.InstructionUnsafe L A X ∨ SharedLifetimeUnsafe L K A X := by
  by_cases hu : SharedLifetimeUnsafe L K A X
  · exact .inr hu
  left
  intro hs
  apply h
  refine ⟨fun i d s accum mask hi => ?_, fun i c hi => ?_, hs.2.2⟩
  · obtain ⟨h1, h2⟩ := hs.1 i d s accum mask hi
    refine ⟨h1, fun owner ho => ?_, h2⟩
    have huse : SharedUse L X (.async i .mmaDone) owner :=
      use_stage (.inr (.inr (.inr (.inl ⟨.inl ⟨d, s, accum, mask, hi⟩, rfl⟩))))
        (.inl ⟨d, s, accum, mask, hi, ho⟩)
    obtain ⟨hst, hfin⟩ := not_unsafe_use hu huse
    exact ⟨hst, fun hx => ⟨(hfin hx).1, (hfin hx).2⟩⟩
  · refine ⟨hs.2.1 i c hi, fun cta hc hx => ?_⟩
    have huse : SharedUse L X (.async i .mmaDone) cta :=
      use_stage (.inr (.inr (.inr (.inl ⟨.inr (.inl ⟨c, hi⟩), rfl⟩)))) (.inr ⟨c, hi, hc⟩)
    exact ⟨((not_unsafe_use hu huse).2 hx).1, ((not_unsafe_use hu huse).2 hx).2⟩

/-- **`tcgen05.commit`.** The per-kind target lifetime is the use of the target mbarrier's CTA
by the arrival at that rank, and the target's initialization is `MbarUninit`; the per-kind issue
lifetime is the use of each CTA of the CTA group by the issuing instruction. -/
theorem tcCommit_covered (h : KindTcCommitUnsafe L K A X) :
    TcCommitUnsafe L X ∨ MbarUninit L X ∨ SharedLifetimeUnsafe L K A X := by
  by_cases hu : SharedLifetimeUnsafe L K A X
  · exact .inr (.inr hu)
  rcases h with ⟨i, s, rank, m, hi, ht, hn⟩ | ⟨i, s, hi, hn⟩
  · by_cases hinit : ∃ init count, X.MbInit init m count ∧ InitPublished L X init i m
    · refine absurd ⟨hinit, fun hx => ?_⟩ hn
      have huse : SharedUse L X (.async i (.tcNotify rank)) m.cta :=
        use_stage (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨s, rank, m, hi, ht, rfl⟩)))))))
          ⟨s, m, hi, ht, rfl⟩
      have hf := (not_unsafe_use hu huse).2 hx
      exact ⟨hf.1, hf.2⟩
    · obtain ⟨pc, hg⟩ := hi
      exact .inr (.inl ⟨i, m, .inr (.inr (.inr (.inl ⟨s, rank, ⟨pc, hg⟩, ht⟩))),
        fun _ => not_mbInit_of_get (fun _ _ h => by cases h) hg, hinit⟩)
  · refine .inl ⟨i, s, hi, fun ⟨h1, h2, h3⟩ => hn ⟨h1, h2, h3, fun peer hp hne => ?_⟩⟩
    have huse : SharedUse L X (.thread i) peer := .inr (.inl ⟨i, s, rfl, hi, hp⟩)
    obtain ⟨hst, hfin⟩ := not_unsafe_use hu huse
    exact ⟨hst hne, fun hx => (hfin hx).2⟩

/-- The executions `KindPeerUnsafe` rejects and `SharedLifetimeUnsafe` accepts: the use is the
planned footprint, in the owner's shared memory, of an asynchronous stage that has not occurred,
the owner has exited, and every use of the owner in the table is finished. -/
def KindPeerException (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution)
    (e : AsyncCopy.Ref) (owner : Nat) : Prop :=
  ∃ i p a, e = .async i p ∧ ¬ X.AsyncPresent i p ∧ X.AsyncFootprint i p a ∧
    a.loc.space = .shared ∧ a.loc.cta = owner ∧ CtaExited L X owner ∧
    ∀ e', SharedUse L X e' owner → SharedFinished L K A X e' owner

/-- **Peer shared memory.** Every execution `KindPeerUnsafe` rejects is rejected by
`SharedLifetimeUnsafe`, or exhibits `KindPeerException`.

The start half has no exception: a use without a start witness is a table use, or a planned
footprint whose issuing instruction has a table use of the same CTA (`footprint_use`), and the
start witness depends on the issuing instruction only.

The exception is in the completion half. `KindPeerSharedFinished` asks every planned footprint of
an exited owner to complete before an owner exit, including the footprint of a stage that has
not occurred and that no other recorded stage contains. `SharedFinished` asks this of the uses
of the table only, which for an operation that has not completed include its completing stage
(the MMA or copy completion, a tensor load's data write or notification, a tensor store's read
completion, a bulk copy's or CLC response's notification), unperformed or not. A stage that
never occurred accessed no memory: it is no use of the owner's memory in that execution, and in
every execution where it occurs it is a performed use of the table, checked against the owner's
exit. In the exception the operation's completing stages are finished as well (the last
conjunct), so the stage is one an operation that completed did not perform, for example the
skipped source read of an out-of-bounds tensor store byte.

Side hypotheses, each excluding only executions with an issue event that no thread rule emits;
in them an access of another CTA's shared memory would have no table use:

* `hpre`: a bulk prefetch (`cp.async.bulk.prefetch`) reads global memory; its issue rule
  computes the source with `effAddr .global`.
* `hunobs`: a linear operation without an observable completion (`Completion.unobserved`, the
  `.release` forms of `st.async` and `red.async`) accesses global memory; its issue rule
  (Core/Async/AsyncStore.lean) requires a global destination for these forms, and its register
  source is an empty range at the destination. -/
theorem peer_covered (hpre : ∀ i a, X.BulkPrefetch i a → a.loc.space = .global)
    (hunobs : ∀ i s, X.Copy i s → s.completion = .unobserved →
      s.src.loc.space = .global ∧ s.dst.loc.space = .global)
    (h : KindPeerUnsafe L K A X) :
    SharedLifetimeUnsafe L K A X ∨
      ∃ e owner, KindPeerSharedUse L X e owner ∧ KindPeerException L K A X e owner := by
  by_cases hu : SharedLifetimeUnsafe L K A X
  · exact .inl hu
  right
  obtain ⟨e, owner, huse, hbad⟩ := h
  have hne := huse.1
  rcases peer_use hpre hunobs huse with hs | ⟨i, p, a, rfl, hnp, hf, hsp, hc, e', hi, hs'⟩
  · exfalso
    obtain ⟨hst, hfin⟩ := not_unsafe_use hu hs
    rcases hbad with hb | ⟨hx, hb⟩
    · exact hb (hst hne)
    · exact hb (hfin hx).2
  · rcases hbad with hb | ⟨hx, hb⟩
    · exfalso
      have hne' : owner ≠ e'.issuer.1 / L.block := by rw [hi]; exact hne
      exact hb (started_of_issuer hi ((not_unsafe_use hu hs').1 hne'))
    · exact ⟨_, owner, huse, i, p, a, rfl, hnp, hf, hsp, hc, hx,
        fun e'' h'' => (not_unsafe_use hu h'').2 hx⟩

/-! ## The issuer's own CTA -/

/-- The per-kind peer use never names the issuer's own CTA. -/
theorem kindPeerUse_not_own {e : AsyncCopy.Ref} :
    ¬ KindPeerSharedUse L X e (e.issuer.1 / L.block) :=
  fun h => h.1 rfl

/-- A thread access of shared memory is a use of the CTA it accesses, whichever CTA the thread
belongs to. -/
theorem thread_access_use {e : EvId} {a : Acc} {w : Bool} (ha : X.Access e a w)
    (hs : a.loc.space = .shared) : SharedUse L X (.thread e) a.loc.cta := by
  refine .inl ⟨?_, .inl ⟨a, w, ha, hs, rfl⟩⟩
  rcases ha with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨old, new, pc, he⟩
  · exact ⟨_, he⟩
  · exact ⟨_, he⟩
  · exact ⟨_, he⟩

/-- An MMA whose completion has not occurred while its issuer's own CTA, holding its low
operand rows, has exited is unsafe. No `KindPeerSharedUse` names that CTA
(`kindPeerUse_not_own`). -/
theorem own_mma_unsafe {i : EvId} {d : Nat} {s : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} (hi : X.MmaIssue i d s accum mask) (hlow : s.lowCta = i.1 / L.block)
    (hd : X.async.mmaDone i = false) (hx : CtaExited L X (i.1 / L.block)) :
    SharedLifetimeUnsafe L K A X := by
  refine ⟨.async i .mmaDone, i.1 / L.block, use_stage
    (.inr (.inr (.inr (.inl ⟨.inl ⟨d, s, accum, mask, hi⟩, rfl⟩))))
    (.inl ⟨d, s, accum, mask, hi, .inl hlow.symm⟩), .inr ⟨hx, ?_⟩⟩
  rintro ⟨hp, -⟩
  change X.async.mmaDone i = true at hp
  rw [hd] at hp
  cases hp

end
end PTX.Tests.SharedLifetimeCoverage
