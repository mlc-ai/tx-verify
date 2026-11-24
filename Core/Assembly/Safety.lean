-- SPDX-License-Identifier: Apache-2.0
module

public import Core.MBarrier.InitPublication
public import Core.Memory.CommitOperandOrder
public import Core.Async.Tma
public import Core.Assembly.SharedLifetime
public import Core.Tmem.TmemPairLifetime
public import Core.Tc.TcMmaRead

@[expose] public section

/-!
# Unsafe accesses and supported protocols

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

variable (L : Launch)

/-! ## ERR-DATA-RACE — unordered conflicting accesses
Statement: An execution is unsafe when two distinct accesses with the same footprint, at least one
  of them a write, are not morally strong and neither precedes the other in model causality order
  (`ByteCausality`) at a byte they access. Two writes of the same bytes with the same value are
  exempt.

Defs: Conflict, StrongScoped, not_strongScoped_write_copy, strongScoped_thread_of_old,
  strongScoped_thread_old, AsyncCopy.Ref.Generic, generic_async_iff, OpFootprint, MorallyStrong,
  SameValueWrites, Race

Source:
- §8.7: "Two operations are said to be morally strong relative to each other if they satisfy all of
    the following conditions: The operations are related in program order (i.e, they are both
    executed by the same thread), or each operation is strong and specifies a scope that includes
    the thread executing the other operation. Both operations are performed via the same proxy . If
    both are memory operations, then they overlap completely."
- §8.7.1: "Two conflicting memory operations are said to be in a data-race if they are not related
    in causality order and they are not morally strong ."
- §8.4 (strong operations)
- §8.6 (proxies)
- §9.7.10.28.5.4: "Each reduction operation performed by cp.reduce.async.bulk.tensor has
    individually .relaxed.gpu memory ordering semantics and are element-wise atomic."
- §9.7.10.28.4.2: "These are element-wise atomic at the specified scope."
- §9.7.10.28.4.2: "When .sem.scope is not specified, it defaults to .relaxed.sys ."
- §9.7.10.28.4.2: "The memory operations are performed in the async proxy."
- §9.7.15.7 (red.async): "The reduce operation is a relaxed memory operation."
- §9.7.15.7 (red.async): "The reduce operation is a strong memory operation with .release semantics
    at the scope specified by .scope ."
- §9.7.10.12 (st.async): "The store operation is a strong memory operation with .release semantics
    at the scope specified by .scope ."
- §9.7.10.28.1 (async access hazards)
- §9.7.18.10 (MMA source stability)
- §8.7.2: "The axioms in the memory consistency model do not apply if a PTX program contains one or
    more mixed-size data-races . But these axioms are sufficient to describe the behavior of a PTX
    program with only uniform-size data-races ."
- §8.9.6: "Two overlapping writes are unrelated in coherence order if they are in a data-race ,
    which gives rise to the partial nature of coherence order ."
- §8.10.1: "If a write W precedes an overlapping write W’ in causality order , then W must precede
    W’ in coherence order ."
- §8.10.6: "If a read R precedes an overlapping write W in causality order , then R cannot read from
    W. If a write W precedes an overlapping read R in causality order , then for any byte accessed
    by both R and W, R cannot read from any write W’ that precedes W in coherence order ."

Direction: stricter

Applies: Ordinary and asynchronous access intents, including still-pending effects and the
  never-completing reads of tensor prefetches (THREAD-TENSOR-PREFETCH, EXT-PREFETCH-PENDING)

Premises: Distinct accesses overlap at a byte, at least one writes, they are not morally strong,
  they are not two writes of the same bytes with the same value (`SameValueWrites`), and neither
  direction is ordered by the causality order at the byte (`ByteCausality`).

Effect: Safety rejection. Source/destination reuse before or after an operation is permitted when
  the corresponding order is proved. A morally strong pair is not a race; a read in such a pair is
  constrained by MEM-READS-FROM and MEM-READ-AXIOMS only. The strong operations represented are the
  thread accesses with a `.relaxed`, `.acquire`, `.release` or `.acq_rel` qualifier (`Acc.Strong`:
  the strong loads and stores of THREAD-ACCESS, `.volatile` ones as `.relaxed` at `.sys`, `.mmio`
  ones with their own `.sem` at `.sys`, and every `atom` and `red`, whose `.sem` is `.relaxed` when
  absent), with the access's `scope` (`.gpu` when absent for `atom` and `red`), the element
  reductions of `cp.reduce.async.bulk.tensor` (`.relaxed.gpu`), the element reductions of
  `cp.reduce.async.bulk` and `red.async` at the scope of their `.sem.scope` (`.relaxed.sys` when
  absent for `cp.reduce.async.bulk`), and the write of `st.async.release` at its scope. Scope
  inclusion is MEM-SCOPE (`MbarScopeIncludes`). An atomic read-modify-write is one access that both
  reads and writes, so two `atom` or `red` operations of the same footprint whose scopes include
  each other's thread are morally strong and are not a race, while an `atom` and a conflicting weak
  access are. Thread accesses and the stages of `cp.async`, `st.async` and `red.async` use the
  generic proxy, the other asynchronous effects the async proxy (§8.6). The issuing thread executes
  an asynchronous operation. A reduction's read and write of a byte are part of its element's
  operation (DEP-REDUCTION-VALUES), so two reductions overlap completely when they reduce the same
  element.

Review: Every data race is reported, uniform-size ones included, which is stricter than §8.10: its
  axioms describe programs with only uniform-size races (§8.7.2), and the model rejects such an
  execution as unsafe. It does not describe the execution's outcomes. The one exception is a pair of
  writes of the same bytes (the same footprint) with the same value (`SameValueWrites`), of any
  write kind the model has: thread stores, tensor-store and tensor-load byte writes, CLC responses
  and linear copy writes (`MemWrites`). The values are compared as the model represents them, as
  byte lists. Such a pair is a uniform-size race that the axioms describe: the two writes are
  unrelated in coherence order (§8.9.6), and the coherence and causality axioms (§8.10.1, §8.10.6)
  constrain a read by the writes that precede it, so a read that may read from either write reads
  the same bytes. Any read that overlaps one of them and is unordered with it is still a race, and
  so are writes with different values and writes that overlap partially (ERR-MIXED-SIZE). The memory
  after the kernel holds their common bytes (CORRECT-FINAL: all co-maximal writes of a byte agree).
  An asynchronous write whose bytes are not yet performed has no value yet (`MemWrites` does not
  hold), so such a pair is not compared in that execution. The check still holds for every
  consistent execution: a consistent execution that performs both writes compares their bytes, and
  if they differ that execution is unsafe, so a kernel is safe only if no consistent execution of it
  performs two unordered writes of one footprint that are not morally strong and have different
  values.
-/

/-- Two distinct accesses `e` and `f`, pending or performed, whose footprints `a` and `b` overlap,
and at least one of which writes (§8.7). -/
def Conflict (X : Execution) (e f : AsyncCopy.Ref) (a b : Acc) : Prop :=
  e ≠ f ∧ ∃ we wf, X.Intent e a we ∧ X.Intent f b wf ∧
    (we = true ∨ wf = true) ∧ a.Overlap b

/-- `e` with footprint `a` is a strong operation whose scope includes thread `g` (§8.4, §8.5): a
thread access with the `.relaxed`, `.acquire`, `.release` or `.acq_rel` qualifier (`Acc.Strong`)
at its scope, or a tensor reduction element at `.gpu` scope. -/
def StrongScoped (X : Execution) : AsyncCopy.Ref → Acc → Nat → Prop
  | .thread i, a, g => (∃ w, X.Access i a w) ∧ a.Strong ∧ MbarScopeIncludes L a.scope i.1 g
  | .async i (.write (.store ..)), _, g | .async i (.old (.store ..)), _, g =>
    (∃ addr s op, X.TensorStoreIssue i addr s ∧ s.reduce = some op) ∧
      MbarScopeIncludes L .gpu i.1 g
  | .async i (.write (.elem _)), _, g | .async i (.old (.elem _)), _, g =>
    ∃ s r sc, X.Copy i s ∧ s.writes = .reduce r ∧ s.scope = some sc ∧ MbarScopeIncludes L sc i.1 g
  | .async i (.write .copy), _, g =>
    ∃ s sc, X.Copy i s ∧ s.writes = .whole ∧ s.scope = some sc ∧ MbarScopeIncludes L sc i.1 g
  | .async .., _, _ => False

/-- The write of a linear operation without a strong scope (every copy) is not strong, as
before. -/
theorem not_strongScoped_write_copy {X : Execution} {i : EvId} {s : AsyncCopy.Spec} {a : Acc}
    {g : Nat} (hc : X.Copy i s) (hs : s.scope = none) :
    ¬ StrongScoped L X (.async i (.write .copy)) a g := by
  rintro ⟨s', sc, hc', -, hsc, -⟩
  cases Execution.Copy.unique hc hc'
  rw [hs] at hsc
  cases hsc

/-- An acquire read or a release write is strong at its scope, as before every strong access was. -/
theorem strongScoped_thread_of_old {X : Execution} {i : EvId} {a : Acc} {g : Nat}
    (h : ((∃ bs, X.Reads i a bs) ∧ a.acquire = true ∨ (∃ bs, X.Writes i a bs) ∧ a.release = true))
    (hs : MbarScopeIncludes L a.scope i.1 g) : StrongScoped L X (.thread i) a g := by
  rcases h with ⟨⟨bs, hr⟩, ha⟩ | ⟨⟨bs, hw⟩, hr⟩
  · exact ⟨⟨false, Or.inl ⟨bs, hr, rfl⟩⟩, Or.inr (Or.inl ha), hs⟩
  · exact ⟨⟨true, Or.inr (Or.inl ⟨bs, hw, rfl⟩)⟩, Or.inr (Or.inr hr), hs⟩

/-- For an event that is not an atomic read-modify-write, whose footprint is not `.relaxed`, that
releases only when it writes and acquires only when it reads (every such event the forms before
THREAD-ATOMIC produce), `StrongScoped` is the acquire read or release write it was before. -/
theorem strongScoped_thread_old {X : Execution} {i : EvId} {a : Acc} {g : Nat}
    (hn : ∀ pc a o n, X.get i ≠ some ⟨pc, .rmw a o n⟩) (hx : a.relaxed = false)
    (hr : (∃ bs, X.Reads i a bs) → a.release = false)
    (hw : (∃ bs, X.Writes i a bs) → a.acquire = false) (h : StrongScoped L X (.thread i) a g) :
    ((∃ bs, X.Reads i a bs) ∧ a.acquire = true ∨ (∃ bs, X.Writes i a bs) ∧ a.release = true) ∧
      MbarScopeIncludes L a.scope i.1 g := by
  obtain ⟨⟨w, hac⟩, hst, hs⟩ := h
  refine ⟨?_, hs⟩
  rw [Execution.access_iff_of_not_rmw hn] at hac
  rcases hac with ⟨bs, hrd, -⟩ | ⟨bs, hwr, -⟩
  · refine Or.inl ⟨⟨bs, hrd⟩, ?_⟩
    rcases hst with h | h | h
    · simp [hx] at h
    · exact h
    · simp [hr ⟨bs, hrd⟩] at h
  · refine Or.inr ⟨⟨bs, hwr⟩, ?_⟩
    rcases hst with h | h | h
    · simp [hx] at h
    · simp [hw ⟨bs, hwr⟩] at h
    · exact h

/-- The access is performed via the generic proxy (§8.6): a thread access, or a stage of a linear
operation performed in the generic proxy (`GenericCopy`: `cp.async`, `st.async`, `red.async`). -/
def AsyncCopy.Ref.Generic (X : Execution) : AsyncCopy.Ref → Prop
  | .thread _ => True
  | .async i _ => GenericCopy X i

/-- A stage of an asynchronous operation that is not a generic-proxy linear operation uses the
async proxy, as every asynchronous stage did before. -/
theorem generic_async_iff {X : Execution} {i : EvId} {p : AsyncCopy.Part} :
    AsyncCopy.Ref.Generic X (.async i p) ↔ GenericCopy X i := Iff.rfl

/-- The footprint of the memory operation that access `a` of `e` is part of: a byte of a tensor
reduction belongs to its element's reduction; any other access is its own operation. -/
def OpFootprint (X : Execution) (e : AsyncCopy.Ref) (a : Acc) : Acc → Prop :=
  match e with
  | .async i (.write (.store x y _)) | .async i (.old (.store x y _)) => fun op =>
      ∃ addr s red loc, X.TensorStoreIssue i addr s ∧
      s.reduce = some red ∧ TensorStore.writeLoc s x y 0 = some loc ∧
      op = { loc := loc, size := s.descriptor.format.bytes }
  | _ => fun op => op = a

/-- §8.7: program-order related, or each strong with a scope including the other's thread;
the same proxy; complete overlap of the two operations. -/
def MorallyStrong (X : Execution) (e f : AsyncCopy.Ref) (a b : Acc) : Prop :=
  ((∃ i j, e = .thread i ∧ f = .thread j ∧ i.1 = j.1) ∨
    (StrongScoped L X e a f.issuer.1 ∧ StrongScoped L X f b e.issuer.1)) ∧
  (e.Generic X ↔ f.Generic X) ∧ ∃ oa ob, OpFootprint X e a oa ∧
    OpFootprint X f b ob ∧ oa.SameFootprint ob

/-- Two writes of the same bytes (one footprint) with the same value, compared as the model
represents values (byte lists), for every write kind (`MemWrites`). A write not yet performed has
no value; such a pair is compared in the executions that perform both. -/
def SameValueWrites (X : Execution) (e f : AsyncCopy.Ref) (a b : Acc) : Prop :=
  X.Intent e a true ∧ X.Intent f b true ∧ a.SameFootprint b ∧
    ∀ bs bs', X.MemWrites e a bs → X.MemWrites f b bs' → bs = bs'

/-- A data race (§8.7.1): two conflicting accesses with the same footprint that are not morally
strong, are not two writes of the same value, and are unordered in both directions in
`ByteCausality` at a byte they access. -/
def Race (X : Execution) : Prop :=
  ∃ e f a b l, Conflict X e f a b ∧ a.SameFootprint b ∧ a.Covers l ∧
    ¬ MorallyStrong L X e f a b ∧ ¬ ByteCausality L X l e f ∧ ¬ ByteCausality L X l f e ∧
    ¬ SameValueWrites X e f a b

/-! ## ERR-MIXED-SIZE — overlapping accesses of different widths
Statement: An execution is unsafe when two conflicting accesses with different footprints overlap at
  a byte and neither precedes the other in `ByteCausality` at that byte.

Defs: Mixed

Source:
- §8.7.2 (mixed-size races)
- §9.7.10.28.1 (async hazards)

Direction: stricter

Applies: Ordinary and asynchronous conflicting access intents with different footprints

Premises: An overlapping byte has no order (`ByteCausality`) in either direction.

Effect: Safety rejection, with read consistency checked byte by byte.
-/

/-- A mixed-size conflict (§8.7.2): two conflicting accesses with different footprints that are
unordered in both directions in `ByteCausality` at a byte both cover. -/
def Mixed (X : Execution) : Prop :=
  ∃ e f a b l, Conflict X e f a b ∧ ¬ a.SameFootprint b ∧ a.Covers l ∧ b.Covers l ∧
    ¬ ByteCausality L X l e f ∧ ¬ ByteCausality L X l f e

/-! ## ERR-OBJECT-LIFETIME — object faults, object lifetimes and async lifetimes
Statement: An execution is unsafe when an mbarrier operation faults, or when an operation on an
  object is not ordered after the initialization of its lifetime or not ordered before the
  invalidation that ends that lifetime. It is also unsafe when an ordinary memory access to an
  object's bytes is ordered neither before its initialization nor after its invalidation, when two
  `cp.async` operations of one group overlap (ERR-CP-ASYNC-OVERLAP), or when the destination range
  of a `.cp_mask` copy covers an unallocated byte (ERR-BULK-MASK-RANGE).

Defs: RecordBefore, ObjectPublished, TmaUnsafe

Source:
- §9.7.15.16 (mbarrier lifetime and initialization): "Performing any mbarrier operation except
    mbarrier.init on an uninitialized mbarrier object results in undefined behavior. Performing any
    non-mbarrier or mbarrier.init operations on an initialized mbarrier object results in undefined
    behavior"
- §9.7.15.16.4: "An mbarrier object must be invalidated to repurpose its memory for any purpose,
    including repurposing it for another mbarrier object."
- §9.7.15.16.13: "An mbarrier object must be invalidated before using its memory location for any
    other purpose. Performing any mbarrier operation except mbarrier.init on a memory location that
    does not contain a valid mbarrier object , results in undefined behavior."
- §9.7.15.16.13 (example): "bar.cta.sync 0; @t0 mbarrier.inval.shared.b64 [shmem]; // shmem can be
    reused here for unrelated use : bar.cta.sync 0; st.shared.b64 [shmem], ...; // shmem can be
    re-initialized as mbarrier object : bar.cta.sync 0; @t0 mbarrier.init.shared.b64 [shmem], 24;"
- §9.7.10.28.4.1 (generic-proxy mbarrier operand)

Direction: reading

Applies: Actual object records and the memory accesses of an object's bytes (the initialization
  published to the issue of every mbarrier operation: ERR-MBAR-UNINITIALIZED; the storage of an
  mbarrier: ERR-UNALLOCATED-ACCESS; shared-memory lifetimes: ERR-SHARED-LIFETIME)

Premises: A recorded object transition faults; an operation is not ordered after the initialization
  of its lifetime (`InitPublished`) or, when that lifetime is invalidated, before the invalidation
  (`RecordBefore`); a re-initialization does not happen after an earlier invalidation; a memory
  access touches a byte of an mbarrier and is neither ordered before an initialization nor after the
  invalidation that ends that initialization's lifetime, at that byte (MEM-MODEL-CAUSALITY
  `modelCausality`: a thread access happens before it; an asynchronous access has its completion
  observed by a wait that happens before it; an asynchronous access after a thread event has a proxy
  fence between them).

Effect: Safety rejection.

Review: The ISA forbids non-mbarrier operations on an initialized object only, so an access of the
  bytes ordered before the initialization or after the invalidation is allowed, whether a thread
  performs it or an asynchronous copy, MMA or CLC response writes it. An access ordered neither way
  may overlap the object's lifetime and is rejected. A lifetime is the interval of the object
  history from a successful initialization to the next invalidation (`InitBefore`); the required
  orders are base causality order (`baseCausality`) and phase observation, and the history's
  position alone orders nothing.
  Operations of one lifetime are ordered before its invalidation: a thread operation happens before
  it, and an asynchronous arrival or complete-tx belongs to a phase whose completion a wait observed
  that happens before it. A re-initialization happens after every earlier invalidation.
-/

/-- Record `id` of the object at `m` is ordered before thread event `v`: a thread operation
happens before `v`; an asynchronous update belongs to a phase observed by a wait that happens
before `v`. -/
def RecordBefore (X : Execution) (m : Loc) (id : AsyncCopy.Ref) (v : EvId) : Prop :=
  (∃ e, id = .thread e ∧ baseCausality L X e v) ∨
  ∃ w, MBarrier.UpdateBeforeWait (X.objects m) id (.thread w) ∧ baseCausality L X w v

/-- The operation lies inside its object lifetime. An initialization happens after every
earlier invalidation; another operation is ordered after the initialization of its lifetime
and before that lifetime's invalidation, if any.
Bulk-copy completion accesses the mbarrier through the generic proxy. -/
def ObjectPublished (X : Execution) (m : Loc) (r : MBarrier.Record AsyncCopy.Ref) : Prop :=
  ((∃ n, r.action = .init n) ∧
    ∀ v, X.MbInval v m → MBarrier.Before (X.objects m) (.thread v) r.id →
      baseCausality L X v r.id.issuer) ∨
  ∃ i count, X.MbInit i m count ∧
    MBarrier.InitBefore (X.objects m) (.thread i) r.id ∧
    InitPublished L X i r.id.issuer m ∧
    ∀ v, X.MbInval v m → MBarrier.InitBefore (X.objects m) (.thread i) (.thread v) →
      r.id ≠ .thread v → RecordBefore L X m r.id v

/-- The mbarrier and bulk-copy safety check. It fails when an object record faults, a record lies
outside its object lifetime (`ObjectPublished`), a memory access to an object's bytes is ordered
neither before its initialization nor after the invalidation that ends that lifetime, two
`cp.async` operations of one group copy to an overlapping location (`CpAsyncOverlap`), or the
destination range of a `.cp_mask` copy covers an unallocated byte (`MaskedRangeUnalloc`). -/
def TmaUnsafe (mem0 : Mem0) (X : Execution) : Prop :=
  (∃ m r, r ∈ X.objects m ∧ r.fault.isSome) ∨
  (∃ m r, r ∈ X.objects m ∧ ¬ ObjectPublished L X m r) ∨
  (∃ e a w i m c l, X.Intent e a w ∧ X.MbInit i m c ∧ a.Covers l ∧
    Acc.Covers { loc := m, size := 8 } l ∧ ¬ modelCausality L X l e (.thread i) ∧
    ¬ ∃ v, X.MbInval v m ∧ MBarrier.InitBefore (X.objects m) (.thread i) (.thread v) ∧
      modelCausality L X l (.thread v) e) ∨
  CpAsyncOverlap X ∨ MaskedRangeUnalloc mem0 X

/-! ## ERR-CLC-REQUEST-AFTER-FAILURE — a request after an observed failure
Statement: An execution is unsafe when a CLC request does not precede, in base causality order
  (`baseCausality`), a query in its CTA that observes a failed cancellation.

Defs: ClcUnsafe

Source:
- §9.7.15.18 (request after observed failure)

Direction: stricter

Applies: Actual CLC issues and response observations

Premises: A request can follow an observed failure in its CTA.

Effect: Unsafe check. Outstanding response footprints also participate in races, and each target's
  notification is a use of its shared memory (ERR-SHARED-LIFETIME). The response mbarrier of each
  target CTA is an mbarrier operand of the request (`UsesMbar`): its initialization is
  ERR-MBAR-UNINITIALIZED and its storage ERR-UNALLOCATED-ACCESS.

Review: For the failure condition, requiring the issue to precede in baseCausality every failed
  observation of its CTA is a sufficient condition, and unordered issue/observation pairs are
  rejected.
-/
/-- The CLC safety check fails: a request does not precede a failed cancellation query of its
CTA in base causality order (`baseCausality`). -/
def ClcUnsafe (L : Launch) (X : Execution) : Prop :=
  ∃ i s targets q pc r, X.ClcIssue i s targets ∧
    X.get q = some ⟨pc, .clcQuery .isCanceled r⟩ ∧ r.firstCta = none ∧
    SameCta L i.1 q.1 ∧ ¬ baseCausality L X i q

/-! ## ERR-BARRIER-MISMATCH — divergent barrier collectives
Statement: An execution is unsafe when two lanes of a warp at their k-th barrier instruction
  disagree on the barrier, the thread count or the form.

Defs: BarArriveMismatch, BarMismatch

Source:
- §9.7.15.1: "barrier{.cta} instruction causes executing thread to wait for all non-exited threads
    from its warp and marks warps’ arrival at barrier"
- §9.7.15.1: "All threads in warp (except for those have exited) must execute barrier{.cta}
    instruction in convergence."
- §9.7.15.1: "Different warps may execute different forms of the barrier{.cta} instruction using the
    same barrier name and thread count."
- EXT-BAR-PARTICIPANTS

Direction: reading

Applies: Warp collective arrivals of either form

Premises: Lanes of a warp at their `k`-th barrier instruction disagree on the barrier, count or form
  (sync or arrive).

Effect: Safety rejection. Independent IDs and different generations are not compared. The source
  instruction of an aligned barrier and the exit of a participant before an aligned whole-CTA
  barrier are ERR-ALIGNED-MISMATCH.

Review: A warp arrives as one unit, so its lanes must agree on the resource and count. Guards of
  aligned instructions are ERR-NONUNIFORM-GUARD. Different warps are not compared by source
  position. The participants of one generation execute "the same barrier{.cta} instruction" when
  they use the same barrier name and thread count (EXT-BAR-PARTICIPANTS). The barrier resource
  compares these. An arrival whose count differs from its generation's is a fault
  (`CtaBarrier.Error.countMismatch`, OBJ-CTA-BARRIER-STATE, rejected by `CtaBarFault`,
  ERR-CTA-BARRIER), and the name is the generation's. The clause for `bar.arrive`
  (`BarArriveMismatch`) needs a `bar.arrive` event, so it rejects nothing in an execution without
  one. The lanes of a warp at their `k`-th barrier instruction (either form) must agree on the form
  as well: the text gives no meaning to one warp arrival made of `bar.sync` and `bar.arrive` lanes
  (stricter).

### EXT-BAR-PARTICIPANTS — the participants of an aligned barrier or setmaxnreg

Statement: The manual's "same instruction" sentences for an aligned `barrier{.cta}` and for
  `setmaxnreg` are read in two parts. (1) Between different warps, "the same" `barrier{.cta}`
  instruction means the same barrier name and thread count, and "the same" `setmaxnreg` instruction
  means the same direction and register count. The lanes of one warp execute one instruction at one
  source position. (2) For an aligned `bar.sync`, `bar.arrive` or `bar.red`, "all threads in CTA"
  means the threads that participate in the barrier generation, that is, the count's worth of warps
  that arrive at it. A thread that does not participate (for example a warp that has another role
  and uses another barrier or count) need not execute the barrier. For an aligned barrier without a
  thread count the participants are all threads of the CTA.

Source:
- §9.7.15.1: "Instruction barrier{.cta} has optional .aligned modifier. When specified, it indicates
    that all threads in CTA will execute the same barrier{.cta} instruction."
- §9.7.15.1: "In conditionally executed code, an aligned barrier{.cta} instruction should only be
    used if it is known that all threads in CTA evaluate the condition identically, otherwise
    behavior is undefined."
- §9.7.15.1: "All threads in warp (except for those have exited) must execute barrier{.cta}
    instruction in convergence."
- §9.7.15.1: "Different warps may execute different forms of the barrier{.cta} instruction using the
    same barrier name and thread count. One example mixes barrier{.cta}.sync and
    barrier{.cta}.arrive to implement producer/consumer models."
- §9.7.15.1 (its producer/consumer example: `bar.arrive 0, 64` and `bar.sync 0, 64` executed by 64
    threads of a larger CTA)
- §9.7.21.5: "The same setmaxnreg instruction must be executed by all warps in a warpgroup ."
- §9.7.21.5: "The mandatory .sync qualifier indicates that setmaxnreg instruction causes the
    executing thread to wait until all threads in the warp execute the same setmaxnreg instruction
    before resuming execution."

Why it is not spec text: (1) The text does not say whether "the same instruction" is one position
  in the program or one barrier or request. Read as one position, warps of different roles, each
  running its own code, could not synchronize on a named barrier or adjust their registers
  together, and the text's producer/consumer example, in which different warps execute
  `barrier{.cta}.arrive` and `barrier{.cta}.sync` (two instructions) on one barrier, would be
  undefined. The text names the barrier name and thread count as what different warps must share.
  (2) Read literally, "all threads in CTA" would make `bar.sync b, n` with `n` below the CTA size
  undefined whenever some CTA thread executes none; the ISA's own example and the explicit
  participant count show that this is not meant, but the text does not restate the clause for the
  participants.

Direction: reading

Effect: ERR-ALIGNED-MISMATCH checks that the lanes of one warp execute their aligned barrier at one
  source position, and that no participant of an aligned barrier without a thread count exits before
  it; the exit of a thread before a barrier with a thread count is not reported as undefined. The
  guard of a guarded aligned barrier is compared among the lanes of one warp (ERR-NONUNIFORM-GUARD).
  Between warps, ERR-BARRIER-MISMATCH and ERR-SETMAXNREG compare only the barrier and count or the
  direction and count.
  If "the same instruction" means one position, a program whose warps reach one barrier generation
  or one warpgroup request from different positions is undefined and is accepted. A divergence
  between a participant and a non-participant is not flagged. If the literal reading of "all
  threads in CTA" holds, such programs are undefined and are accepted. Disclosed by every kernel
  whose statement names `Op.barSync`, `Op.barSyncN`, `Op.barArrive` or `Op.setMaxReg`: BlockSum,
  FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, TcGemm.
-/

/-- A `bar.arrive` lane disagrees with a lane of its warp at the same barrier ordinal on the
barrier, count or form. -/
def BarArriveMismatch (X : Execution) : Prop :=
  ∃ g h i j id id' count count' mode' pc pc', SameWarp L g h ∧
    X.get (g, i) = some ⟨pc, .bar id count .arrive⟩ ∧
    X.get (h, j) = some ⟨pc', .bar id' count' mode'⟩ ∧
    ((X.tr g).take i).countP Execution.isBar = ((X.tr h).take j).countP Execution.isBar ∧
    (id ≠ id' ∨ count ≠ count' ∨ mode' ≠ .arrive)

/-- The barrier divergence check fails: lanes of a warp at their `k`-th barrier instruction
disagree on the barrier, count or form. -/
def BarMismatch (X : Execution) : Prop :=
  (∃ g h i j id id' count count' pc pc', SameWarp L g h ∧
    X.IsBarrier (g, i) id count pc ∧ X.IsBarrier (h, j) id' count' pc' ∧
    ((X.tr g).take i).countP Execution.isBar = ((X.tr h).take j).countP Execution.isBar ∧
    (id ≠ id' ∨ count ≠ count')) ∨
  BarArriveMismatch L X

/-! ## ERR-UNDEFINED-INSTRUCTION — instruction faults
Statement: An execution that contains an undefined-behaviour event is unsafe. Such events come from
  the "behavior is undefined" sentences of the instruction descriptions, from instruction forms that
  the model has no rule for, and from the model's checks that are stricter than the text.

Defs: HasUb

Source:
- no ISA section (the model's own accounting rule: an event of kind `ub` makes an execution unsafe)
- §9.7: "behavior is undefined"
- ERR-FAULT-REASON (an instruction form without a rule, `noRule`, and the checks that are stricter
    than the text are also faults)

Direction: stricter

Applies: Instruction fault events

Premises: An event has kind ub.

Effect: Safety rejection.
-/

/-- Some event of `X` is an undefined-behaviour event (kind `ub`). -/
def HasUb (X : Execution) : Prop := ∃ e pc f, X.get e = some ⟨pc, .ub f⟩


/-! ## ERR-UNALLOCATED-ACCESS — allocation checks
Statement: An execution is unsafe when an access touches a byte that is not allocated at launch.
  This covers thread loads, including non-coherent loads, thread stores and the footprints of
  asynchronous accesses, pending ones and tensor prefetch reads included. It also covers the eight
  bytes of every mbarrier object that an instruction names as an operand.

Defs: Unalloc

Source:
- §8.2.6 (the initial write W0 covers the allocated memory); no ISA sentence makes an access to an
    unallocated byte undefined
- §9.7.15.16: "An mbarrier object is an opaque object in memory"

Direction: stricter

Applies: Bytes touched by load/store events, including nc, the footprints of asynchronous
  accesses, pending ones and tensor prefetch reads (EXT-PREFETCH-PENDING) included, and the eight
  bytes of each mbarrier operand (`UsesMbar`: arrivals, polls, initializations, invalidations, the
  completion mbarriers of linear copies and tensor loads, `cp.async.mbarrier.arrive`, the targets of
  `tcgen05.commit` and the response mbarriers of the target CTAs of a CLC request)

Premises: A touched location is unallocated in mem0.

Effect: Safety rejection.
-/

/-- Some access of `X`, pending or performed, touches a byte that is unallocated in `mem0`, or an
mbarrier operand of some event covers such a byte. -/
def Unalloc (mem0 : Mem0) (X : Execution) : Prop :=
  (∃ e a l, X.MemTouches e a ∧ a.Covers l ∧ mem0 l = none) ∨
  ∃ e m l, X.UsesMbar e m ∧ Acc.Covers { loc := m, size := 8 } l ∧ mem0 l = none

end

end PTX
