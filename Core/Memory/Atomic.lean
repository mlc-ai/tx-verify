-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Safety
public import Core.Async.Tensor.TensorReduce
public import Core.Async.BulkExecution

@[expose] public section

/-!
# Atomicity of read-modify-write operations

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

variable (L : Launch)

/-! ## MEM-ATOMICITY — atomicity of read-modify-write operations
Statement: Two atomic read-modify-write operations of the same footprint that are morally strong
  never read a byte from the same write, and never both read a byte from the initial write W0.
  Reads-from among morally strong atomic read-modify-writes of one footprint has no cycle. The
  atomic read-modify-writes are the elements of `atom` and `red` and of tensor and linear
  reductions.

Defs: RmwId, RmwId.newRef, Execution.oldRf, Execution.RmwAt, RmwStrong, AtomicReads, AtomicUnique,
  AtomicAcyclic, AtomicOk, rmwStrong_tensor, atomicReads_of_reduceReads, reduceUnique_of_atomic,
  reduceAcyclic_of_atomic

Source:
- §8.10.3: "Atomicity of read-modify-write (RMW) operations When an atomic operation A and a write W
    overlap and are morally strong , then the following two communications cannot both exist in the
    same execution, for the set of bytes accessed by both A and W: A reads any byte from a write W’
    that precedes W in coherence order . A follows W in coherence order ."
- §8.10.3: "Atomicity is guaranteed when the operations are morally strong ."
- §8.10.3: "Atomicity is not guaranteed if the operations are not morally strong ."
- §8.9.6: "Two overlapping write operations are related in coherence order if they are morally
    strong or if they are related in causality order ."
- §9.7.15.5 (atom): "Two atomic operations ( atom or red ) are performed atomically with respect to
    each other only if each operation specifies a scope that includes the other. When this condition
    is not met, each operation observes the other operation being performed as if it were split into
    a read followed by a dependent write."
- §9.7.15.6 (red)
- ERR-DATA-RACE (`MorallyStrong`)
- §9.7.10.28.4.2: "These are element-wise atomic at the specified scope."
- THREAD-ATOMIC
- EXT-TMA-REDUCE-ATOMIC

Direction: reading

Applies: Every pair of performed atomic read-modify-writes (`RmwId`) of one footprint that are
  morally strong

Premises: Both operations are performed at the same footprint (`RmwAt`) and are morally strong
  (`RmwStrong`: ERR-DATA-RACE's `MorallyStrong` of their writes, which requires the same proxy,
  scopes that include each other's thread or the same thread, and complete overlap).

Effect: Execution constraint in Consistent.atomic; the reads-from edges among such operations are
  coherence edges of CORRECT-FINAL (`CoStep`). An atomic read-modify-write is one operation that
  reads and writes its footprint: a thread's `.rmw` event (one per element of an `atom` or `red`,
  THREAD-ATOMIC), one element of a tensor reduction (EXT-TMA-REDUCE-ATOMIC), whose read of byte `k`
  is its `.old` stage and whose write of byte `k` is its `.write` stage, or one element of a linear
  reduction (`cp.reduce.async.bulk`, `red.async`), whose old-value read and write are its stages
  `.old (.elem j)` and `.write (.elem j)` (§9.7.10.28.4.2: "These are element-wise atomic at the
  specified scope."). The model imposes two consequences of §8.10.3 and records no coherence order.
  Let `A1` and `A2` be distinct morally strong atomic operations of one footprint. They are related
  in coherence order (§8.9.6), say `A1` before `A2`. The model reads an atomic operation as
  following, in coherence order, the write it reads a byte from, and W0 precedes every write. If
  both read byte `k` from the same write `W’`, or both from W0, then `W’` precedes `A1`, so `A2`
  reads a byte from a write that precedes `A1` while following `A1`, which §8.10.3 forbids with `A =
  A2` and `W = A1` (`AtomicUnique`). Every reads-from edge between them goes forward in coherence
  order, a strict order, so these edges have no cycle (`AtomicAcyclic`), which also excludes an
  operation reading its own write. Together they make the morally strong atomic operations of one
  footprint a single reads-from chain per byte.

Review: Operations that are not morally strong are not constrained: §9.7.15.5 says they observe each
  other as a read followed by a dependent write, and Litmus Test 2 allows `x == 1`. Two such
  operations that are unordered are a race (ERR-DATA-RACE). The model imposes no constraint between
  an atomic operation and a morally strong write that is not atomic, which needs the coherence
  order; no atomicity across footprints of different sizes (§8.7.2), whose partial overlaps
  ERR-MIXED-SIZE rejects; and no synchronization that §8.9 derives from chains of atomic operations
  (MEM-RELEASE-ACQUIRE gives an edge only for a direct read). Each of these leaves more executions
  possible, which is conservative for safety, results and progress.
-/

/-- An atomic read-modify-write operation: the `.rmw` event `e` of a thread (an element of an
`atom` or `red`), element `(x, y)` of the tensor reduction issued by `i`, or element `j` of the
linear reduction issued by `i`. -/
inductive RmwId where
  | thread (e : EvId)
  | tensor (i : EvId) (x y : Nat)
  /-- Element `j` of the linear reduction (`cp.reduce.async.bulk`, `red.async`) issued by `i`. -/
  | copy (i : EvId) (j : Nat)
  deriving DecidableEq

/-- The write of byte `k` of the operation. -/
def RmwId.newRef : RmwId → Nat → AsyncCopy.Ref
  | .thread e, _ => .thread e
  | .tensor i x y, k => .async i (.write (.store x y k))
  | .copy i j, _ => .async i (.write (.elem j))

/-- The source of byte `k` of the old value the operation read: a write, or `none` for W0. -/
def Execution.oldRf (X : Execution) : RmwId → Nat → Option AsyncCopy.Ref
  | .thread e, k => X.rf (.thread e) k
  | .tensor i x y, k => X.rf (.async i (.old (.store x y k))) 0
  | .copy i j, k => X.rf (.async i (.old (.elem j))) k

/-- `p` is a performed atomic read-modify-write of the `n` bytes from `l`. -/
def Execution.RmwAt (X : Execution) : RmwId → Loc → Nat → Prop
  | .thread e, l, n => ∃ a old new, X.Rmw e a old new ∧ a.loc = l ∧ a.size = n
  | .tensor i x y, l, n => ∃ fp, TensorStore.Reduced X i x y fp ∧ fp.loc = l ∧ fp.size = n
  | .copy i j, l, n => ∃ s r a, X.Copy i s ∧ s.writes = .reduce r ∧ s.elems[j]? = some a ∧
      ((X.async.copies i).elemWrites j).isSome ∧ a.loc = l ∧ a.size = n

/-- The atomic operations `p` and `q` are morally strong (§8.7): ERR-DATA-RACE's `MorallyStrong` of
the writes of their first bytes. -/
def RmwStrong (X : Execution) (p q : RmwId) : Prop :=
  ∃ a b, X.Intent (p.newRef 0) a true ∧ X.Intent (q.newRef 0) b true ∧
    MorallyStrong L X (p.newRef 0) (q.newRef 0) a b

/-- The atomic operation `q` read a byte of its old value from the atomic operation `p`; both are
performed at one footprint and are morally strong. -/
def AtomicReads (X : Execution) (p q : RmwId) : Prop :=
  ∃ l n, X.RmwAt p l n ∧ X.RmwAt q l n ∧ RmwStrong L X p q ∧
    ∃ k k', k < n ∧ X.oldRf q k = some (p.newRef k')

/-- Two distinct morally strong atomic operations of one footprint never read a byte from the same
write, and never both from W0 (§8.10.3). -/
def AtomicUnique (X : Execution) : Prop :=
  ∀ p q l n k, X.RmwAt p l n → X.RmwAt q l n → p ≠ q → RmwStrong L X p q → k < n →
    X.oldRf p k ≠ X.oldRf q k

/-- Reads-from among morally strong atomic operations of one footprint has no cycle (§8.10.3). -/
def AtomicAcyclic (X : Execution) : Prop :=
  ∀ p, ¬ Relation.TransGen (AtomicReads L X) p p

/-- The atomic operations of `X` are atomic with respect to each other (MEM-ATOMICITY). -/
structure AtomicOk (X : Execution) : Prop where
  unique : AtomicUnique L X
  acyclic : AtomicAcyclic L X

/-- Two performed elements of tensor reductions at one footprint are morally strong, when every
tensor reduction has its issue event and every issuing thread is a thread of the launch. -/
theorem rmwStrong_tensor {X : Execution} (hS : TensorStoreOk L X)
    (hout : ∀ g, L.threads ≤ g → X.tr g = []) {i j : EvId} {x y x' y' : Nat} {fp : Acc}
    (hp : TensorStore.Reduced X i x y fp) (hq : TensorStore.Reduced X j x' y' fp) :
    RmwStrong L X (.tensor i x y) (.tensor j x' y') := by
  obtain ⟨o, red, loc, ho, hred, hloc, rfl, -⟩ := hp
  obtain ⟨o', red', loc', ho', hred', hloc', hfp, -⟩ := hq
  obtain ⟨⟨addr, hi⟩, -⟩ := hS i o ho
  obtain ⟨⟨addr', hj⟩, -⟩ := hS j o' ho'
  have hlt : ∀ {k : EvId} {a : Nat} {s : TensorStore.Spec}, X.TensorStoreIssue k a s →
      k.1 < L.threads := by
    intro k a s ⟨pc, h⟩
    by_contra hge
    simp [Execution.get, hout k.1 (Nat.le_of_not_lt hge)] at h
  refine ⟨{ loc := loc, size := 1 }, { loc := loc', size := 1 }, ⟨rfl, o.spec, addr, hi, hloc, rfl⟩,
    ⟨rfl, o'.spec, addr', hj, hloc', rfl⟩, Or.inr ⟨⟨⟨addr, o.spec, red, hi, hred⟩, ?_⟩,
      ⟨⟨addr', o'.spec, red', hj, hred'⟩, ?_⟩⟩, ?_, ?_⟩
  · exact ⟨hlt hi, hlt hj⟩
  · exact ⟨hlt hj, hlt hi⟩
  · have hn : ∀ {k : EvId} {a : Nat} {s : TensorStore.Spec}, X.TensorStoreIssue k a s →
        ¬ GenericCopy X k := by
      rintro k a s ⟨pc, h⟩ ⟨s', ⟨pc', h'⟩, -⟩
      rw [h] at h'
      cases h'
    exact ⟨fun h => absurd h (hn hi), fun h => absurd h (hn hj)⟩
  · refine ⟨_, _, ⟨addr, o.spec, red, loc, hi, hred, hloc, rfl⟩,
      ⟨addr', o'.spec, red', loc', hj, hred', hloc', rfl⟩, ?_⟩
    simp only [Acc.mk.injEq] at hfp
    exact ⟨hfp.1, hfp.2.1⟩

/-- A tensor reduction element that read a byte from another one, both performed at one footprint,
is an atomic read of MEM-ATOMICITY. -/
theorem atomicReads_of_reduceReads {X : Execution} (hS : TensorStoreOk L X)
    (hout : ∀ g, L.threads ≤ g → X.tr g = []) {fp : Acc} {p q : EvId × Nat × Nat}
    (h : TensorStore.ReduceReads X fp p q) :
    AtomicReads L X (.tensor p.1 p.2.1 p.2.2) (.tensor q.1 q.2.1 q.2.2) := by
  obtain ⟨hp, hq, k, k', hk, hrf⟩ := h
  exact ⟨fp.loc, fp.size, ⟨fp, hp, rfl, rfl⟩, ⟨fp, hq, rfl, rfl⟩,
    rmwStrong_tensor L hS hout hp hq, k, k', hk, hrf⟩

/-- EXT-TMA-REDUCE-ATOMIC: the reductions of one element read their old bytes uniquely. -/
theorem reduceUnique_of_atomic {X : Execution} (hA : AtomicUnique L X) (hS : TensorStoreOk L X)
    (hout : ∀ g, L.threads ≤ g → X.tr g = []) : TensorStore.ReduceUnique X := by
  intro fp p q k hp hq hne hk
  refine hA (.tensor p.1 p.2.1 p.2.2) (.tensor q.1 q.2.1 q.2.2) fp.loc fp.size k
    ⟨fp, hp, rfl, rfl⟩ ⟨fp, hq, rfl, rfl⟩ ?_ (rmwStrong_tensor L hS hout hp hq) hk
  intro h
  apply hne
  obtain ⟨p1, p2, p3⟩ := p
  obtain ⟨q1, q2, q3⟩ := q
  simp only [RmwId.tensor.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-- EXT-TMA-REDUCE-ATOMIC: reads among the reductions of one element have no cycle. -/
theorem reduceAcyclic_of_atomic {X : Execution} (hA : AtomicAcyclic L X)
    (hS : TensorStoreOk L X) (hout : ∀ g, L.threads ≤ g → X.tr g = []) :
    TensorStore.ReduceAcyclic X := by
  intro fp p hcyc
  apply hA (.tensor p.1 p.2.1 p.2.2)
  have key : ∀ a b, Relation.TransGen (TensorStore.ReduceReads X fp) a b →
      Relation.TransGen (AtomicReads L X) (.tensor a.1 a.2.1 a.2.2) (.tensor b.1 b.2.1 b.2.2) := by
    intro a b h
    induction h with
    | single h => exact .single (atomicReads_of_reduceReads L hS hout h)
    | tail _ h ih => exact .tail ih (atomicReads_of_reduceReads L hS hout h)
  exact key p p hcyc

end

end PTX
