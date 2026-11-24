-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.Barrier

@[expose] public section

namespace PTX
noncomputable section

/-! ## MEM-RELEASE-ACQUIRE — release and acquire patterns
Statement: A release pattern synchronizes with an acquire pattern when the acquire pattern's strong
  read reads every one of its bytes from the release pattern's strong write, the two have the same
  nonempty footprint and mutually including scopes, and the scopes of the pattern's first and last
  instructions include each other's thread. A release pattern is a release write, or a release or
  acquire-release fence followed in program order by a strong write; an acquire pattern is an
  acquire read, or a strong read followed in program order by an acquire or acquire-release fence.

Defs: synchronizesWith, synchronizesWith_iff_of_not_rmw, ReleaseHead, AcquireTail, StrongRead,
  FenceSync, not_fenceSync_of_noFence

Source:
- §8.9.4: "A release pattern X synchronizes with an acquire pattern Y, if a write operation in X
    precedes a read operation in Y in observation order , and the first operation in X and the last
    operation in Y are morally strong ."
- §8.9.2: "A write W precedes a read R in observation order if: R and W are morally strong and R
    reads the value written by W, or For some atomic operation Z, W precedes Z and Z precedes R in
    observation order ."
- §8.8: "A release pattern on a location M consists of one of the following: A release operation on
    M E.g.: st.release [M]; or atom.release [M]; or mbarrier.arrive.release [M];"
- §8.8: "Or a release or acquire-release memory fence followed by a strong write on M in program
    order E.g.: fence.release; st.relaxed [M]; or fence.release; atom.relaxed [M];"
- §8.8: "An acquire pattern on a location M consists of one of the following: An acquire operation
    on M E.g.: ld.acquire [M]; or atom.acquire [M]; or mbarrier.test_wait.acquire [M];"
- §8.8: "Or a strong read on M followed by an acquire memory fence in program order E.g.: ld.relaxed
    [M]; fence.acquire; or atom.relaxed [M]; fence.acquire;"
- §8.8: "Note that while atomic reductions conceptually perform a strong read as part of its
    read-modify-write sequence, this strong read does not form an acquire pattern."
- §8.7 (morally strong)
- §8.2 (Table 20): "read operation All variants of ld instruction and atom instruction (but not red
    instruction)."
- §9.7.15.4 (fence)
- §9.7.10.8 (ld)
- §9.7.10.11 (st)
- §9.7.15.5 (atom)
- §9.7.15.6 (red)

Direction: stricter

Applies: Generic-proxy release and acquire patterns of thread loads, stores, atomic
  read-modify-writes and thread fences, with mutually covering scopes

Premises: Equal nonempty footprints; every byte of the read reads from the pattern's write; the
  write and the read are strong with scopes that include each other's thread; the first instruction
  of the release pattern and the last of the acquire pattern have scopes that include each other's
  thread; a fence precedes its write, or follows its read, in program order.

Effect: Adds a synchronization edge to baseCausality from the first instruction of each release
  pattern to the last instruction of each acquire pattern under the premises (`synchronizesWith`
  when both are memory operations, `FenceSync` when one is a fence); every read keeps the ordinary
  read, allocation and race checks. `synchronizesWith` is the pattern of a release write read
  directly by an acquire read. `FenceSync` is the pattern with a release or acquire-release fence at
  its start, an acquire or acquire-release fence at its end, or both, and it also carries the
  `fence.sc` synchronization of MEM-FENCE-SC. The edge starts at the first instruction of the
  release pattern and ends at the last instruction of the acquire pattern, so it orders the
  operations before the first instruction (§8.8: "Any memory synchronization established by a
  release pattern only affects operations occurring in program order before the first instruction in
  that pattern.") and those after the last one.

Review: The acquire read must read from the release pattern's write itself. These forms of
  synchronization give no edge, which keeps the model stricter: synchronization through a chain of
  atomic operations (§8.9.2 observation order), the patterns of a release operation followed by a
  strong write and of a strong read followed by an acquire operation, the asynchronous patterns (the
  model treats `.relaxed` bulk copies as weak, THREAD-TMA), and a relaxed `atom` followed by an
  acquire fence. The `atom` and `red` events without acquire semantics are the same, and a `red`
  does not form an acquire pattern, so only an `atom` with `.acquire` or `.acq_rel` counts as an
  atomic strong read (`StrongRead`). A `.relaxed` operation neither releases nor acquires; a
  `fence.sc` is neither a release nor an acquire fence here, since the text names only release and
  acquire-release fences, and orders through MEM-FENCE-SC. Strong accesses are those of
  `Acc.Strong`, `.volatile` and `.mmio` included (THREAD-ACCESS).
-/
/-! ## MEM-FENCE-SC — the Fence-SC order
Statement: The `fence.sc` events of an execution are ordered by an acyclic order that relates every
  two morally strong `fence.sc` and agrees with causality, and a `fence.sc` synchronizes with every
  morally strong `fence.sc` that follows it in this order.

Defs: ScStrong, FenceScSync, FenceScOk, fenceScOk_of_noSc

Source:
- §8.9.3: "The Fence-SC order is an acyclic partial order, determined at runtime, that relates every
    pair of morally strong fence.sc operations."
- §8.9.4: "A fence.sc operation X synchronizes with a fence.sc operation Y if X precedes Y in the
    Fence-SC order."
- §8.10.2: "Fence-SC order cannot contradict causality order . For a pair of morally strong fence.sc
    operations F1 and F2, if F1 precedes F2 in causality order , then F1 must precede F2 in Fence-SC
    order."
- §8.7 (morally strong)
- §9.7.15.4: "On sm_70 and higher membar is a synonym for fence.sc"

Direction: reading

Applies: Thread fences with `.sc` semantics (`fence.sc`, `membar`)

Premises: Two `fence.sc` are morally strong: one thread executes both, or the scope of each includes
  the other's thread.

Effect: `Execution.fenceSC` is the order; `FenceScOk` constrains it (CORRECT-CONSISTENT), and its
  edges between morally strong `fence.sc` enter baseCausality through `FenceSync`.

Review: The order is part of the execution and is chosen with it. It is constrained against
  baseCausality (base causality), which the text's causality order contains, so the constraint is
  weaker than the text's: the model admits Fence-SC orders, and with them executions, that §8.10.2
  excludes, namely those that order two `fence.sc` against a causality path that baseCausality does
  not contain. The direction is therefore a reading. It is safe because a weaker constraint only
  adds executions: every execution the text allows satisfies `FenceScOk`, and the safety checks
  reject an unsafe added execution as they would any other, so a kernel proved safe here is safe
  under the text's order. An execution without a `fence.sc` satisfies `FenceScOk` for any order
  (`fenceScOk_of_noSc`).
-/

/-- `e` and `f` are morally strong `fence.sc` events (§8.7): one thread executes both, or the scope
of each includes the other's thread. -/
def ScStrong (L : Launch) (X : Execution) (e f : EvId) : Prop :=
  ∃ s s', X.ThreadFence e .sc s ∧ X.ThreadFence f .sc s' ∧
    (e.1 = f.1 ∨ (MbarScopeIncludes L s e.1 f.1 ∧ MbarScopeIncludes L s' f.1 e.1))

/-- `e` synchronizes with `f` (§8.9.4): two morally strong `fence.sc`, `e` before `f` in the
Fence-SC order. -/
def FenceScSync (L : Launch) (X : Execution) (e f : EvId) : Prop :=
  ScStrong L X e f ∧ X.fenceSC e f

/-- The Fence-SC order of `X` is acyclic on morally strong `fence.sc` events, relates every two of
them, and contains the causality relation `causal` between them (§8.9.3, §8.10.2). -/
structure FenceScOk (L : Launch) (X : Execution) (causal : EvId → EvId → Prop) : Prop where
  total : ∀ e f, ScStrong L X e f → e ≠ f → X.fenceSC e f ∨ X.fenceSC f e
  acyclic : ∀ e, ¬ Relation.TransGen (FenceScSync L X) e e
  causal : ∀ e f, ScStrong L X e f → causal e f → X.fenceSC e f

/-- An execution without `fence.sc` satisfies `FenceScOk` for any order. -/
theorem fenceScOk_of_noSc {L : Launch} {X : Execution} {causal : EvId → EvId → Prop}
    (h : ∀ e s, ¬ X.ThreadFence e .sc s) : FenceScOk L X causal where
  total _ _ hs := by obtain ⟨s, -, h1, -⟩ := hs; exact absurd h1 (h _ _)
  acyclic e hc := by
    cases hc with
    | single hs => obtain ⟨⟨s, -, h1, -⟩, -⟩ := hs; exact h _ _ h1
    | tail _ hs => obtain ⟨⟨s, -, h1, -⟩, -⟩ := hs; exact h _ _ h1
  causal _ _ hs := by obtain ⟨s, -, h1, -⟩ := hs; exact absurd h1 (h _ _)

/-- Release/acquire synchronization from `e` to `f` (§8.9.4): `e` writes with release semantics
(a release store or the write of a releasing atomic read-modify-write) and `f` reads with acquire
semantics (an acquire load or the read of an acquiring `atom`), with the same nonempty footprint,
`f` reads every byte from `e`, and the scope of each includes the thread of the other. -/
def synchronizesWith (L : Launch) (X : Execution) (e f : EvId) : Prop :=
  ∃ a b bs cs, X.MemWrites (.thread e) a bs ∧ X.MemReads (.thread f) b cs ∧
    a.release = true ∧ b.acquire = true ∧ a.loc = b.loc ∧ a.size = b.size ∧
    0 < b.size ∧ MbarScopeIncludes L a.scope e.1 f.1 ∧
    MbarScopeIncludes L b.scope f.1 e.1 ∧
    ∀ k < b.size, X.rf (.thread f) k = some (.thread e)

/-- Between two events that are not atomic read-modify-writes, `synchronizesWith` is the release
store and acquire load pattern it was before THREAD-ATOMIC. -/
theorem synchronizesWith_iff_of_not_rmw {L : Launch} {X : Execution} {e f : EvId}
    (he : ∀ pc a o n, X.get e ≠ some ⟨pc, .rmw a o n⟩)
    (hf : ∀ pc a o n, X.get f ≠ some ⟨pc, .rmw a o n⟩) :
    synchronizesWith L X e f ↔ ∃ a b bs cs, X.Writes e a bs ∧ X.Reads f b cs ∧
      a.release = true ∧ b.acquire = true ∧ a.loc = b.loc ∧ a.size = b.size ∧
      0 < b.size ∧ MbarScopeIncludes L a.scope e.1 f.1 ∧
      MbarScopeIncludes L b.scope f.1 e.1 ∧
      ∀ k < b.size, X.rf (.thread f) k = some (.thread e) := by
  simp only [synchronizesWith, Execution.memWrites_thread_iff_of_not_rmw he,
    Execution.memReads_thread_iff_of_not_rmw hf]


/-- `e` begins a release pattern whose strong write is `w` with footprint `a`, and `s` is the
scope of `e`: `e` is the release write `w` itself, or a release or acquire-release fence before `w`
in `w`'s thread (§8.8). -/
def ReleaseHead (X : Execution) (e w : EvId) (a : Acc) (s : MbarScope) : Prop :=
  (e = w ∧ a.release = true ∧ s = a.scope) ∨
    ∃ sem, X.ThreadFence e sem s ∧ sem.releases = true ∧ e.1 = w.1 ∧ e.2 < w.2

/-- `f` ends an acquire pattern whose strong read is `r` with footprint `b`, and `s` is the scope
of `f`: `f` is the acquire read `r` itself, or an acquire or acquire-release fence after `r` in
`r`'s thread (§8.8). -/
def AcquireTail (X : Execution) (r f : EvId) (b : Acc) (s : MbarScope) : Prop :=
  (f = r ∧ b.acquire = true ∧ s = b.scope) ∨
    ∃ sem, X.ThreadFence f sem s ∧ sem.acquires = true ∧ r.1 = f.1 ∧ r.2 < f.2

/-- `r` is a strong read operation (§8.2 Table 20, §8.4) that can be part of an acquire pattern: a
strong load, or the read of an `atom` with acquire semantics. A `red` is never one (§8.8). -/
def StrongRead (X : Execution) (r : EvId) (b : Acc) (cs : List (Option Byte)) : Prop :=
  (X.Reads r b cs ∧ b.Strong) ∨ ∃ n, X.Rmw r b cs n ∧ b.acquire = true

/-- The synchronization of a release pattern starting at `e` with an acquire pattern ending at `f`
where at least one of them is a fence (§8.8, §8.9.4), or of two `fence.sc` ordered by the Fence-SC
order (MEM-FENCE-SC). -/
def FenceSync (L : Launch) (X : Execution) (e f : EvId) : Prop :=
  (∃ w r a b bs cs se sf, X.MemWrites (.thread w) a bs ∧ a.Strong ∧ StrongRead X r b cs ∧
    ReleaseHead X e w a se ∧ AcquireTail X r f b sf ∧
    (∃ sem s, X.ThreadFence e sem s ∨ X.ThreadFence f sem s) ∧
    a.loc = b.loc ∧ a.size = b.size ∧ 0 < b.size ∧
    MbarScopeIncludes L a.scope w.1 r.1 ∧ MbarScopeIncludes L b.scope r.1 w.1 ∧
    MbarScopeIncludes L se e.1 f.1 ∧ MbarScopeIncludes L sf f.1 e.1 ∧
    ∀ k < b.size, X.rf (.thread r) k = some (.thread w)) ∨
  FenceScSync L X e f

/-- An execution without thread fences has no fence synchronization. -/
theorem not_fenceSync_of_noFence {L : Launch} {X : Execution}
    (h : ∀ e sem s, ¬ X.ThreadFence e sem s) (e f : EvId) : ¬ FenceSync L X e f := by
  rintro (⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ⟨sem, s, hf | hf⟩, -⟩ | ⟨⟨s, -, hs, -⟩, -⟩)
  · exact h _ _ _ hf
  · exact h _ _ _ hf
  · exact h _ _ _ hs

end
end PTX
