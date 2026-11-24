-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.CtaBarrierExecution
public import Core.Sync.ClusterBarrierExecution
public import Core.Thread.Local
public import Core.MBarrier.AsyncMBarrier

@[expose] public section

/-!
# Barrier events and synchronization

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

variable (L : Launch)

/-! ## THREAD-BAR — barrier arrival

Statement: `bar.sync` and `bar.arrive` produce an arrival at one of the sixteen CTA barrier
  resources, with an optional participant count. The barrier number must be below 16 and an explicit
  count must be a multiple of 32, nonzero for `bar.arrive`; any other operand is a fault. A count
  equal to the CTA size, or zero on `bar.sync`, means every thread of the CTA.

Defs: barTmpl

Source:
- §9.7.15.1 (bar, barrier): "Source operand a specifies a logical barrier resource as an immediate
    constant or register with value 0 through 15 ."
- §9.7.15.1 (bar, barrier): "Note that a non-zero thread count is required for barrier{.cta}.arrive
    ."
- EXT-BAR-ZERO-COUNT

Direction: reading

Applies: bar.sync with omitted or explicit participant count; bar.arrive with its participant count

Premises: Barrier ID is below 16; an explicit count is a multiple of 32, and nonzero for
  `bar.arrive`.

Effect: Event production; completion is decided by the named resource history. The zero-count
  reading is EXT-BAR-ZERO-COUNT. A zero count of `bar.arrive` is a `badBarrier` fault, as is any
  other operand outside these ranges.

### EXT-BAR-ZERO-COUNT — `bar.sync b, 0` means every thread of the CTA

Statement: An explicit participant count of zero on `bar.sync` is read as every thread of the CTA,
  the same as an omitted count. A count equal to the CTA size has the same meaning.

Source:
- §9.7.15.1: "If no thread count is specified, all threads in the CTA participate in the barrier"
- §9.7.15.1: "When specifying a thread count, the value must be a multiple of the warp size"
- §9.7.15.1: "Note that a non-zero thread count is required for barrier{.cta}.arrive"
- §9.7.15.1: "Depending on operand b , either specified number of threads (in multiple of warp size)
    or all threads in the CTA participate in barrier{.cta} instruction."
- implementation cross-check: ptxas 13.2.51 targeting sm_100a emits identical SASS for
    `bar.sync 0, 0` and `bar.sync 0`

Why it is not spec text: The text requires a nonzero count only for `bar.arrive` and says nothing
  about the meaning of an explicit zero on `bar.sync`; zero is a multiple of the warp size, so the
  count may be read as zero participating threads (a barrier that no thread completes) as well as
  all threads.

Direction: reading

Effect: A program using `bar.sync b, 0` is accepted with the whole-CTA meaning; if the hardware
  meaning differed, that program's synchronization would be wrong. Disclosed by every kernel whose
  statement names `Op.barSyncN`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192,
  InklingRelDecode, RmsNorm.
-/

/-- The event of a `bar.sync` or `bar.arrive` (as selected by `mode`) in a thread: an arrival at
the named barrier resource with its participant count, or a fault for an invalid operand. -/
def barTmpl (L : Launch) (g : Nat) (t : TState) (a : Opnd) (count : Option Opnd)
    (mode : BarMode := .sync) : Tmpl :=
  match readBits L g t 32 a with
  | .error f => .ub f
  | .ok id =>
    if 16 ≤ id.toNat then .ub .badBarrier
    else match count with
      | none => .bar id.toNat (next t) none mode
      | some b => match readBits L g t 32 b with
        | .error f => .ub f
        | .ok n =>
          if n.toNat % 32 = 0 ∧ (mode = .arrive → n.toNat ≠ 0) then
            .bar id.toNat (next t) (if n.toNat = 0 ∨ n.toNat = L.block then none else some n.toNat)
              mode
          else .ub .badBarrier

/-! ## MEM-SCOPE — the threads a scope includes

Statement: The scope `.cta` of a strong operation by thread `g` includes the threads of the launch
  in the CTA of `g`, and `.cluster` includes those in the cluster of `g`. The scopes `.gpu` and
  `.sys` include every thread of the launch.

Defs: MbarScopeIncludes

Source:
- §8.5: "Each strong operation must specify a scope , which is the set of threads that may interact
    directly with that operation and establish any of the relations described in the memory
    consistency model."
- §8.5: ".cta The set of all threads executing in the same CTA as the current thread."
- §8.5: ".cluster The set of all threads executing in the same cluster as the current thread."
- §8.5: ".gpu The set of all threads in the current program executing on the same compute device as
    the current thread. This also includes other kernel grids invoked by the host program on the
    same compute device."
- §8.5: ".sys The set of all threads in the current program, including all kernel grids invoked by
    the host program on all compute devices, and all threads constituting the host program itself."

Direction: reading

Applies: The scope of every strong operation the model represents

Premises: Both threads are threads of the launch.

Effect: Determines which pairs of strong operations are morally strong (ERR-DATA-RACE) and which
  release/acquire pairs synchronize (MEM-RELEASE-ACQUIRE, MEM-MBAR-SYNCHRONIZES).

Review: The model executes one grid on one device and has no host threads. Every thread it
  represents is therefore a thread of the current program on the same compute device, so `.gpu` and
  `.sys` both include every thread of the launch. The reading is that the other grids and the host
  threads, which §8.5 also places in these scopes, perform no operation that interacts with the
  launch; EXT-LAUNCH orders the host's accesses before the kernel starts and after it ends.
-/

/-- Scope `scope` of thread `g` includes thread `h` (§8.5): the two threads of the launch are in
the same CTA for `.cta` and in the same cluster for `.cluster`; `.gpu` and `.sys` include every
thread of the launch. -/
def MbarScopeIncludes (scope : MbarScope) (g h : Nat) : Prop :=
  match scope with
  | .cta => SameCta L g h
  | .cluster => SameCluster L g h
  | .gpu | .sys => g < L.threads ∧ h < L.threads

/-! ## MEM-MBAR-SYNCHRONIZES — mbarrier release/acquire synchronization
Statement: A release arrival on an mbarrier synchronizes with a successful acquire wait that
  observes the arrival's phase, provided the scope of each operation includes the other thread. The
  accesses of the arriving thread before the arrival then happen before the accesses of the waiting
  thread after the wait.

Defs: ScopesMeet, MbarRelease, MSync

Source:
- §8.7: "each operation is strong and specifies a scope that includes the thread executing the other
    operation"
- §8.9.4 (synchronization)
- §9.7.15.16.16 (release arrival)
- §9.7.15.16.19 (acquire wait observes the completed phase)
- MEM-SCOPE (scopes, §8.5)
- OBJ-MBAR-OBSERVE

Direction: reading

Applies: Release arrivals and successful acquire waits on one mbarrier object, at CTA or cluster
  scope

Premises: Each scope includes the other participant; the arrival's actual object-history record
  belongs to the generation and phase observed by the wait; the source is at or before the arrival
  and the target follows the wait.

Effect: Adds baseCausality edges between thread events. The edges come from release arrivals and
  acquire waits at the instruction's scope.
-/

/-- `e` is an arrival on `m` with release semantics at scope `scope`. -/
def MbarRelease (X : Execution) (e : EvId) (m : Loc) (scope : MbarScope) : Prop :=
  ∃ tx count, X.Arrive e m tx count true scope

/-- An update by thread `g` with scope `us` and a wait by thread `h` with scope `ws` are morally
strong relative to each other: each scope includes the other thread (§8.7). -/
def ScopesMeet (us : MbarScope) (g : Nat) (ws : MbarScope) (h : Nat) : Prop :=
  MbarScopeIncludes L us g h ∧ MbarScopeIncludes L ws h g

/-- Mbarrier synchronization from `e` to `f` (§8.9.4): a release arrival `x` at or after `e` in
`e`'s thread is observed by a successful acquire wait `w`, the scope of each of `x` and `w`
includes the other's thread, and `f` follows `w` in `w`'s thread. -/
def MSync (X : Execution) (e f : EvId) : Prop :=
  ∃ x w m releaseScope acquireScope,
    MbarRelease X x m releaseScope ∧
    AsyncCopy.WaitObserves X (.thread x) w m true acquireScope ∧
    ScopesMeet L releaseScope x.1 acquireScope w.1 ∧
    w.1 = f.1 ∧ w.2 < f.2 ∧ f.2 < (X.tr f.1).length ∧
    x.1 = e.1 ∧ e.2 ≤ x.2

end

end PTX
