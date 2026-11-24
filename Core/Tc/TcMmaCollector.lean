-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events

@[expose] public section

namespace PTX.TcMma
noncomputable section

/-! ## ERR-TC-COLLECTOR-REUSE — collector buffer reuse
Statement: An MMA that may read A or B from a collector buffer (`::use`, `::lastuse`) is safe only
  when the latest earlier MMA of its thread that does not reuse that buffer fills it, no other
  thread issues MMAs on the CTAs of the issue, and the operand bytes it reads are those the filling
  MMA read. Any other reuse makes the execution unsafe.

Defs: TcMma.CollectorId, TcMma.Collectors.op, TcMma.CollectorId.bytes, TcMma.SoleIssuer,
  TcMma.CollectorFill, TcMma.CollectorSafe, TcMma.collectorSafe_of_noReuse

Source:
- §9.7.18.10: "The collector qualifier is used to give the TensorCore permission to reuse a
    previously loaded A or B matrix; however reuse is opportunistic in that the TensorCore may
    reload a matrix even when it has permission to reuse that matrix."
- §9.7.18.10: "Thus, the source memory of an A or B matrix must not be modified while the MMA
    instruction using those matrices has not completed - regardless of collector qualifier
    permissions."
- §9.7.18.10.10.1: ".collector::a::use , .collector::b::use Specified matrix can be read from the
    collector buffer."
- §9.7.18.10.10.1: "This requires a previous fill to the collector buffer to be still valid."
- §9.7.18.10.10.1: "This requires a previous fill to the collector buffer to be valid till the
    collector buffer is read."
- §9.7.18.10.10.1: "If no .collector_a_usage qualifier is specified, then it defaults to
    .collector::a::discard ."
- §9.7.18.10.10.3: "This requires a previous fill to the collector buffer #N to be still valid."

Direction: stricter

Applies: Every MMA issue whose collector usage of A or of a B buffer is `use` or `lastuse`

Premises: The thread's latest earlier MMA that names the buffer with another usage fills it; every
  MMA of the thread between them names the buffer with `use` or not at all; every MMA issue on a CTA
  of the issue is by the same thread; when both have read their operands, the reused operand's bytes
  equal those of the filling MMA.

Effect: `CollectorSafe` is a conjunct of `InstructionSafe` (ERR-TC-MMA); a violation makes
  the execution unsafe and filters none. An MMA reads its operands from memory in the model
  (DEP-TC-LOAD-VALUE, THREAD-TC-MMA-OPERANDS), whatever its collector usage. A reusing MMA on
  hardware reads either the buffer, which holds what the filling MMA read, or memory, since reuse is
  opportunistic. The two agree when the bytes this MMA reads equal those the filling MMA read, which
  is the last premise; when they may differ, the value of the result is not determined and the
  execution is unsafe. The text does not say which MMAs can invalidate a buffer: every MMA names the
  A buffer (`discard` by default), and the model counts every MMA of the thread between the fill and
  the reuse that names the buffer with an operation other than `use` as ending it. The non-`.ws` B
  buffer `::b` and the `.ws` buffer `::b0` are taken to be one buffer, and an MMA that names another
  `.ws` buffer leaves this one as it is. MMAs of other threads are not ordered with the issue by
  program order, so any MMA of another thread on a CTA of the issue makes a reuse unsafe. These
  choices only reject programs.
-/

/-- A collector buffer: the A buffer, or B buffer `n` (`::b` is buffer 0). -/
inductive CollectorId where
  | a
  | b (buffer : Nat)
  deriving DecidableEq, Repr

/-- The usage an issue names for a buffer; `none` for a B buffer it does not name. -/
def Collectors.op (c : Collectors) : CollectorId → Option MmaCollector
  | .a => some c.a
  | .b n => if n = c.bBuffer then some c.b else none

/-- The operand bytes a buffer holds: A's or B's. -/
def CollectorId.bytes : CollectorId → AsyncCopy.MmaOperands → List (Option Byte)
  | .a, o => o.a
  | .b _, o => o.b

/-- Every MMA issue on a CTA of `s` is by the thread of `u`. -/
def SoleIssuer (X : Execution) (u : EvId) (s : OperandSpec) : Prop :=
  ∀ e d s' acc mask, X.MmaIssue e d s' acc mask →
    (s'.lowCta = s.lowCta ∨ s'.lowCta = s.highCta ∨ s'.highCta = s.lowCta ∨
      s'.highCta = s.highCta) → e.1 = u.1

/-- `f` is an MMA of `u`'s thread before `u` that fills buffer `k`, and every MMA of the thread
between them names `k` with `use` or does not name it. -/
def CollectorFill (X : Execution) (f u : EvId) (k : CollectorId) : Prop :=
  f.1 = u.1 ∧ f.2 < u.2 ∧
    (∃ d s acc mask, X.MmaIssue f d s acc mask ∧ s.collector.op k = some .fill) ∧
    ∀ j, f.2 < j → j < u.2 → ∀ d s acc mask, X.MmaIssue (u.1, j) d s acc mask →
      s.collector.op k = some .use ∨ s.collector.op k = none

/-- Every reuse of a collector buffer has a fill that is still valid, a sole issuer and the
filling MMA's bytes. -/
def CollectorSafe (X : Execution) : Prop :=
  ∀ u d s acc mask k, X.MmaIssue u d s acc mask →
    ((s.collector.op k).map MmaCollector.reuses).getD false = true →
    SoleIssuer X u s ∧ ∃ f, CollectorFill X f u k ∧
      ∀ of ou, X.async.mmaOperands f = some of → X.async.mmaOperands u = some ou →
        k.bytes of = k.bytes ou

/-- An execution whose MMA issues reuse no collector buffer (every usage is `fill` or `discard`,
as for every MMA form without collector qualifiers) satisfies the collector rule. -/
theorem collectorSafe_of_noReuse {X : Execution}
    (h : ∀ u d s acc mask, X.MmaIssue u d s acc mask →
      s.collector.a.reuses = false ∧ s.collector.b.reuses = false) : CollectorSafe X := by
  intro u d s acc mask k hu hk
  obtain ⟨ha, hb⟩ := h u d s acc mask hu
  cases k with
  | a => simp [Collectors.op, ha] at hk
  | b n => by_cases hn : n = s.collector.bBuffer <;> simp [Collectors.op, hn, hb] at hk

end
end PTX.TcMma
