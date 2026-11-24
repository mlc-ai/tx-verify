-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Memory.CommitOperandOrder

@[expose] public section

/-!
# Allowed sources and values of reads

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

variable (L : Launch)

/-! ## MEM-READS-FROM — reads-from
Statement: Each byte that a read returns comes from a write that covers the byte, or from the
  initial write W0. W0 supplies the launch content of the byte, or, for an allocated byte whose
  content is unspecified, one value that is fixed for the whole execution.

Defs: RfWf

Source:
- §8.2.6 (W0)
- §8.9.7 (communication order: reads-from)

Direction: equal

Applies: Each byte of an ordinary or asynchronous read

Premises: The execution contains that read and its chosen source.

Effect: Execution constraint in Consistent.rf. `W0` supplies known launch bytes from `Mem0` and
  unspecified allocated bytes from `X.initial`, so two W0 reads of one address cannot choose
  different initial values. This choice supplies bytes to copies as well as ordinary reads.
-/

/-- Reads-from is well formed (§8.9.7): every read, ordinary or asynchronous, returns one byte
per byte of its footprint, and each byte is the value of its source, the covering write it reads
from or the initial write `W0`. -/
def RfWf (mem0 : Mem0) (X : Execution) : Prop :=
  ∀ e a bs, X.MemReads e a bs → bs.length = a.size ∧ ∀ k < a.size,
    match X.rf e k with
    | none => ∀ c, mem0 (a.loc.at k) = some c → bs[k]? = some (X.initialByte c (a.loc.at k))
    | some w => ∃ a' bs', X.MemWrites w a' bs' ∧ a'.Covers (a.loc.at k) ∧
        bs[k]? = some (wbyte a' bs' (a.loc.at k))

/-! ## MEM-READ-AXIOMS — the memory model axioms
Statement: A read never reads a byte from a write that the read precedes at that byte. When a write
  precedes a read at a byte, the read reads that byte neither from the initial write nor from a
  write that precedes that write at the byte; "precedes" is the model causality order
  `ByteCausality` (MEM-MODEL-CAUSALITY and EXT-TC-COMMIT-OPERAND-ORDER).

Defs: NoFuture, Hidden

Source:
- §8.10.6 (causality)
- §8.10.1 (coherence)
- §8.9.6 (coherence order)

Direction: stricter

Applies: Ordinary/async reads and covering writes

Premises: A read chooses a source; another write may be visible at the same byte.

Effect: Execution constraints in Consistent.noFuture and Consistent.hidden.

Review: `Hidden` forbids reading a write that precedes the causally preceding write in
  `ByteCausality`, where §8.10.6 says coherence order ("R cannot read from any write W’ that
  precedes W in coherence order"); coherence order (§8.9.6) also relates overlapping morally strong
  writes, so the model forbids fewer sources than the text and admits more executions (stricter).
  `W0` is first; ordinary thread order and the explicit cross-proxy patterns supply
  `ByteCausality` edges. Without races and with ordered strong pairs these identify a latest
  visible source. `visible_write` in `Lemmas/Order/Order.lean` derives the latest visible source.
-/

/-- Causality axiom, first clause (§8.10.6): no read reads a byte from a write that the read
precedes in `ByteCausality` at that byte. -/
def NoFuture (X : Execution) : Prop :=
  ∀ e a bs k w, X.MemReads e a bs → k < a.size → X.rf e k = some w →
    ¬ ByteCausality L X (a.loc.at k) e w

/-- Causality axiom, second clause, and coherence (§8.10.1, §8.10.6): when a write precedes a read
in `ByteCausality` at a byte, the read does not read that byte from the initial write `W0`
or from a write that precedes the first write in `ByteCausality` at that byte. -/
def Hidden (X : Execution) : Prop :=
  ∀ e a bs k w a' bs', X.MemReads e a bs → k < a.size → X.MemWrites w a' bs' →
    a'.Covers (a.loc.at k) → ByteCausality L X (a.loc.at k) w e →
    match X.rf e k with
    | none => False
    | some w' => ¬ ByteCausality L X (a.loc.at k) w' w

end

end PTX
