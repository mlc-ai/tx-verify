-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness

@[expose] public section

/-! # Source of a returned value: a protected read

A proof tool, generic over the kernel. A read returns the bytes of the write it reads from
(`rf`). The model does not order that write before the read (it has no no-thin-air axiom), so the
value is classified through the two orders the model excludes instead (`NoFuture`, `Hidden`):

* `read_byte_of_source`: given a write `w` of the byte that is before the read in model causality
  (the protecting hand-off), the read returns byte `b` when its actual source is, up to "after
  the read" and "before `w`", a write of `b`. Only the actual source needs a classification.

How a kernel meets the classification: a write that is before the read in base causality belongs
to a thread that `Frame.followedAt_of_noBad` follows up to the write, so the writer's shape table
names its bytes. A write concurrent with the read is excluded by the classification's two cases
only when the kernel knows its footprint; for a writer whose machine can stop on a returned
value's kind, that footprint is not available from the shapes alone (risk R4 of the plan; see
`Lemmas/DECISIONS.md`). -/

namespace PTX.Frame

open PTX

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A read returns the byte of its source** when its actual source is, up to the two orders
the model excludes, a write of that byte. -/
theorem read_byte_of_source (hX : Consistent L K A mem0 X) {e w : AsyncCopy.Ref}
    {a dst : Acc} {bs : List (Option Byte)} {written : List Byte} (he : X.MemReads e a bs) {k : Nat}
    (hk : k < a.size) (hw : X.MemWrites w dst written) (hc : dst.Covers (a.loc.at k))
    (hv : modelCausality L X (a.loc.at k) w e) {b : Byte}
    (hall : ∀ w' dst' bytes, X.rf e k = some w' → X.MemWrites w' dst' bytes →
      dst'.Covers (a.loc.at k) →
      modelCausality L X (a.loc.at k) e w' ∨ modelCausality L X (a.loc.at k) w' w ∨
        wbyte dst' bytes (a.loc.at k) = b) :
    bs[k]? = some (some b) := by
  have hh := hX.hidden e a bs k w dst written he hk hw hc (.direct hv)
  have hrf := (hX.rf e a bs he).2 k hk
  cases hs : X.rf e k with
  | none => simp [hs] at hh
  | some source =>
    rw [hs] at hh hrf
    obtain ⟨dst', bytes, hsource, hcov, hvalue⟩ := hrf
    rcases hall source dst' bytes hs hsource hcov with hafter | hbefore | hval
    · exact (hX.noFuture e a bs k source he hk hs (.direct hafter)).elim
    · exact (hh (.direct hbefore)).elim
    · rw [hvalue, hval]

/-- **The bytes a protected read returns**: byte by byte, from a protecting write of each byte and
the classification of the actual sources. -/
theorem read_bytes_of_sources (hX : Consistent L K A mem0 X) {e : AsyncCopy.Ref} {a : Acc}
    {bs : List (Option Byte)} (he : X.MemReads e a bs) {val : Nat → Byte}
    (hprot : ∀ k < a.size, ∃ w dst written, X.MemWrites w dst written ∧
      dst.Covers (a.loc.at k) ∧ modelCausality L X (a.loc.at k) w e ∧
      ∀ w' dst' bytes, X.rf e k = some w' → X.MemWrites w' dst' bytes →
        dst'.Covers (a.loc.at k) →
        modelCausality L X (a.loc.at k) e w' ∨ modelCausality L X (a.loc.at k) w' w ∨
          wbyte dst' bytes (a.loc.at k) = val k) :
    ∀ k < a.size, bs[k]? = some (some (val k)) := by
  intro k hk
  obtain ⟨w, dst, written, hw, hc, hv, hall⟩ := hprot k hk
  exact read_byte_of_source hX he hk hw hc hv hall

end PTX.Frame
