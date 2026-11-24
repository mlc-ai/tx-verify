-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.FootCopy
public import Lemmas.Order.ReadLast

@[expose] public section

/-!
# The source of a read of a shared byte

* `read_byte_of_source`: the reads-from step of `PrefixRf.read_byte_of_common_value`, asking the
  classification only of the read's actual source: a visible write `w` of the byte, and for the
  source `w'` of the read, one of: the read is before `w'` (then `NoFuture` excludes it), `w'` is
  before `w` (then `Hidden` excludes it), or `w'` writes the byte `b`. The classification of the
  source is available because the source is a dependency of the read (`Dep.rf`) and the induction
  has `GoodP` there.
* `source_class`: a write of shared memory whose issuing event the machines tracked through is a
  thread write of one of the seven kinds (`TWrite`) at the state of its thread, or a write stage of
  a tensor copy, below the end of the rings or wrapped to the top of the 32-bit space.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A read returns the byte of its source** when its actual source is, up to the two orders
the model excludes, a write of that byte. -/
theorem read_byte_of_source (hX : Consistent L kernel asms mem0 X) {e w : AsyncCopy.Ref}
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

/-- **The classification of a shared write whose issuing event is tracked.** A thread write is
one of the seven kinds at the state of its thread; a write stage of a tensor copy is of the issuing
thread's CTA, below the end of the rings or wrapped to the top of the 32-bit space
(`async_write_foot`). -/
theorem source_class (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {r : AsyncCopy.Ref} {dst : Acc}
    {bytes : List Byte} (hw : X.MemWrites r dst bytes) (hsp : dst.loc.space = .shared)
    (hTT : TT Q L X (refEvent r)) :
    (∃ g k s, r = .thread (g, k) ∧ g < L.threads ∧ St Q L X g k = some (some s) ∧
      TWrite Q L g s dst bytes) ∨
    (∃ i, (∃ x y z, r = .async i (.write (.load x y z))) ∧ dst.loc.cta = i.1 / L.block ∧
      (dst.loc.addr + dst.size ≤ L.sharedBase + 196608 ∨ 2 ^ 32 - 65536 ≤ dst.loc.addr)) := by
  rcases r with ⟨g, k⟩ | ⟨i, p⟩
  · left
    rcases hw with ⟨pc, hget⟩ | ⟨old, pc, hget⟩
    · have hg := Frame.lt_of_get hX hget
      obtain ⟨s, hσ⟩ := event_state_at hS hX hget (by intro pc' f h; cases h) hTT
      exact ⟨g, k, s, rfl, hg, hσ, thread_write_class hpre hX hS hg hget hσ hsp⟩
    · exact absurd hget (no_rmw hX)
  · right
    refine ⟨i, ?_⟩
    cases p
    case writeLoad x y z =>
      obtain ⟨h1, h2, h3⟩ := async_write_foot hpre hX hS hw hTT
      exact ⟨⟨x, y, z, rfl⟩, h2, h3⟩
    case writeStore x y k =>
      obtain ⟨o, addr, b, -, ⟨pc, hget⟩, -⟩ := hw
      exact absurd hget (no_tensorStore hX)
    case writeCta c =>
      obtain ⟨s, targets, ⟨pc, hget⟩, -⟩ := hw
      exact absurd hget (no_clc hX)
    case writeCopy =>
      obtain ⟨s, ⟨pc, hget⟩, -⟩ := hw
      exact absurd hget (no_copy hX)
    case writeElem j =>
      obtain ⟨s, ⟨pc, hget⟩, -⟩ := hw
      exact absurd hget (no_copy hX)
    all_goals exact (hw : False).elim

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
