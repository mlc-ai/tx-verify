-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Memory

/-! # Final memory of unordered writes (CORRECT-FINAL)

Two writes of one byte that are in a data race are unrelated in coherence order (§8.9.6: "Two
overlapping writes are unrelated in coherence order if they are in a data-race , which gives
rise to the partial nature of coherence order ."), so both are co-maximal and a read after the
kernel may read either (§8.10.6).

(a) When the two write the same value, the memory after the kernel holds it, with no order
between them assumed. (b) When they write different values and a coherence order leaves them
unordered, the byte's clauses of `IsFinal` hold for every value: the final byte is not
determined. -/

namespace PTX.Tests.IdenticalWritesFinal
open PTX

variable {L : Launch} {mem0 : Mem0} {X : Execution} {m : FinalMem}
  {e f : AsyncCopy.Ref} {ae af : Acc} {bse bsf : List Byte} {l : Loc}

/-- (a) Two writes of `l` with the same value, its only writers: the final byte is that value. -/
theorem identical_final (he : X.MemWrites e ae bse) (hf : X.MemWrites f af bsf)
    (hle : ae.Covers l) (hlf : af.Covers l)
    (honly : ∀ w a bs, X.MemWrites w a bs → a.Covers l → w = e ∨ w = f)
    (hsame : wbyte ae bse l = wbyte af bsf l) (hfin : IsFinal L mem0 X m) :
    m l = some (wbyte ae bse l) := by
  -- The statement keeps both covers; the value below is read at `e`, the first writer.
  have _ := hlf
  refine IsFinal.of_agree hfin (ws := [e, f]) (fun w a bs hw hc => ?_) he hle
    fun w a bs hw hc => ?_
  · rcases honly w a bs hw hc with rfl | rfl <;> simp
  · rcases honly w a bs hw hc with rfl | rfl
    · obtain ⟨hfp, hbs⟩ := hw.unique he
      subst hbs
      simp [wbyte, hfp.1]
    · obtain ⟨hfp, hbs⟩ := hw.unique hf
      subst hbs
      simp only [wbyte, hfp.1]
      exact hsame.symm

/-- (b) Two writes of `l` with different values, its only writers, unordered in a strict order
`co`: every value `c` satisfies the clauses of `IsFinal` at `l` (its body at `l`). -/
theorem differing_unconstrained {co : AsyncCopy.Ref → AsyncCopy.Ref → Prop}
    (hirr : ∀ w, ¬ co w w) (he : X.MemWrites e ae bse) (hf : X.MemWrites f af bsf)
    (hle : ae.Covers l) (hlf : af.Covers l)
    (honly : ∀ w a bs, X.MemWrites w a bs → a.Covers l → w = e ∨ w = f)
    (hef : ¬ co e f) (hfe : ¬ co f e) (hdiff : wbyte ae bse l ≠ wbyte af bsf l)
    (c : Option Byte) :
    (∀ w a bs, X.MemWrites w a bs → a.Covers l →
      (∀ w' a' bs', X.MemWrites w' a' bs' → a'.Covers l → w' = w ∨ co w' w) →
      some c = some (wbyte a bs l)) ∧
    ((∀ w a bs, X.MemWrites w a bs → ¬ a.Covers l) → some c = mem0 l) ∧
    ∀ b, (∃ w, CoMaximal X co l w) →
      (∀ w a bs, CoMaximal X co l w → X.MemWrites w a bs → wbyte a bs l = b) →
        some c = some b := by
  have hne : e ≠ f := by
    rintro rfl
    obtain ⟨hfp, hbs⟩ := he.unique hf
    subst hbs
    exact hdiff (by simp [wbyte, hfp.1])
  have maxe : CoMaximal X co l e := ⟨⟨ae, bse, he, hle⟩, fun w a bs hw hc h => by
    rcases honly w a bs hw hc with rfl | rfl
    · exact hirr _ h
    · exact hef h⟩
  have maxf : CoMaximal X co l f := ⟨⟨af, bsf, hf, hlf⟩, fun w a bs hw hc h => by
    rcases honly w a bs hw hc with rfl | rfl
    · exact hfe h
    · exact hirr _ h⟩
  refine ⟨fun w a bs hw hc hlast => ?_, fun hn => absurd hle (hn e ae bse he), ?_⟩
  · rcases honly w a bs hw hc with rfl | rfl
    · rcases hlast f af bsf hf hlf with h | h
      · exact absurd h.symm hne
      · exact absurd h hfe
    · rcases hlast e ae bse he hle with h | h
      · exact absurd h hne
      · exact absurd h hef
  · intro b _ hall
    exact absurd ((hall e ae bse maxe he).trans (hall f af bsf maxf hf).symm) hdiff

end PTX.Tests.IdenticalWritesFinal
