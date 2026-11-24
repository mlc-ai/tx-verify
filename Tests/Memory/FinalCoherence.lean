-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Lemmas.Order.Order

/-! # Final memory follows the coherence order (CORRECT-FINAL)

Split-K litmus: two `cp.reduce.async.bulk.tensor .add` reductions of one element, issued by
different CTAs with no synchronization between them, so neither is `ByteCausality`-before the
other. The element-wise atomicity rule (DEP-REDUCTION-VALUES) leaves two executions: one reduction
reads the launch value and the other reads its result. In both, the final byte is that of the
coherence-last reduction, the one that read the other's result (§8.10.3 Litmus Test 1: "FINAL STATE
: x == 2"). Totality of the coherence order alone would leave either reduction last; the reads-from
edge picks the one that read the other's result. -/

namespace PTX.Tests.FinalCoherence
open PTX TensorStore

/-- The write of byte `k` of reduction element `p`. -/
abbrev wr (p : EvId × Nat × Nat) (k : Nat) : AsyncCopy.Ref :=
    .async p.1 (.write (.store p.2.1 p.2.2 k))
/-- The read of old byte `k` of reduction element `p`. -/
abbrev old (p : EvId × Nat × Nat) (k : Nat) : AsyncCopy.Ref :=
    .async p.1 (.old (.store p.2.1 p.2.2 k))

theorem reduced_fp {X : Execution} {i : EvId} {x y : Nat} {fp fp' : Acc}
    (h : Reduced X i x y fp) (h' : Reduced X i x y fp') : fp = fp' := by
  obtain ⟨o, -, loc, ho, -, hl, rfl, -⟩ := h
  obtain ⟨o', -, loc', ho', -, hl', rfl, -⟩ := h'
  rw [ho] at ho'; cases ho'
  rw [hl] at hl'; cases hl'
  rfl

variable {L : Launch} {mem0 : Mem0} {X : Execution} {m : FinalMem} {fp : Acc}
  {p q : EvId × Nat × Nat} {k : Nat} {l : Loc} {ap aq : Acc} {bsp bsq : List Byte}

/-- A coherence edge out of the write of reduction `q`, when the only writes to the bytes of
the two reductions' writes are those writes, `ByteCausality` orders nothing and `p` read no byte
from `q`. -/
theorem no_step_from (ha : ReduceAcyclic X) (hqr : Reduced X q.1 q.2.1 q.2.2 fp)
    (hpq : ReduceReads X fp p q) (hwq : X.MemWrites (wr q k) aq bsq)
    (honly : ∀ w a bs l', X.MemWrites w a bs → a.Covers l' → (ap.Covers l' ∨ aq.Covers l') →
      w = wr p k ∨ w = wr q k)
    (hnv : ∀ l' u v, ¬ ByteCausality L X l' u v) {w : AsyncCopy.Ref} :
    ¬ CoStep L X (wr q k) w := by
  rintro ⟨l', a0, bs0, a1, bs1, hw0, hc0, hw1, hc1,
    hv | ⟨p', q', k1, k2, hr, h1, h2⟩ | ⟨-, -, r, ar, rbs, kr, -, -, -, -, hv'⟩⟩
  · exact hnv _ _ _ hv
  · obtain ⟨hsf, -⟩ := Execution.MemWrites.unique hw0 hwq
    obtain ⟨l0, n0, hrat, -, -, kk, kk', hkk, hread⟩ := hr
    -- `q`'s write is `p'`'s new value, so `p'` is the reduction of `q`
    have hp' : p' = .tensor q.1 q.2.1 q.2.2 := by
      cases p' with
      | thread e =>
        simp only [wr, RmwId.newRef] at h1
        cases h1
      | copy i j =>
        simp only [wr, RmwId.newRef] at h1
        cases h1
      | tensor i x y =>
        simp only [wr, RmwId.newRef, AsyncCopy.Ref.async.injEq, AsyncCopy.Part.write.injEq,
          AsyncCopy.Slot.store.injEq] at h1
        obtain ⟨e1, e2, e3, -⟩ := h1
        rw [← e1, ← e2, ← e3]
    rw [hp'] at hrat
    obtain ⟨fp', hred', -, hsize⟩ := hrat
    have hfp := reduced_fp hqr hred'
    subst hfp
    rcases honly w a1 bs1 l' hw1 hc1 (.inr ((hsf.covers l').1 hc0)) with rfl | rfl
    · -- `q`'s write is the new value of the element `p`'s old byte came from
      have hq' : q' = .tensor p.1 p.2.1 p.2.2 := by
        cases q' with
        | thread e =>
          simp only [wr, RmwId.newRef] at h2
          cases h2
        | copy i j =>
          simp only [wr, RmwId.newRef] at h2
          cases h2
        | tensor i x y =>
          simp only [wr, RmwId.newRef, AsyncCopy.Ref.async.injEq, AsyncCopy.Part.write.injEq,
            AsyncCopy.Slot.store.injEq] at h2
          obtain ⟨f1, f2, f3, -⟩ := h2
          rw [← f1, ← f2, ← f3]
      rw [hq', hp'] at hread
      simp only [Execution.oldRf, RmwId.newRef] at hread
      exact ha fp _ (.tail (.single hpq) ⟨hpq.2.1, hpq.1, kk, kk', by omega, hread⟩)
    · have hq'' : q' = .tensor q.1 q.2.1 q.2.2 := by
        cases q' with
        | thread e =>
          simp only [wr, RmwId.newRef] at h2
          cases h2
        | copy i j =>
          simp only [wr, RmwId.newRef] at h2
          cases h2
        | tensor i x y =>
          simp only [wr, RmwId.newRef, AsyncCopy.Ref.async.injEq, AsyncCopy.Part.write.injEq,
            AsyncCopy.Slot.store.injEq] at h2
          obtain ⟨f1, f2, f3, -⟩ := h2
          rw [← f1, ← f2, ← f3]
      rw [hq'', hp'] at hread
      simp only [Execution.oldRf, RmwId.newRef] at hread
      exact ha fp _ (.single ⟨hpq.2.1, hpq.2.1, kk, kk', by omega, hread⟩)
  · exact hnv _ _ _ hv'

/-- The final byte of `q`, when `q` read byte `k` from `p`. -/
theorem final_of_reads (hS : TensorStoreOk L X) (hout : ∀ g, L.threads ≤ g → X.tr g = [])
    (ha : ReduceAcyclic X) (hpr : Reduced X p.1 p.2.1 p.2.2 fp)
    (hqr : Reduced X q.1 q.2.1 q.2.2 fp) (hk : k < fp.size)
    (hwp : X.MemWrites (wr p k) ap bsp) (hcp : ap.Covers l)
    (hwq : X.MemWrites (wr q k) aq bsq) (hcq : aq.Covers l)
    (honly : ∀ w a bs l', X.MemWrites w a bs → a.Covers l' → (ap.Covers l' ∨ aq.Covers l') →
      w = wr p k ∨ w = wr q k)
    (hnv : ∀ l' u v, ¬ ByteCausality L X l' u v)
    (hread : X.rf (old q k) 0 = some (wr p k)) (hf : IsFinal L mem0 X m) :
    m l = some (wbyte aq bsq l) := by
  have hrr : ReduceReads X fp p q := ⟨hpr, hqr, k, k, hk, hread⟩
  obtain ⟨co, hco, hf⟩ := hf
  apply (hf l).1 _ aq bsq hwq hcq
  intro w a bs hw hc
  rcases honly w a bs l hw hc (.inr hcq) with rfl | rfl
  · refine .inr (hco.before _ _ (.single (coStep_of_reduceReads L hS hout hwp hcp hwq hcq hrr))
      fun h => ?_)
    obtain ⟨w, hs⟩ := Relation.TransGen.head'_iff.mp h
    exact no_step_from ha hqr hrr hwq honly hnv hs.1
  · exact .inl rfl

/-- Split-K: two unordered reductions of one element. Atomicity makes one read the launch value
and the other read its result; the final byte is the latter's. -/
theorem split_k_final (hS : TensorStoreOk L X) (hout : ∀ g, L.threads ≤ g → X.tr g = [])
    (hu : ReduceUnique X) (ha : ReduceAcyclic X)
    (hpr : Reduced X p.1 p.2.1 p.2.2 fp) (hqr : Reduced X q.1 q.2.1 q.2.2 fp) (hpq : p ≠ q)
    (hk : k < fp.size)
    (hwp : X.MemWrites (wr p k) ap bsp) (hcp : ap.Covers l)
    (hwq : X.MemWrites (wr q k) aq bsq) (hcq : aq.Covers l)
    (honly : ∀ w a bs l', X.MemWrites w a bs → a.Covers l' → (ap.Covers l' ∨ aq.Covers l') →
      w = wr p k ∨ w = wr q k)
    (hsp : X.rf (old p k) 0 = none ∨ X.rf (old p k) 0 = some (wr q k))
    (hsq : X.rf (old q k) 0 = none ∨ X.rf (old q k) 0 = some (wr p k))
    (hnv : ∀ l' u v, ¬ ByteCausality L X l' u v) (hf : IsFinal L mem0 X m) :
    (X.rf (old p k) 0 = none ∧ X.rf (old q k) 0 = some (wr p k) ∧ m l = some (wbyte aq bsq l)) ∨
    (X.rf (old q k) 0 = none ∧ X.rf (old p k) 0 = some (wr q k) ∧ m l = some (wbyte ap bsp l)) := by
  have honly' : ∀ w a bs l', X.MemWrites w a bs → a.Covers l' → (aq.Covers l' ∨ ap.Covers l') →
      w = wr q k ∨ w = wr p k :=
    fun w a bs l' hw hc hl => (honly w a bs l' hw hc hl.symm).symm
  rcases hsp with hp | hp <;> rcases hsq with hq | hq
  · exact False.elim (hu fp p q k hpr hqr hpq hk (hp.trans hq.symm))
  · exact .inl ⟨hp, hq, final_of_reads hS hout ha hpr hqr hk hwp hcp hwq hcq honly hnv hq hf⟩
  · exact .inr ⟨hq, hp, final_of_reads hS hout ha hqr hpr hk hwq hcq hwp hcp honly' hnv hp hf⟩
  · exact False.elim (ha fp p (.tail (.single ⟨hpr, hqr, k, k, hk, hq⟩) ⟨hqr, hpr, k, k, hk, hp⟩))

/-- The integer `.add` of two concurrent reductions is the sum of both in either coherence
order. -/
theorem add_either_order (v s t : Nat) :
    AtomOp.apply .add false 32 (AtomOp.apply .add false 32 v s) t =
      AtomOp.apply .add false 32 (AtomOp.apply .add false 32 v t) s := by
  simp only [AtomOp.apply]
  omega

end PTX.Tests.FinalCoherence
