-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Lemmas.Order.Order

/-! # Coherence order of morally strong stores (CORRECT-FINAL)

Two threads store to one location with `st.release`, each with a scope that includes the other
thread, and nothing orders the two stores. They are morally strong (§8.7), so they are related in
coherence order (§8.9.6: "Two overlapping write operations are related in coherence order if they
are morally strong or if they are related in causality order."), and the memory after the kernel
is that of the coherence-last store.

(a) Every byte of the location holds the value of one of the two stores, the same store for every
byte. (b) A reader that both stores precede in `modelCausality` and that reads from one of them
reads from the coherence-last one (§8.10.6: "If a write W precedes an overlapping read R in
causality order, then for any byte accessed by both R and W, R cannot read from any write W’ that
precedes W in coherence order."): the final location holds the store the reader read. -/

namespace PTX.Tests.StrongStoreCoherence
open PTX

variable {L : Launch} {mem0 : Mem0} {X : Execution} {m : FinalMem}

/-- Two release stores of the same footprint, each with a scope that includes the other's thread,
are morally strong (§8.7). -/
theorem release_stores_strong {i j : EvId} {a b : Acc} {bs cs : List Byte}
    (hi : X.Writes i a bs) (hj : X.Writes j b cs) (ha : a.release = true) (hb : b.release = true)
    (hsa : MbarScopeIncludes L a.scope i.1 j.1) (hsb : MbarScopeIncludes L b.scope j.1 i.1)
    (hab : a.SameFootprint b) :
    MorallyStrong L X (.thread i) (.thread j) a b :=
  ⟨.inr ⟨⟨⟨_, hi.access⟩, .inr (.inr ha), hsa⟩, ⟨⟨_, hj.access⟩, .inr (.inr hb), hsb⟩⟩, Iff.rfl,
    a, b, rfl, rfl, hab⟩

/-- (a) The location holds one of two morally strong stores, the same one at every byte, when
they are the only writes to its bytes. No order between the two stores is assumed. -/
theorem final_one_of_two {e f : AsyncCopy.Ref} {ae af : Acc} {bse bsf : List Byte} {l0 : Loc}
    (he : X.MemWrites e ae bse) (hf : X.MemWrites f af bsf) (hne : e ≠ f)
    (hl0e : ae.Covers l0) (hl0f : af.Covers l0) (hms : MorallyStrong L X e f ae af)
    (honly : ∀ w a bs l, X.MemWrites w a bs → a.Covers l → (ae.Covers l ∨ af.Covers l) →
      w = e ∨ w = f)
    (hfin : IsFinal L mem0 X m) :
    (∀ l, ae.Covers l → m l = some (wbyte ae bse l)) ∨
      (∀ l, af.Covers l → m l = some (wbyte af bsf l)) := by
  obtain ⟨co, hco, hfin⟩ := hfin
  rcases hco.strong e ae bse f af bsf l0 he hl0e hf hl0f hne hms with h | h
  · refine .inr fun l hl => (hfin l).1 f af bsf hf hl fun w a bs hw hc => ?_
    rcases honly w a bs l hw hc (.inr hl) with rfl | rfl
    · exact .inr h
    · exact .inl rfl
  · refine .inl fun l hl => (hfin l).1 e ae bse he hl fun w a bs hw hc => ?_
    rcases honly w a bs l hw hc (.inl hl) with rfl | rfl
    · exact .inl rfl
    · exact .inr h

/-- (a) for two unordered `st.release` stores of threads `i` and `j` to one location. -/
theorem release_final_one_of_two {i j : EvId} {a b : Acc} {bs cs : List Byte} {l0 : Loc}
    (hi : X.Writes i a bs) (hj : X.Writes j b cs) (hij : i ≠ j)
    (ha : a.release = true) (hb : b.release = true)
    (hsa : MbarScopeIncludes L a.scope i.1 j.1) (hsb : MbarScopeIncludes L b.scope j.1 i.1)
    (hab : a.SameFootprint b) (hl0 : a.Covers l0)
    (honly : ∀ w c ds l, X.MemWrites w c ds → c.Covers l → (a.Covers l ∨ b.Covers l) →
      w = .thread i ∨ w = .thread j)
    (hfin : IsFinal L mem0 X m) :
    (∀ l, a.Covers l → m l = some (wbyte a bs l)) ∨ (∀ l, b.Covers l → m l = some (wbyte b cs l)) :=
  final_one_of_two (e := .thread i) (f := .thread j) (.inl hi) (.inl hj)
    (fun h => hij (AsyncCopy.Ref.thread.inj h)) hl0
    (by unfold Acc.Covers; rw [← hab.1, ← hab.2]; exact hl0)
    (release_stores_strong hi hj ha hb hsa hsb hab) honly hfin

/-- (b) Thread `k`'s read of byte `l`, which the stores of threads `i` and `j` both precede in
`modelCausality`, reads from the store of `j`. When no read that the store of `j` precedes reads
from the store of `i`, the location holds the store of `j` at every byte. -/
theorem reader_reads_last {i j : EvId} {ae af : Acc} {bse bsf : List Byte}
    {r : AsyncCopy.Ref} {ar : Acc} {rbs : List (Option Byte)} {k : Nat}
    (he : X.MemWrites (.thread i) ae bse) (hf : X.MemWrites (.thread j) af bsf) (hij : i ≠ j)
    (hms : MorallyStrong L X (.thread i) (.thread j) ae af)
    (honly : ∀ w a bs l, X.MemWrites w a bs → a.Covers l → (ae.Covers l ∨ af.Covers l) →
      w = .thread i ∨ w = .thread j)
    (hr : X.MemReads r ar rbs) (hk : k < ar.size)
    (hcover : ae.Covers (ar.loc.at k)) (hcoverf : af.Covers (ar.loc.at k))
    (hrf : X.rf r k = some (.thread j)) (hvis : modelCausality L X (ar.loc.at k) (.thread i) r)
    (hunord : ∀ l, ¬ ByteCausality L X l (.thread j) (.thread i))
    (hirr : ∀ l, ¬ ByteCausality L X l (.thread j) (.thread j))
    (hreads : ∀ r' ar' rbs' k', X.MemReads r' ar' rbs' → k' < ar'.size →
      X.rf r' k' = some (.thread i) → ¬ ByteCausality L X (ar'.loc.at k') (.thread j) r')
    (hrnw : ∀ e a old new, ¬ X.Rmw e a old new)
    (hfin : IsFinal L mem0 X m) :
    ∀ l, af.Covers l → m l = some (wbyte af bsf l) := by
  obtain ⟨co, hco, hfin⟩ := hfin
  have hne : (AsyncCopy.Ref.thread i) ≠ .thread j := fun h => hij (AsyncCopy.Ref.thread.inj h)
  have hstep : CoStep L X (.thread i) (.thread j) :=
    ⟨_, ae, bse, af, bsf, he, hcover, hf, hcoverf,
      .inr (.inr ⟨hne, hms, r, ar, rbs, k, hr, hk, rfl, hrf, .direct hvis⟩)⟩
  have hnostep : ∀ w, ¬ CoStep L X (.thread j) w := by
    rintro w ⟨l', a0, bs0, a1, bs1, hw0, hc0, hw1, hc1, h⟩
    rcases h with hv | ⟨p, q, k1, k2, hrr, h1, h2⟩ |
      ⟨hne', -, r', ar', rbs', k', hr', hk', rfl, hrf', hv'⟩
    · obtain ⟨hsame, -⟩ := Execution.MemWrites.unique hw0 hf
      rw [Acc.SameFootprint.covers hsame] at hc0
      rcases honly w a1 bs1 _ hw1 hc1 (.inr hc0) with rfl | rfl
      · exact hunord _ hv
      · exact hirr _ hv
    · cases p with
      | thread e =>
        obtain rfl := AsyncCopy.Ref.thread.inj h1
        obtain ⟨l0, n0, hAt, -, -, -⟩ := hrr
        obtain ⟨a, old, new, hrmw, -, -⟩ := hAt
        exact hrnw j a old new hrmw
      | tensor i x y => cases h1
      | copy i j => cases h1
    · obtain ⟨hsame, -⟩ := Execution.MemWrites.unique hw0 hf
      rw [Acc.SameFootprint.covers hsame] at hc0
      rcases honly w a1 bs1 _ hw1 hc1 (.inr hc0) with rfl | rfl
      · exact hreads r' ar' rbs' k' hr' hk' hrf' hv'
      · exact hne' rfl
  have hco' : co (.thread i) (.thread j) := hco.before _ _ (.single hstep) fun h => by
    obtain ⟨w, hs, -⟩ := Relation.TransGen.head'_iff.mp h
    exact hnostep w hs
  intro l hl
  refine (hfin l).1 _ af bsf hf hl fun w a bs hw hc => ?_
  rcases honly w a bs l hw hc (.inr hl) with rfl | rfl
  · exact .inr hco'
  · exact .inl rfl

end PTX.Tests.StrongStoreCoherence
