-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.AddOne.Proof.Interface
public import Lemmas.Kernel.Memory
public import Lemmas.Execution.NoAsync
public import Lemmas.Order.Order

@[expose] public section

/-! # `add_one`: the bytes a thread reads

Distinct elements of `A` are disjoint (`covers_A_A`). Every write is a thread's write of its own
element (`ThreadFacts.writes`), so the only write that covers a byte of `A[g]` is thread `g`'s
own write, which comes after its read in program order (`read_before_write`). A read never reads
from a write it precedes (causality, MEM-READ-AXIOMS `NoFuture`), so the read of `A[g]` returns its
launch content: the bytes of `x g`, which rebuild to `word (x g)` (`read_value`). -/

namespace PTX.Kernels.AddOne.Proof
open PTX

noncomputable section

variable {L : Launch} {A : Nat} {x : Nat → BitVec 32} {mem0 : Mem0} {X : Execution}

/-- The kernel has no asynchronous instruction. -/
theorem noTma : kernel.NoTma := rfl

/-- No event is a barrier. -/
theorem no_bar (ht : ThreadFacts L A X) : ∀ e id count pc, ¬ X.IsBarrier e id count pc :=
  fun _ _ _ _ hb => by
    rcases ht.kinds hb with ⟨_, _, h⟩ | ⟨_, _, h⟩ | h | ⟨_, h⟩ <;> simp at h

/-- A thread runs only for an element of `A`: there are `L.block` threads in the one CTA. -/
theorem lt_block (hpre : Pre L A x mem0) {g : Nat} (hg : g < L.threads) : g < L.block := by
  simpa [Launch.threads, hpre.grid] using hg

/-- Distinct elements of `A` are disjoint. -/
theorem covers_A_A {g h : Nat} {l : Loc} (h1 : (accA A g).Covers l)
    (h2 : (accA A h).Covers l) : g = h := by
  simp only [Acc.Covers, Loc.InRange, accA] at h1 h2
  omega

/-- No event is an atomic read-modify-write. -/
theorem no_rmw (ht : ThreadFacts L A X) {e : EvId} {a : Acc} {old : List (Option Byte)}
    {new : Option (List Byte)} : ¬ X.Rmw e a old new := by
  rintro ⟨pc, he⟩
  rcases ht.kinds he with ⟨_, _, h⟩ | ⟨_, _, h⟩ | h | ⟨_, h⟩ <;> simp at h

/-- A write of an execution is a thread's write of its own element of `A`. -/
theorem write_A (hX : Consistent L kernel [] mem0 X) (ht : ThreadFacts L A X)
    {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte} (hw : X.MemWrites w a bs) :
    ∃ g, w = .thread (g, 1) ∧ a = accA A g ∧
      ∃ rb v u u', X.get (g, 0) = some (rdE A g rb) ∧ rebuild 3 rb = .ok v ∧
        incr L g v = .ok u ∧ storeValue 32 u = .ok u' ∧ bs = u'.toBytes := by
  obtain ⟨⟨g, k⟩, rfl, hw | hrmw⟩ :=
    Execution.NoTma.memWrites_thread ((noTma_of_consistent noTma hX).emptyAsync hX) hw
  · obtain ⟨pc, hw⟩ := hw
    obtain ⟨rfl, rfl, h⟩ := ht.writes hw
    exact ⟨g, rfl, rfl, h⟩
  · obtain ⟨old, hrmw⟩ := hrmw
    exact absurd hrmw (no_rmw ht)

/-- **A thread's read of its element precedes its write of it**, at every byte (program order,
MEM-BASE-CAUSALITY). -/
theorem read_before_write {g : Nat} {rb : List (Option Byte)} {pc : Nat} {a : Acc}
    {bs : List Byte} (h0 : X.get (g, 0) = some (rdE A g rb))
    (h1 : X.get (g, 1) = some ⟨pc, .wr a bs⟩) (ha : a = accA A g) (l : Loc) :
    modelCausality L X l (.thread (g, 0)) (.thread (g, 1)) := by
  subst ha
  have hov : (accA A g).Overlap (accA A g) :=
    ⟨(accA A g).loc, by simp [Acc.Covers, Loc.InRange, accA]⟩
  exact .inl (.single (.inl (po_of_overlap (.inl ⟨rb, ⟨_, h0⟩, rfl⟩)
    (.inr (Or.inl ⟨bs, ⟨pc, h1⟩, rfl⟩)) rfl Nat.zero_lt_one hov)))

/-- **The read of `A[g]` returns the bytes of `x g`**, which rebuild to `word (x g)`. -/
theorem read_value (hpre : Pre L A x mem0) (hX : Consistent L kernel [] mem0 X)
    (ht : ThreadFacts L A X) {g : Nat} {rb : List (Option Byte)}
    (h0 : X.get (g, 0) = some (rdE A g rb)) : rebuild 3 rb = .ok (word (x g)) := by
  have hgB : g < L.block := lt_block hpre (Frame.lt_of_get hX h0)
  have hr : X.MemReads (.thread (g, 0)) (accA A g) rb := Or.inl ⟨_, h0⟩
  have hlen := hX.read_length hr
  have hbs : rb = (word (x g)).toBytes.map some := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < 4
    · have hb : ((word (x g)).toBytes.map some)[k]? = some (some (word (x g), k)) := by
        simp [Value.toBytes, word, Value.bytes, Value.byteAt, List.getElem?_range hk]
      rw [hb]
      have hrf := (hX.rf _ _ _ hr).2 k hk
      cases hsrc : X.rf (.thread (g, 0)) k with
      | none =>
        rw [hsrc] at hrf
        rw [hrf _ (by simpa [accA, Loc.at, Nat.add_assoc] using hpre.input g hgB k hk)]
        rfl
      | some w =>
        rw [hsrc] at hrf
        obtain ⟨a', bs', hw, hc, -⟩ := hrf
        obtain ⟨h, rfl, rfl, -⟩ := write_A hX ht hw
        obtain rfl := covers_A_A (Acc.covers_at hk) hc
        rcases hw with ⟨pc, hw1⟩ | ⟨old, hrmw⟩
        · exact absurd (.direct (read_before_write h0 hw1 rfl _)) (hX.noFuture _ _ _ k _ hr hk hsrc)
        · exact absurd hrmw (no_rmw ht)
    · rw [List.getElem?_eq_none (by simp [accA] at hlen; omega), List.getElem?_eq_none]
      simp [Value.toBytes, word, Value.bytes]
      omega
  rw [hbs]
  exact Proof.rebuild_scalar (by simp [word, Value.bytes]) rfl

end

end PTX.Kernels.AddOne.Proof
