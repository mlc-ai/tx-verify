-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Safety.Regions

@[expose] public section

/-!
# The memory branches of `Unsafe`: races and mixed-size conflicts

Global memory is decided from the thread layer. A byte of an output array is written only by the
epilogue's stores (`ThreadFacts.global_wr`), and two stores whose footprints overlap are stores
of one output element (`Interface.global_writes_same_element`), so one event if each element has
one store event (`StoreOnce`). A byte the kernel reads is an input byte (`GlobalReads`), which the
precondition keeps apart from both output arrays (`Pre.outputsApart`). So a conflicting pair at a
global byte cannot exist (`global_ordered`).

Shared memory is region by region (`Regions.lean`): each region's conflicting accesses are
ordered by its protocol (`SharedOrder`): the base word, the K and V rings (the RAW and WAR order
of `Ring.Kv.copy_read_order`), the Q tile, the pair `(num_pre, num_iters)` and the role table. The
last two regions are written by every thread of the default partition with one value
(`SameValueWrites`), so their order is `ConflictsOrderedExcept`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The inputs of the global branch -/

/-- Every write stage of an asynchronous operation writes shared memory: the kernel's only
asynchronous writes are the tensor loads, which land in the CTA's shared window. -/
def AsyncWritesShared (X : Execution) : Prop :=
  ∀ i p a, X.Intent (.async i p) a true → a.loc.space = .shared

/-- Two global stores of one execution whose footprints overlap are one event: an output element
has one store (its thread is determined, and a thread stores each element once). -/
def StoreOnce (X : Execution) : Prop :=
  ∀ {g k g' k' pc pc' : Nat} {a a' : Acc} {bs bs' : List Byte},
    X.get (g, k) = some ⟨pc, .wr a bs⟩ → X.get (g', k') = some ⟨pc', .wr a' bs'⟩ →
    a.loc.space = .global → a'.loc.space = .global → a.Overlap a' → (g, k) = (g', k')

/-! ### Every global write intent is an output store -/

/-- **A global write intent is a thread's store of an output byte.** -/
theorem global_intent_write (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (has : AsyncWritesShared X) {e : AsyncCopy.Ref} {a : Acc}
    (h : X.Intent e a true) (hsp : a.loc.space = .global) :
    ∃ g k pc bs, e = .thread (g, k) ∧ X.get (g, k) = some ⟨pc, .wr a bs⟩ ∧
      a.loc.cta = 0 ∧ ∀ l, a.Covers l → InOut Q l := by
  rcases e with ⟨g, k⟩ | ⟨i, p⟩
  · rcases h with ⟨bs, hw⟩ | ⟨bs, ⟨pc, hw⟩, -⟩ | ⟨old, new, ⟨pc, hr⟩⟩
    · cases hw.2
    · have hg := Frame.lt_of_get hX hw
      have hmw : X.MemWrites (.thread (g, k)) a bs := Or.inl ⟨pc, hw⟩
      obtain ⟨d, -, -, -, -, hcases⟩ := hf.global_wr hg hw hsp
      have hcta : a.loc.cta = 0 := by
        rcases hcases with ⟨j, -, v, -, -, hacc⟩ | ⟨-, v, -, -, hacc⟩ <;> subst hacc <;> rfl
      refine ⟨g, k, pc, bs, rfl, hw, hcta, fun l hc => ?_⟩
      refine ⟨hc.1.trans hsp, hc.2.1.trans hcta, ?_⟩
      exact global_write_in_arrays hpre hX hf.sound hf.tracked hmw hsp hc
    · exact absurd hr (no_rmw hX)
  · have := has i p a h
    rw [this] at hsp
    cases hsp

/-! ### The global branch -/

/-- **A write of an output byte conflicts with nothing else**: the other access is an input read,
which the precondition keeps apart, or a store of the same element, which is the same event. -/
theorem global_ordered (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (has : AsyncWritesShared X) (hgr : GlobalReads Q X)
    (hgp : GlobalPlaced Q X) (hso : StoreOnce X) :
    ConflictsOrderedExcept L X (fun l => l.space ≠ .shared) := by
  intro e f a b l hc ha hb hsp _
  exfalso
  obtain ⟨hne, we, wf, hie, hif, hw, hov⟩ := hc
  have hlg : l.space = .global := by
    rcases hgp e a l (.inl ⟨_, hie⟩) ha hsp with h | h
    · exact h.1
    · exact h.1
  have hasp : a.loc.space = .global := ha.1.symm.trans hlg
  have hbsp : b.loc.space = .global := hb.1.symm.trans hlg
  -- a read of an output byte is an input byte, which is no output byte
  have hrd : ∀ {x : AsyncCopy.Ref} {c : Acc}, X.Intent x c false → c.Covers l →
      InOut Q l → False := by
    intro x c hi hcv hout
    have hin := hgr x c l hi hcv hsp
    obtain ⟨-, -, hr⟩ := hin
    obtain ⟨-, -, ho | hl⟩ := hout
    · exact (hpre.outputsApart _ hr).1 ho
    · exact (hpre.outputsApart _ hr).2 hl
  have hout : InOut Q l := by
    rcases hw with rfl | rfl
    · obtain ⟨g, k, pc, bs, rfl, -, -, hall⟩ := global_intent_write hpre hX hf has hie hasp
      exact hall l ha
    · obtain ⟨g, k, pc, bs, rfl, -, -, hall⟩ := global_intent_write hpre hX hf has hif hbsp
      exact hall l hb
  rcases hw with rfl | rfl
  · obtain ⟨g, k, pc, bs, rfl, hge, -, -⟩ := global_intent_write hpre hX hf has hie hasp
    cases wf
    · exact hrd hif hb hout
    · obtain ⟨g', k', pc', bs', rfl, hge', -, -⟩ := global_intent_write hpre hX hf has hif hbsp
      exact hne (by rw [hso hge hge' hasp hbsp ⟨l, ha, hb⟩])
  · obtain ⟨g', k', pc', bs', rfl, hge', -, -⟩ := global_intent_write hpre hX hf has hif hbsp
    cases we
    · exact hrd hie ha hout
    · obtain ⟨g, k, pc, bs, rfl, hge, -, -⟩ := global_intent_write hpre hX hf has hie hasp
      exact hne (by rw [hso hge hge' hasp hbsp ⟨l, ha, hb⟩])

/-! ### The shared branch: the protocols' orders -/

/-- **The conflicting accesses of each shared region are ordered by its protocol.** -/
structure SharedOrder (L : Launch) (X : Execution) : Prop where
  /-- The base word: the allocation's store, then every thread's load, then K slot 0's first
  copy (the `bar.sync 0` pair of the common start). -/
  base : ConflictsOrdered L X (InBase L)
  /-- The K and V rings: `Ring.Kv.copy_read_order`, RAW and WAR on each slot. -/
  kv : ConflictsOrdered L X (InKv L)
  /-- The Q tile: the default partition's stores, `fence.proxy.async` and `bar.sync 0, 128`, then
  the MMA warp's reads. -/
  q : ConflictsOrdered L X (InQ L)
  /-- `(num_pre, num_iters)` and the scratch words that overlap it: the pair is written with one
  value by every default-partition thread and read by the loader and the MMA warp after
  `barrier.sync 1`; the softmax region's min-exchange writes words 0 and 1 of its scratch
  (`store10`: one value per warp) and reads them (`ldL`), each side of a `bar.sync 0, 128`. -/
  count : ConflictsOrderedExcept L X (InCount L)
  /-- The scratch words 2 and 3 (`[sharedBase + 213000, sharedBase + 213008)`): the softmax
  region's min-exchange of warps 2 and 3, each store and the loads of it on the two sides of a
  `bar.sync 0, 128` of the default partition. -/
  scratch : ConflictsOrderedExcept L X (InScratch L)
  /-- The role table: written with one value by every default-partition thread, before and after
  the roles, and read by the workers' dispatch. -/
  role : ConflictsOrderedExcept L X (InRole L)

/-- **The shared bytes are ordered**, region by region. -/
theorem shared_ordered (hsh : SharedPlaced L X) (ho : SharedOrder L X) :
    ConflictsOrderedExcept L X (fun l => l.space = .shared) := by
  intro e f a b l hc ha hb' hsp hE
  obtain ⟨-, we, -, he, -⟩ := id hc
  rcases (hsh e a l (.inl ⟨we, he⟩) ha hsp).2 with h | h | h | h | h | h
  · exact ho.base e f a b l hc ha hb' h
  · exact ho.kv e f a b l hc ha hb' h
  · exact ho.q e f a b l hc ha hb' h
  · exact ho.count e f a b l hc ha hb' h hE
  · exact ho.scratch e f a b l hc ha hb' h hE
  · exact ho.role e f a b l hc ha hb' h hE

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (has : AsyncWritesShared X) (hgr : GlobalReads Q X) (hgp : GlobalPlaced Q X) (hso : StoreOnce X)
include hpre hX hf has hgr hgp hso

/-- **Every byte is ordered**, but for the identical-value write pairs. -/
theorem conflicts_ordered (hsh : SharedPlaced L X) (ho : SharedOrder L X)
    : ConflictsOrderedExcept L X (fun _ => True) :=
  ((shared_ordered hsh ho).or (global_ordered hpre hX hf has hgr hgp hso)).mono fun l _ =>
    Classical.em (l.space = .shared)

/-- **No race.** -/
theorem no_race (hsh : SharedPlaced L X) (ho : SharedOrder L X) : ¬ Race L X :=
  (conflicts_ordered hpre hX hf has hgr hgp hso hsh ho).no_race

/-- **No mixed-size conflict.** -/
theorem no_mixed (hsh : SharedPlaced L X) (ho : SharedOrder L X) : ¬ Mixed L X :=
  (conflicts_ordered hpre hX hf has hgr hgp hso hsh ho).no_mixed

end
end PTX.Kernels.InklingRelDecode.Proof.Safety
