-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SxAsync
public import Kernels.InklingRelDecode.Proof.Interface.ScRead
public import Kernels.InklingRelDecode.Proof.Interface.ScNum
public import Kernels.InklingRelDecode.Proof.Interface.LedgerInv

@[expose] public section

/-!
# The accesses to the shared words above the query tile, and the barrier-1 order

The shared words at and above `sharedBase + 212992` (the pair `(num_pre, num_iters)`, the scratch
words, the role table) are touched only by threads: no asynchronous access reaches them
(`async_not_high`). `high_thread` turns an intent at such a byte into a thread's read or write
event with the abstract state before it, classified by `TWrite` or `TRead`.

The orders the regions' proofs use:

* `same_thread`: two overlapping accesses of one thread are in program order;
* `b1_before`: an event of a thread with at most `φ` barrier-1 events before it is causally before
  an event of a thread of its CTA with more than `φ` (the barrier-1 generation of ordinal `φ`,
  `Bar.bar1_baseCausality`);
* `b1N_phase`: the number of barrier-1 events before an event is the phase of its state plus three
  per round of the dispatch loop (`phase_inv`).

`same_value`: two write events with the same bytes and the same footprint are `SameValueWrites`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The role table's address is below `2 ^ 32`. -/
theorem role_mod (hpre : Pre Q L mem0) :
    (L.sharedBase + 213336) % 2 ^ 32 = L.sharedBase + 213336 := by
  have hsh := hpre.sharedRange
  unfold sharedBytes at hsh
  exact Nat.mod_eq_of_lt (by omega)

/-- The pair's address is below `2 ^ 32`. -/
theorem pair_mod (hpre : Pre Q L mem0) :
    (L.sharedBase + 212992) % 2 ^ 32 = L.sharedBase + 212992 := by
  have hsh := hpre.sharedRange
  unfold sharedBytes at hsh
  exact Nat.mod_eq_of_lt (by omega)

/-- **A thread's access to a shared byte at or above `sharedBase + 212992`**: an intent there is a
thread's read or write event, with the state before it and its class. -/
theorem high_thread (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    {e : AsyncCopy.Ref} {a : Acc} {w : Bool} {l : Loc} (hI : X.Intent e a w) (hc : a.Covers l)
    (hsp : l.space = .shared) (hl : L.sharedBase + 212992 ≤ l.addr) :
    ∃ g k s, e = .thread (g, k) ∧ g < L.threads ∧ k < (X.tr g).length ∧
      St Q L X g k = some (some s) ∧
      ((w = true ∧ ∃ pc bs, X.get (g, k) = some ⟨pc, .wr a bs⟩ ∧ TWrite Q L g s a bs) ∨
        (w = false ∧ ∃ pc bs, X.get (g, k) = some ⟨pc, .rd a bs⟩ ∧ TRead L g s a)) := by
  have hsa : a.loc.space = .shared := hc.1.symm.trans hsp
  rcases e with ⟨g, k⟩ | ⟨i, p⟩
  · rcases hI with ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨old, new, pc, he⟩
    · have hg := Frame.lt_of_get hX he
      have hTT : TT Q L X (g, k) := fun h => hf.tracked g (k + 1) hg h
      obtain ⟨s, hσ⟩ := event_state_at hf.sound hX he (by intro pc f h; cases h) hTT
      exact ⟨g, k, s, rfl, hg, (List.getElem?_eq_some_iff.mp he).1, hσ,
        .inr ⟨rfl, pc, bs, he, thread_read_class hpre hX hf.sound hT hg he hσ hsa⟩⟩
    · have hg := Frame.lt_of_get hX he
      have hTT : TT Q L X (g, k) := fun h => hf.tracked g (k + 1) hg h
      obtain ⟨s, hσ⟩ := event_state_at hf.sound hX he (by intro pc f h; cases h) hTT
      exact ⟨g, k, s, rfl, hg, (List.getElem?_eq_some_iff.mp he).1, hσ,
        .inl ⟨rfl, pc, bs, he, thread_write_class hpre hX hf.sound hg he hσ hsa⟩⟩
    · exact absurd he (no_rmw hX)
  · exact (async_not_high hpre hX hf hI hc hsp hl).elim

/-- **Overlapping accesses of one thread are ordered** (program order). -/
theorem same_thread {g k k' : Nat} {a b : Acc} {we wf : Bool} {l : Loc}
    (he : X.Access (g, k) a we) (hf : X.Access (g, k') b wf) (hne : k ≠ k') (hov : a.Overlap b) :
    modelCausality L X l (.thread (g, k)) (.thread (g, k')) ∨
      modelCausality L X l (.thread (g, k')) (.thread (g, k)) := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact .inl (.inl (.single (.inl (po_of_overlap he hf rfl hlt hov))))
  · exact .inr (.inl (.single (.inl (po_of_overlap hf he rfl hlt hov.symm))))

/-- **Barrier-1 order.** An event that is no barrier-1 event, with at most `φ` barrier-1 events of
its thread before it, is causally before an event of a thread of its CTA with more than `φ`. -/
theorem b1_before (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hE : Bar1Exits L X) {g1 k1 g2 k2 φ : Nat} {e1 : Event} (hg1 : g1 < L.threads)
    (hg2 : g2 < L.threads) (hcta : g1 / L.block = g2 / L.block)
    (he1 : X.get (g1, k1) = some e1) (hnb : ¬ Execution.isBarId 1 e1 = true)
    (h1 : b1N X g1 k1 ≤ φ) (h2 : φ < b1N X g2 k2) (hk2 : k2 < (X.tr g2).length) :
    baseCausality L X (g1, k1) (g2, k2) := by
  obtain ⟨i2, pc2, hi2, hf2, hc2⟩ := arrival1_before hpre hX (h := g2) (k := k2) (r := φ) h2
  obtain ⟨j1, pcj, hf, hcj⟩ := bar1_has hpre hX hE (g := g1) hf2 (by omega) hcta
  have hgj : (X.tr g1)[j1]? = some ⟨pcj, .bar 1 none .sync⟩ := hf
  have hlt : k1 < j1 := before_lt1 (φ := φ) h1 he1 hnb hgj isBarId_bar (by rw [hcj]; exact hc2)
  exact Bar.bar1_baseCausality hpre hX ⟨hg1, hg2, hcta⟩ hf hf2 (by omega)
    (by rw [hcj, hc2]) hlt hi2 hk2

/-- A read event is no barrier-1 event. -/
theorem rd_not_b1 {pc : Nat} {a : Acc} {bs : List (Option Byte)} :
    ¬ Execution.isBarId 1 (⟨pc, .rd a bs⟩ : Event) = true := isBarId_rd

/-- A write event is no barrier-1 event. -/
theorem wr_not_b1 {pc : Nat} {a : Acc} {bs : List Byte} :
    ¬ Execution.isBarId 1 (⟨pc, .wr a bs⟩ : Event) = true := isBarId_wr

/-- **The barrier-1 count before an event**: the phase of its state, plus three per round of the
dispatch loop, which is at most one and none for the default partition and inside a role. -/
theorem b1N_phase (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) {g k : Nat} {s : TSt}
    (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some s)) :
    ∃ t, b1N X g k = (tPh s).2 + 3 * t ∧ (tKind s = 3 → t = 0) ∧ (tKind s = 1 → t = 0) ∧
      t ≤ 1 := by
  obtain ⟨-, t, -, h1, h3, h4, -, h5⟩ := phase_inv hpre hX hf.sound hR k s hk hσ
  exact ⟨t, h1, h3, h4, h5⟩

/-- **Two writes of one footprint and the same bytes are `SameValueWrites`.** -/
theorem same_value (hX : Consistent L kernel asms mem0 X) {e f : EvId} {pc pc' : Nat}
    {a b : Acc} {bs : List Byte} (he : X.get e = some ⟨pc, .wr a bs⟩)
    (hf : X.get f = some ⟨pc', .wr b bs⟩) (hl : a.loc = b.loc) (hz : a.size = b.size) :
    SameValueWrites X (.thread e) (.thread f) a b := by
  refine ⟨.inr (.inl ⟨bs, ⟨pc, he⟩, rfl⟩), .inr (.inl ⟨bs, ⟨pc', hf⟩, rfl⟩), ⟨hl, hz⟩, ?_⟩
  intro b1 b2 h1 h2
  rcases h1 with ⟨p1, h1⟩ | ⟨o1, p1, h1⟩
  · rcases h2 with ⟨p2, h2⟩ | ⟨o2, p2, h2⟩
    · rw [he] at h1
      rw [hf] at h2
      simp only [Option.some.injEq, Event.mk.injEq, Kind.wr.injEq] at h1 h2
      rw [← h1.2.2, ← h2.2.2]
    · exact absurd h2 (no_rmw hX)
  · exact absurd h1 (no_rmw hX)

end
end PTX.Kernels.InklingRelDecode.Proof.Safety
