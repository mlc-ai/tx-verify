-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.KvSame

@[expose] public section

/-! # The base word on the role table

The four bytes at a CTA's shared base (`InBase`) are the base word the allocation stores and
every thread loads, and the first bytes of K slot 0.

* **Thread accesses** (`base_thread`): the allocation's store (before the thread's second
  barrier-0 event, so the CTA's thread 0's second event, `early_write`) and the startup's load
  (after exactly one barrier-0 event), by `wr_class`/`rd_class`.
* The store is before every load by barrier 0's first instance (`writer`, `bar0_before`).
* A thread access is before every tensor copy's write through the issuer's CTA's proxy fence,
  which comes after two barrier-0 events of its thread (`issue_fence`, `fence_c0`), and the
  store is before every MMA read through thread 0's fence and barrier 1's first instance
  (`thread0_before`).
* Two asynchronous accesses: `ring_async`.

`base_ordered : ConflictsOrdered L X (InBase L)`. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame AsyncCopy

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **A thread access of the base word**: the allocation's store, with at most one barrier-0
event before it, or a load after exactly one. -/
theorem base_thread (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {a : Acc} {w : Bool} {l : Loc} (hI : X.Access (g, k) a w) (hc : a.Covers l)
    (hl : Proof.Safety.InBase L l) :
    g < L.threads ∧ k < (X.tr g).length ∧ l.cta = g / L.block ∧ c0 X g (k + 1) ≤ 1 ∧
      ((w = true ∧ c0 X g k ≤ 1 ∧ ∃ pc bs, X.get (g, k) = some ⟨pc, .wr a bs⟩) ∨
        (w = false ∧ c0 X g k = 1)) := by
  obtain ⟨hsp, hlo, hhi⟩ := hl
  have hsr := hp.sharedRange
  unfold sharedBytes at hsr
  have hsa : a.loc.space = .shared := hc.1.symm.trans hsp
  obtain ⟨-, hcc, hca, hcb⟩ := hc
  rcases hI with ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨old, new, pc, he⟩
  · have hg := Frame.lt_of_get hX he
    have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    have hs1 : c0 X g (k + 1) = c0 X g k := by
      rw [c0_succ (show (X.tr g)[k]? = _ from he)]; simp [Execution.isBarId]
    cases rd_class hp hX he hsa with
    | base h hz h1 =>
      rw [h] at hcc
      exact ⟨hg, hk, hcc, by omega, .inr ⟨rfl, h1⟩⟩
    | role h4 _ h hz => simp only [h, hz] at hca hcb; omega
    | pair _ _ hz h => rcases h with h | h <;> omega
    | scratch h hz => simp only [h, hz] at hca hcb; omega
  · have hg := Frame.lt_of_get hX he
    have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    have hs1 : c0 X g (k + 1) = c0 X g k := by
      rw [c0_succ (show (X.tr g)[k]? = _ from he)]; simp [Execution.isBarId]
    cases wr_class hp hX he hsa with
    | base _ h1 => exact ⟨hg, hk, hcc, by omega, .inl ⟨rfl, h1, pc, _, he⟩⟩
    | qtile _ _ hz h1 _ => omega
    | role _ _ =>
      simp only [Proof.EvD.wordAcc] at hca hcb
      rw [Nat.mod_eq_of_lt (by omega)] at hca
      omega
    | pair _ _ hz h =>
      rw [Nat.mod_eq_of_lt (by omega)] at h
      rcases h with h | h <;> omega
    | scratch => simp only [Proof.EvD.wordAcc] at hca hcb; omega
  · exact absurd he (no_rmw hX)

/-- **A thread access of the base word is before every tensor copy's write of the CTA**, through
the issuer's CTA's proxy fence. -/
theorem base_before_copy (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k h j pc a' : Nat} {sp : TensorCopy.Spec} (hg : g < L.threads)
    (hc0 : c0 X g (k + 1) ≤ 1) (hi : X.get (h, j) = some ⟨pc, .tensorIssue a' sp⟩)
    {l : Loc} (hls : l.space = .shared) (hlc : l.cta = g / L.block)
    (hcta : h / L.block = g / L.block) : ProxyBefore L X (g, k) (h, j) l := by
  obtain ⟨f, jf, pcf, hfc, hft, hfget, hfb⟩ := issue_fence hp hX hi
  have hfl : jf < (X.tr f).length := (List.getElem?_eq_some_iff.mp hfget).1
  have hf2 := fence_c0 (Q := Q) hp hX hfget
  have hh := Frame.lt_of_get hX hi
  refine ⟨(f, jf), some (.shared .cta), none, ⟨pcf, hfget⟩, hft, ⟨hls, ?_⟩,
    ⟨hft, hh, by rw [hfc]⟩, ?_, hfb⟩
  · simp only; rw [hlc, hfc, hcta]
  · exact bar0_before (Q := Q) hp hX ⟨hg, hft, by rw [hfc, hcta]⟩ hfl (by omega) hc0

/-- **The allocation's store is before every MMA read of its CTA**, through thread 0's fence and
barrier 1's first instance. -/
theorem store_before_mma (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k h j : Nat} (hg : g < L.threads) (hk1 : k = 1)
    (h0 : g % L.block = 0) (hh : h < L.threads) (hc1 : 1 ≤ c1 X h j)
    (hj : j < (X.tr h).length) (hcta : h / L.block = g / L.block) {l : Loc}
    (hls : l.space = .shared) (hlc : l.cta = g / L.block) :
    ProxyBefore L X (g, k) (h, j) l := by
  have hb : L.block = 256 := hp.block
  have hg0 : h / L.block * L.block = g := by
    have := Nat.div_add_mod g L.block
    rw [hcta, Nat.mul_comm]; omega
  obtain ⟨jf, pcf, hget, hbase⟩ := thread0_before hp hX hh hc1 hj
  rw [hg0] at hget hbase
  have hjfl : jf < (X.tr g).length := (List.getElem?_eq_some_iff.mp hget).1
  have hf2 := fence_c0 (Q := Q) hp hX hget
  have hlt : k < jf := by
    have : c0 X g jf ≤ jf := by
      unfold c0
      exact List.countP_le_length.trans (by simp)
    omega
  refine ⟨(g, jf), some (.shared .cta), none, ⟨pcf, hget⟩, hg, ⟨hls, hlc⟩,
    ⟨hg, hh, by simp only; rw [hcta]⟩, ?_, hbase⟩
  exact .single (.inl (po_of_not_access rfl hlt hjfl (by rw [hget]; rfl)))

/-- **`SharedOrder.base` on the role table.** -/
theorem base_ordered (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    ConflictsOrdered L X (Proof.Safety.InBase L) := by
  intro e f a b l hc ha hb hl
  obtain ⟨hne, we, wf, hie, hif, hw, -⟩ := id hc
  have hl' := hl
  obtain ⟨hsp, hlo, hhi⟩ := hl
  have hhi' : l.addr < L.sharedBase + 196608 := by omega
  -- a thread access and an asynchronous one: the thread's access first
  have mixed : ∀ {g k h jj : Nat} {p : AsyncCopy.Part} {a b : Acc} {we wf : Bool},
      X.Intent (.thread (g, k)) a we → X.Intent (.async (h, jj) p) b wf → a.Covers l →
      b.Covers l → (we = true ∨ wf = true) →
      modelCausality L X l (.thread (g, k)) (.async (h, jj) p) := by
    intro g k h jj p a b we wf hie hif ha hb hw
    obtain ⟨hg, hk, hcg, hc0, hcl⟩ := base_thread hp hX hie ha hl'
    obtain ⟨hjt, hjc, -, hcls⟩ := async_shared hp hX hif hb hsp
    have hcta : h / L.block = g / L.block := hjc.symm.trans hcg
    refine ⟨⟨b, wf, hif, hb⟩, .inl ?_⟩
    rcases hcls with ⟨isB, idx, rfl, -, hjl, ⟨tm', d, P, n', hσm⟩, -, -⟩ | ⟨x, y, z, rfl, -⟩
    · have hwf : wf = false := hif.1
      rcases hcl with ⟨-, h1, pc, bs, hget⟩ | ⟨rfl, -⟩
      · obtain ⟨hk1, h0, -, -⟩ := early_write (Q := Q) hp hX hget h1
        exact store_before_mma hp hX hg hk1 h0 hjt (mma_c1 hp hX hjt hjl hσm) hjl hcta hsp hcg
      · rcases hw with h | h <;> simp_all
    · obtain ⟨pc, a', sp, hei, -⟩ := copy_write_at ⟨b, wf, hif, hb⟩
      exact base_before_copy hp hX hg hc0 hei hsp hcg hcta
  rcases e with ⟨g, k⟩ | ⟨⟨h, jj⟩, p⟩ <;> rcases f with ⟨g', k'⟩ | ⟨⟨h', jj'⟩, q⟩
  · obtain ⟨hg, hk, hcg, -, hcl⟩ := base_thread hp hX hie ha hl'
    obtain ⟨hg', hk', hcg', -, hcl'⟩ := base_thread hp hX hif hb hl'
    have hsc : SameCta L g g' := ⟨hg, hg', hcg.symm.trans hcg'⟩
    -- the store is the CTA's thread 0's second event
    have hst : ∀ {u v : Nat}, c0 X u v ≤ 1 → ∀ {pc a bs}, X.get (u, v) = some ⟨pc, .wr a bs⟩ →
        u = u / L.block * L.block ∧ v = 1 := by
      intro u v h1 pc a bs hget
      obtain ⟨rfl, h0, -, -⟩ := early_write (Q := Q) hp hX hget h1
      refine ⟨?_, rfl⟩
      have := Nat.div_add_mod u L.block
      rw [h0] at this
      rw [Nat.mul_comm]; omega
    -- the store is before a load
    have hsl : ∀ {u v u' v' : Nat}, SameCta L u u' → c0 X u v ≤ 1 →
        (∃ pc a bs, X.get (u, v) = some ⟨pc, .wr a bs⟩) → v' < (X.tr u').length →
        c0 X u' v' = 1 → baseCausality L X (u, v) (u', v') := by
      intro u v u' v' hs h1 ⟨pc, a, bs, hget⟩ hv' h1'
      obtain ⟨hu0, hv⟩ := hst h1 hget
      obtain ⟨-, hc2⟩ := writer (Q := Q) hp hX hs.2.1 hv' h1'
      have hcc : u' / L.block * L.block = u := by rw [← hs.2.2, ← hu0]
      rw [hcc] at hc2
      rw [hv]
      exact bar0_before (Q := Q) hp hX hs hv' (by rw [hc2, h1']; omega) (by rw [hc2]; omega)
    rcases hcl with ⟨rfl, h1, pc, bs, he⟩ | ⟨rfl, h1⟩ <;>
      rcases hcl' with ⟨rfl, h1', pc', bs', he'⟩ | ⟨rfl, h1'⟩
    · exfalso
      obtain ⟨e1, e2⟩ := hst h1 he
      obtain ⟨e3, e4⟩ := hst h1' he'
      have hgg : g = g' := by rw [e1, e3, hsc.2.2]
      exact hne (by rw [hgg, e2, e4])
    · exact .inl (.inl (hsl hsc h1 ⟨pc, a, bs, he⟩ hk' h1'))
    · exact .inr (.inl (hsl ⟨hg', hg, hsc.2.2.symm⟩ h1' ⟨pc', b, bs', he'⟩ hk h1))
    · exfalso
      rcases hw with h | h <;> cases h
  · exact .inl (mixed hie hif ha hb hw)
  · exact .inr (mixed hif hie hb ha hw.symm)
  · exact ring_async hp hX hc ha hb hsp hhi'

end
end PTX.Kernels.InklingRelDecode.Proof2
