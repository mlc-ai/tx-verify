-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SxRing
public import Kernels.InklingRelDecode.Proof.Protocol.SxTScratch
public import Kernels.InklingRelDecode.Proof.Protocol.IpTmAlloc
public import Kernels.InklingRelDecode.Proof.Interface.SxBaseFence
public import Kernels.InklingRelDecode.Proof.Interface.LpQStore

@[expose] public section

/-!
# `SharedOrder.base`

The thread accesses of the rings `[sharedBase, sharedBase + 196608)` are the allocation's store of
the base word (lane 0 of warp 0, `AllocStoreAt`) and the reads of the base word (`BaseReadAt`),
all of the four bytes at `sharedBase` (`ring_thread`). On the base word (`base_ordered`):

* the allocation's store is before every read (`Bar.allocStore_baseCausality_read`) and is the
  only store of the CTA's word but for the copies (one thread, `alloc_thread`);
* the store and the reads are before every copy's write through a `fence.proxy.async`
  (`early_before_copy`), and the store before every MMA read (`early_before_b1`: the MMA warp
  passed barrier 1, after thread 0's `fnc1`);
* the asynchronous pairs: `ring_async_ordered`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sx
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof AsyncCopy
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX.Kernels.InklingRelDecode.Proof.Bar

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The allocation's store is lane 0 of warp 0's.** -/
theorem alloc_thread (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    {g k : Nat} {e : Event} (he : X.get (g, k) = some e) (ha : AllocStoreAt Q L X g k) :
    g % L.block = 0 := by
  obtain ⟨tm, hσ⟩ := ha
  have h32 : g % L.block < 32 := by
    obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hf.sound hX he hσ
    simp [TSt.inv] at hinv
    have := hinv.2
    simp [DComp.Inv] at this
    exact this.lane0 (by simp)
  have hinit : TSt.d (.dstart ⟨.allocWr, tm⟩) ≠ (code L Q g).init := by
    intro h
    have : g % L.block < 128 := by omega
    have h' : TSt.d (.dstart ⟨.allocWr, tm⟩) = (if g % L.block < 128 then
        TSt.d (DComp.code L g Q).init else .w (WComp.code L g Q).init) := h
    simp only [this, ite_true, TSt.d.injEq] at h'
    simp only [DComp.St.dstart.injEq, DStart.D.start, h32, ite_true] at h'
    cases h'
  obtain ⟨k0, e0, s0, -, -, -, hn⟩ := stateAt_pred hσ hinit
  obtain ⟨-, hl⟩ := Tmem1.pred_allocWr hn
  unfold laneOf at hl
  omega

/-- **A thread access of a byte of the rings** is the allocation's store or a read of the base
word, of the four bytes at `sharedBase`. -/
theorem ring_thread (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    {g k : Nat} {a : Acc} {w : Bool} {l : Loc} (hI : X.Intent (.thread (g, k)) a w)
    (hc : a.Covers l) (hsp : l.space = .shared) (hhi : l.addr < L.sharedBase + 196608) :
    g < L.threads ∧ k < (X.tr g).length ∧ l.cta = g / L.block ∧ L.sharedBase ≤ l.addr ∧
      l.addr < L.sharedBase + 4 ∧
      ((w = true ∧ AllocStoreAt Q L X g k ∧ ∃ pc bs, X.get (g, k) = some ⟨pc, .wr a bs⟩) ∨
        (w = false ∧ BaseReadAt Q L X g k)) := by
  have hsa : a.loc.space = .shared := hc.1.symm.trans hsp
  have hm1 := role_mod hpre
  have hm2 := pair_mod hpre
  obtain ⟨-, hcc, hca, hcb⟩ := hc
  rcases hI with ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨old, new, pc, he⟩
  · have hg := Frame.lt_of_get hX he
    have hTT : TT Q L X (g, k) := fun h => hf.tracked g (k + 1) hg h
    obtain ⟨s, hσ⟩ := event_state_at hf.sound hX he (by intro pc f h; cases h) hTT
    have hR' := thread_read_class hpre hX hf.sound hT hg he hσ hsa
    refine ⟨hg, (List.getElem?_eq_some_iff.mp he).1, hcc.trans (tread_cta hR'), ?_⟩
    cases hR' with
    | @dstart d _ hs hl' hz =>
      rw [hl'] at hca hcb
      simp only [hz] at hcb
      simp only at hca hcb
      obtain ⟨site, tm⟩ := d
      simp only at hs
      subst hs
      exact ⟨hca, by omega, .inr ⟨rfl, .inl ⟨tm, hσ⟩⟩⟩
    | @base wd _ hs hl' hz =>
      rw [hl'] at hca hcb
      simp only [hz] at hcb
      simp only at hca hcb
      obtain ⟨site, P⟩ := wd
      simp only at hs
      subst hs
      exact ⟨hca, by omega, .inr ⟨rfl, .inr ⟨P, hσ⟩⟩⟩
    | role _ hl' hz | ld0 _ hl' hz | ld1 _ hl' hz | ldNum _ hl' hz | scratch _ hl' hz =>
      rw [hl'] at hca hcb
      simp only [hz] at hcb
      simp only at hca hcb
      omega
  · have hg := Frame.lt_of_get hX he
    have hTT : TT Q L X (g, k) := fun h => hf.tracked g (k + 1) hg h
    obtain ⟨s, hσ⟩ := event_state_at hf.sound hX he (by intro pc f h; cases h) hTT
    have hW := thread_write_class hpre hX hf.sound hg he hσ hsa
    refine ⟨hg, (List.getElem?_eq_some_iff.mp he).1, hcc.trans (twrite_cta hW), ?_⟩
    cases hW with
    | stq _ _ hl' hz h1 h2 =>
      rw [hl'] at hca hcb
      simp only [hz] at hcb
      simp only at hca hcb
      omega
    | st8 _ ha | st9_0 _ ha | stTab _ ha =>
      subst ha
      simp only [EvD.wordAcc, hm1, hm2] at hca hcb
      omega
    | st9_1 _ ha =>
      subst ha
      simp only [EvD.wordAcc, hm2] at hca hcb
      omega
    | store10 _ ha =>
      subst ha
      simp only [EvD.wordAcc] at hca hcb
      omega
    | @allocWr d _ _ hs ha =>
      subst ha
      simp only at hca hcb
      obtain ⟨site, tm⟩ := d
      simp only at hs
      subst hs
      exact ⟨hca, by omega, .inl ⟨rfl, ⟨tm, hσ⟩, pc, bs, he⟩⟩
  · exact absurd he (no_rmw hX)

/-- The barrier-0 facts of an access of the rings by a thread: at most one barrier-0 event before
it, and it is none. -/
theorem early_facts (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    {g k : Nat} (hk : k < (X.tr g).length)
    (h : AllocStoreAt Q L X g k ∨ BaseReadAt Q L X g k) :
    ((X.tr g).take k).countP (Execution.isBarId 0) ≤ 1 ∧
      ∀ ev, (X.tr g)[k]? = some ev → ¬ Execution.isBarId 0 ev = true := by
  rcases h with h | h
  · obtain ⟨h1, h2⟩ := allocStore_facts hX hf.sound hk h
    exact ⟨by omega, h2⟩
  · obtain ⟨h1, h2⟩ := baseRead_facts hX hf.sound hk h
    exact ⟨by omega, h2⟩

/-- **A thread access of the base word and an asynchronous access of it are ordered**: the
thread's comes first. -/
theorem base_thread_async (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    (hR : RoleReads L X) (hE : Bar1Exits L X) {g k : Nat} {i : EvId} {p : AsyncCopy.Part}
    {a b : Acc} {l : Loc} (hc : Conflict X (.thread (g, k)) (.async i p) a b) (ha : a.Covers l)
    (hb : b.Covers l) (hsp : l.space = .shared) (hhi : l.addr < L.sharedBase + 196608) :
    modelCausality L X l (.thread (g, k)) (.async i p) := by
  obtain ⟨-, we, wf, hie, hif, hw, -⟩ := hc
  obtain ⟨hg, hk, hcg, -, -, hcl⟩ := ring_thread hpre hX hf hT hie ha hsp hhi
  have hearly : AllocStoreAt Q L X g k ∨ BaseReadAt Q L X g k := by
    rcases hcl with ⟨-, h, -⟩ | ⟨-, h⟩
    · exact .inl h
    · exact .inr h
  obtain ⟨hc1, hn1⟩ := early_facts hX hf hk hearly
  have hcov : AsyncCovers X i p l := ⟨b, wf, hif, hb⟩
  obtain ⟨hgi, hci, h2⟩ := async_shared hpre hX hf hif hb hsp
  have hcta : i.1 / L.block = g / L.block := hci.symm.trans hcg
  rcases h2 with ⟨-, -, -, -, -, -, -, hq⟩ | ⟨idx, d, P, rfl, rfl, hσ, -⟩ |
      ⟨x, y, z, rfl, rfl, -⟩
  · exact absurd hq.2.1 (by omega)
  · -- an MMA read: the thread's access is the store
    have hwe : we = true := by rcases hw with h | h <;> first | exact h | cases h
    subst hwe
    obtain ⟨pc, c2, spec, acc, mask, hem, -⟩ := mma_read_at hX hcov
    have hli : i.2 < (X.tr i.1).length := len_of_get hem
    have hb1 := Lp.mma_b1 hpre hX hf hR hli.le hσ
    exact ⟨hcov, .inl (early_before_b1 hpre hX hf.sound hT hf.tracked hE hk hc1 hn1 hgi hli hb1
      hcta hg hsp hcg)⟩
  · obtain ⟨pc, a', sp, hei, -⟩ := copy_write_at hcov
    exact ⟨hcov, .inl (early_before_copy hpre hX hf.sound hT hf.tracked hE hR hk hc1 hn1 hei hcta
      hg hsp hcg)⟩

/-- **`SharedOrder.base`.** -/
theorem base_ordered (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    (hR : RoleReads L X) (hE : Bar1Exits L X) (hp : NumPreRead Q L X)
    (G : Sr.SrPkg L kernel asms mem0 X) (hMB : Mma.MmaBcast L X) (hpr : Lp.PreRing Q L X)
    (hsame : SameUseCopy Q L X) :
    ConflictsOrdered L X (InBase L) := by
  intro e f a b l hc ha hb hl
  obtain ⟨hsp, hlo, hhi⟩ := hl
  have hhi' : l.addr < L.sharedBase + 196608 := by omega
  obtain ⟨hne, we, wf, hie, hif, hw, hov⟩ := id hc
  rcases e with ⟨g, k⟩ | ⟨i, p⟩ <;> rcases f with ⟨g', k'⟩ | ⟨j, q⟩
  · obtain ⟨hg, hk, hcg, -, -, hcl⟩ := ring_thread hpre hX hf hT hie ha hsp hhi'
    obtain ⟨hg', hk', hcg', -, -, hcl'⟩ := ring_thread hpre hX hf hT hif hb hsp hhi'
    have hsc : SameCta L g g' := ⟨hg, hg', hcg.symm.trans hcg'⟩
    rcases hcl with ⟨rfl, ha1, pc, bs, he⟩ | ⟨rfl, hr1⟩ <;>
      rcases hcl' with ⟨rfl, ha2, pc', bs', he'⟩ | ⟨rfl, hr2⟩
    · have h0 := alloc_thread hX hf he ha1
      have h0' := alloc_thread hX hf he' ha2
      have hgg : g = g' := by
        have e1 := Nat.div_add_mod g L.block
        have e2 := Nat.div_add_mod g' L.block
        rw [h0] at e1
        rw [h0'] at e2
        rw [hsc.2.2] at e1
        omega
      subst hgg
      exact same_thread hie hif (fun h => hne (by rw [h])) hov
    · exact .inl (.inl (allocStore_baseCausality_read hpre hX hf.sound hf.tracked hsc hk ha1 hk'
        hr2))
    · exact .inr (.inl (allocStore_baseCausality_read hpre hX hf.sound hf.tracked
        ⟨hg', hg, hsc.2.2.symm⟩ hk' ha2 hk hr1))
    · exfalso
      rcases hw with h | h <;> cases h
  · exact .inl (base_thread_async hpre hX hf hT hR hE hc ha hb hsp hhi')
  · have hc' : Conflict X (.thread (g', k')) (.async i p) b a :=
      ⟨fun h => hne h.symm, wf, we, hif, hie, hw.symm, hov.symm⟩
    exact .inr (base_thread_async hpre hX hf hT hR hE hc' hb ha hsp hhi')
  · exact ring_async_ordered hpre hX hf hR hp G hMB hpr hsame hc ha hb hsp hhi'

end
end PTX.Kernels.InklingRelDecode.Proof.Sx
