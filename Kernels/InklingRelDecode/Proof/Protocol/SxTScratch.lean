-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SxTSm

@[expose] public section

/-!
# `SharedOrder.scratch`: the scratch words 2 and 3

The bytes `[sharedBase + 213000, sharedBase + 213008)` are the scratch words of warps 2 and 3 of
the default partition. The only accesses to them are the softmax region's `store10` and `ldL`
(`scratch_acc`: every other store and load of the program is at another address). Two conflicting
accesses of one thread are in program order, of two threads they are ordered by the barriers of
the softmax loop or are two stores of one warp in one iteration, which write the same value
(`sm_pair`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A thread's shared write is in its own CTA. -/
theorem twrite_cta {g : Nat} {s : TSt} {a : Acc} {bs : List Byte} (h : TWrite Q L g s a bs) :
    a.loc.cta = g / L.block := by
  cases h with
  | stq _ _ hl => rw [hl]
  | st8 _ ha => rw [ha]; rfl
  | st9_0 _ ha => rw [ha]; rfl
  | st9_1 _ ha => rw [ha]; rfl
  | store10 _ ha => rw [ha]; rfl
  | allocWr _ ha => rw [ha]
  | stTab _ ha => rw [ha]; rfl

/-- A thread's shared read is in its own CTA. -/
theorem tread_cta {g : Nat} {s : TSt} {a : Acc} (h : TRead L g s a) : a.loc.cta = g / L.block := by
  cases h with
  | dstart _ hl => rw [hl]
  | base _ hl => rw [hl]
  | role _ hl => rw [hl]
  | ld0 _ hl => rw [hl]
  | ld1 _ hl => rw [hl]
  | ldNum _ hl => rw [hl]
  | scratch _ hl => rw [hl]

/-- **The accesses to a byte of the scratch words 2 and 3** are the softmax region's. -/
theorem scratch_acc (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    {e : AsyncCopy.Ref} {a : Acc} {w : Bool} {l : Loc} (hI : X.Intent e a w) (hc : a.Covers l)
    (hl : InScratch L l) :
    ∃ g k, e = .thread (g, k) ∧ g < L.threads ∧ k < (X.tr g).length ∧ l.cta = g / L.block ∧
      SmAcc Q L X g k w := by
  obtain ⟨hsp, hlo, hhi⟩ := hl
  have hm1 := role_mod hpre
  have hm2 := pair_mod hpre
  obtain ⟨g, k, s, rfl, hg, hk, hσ, hcl⟩ := high_thread hpre hX hf hT hI hc hsp (by omega)
  obtain ⟨-, hcc, hca, hcb⟩ := hc
  rcases hcl with ⟨rfl, pc, bs, he, hW⟩ | ⟨rfl, pc, bs, he, hR'⟩
  · refine ⟨g, k, rfl, hg, hk, hcc.trans (twrite_cta hW), ?_⟩
    cases hW with
    | stq _ _ hl' hz h1 h2 =>
      rw [hl'] at hca hcb
      simp only [hz] at hcb
      simp only at hca hcb
      omega
    | st8 _ ha =>
      subst ha
      simp only [EvD.wordAcc, hm1] at hca hcb
      omega
    | st9_0 _ ha =>
      subst ha
      simp only [EvD.wordAcc, hm2] at hca hcb
      omega
    | st9_1 _ ha =>
      subst ha
      simp only [EvD.wordAcc, hm2] at hca hcb
      omega
    | store10 hs _ => exact ⟨_, hσ, .inl ⟨hs, rfl⟩⟩
    | allocWr _ ha =>
      subst ha
      simp only at hca hcb
      omega
    | stTab _ ha =>
      subst ha
      simp only [EvD.wordAcc, hm1] at hca hcb
      omega
  · refine ⟨g, k, rfl, hg, hk, hcc.trans (tread_cta hR'), ?_⟩
    cases hR' with
    | scratch hs _ _ => exact ⟨_, hσ, .inr ⟨hs, rfl⟩⟩
    | dstart _ hl' hz | base _ hl' hz | role _ hl' hz | ld0 _ hl' hz | ld1 _ hl' hz
    | ldNum _ hl' hz =>
      rw [hl'] at hca hcb
      simp only [hz] at hcb
      simp only at hca hcb
      omega

/-- **`SharedOrder.scratch`**: the conflicting accesses of the scratch words 2 and 3 are ordered,
but for the stores of one warp in one iteration. -/
theorem scratch_ordered (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    (hI : ∀ i, Lk.ScratchIt Q L X i) (hz : Rs.SmBaseZero Q L X) :
    ConflictsOrderedExcept L X (InScratch L) := by
  obtain ⟨hB, hP, hW⟩ := sm_facts hpre hX hf hI hz
  intro e f a b l hc ha hb hl hS
  obtain ⟨hne, we, wf, hie, hif, hw, hov⟩ := hc
  obtain ⟨g, k, rfl, hg, hk, hcg, h1⟩ := scratch_acc hpre hX hf hT hie ha hl
  obtain ⟨g', k', rfl, hg', hk', hcg', h2⟩ := scratch_acc hpre hX hf hT hif hb hl
  by_cases hgg : g = g'
  · subst hgg
    exact same_thread hie hif (fun h => hne (by rw [h])) hov
  exact (sm_pair hpre hX hf hB hP hW hg hg' hk hk' (hcg.symm.trans hcg') hie hif hw hov h1 h2
    hS).imp .inl .inl

end
end PTX.Kernels.InklingRelDecode.Proof.Safety
