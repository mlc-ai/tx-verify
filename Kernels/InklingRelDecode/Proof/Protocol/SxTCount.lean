-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SxTScratch
public import Kernels.InklingRelDecode.Proof.Protocol.MbarWords

@[expose] public section

/-!
# `SharedOrder.count`: the pair `(num_pre, num_iters)` and the scratch words 0 and 1

The bytes `[sharedBase + 212992, sharedBase + 213000)` have three groups of accesses
(`count_acc`), each with its number of barrier-1 events before it:

* the prologue's stores of `num_pre` and `num_iters` (`ProA.Site.st9_0`, `st9_1`), none;
* the loader's and the MMA warp's reads of the pair (`Loader.Site.ld0`, `ld1`, `Mma.Site.ldNum`),
  one (they are inside a role, in the first round of the dispatch loop);
* the softmax region's `store10` of warps 0 and 1 and its `ldL` (`SmAcc`), two.

Two conflicting accesses of one thread are in program order. Of two threads, the access with fewer
barrier-1 events before it is causally before the other (`b1_before`). With equal counts: two
prologue stores at one site write the same word (`Interface.early_stores_same`), two at different
sites do not overlap, two reads do not conflict, and two softmax accesses are `sm_pair`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The accesses to a byte of the pair `(num_pre, num_iters)`.** -/
theorem count_acc (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    (hR : RoleReads L X) {e : AsyncCopy.Ref} {a : Acc} {w : Bool} {l : Loc}
    (hI : X.Intent e a w) (hc : a.Covers l) (hl : InCount L l) :
    ∃ g k ev, e = .thread (g, k) ∧ g < L.threads ∧ k < (X.tr g).length ∧ l.cta = g / L.block ∧
      X.get (g, k) = some ev ∧ ¬ Execution.isBarId 1 ev = true ∧
      ((w = true ∧ b1N X g k = 0 ∧ ∃ d : ProA.D, St Q L X g k = some (some (.d (.pro d))) ∧
          ((d.site = .st9_0 ∧ l.addr < L.sharedBase + 212996) ∨
            (d.site = .st9_1 ∧ L.sharedBase + 212996 ≤ l.addr))) ∨
        (w = false ∧ b1N X g k = 1) ∨
        (b1N X g k = 2 ∧ SmAcc Q L X g k w)) := by
  obtain ⟨hsp, hlo, hhi⟩ := hl
  have hm1 := role_mod hpre
  have hm2 := pair_mod hpre
  obtain ⟨g, k, s, rfl, hg, hk, hσ, hcl⟩ := high_thread hpre hX hf hT hI hc hsp (by omega)
  obtain ⟨-, hcc, hca, hcb⟩ := hc
  obtain ⟨t, hb1, ht3, ht1, ht⟩ := b1N_phase hpre hX hf hR hk.le hσ
  rcases hcl with ⟨rfl, pc, bs, he, hW⟩ | ⟨rfl, pc, bs, he, hR'⟩
  · refine ⟨g, k, _, rfl, hg, hk, hcc.trans (twrite_cta hW), he, wr_not_b1, ?_⟩
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
    | @st9_0 d _ _ hs ha =>
      subst ha
      simp only [EvD.wordAcc, hm2] at hca hcb
      refine .inl ⟨rfl, ?_, d, hσ, .inl ⟨hs, by omega⟩⟩
      rw [hb1, ht3 rfl]
      simp [tPh, dPh, hs]
    | @st9_1 d _ _ hs ha =>
      subst ha
      simp only [EvD.wordAcc, hm2] at hca hcb
      refine .inl ⟨rfl, ?_, d, hσ, .inr ⟨hs, by omega⟩⟩
      rw [hb1, ht3 rfl]
      simp [tPh, dPh, hs]
    | @store10 d _ _ hs _ =>
      refine .inr (.inr ⟨?_, d, hσ, .inl ⟨hs, rfl⟩⟩)
      rw [hb1, ht3 rfl]
      simp [tPh, dPh, hs]
    | allocWr _ ha =>
      subst ha
      simp only at hca hcb
      omega
    | stTab _ ha =>
      subst ha
      simp only [EvD.wordAcc, hm1] at hca hcb
      omega
  · refine ⟨g, k, _, rfl, hg, hk, hcc.trans (tread_cta hR'), he, rd_not_b1, ?_⟩
    cases hR' with
    | @scratch d _ hs _ _ =>
      refine .inr (.inr ⟨?_, d, hσ, .inr ⟨hs, rfl⟩⟩)
      rw [hb1, ht3 rfl]
      simp [tPh, dPh, hs]
    | @ld0 d P _ hs _ _ =>
      refine .inr (.inl ⟨rfl, ?_⟩)
      rw [hb1, ht1 rfl]
      simp [tPh, wPh, hs]
    | @ld1 d P _ hs _ _ =>
      refine .inr (.inl ⟨rfl, ?_⟩)
      rw [hb1, ht1 rfl]
      simp [tPh, wPh, hs]
    | @ldNum d P _ hs _ _ =>
      refine .inr (.inl ⟨rfl, ?_⟩)
      rw [hb1, ht1 rfl]
      simp [tPh, wPh, hs]
    | dstart _ hl' hz | base _ hl' hz | role _ hl' hz =>
      rw [hl'] at hca hcb
      simp only [hz] at hcb
      simp only at hca hcb
      omega

/-- **`SharedOrder.count`**: the conflicting accesses of the pair `(num_pre, num_iters)` and of the
scratch words 0 and 1 are ordered, but for two stores of one word with one value. -/
theorem count_ordered (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    (hR : RoleReads L X) (hE : Bar1Exits L X) (hI : ∀ i, Lk.ScratchIt Q L X i)
    (hz : Rs.SmBaseZero Q L X) : ConflictsOrderedExcept L X (InCount L) := by
  obtain ⟨hB, hP, hW⟩ := sm_facts hpre hX hf hI hz
  have hwm : ProWordsMatch Q L X := Mbar.proWordsMatch hpre hX hf
  intro e f a b l hc ha hb hl hS
  obtain ⟨hne, we, wf, hie, hif, hw, hov⟩ := hc
  obtain ⟨g, k, ev, rfl, hg, hk, hcg, hev, hnb, hcl⟩ := count_acc hpre hX hf hT hR hie ha hl
  obtain ⟨g', k', ev', rfl, hg', hk', hcg', hev', hnb', hcl'⟩ :=
    count_acc hpre hX hf hT hR hif hb hl
  by_cases hgg : g = g'
  · subst hgg
    exact same_thread hie hif (fun h => hne (by rw [h])) hov
  have hcta : g / L.block = g' / L.block := hcg.symm.trans hcg'
  rcases lt_trichotomy (b1N X g k) (b1N X g' k') with hlt | heq | hgt
  · exact .inl (.inl (b1_before hpre hX hE hg hg' hcta hev hnb le_rfl hlt hk'))
  · rcases hcl with ⟨rfl, h0, d, hσ, hd⟩ | ⟨rfl, h0⟩ | ⟨h0, h1⟩ <;>
      rcases hcl' with ⟨rfl, h0', d', hσ', hd'⟩ | ⟨rfl, h0'⟩ | ⟨h0', h2⟩
    all_goals try (exfalso; omega)
    · -- two prologue stores
      exfalso
      have hsite : d.site = d'.site := by
        rcases hd with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases hd' with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
        all_goals first | omega | rw [h1, h2]
      have hE' : ProA.EarlySite d.site := by
        rcases hd with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [ProA.EarlySite]
      obtain ⟨-, rfl⟩ := early_stores_same hpre hX hf hwm hev hev' hσ hσ' hsite hE' hcta
      obtain ⟨pc1, bs1, he1⟩ := Safety.wr_of_intent hX hie
      obtain ⟨pc2, bs2, he2⟩ := Safety.wr_of_intent hX hif
      rw [hev'] at he2
      rw [hev] at he1
      rw [he1] at he2
      simp only [Option.some.injEq, Event.mk.injEq, Kind.wr.injEq] at he2
      obtain ⟨-, rfl, rfl⟩ := he2
      exact hS (same_value hX (hev.trans he1) (hev'.trans he1) rfl rfl)
    · rcases hw with h | h <;> cases h
    · exact (sm_pair hpre hX hf hB hP hW hg hg' hk hk' hcta hie hif hw hov h1 h2 hS).imp .inl .inl
  · exact .inr (.inl (b1_before hpre hX hE hg' hg hcta.symm hev' hnb' le_rfl hgt hk))

end
end PTX.Kernels.InklingRelDecode.Proof.Safety
