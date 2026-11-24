-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Region.Accessors

@[expose] public section

/-! # The Tensor Memory base word is ordered

Only threads access the base word (`regions`). A thread's write of it is not a consumer's, whose
writes are its staging stores (`ThreadFacts.cons_out`): it is CTA thread 0's allocation write,
event 21, which happens before every role event of its cluster (`ThreadFacts.base_write`). A
thread's read of it is a role event (`ThreadFacts.read_role`). So two writes of a CTA's base word
are one event, and a write happens before every read (`baseOrdered`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

namespace Region

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A thread's access of a base word byte: CTA thread 0's write at event 21, happening before
every role event of its cluster, or a read from a role state. -/
theorem base_access (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {g k : Nat}
    {a : Acc} {w : Bool} {l : Loc} (h : X.Access (g, k) a w) (hc : a.Covers l)
    (hl : IsBase L l) :
    l.cta = g / L.block ∧
      ((w = true ∧ g % L.block = 0 ∧ k = 21 ∧ ∀ h j ev r, X.get (h, j) = some ev →
          Frame.stateAt (code L) X h j = some (some (.inr r)) → SameCluster L g h → baseCausality L
              X (g, k)
            (h, j)) ∨
        (w = false ∧ (∃ ev, X.get (g, k) = some ev) ∧
          ∃ r, Frame.stateAt (code L) X g k = some (some (.inr r)))) := by
  obtain ⟨hsp, hct, hlo, hhi⟩ := hc
  obtain ⟨-, hb1, hb2⟩ := hl
  rcases h with ⟨bs, ⟨pc, hget⟩, rfl⟩ | ⟨bs, ⟨pc, hget⟩, rfl⟩ | ⟨old, new, pc, hget⟩
  rotate_right
  · exact (Safety.no_rmw hX ht hget).elim
  · have hg := Frame.lt_of_get hX hget
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
    rcases (ht.access_region hg hget hσ).1 a bs rfl with ⟨hloc, -⟩ | ⟨hloc, -⟩
    · rw [hloc] at hlo
      simp only at hlo
      omega
    · rw [hloc] at hct
      obtain ⟨r, rfl⟩ := ht.read_role hg hget hσ rfl
      exact ⟨hct, .inr ⟨rfl, ⟨_, hget⟩, r, hσ⟩⟩
  · have hg := Frame.lt_of_get hX hget
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
    have hnc : ∀ c, d ≠ .inr (.cons c) := by
      rintro c rfl
      obtain ⟨-, hst, -⟩ := ht.cons_out hg hget hσ
      obtain ⟨s0, i0, el0, -, hloc, -⟩ := hst a bs rfl
      rw [hloc] at hlo
      simp only [Consumer.stagingOff] at hlo
      omega
    rcases (ht.access_region hg hget hσ).2.1 a bs rfl with ⟨c, rfl⟩ | ⟨hloc, -⟩
    · exact absurd rfl (hnc c)
    · rw [hloc] at hct
      obtain ⟨h0, h21, hhb⟩ := ht.base_write hg hget hσ rfl hnc
      exact ⟨hct, .inl ⟨rfl, h0, h21, hhb⟩⟩

/-- **The base word is ordered.** -/
theorem baseOrdered (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : BaseOrdered L X := by
  intro e f a b l hcon ha hb hl
  obtain ⟨hne, we, wf, he, hf, hw, -⟩ := hcon
  have thread_of : ∀ {ref : Ref} {c : Acc} {w : Bool}, X.Intent ref c w → c.Covers l →
      ∃ g k, ref = .thread (g, k) ∧ X.Access (g, k) c w := by
    intro ref c w h hc
    rcases regions hpre hX ht h hc hl.1 with ⟨⟨-, h1, -⟩, -⟩ | ⟨⟨-, h1, -⟩, -⟩ |
        ⟨⟨-, h1, -⟩, -⟩ | ⟨-, ⟨g, k⟩, rfl⟩
    all_goals try (exfalso; obtain ⟨-, -, h2⟩ := hl; omega)
    exact ⟨g, k, rfl, h⟩
  obtain ⟨g, k, rfl, hae⟩ := thread_of he ha
  obtain ⟨g', k', rfl, haf⟩ := thread_of hf hb
  obtain ⟨hcg, hce⟩ := base_access hX ht hae ha hl
  obtain ⟨hcg', hcf⟩ := base_access hX ht haf hb hl
  have hsame : ∀ {u v : Nat}, u < L.threads → v < L.threads → l.cta = u / L.block →
      l.cta = v / L.block → SameCluster L u v :=
    fun hu hv h1 h2 => ⟨hu, hv, by rw [← h1, ← h2]⟩
  rcases hce with ⟨rfl, h0, h21, hhb⟩ | ⟨rfl, ⟨ev, hev⟩, r, hr⟩ <;>
    rcases hcf with ⟨rfl, h0', h21', hhb'⟩ | ⟨rfl, ⟨ev', hev'⟩, r', hr'⟩
  · exfalso
    apply hne
    have hg : g = g' := by
      have h1 := Nat.div_add_mod g L.block
      have h2 := Nat.div_add_mod g' L.block
      rw [h0] at h1
      rw [h0'] at h2
      rw [← hcg, ← hcg'] at *
      omega
    rw [hg, h21, h21']
  · obtain ⟨evw, hevw⟩ : ∃ ev, X.get (g, k) = some ev := by
      rcases hae with ⟨bs, ⟨pc, h⟩, -⟩ | ⟨bs, ⟨pc, h⟩, -⟩ | ⟨o, n, pc, h⟩ <;> exact ⟨_, h⟩
    exact .inl (.inl
      (hhb g' k' ev' r' hev' hr'
        (hsame (Frame.lt_of_get hX hevw) (Frame.lt_of_get hX hev') hcg hcg')))
  · obtain ⟨evw, hevw⟩ : ∃ ev, X.get (g', k') = some ev := by
      rcases haf with ⟨bs, ⟨pc, h⟩, -⟩ | ⟨bs, ⟨pc, h⟩, -⟩ | ⟨o, n, pc, h⟩ <;> exact ⟨_, h⟩
    exact .inr (.inl
      (hhb' g k ev r hev hr (hsame (Frame.lt_of_get hX hevw) (Frame.lt_of_get hX hev) hcg' hcg)))
  · rcases hw with h | h <;> cases h

end Region

end

end PTX.Kernels.Fp16Gemm8192.Proof
