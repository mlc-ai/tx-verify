-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.QRingSlot
public import Kernels.FlashAttn4Fwd.Proof.Protocol.InitFirst
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Base
public import Lemmas.Protocol.PairTmaRing.CommitBound
public import Lemmas.Order.ElectOrdinal

@[expose] public section

/-! # Who blocks the MMA warp at a Q-full or KV-full poll

A slot of the Q or KV ring of pair `c` is the pair TMA ring slot `Rings.slot L X c b` (`b` its
full barrier). Its consumer is the elected lane of the even CTA's MMA warp, and its producers
are the elected loader lanes of both CTAs (`Rings.leadOf`). Every lane of the MMA warp polls the
full barrier, so a waiting lane need not be the consumer. Its blocker is stated through the
consumer's commits:

* `MmaRingBlocked`: when the full barrier's final phase has the parity of a number `n` at least
  the consumer's commits to the slot, the leader CTA's loader lane has made at most `n` arrivals
  on the barrier, or a loader lane of the pair has issued fewer than `n + 1` uses' copies on it,
  or a tensor copy has not completed (`PairTmaRing.full_blocked_of_commits`).
* `leadOf_selfElected`: each election a warp's lead thread made returned its lane, since all
  of the kernel's elections name the full mask (`ElectOk.deterministic`). When no thread of the
  warp is elected, its lane 0 made no election.
* `full_state`: the full barrier has a final state once a thread of the pair has made an event
  after the cluster start (its initialization precedes the start, `InitFirst.init_exists`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof AsyncCopy MBarrier

noncomputable section

namespace MmaRing

open Rings

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The lead thread of a warp of a launched CTA is a launched thread. -/
theorem leadOf_lt (hpre : Pre P L mem0) {cta w : Nat} (hc : cta < L.grid) (hw : w < 16) :
    leadOf L X cta w < L.threads := by
  unfold leadOf
  split
  · rename_i h
    exact h.choose_spec.1
  · have hb := hpre.block
    simp only [Launch.threads, hb] at ⊢
    nlinarith

/-- **A warp's lead thread is self-elected**: every election it made returned its lane. -/
theorem leadOf_selfElected (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    {cta w : Nat} (hw : w < 16) : SelfElected L X (leadOf L X cta w) := by
  intro j pc mask inst leader he
  have hy : leadOf L X cta w < L.threads := (hX.elect.1 _ _ _ _ _ he).1
  have hself : SameWarp L (leadOf L X cta w) (leadOf L X cta w) := ⟨⟨hy, hy, rfl⟩, rfl⟩
  by_cases hex : ∃ g, g < L.threads ∧ ctaOf L g = cta ∧ warpOf L g = w ∧ ∃ k, LeadAt L X g k
  · have hg : leadOf L X cta w = hex.choose := by simp only [leadOf, hex, dite_true]
    obtain ⟨-, -, -, k, j', -, pc', inst', hel⟩ := hex.choose_spec
    rw [← hg] at hel
    have hm := elect_full hX he
    subst hm
    exact hX.elect.deterministic he hel hself
  · -- the leader lane made an election of the same instance (`ElectOrd.partner`), which
    -- returned the same lane, so it is an elected thread of the warp
    have hb := hpre.block
    obtain ⟨-, -, hm⟩ := hX.elect.1 _ _ _ _ _ he
    have hl32 : leader < 32 := hm.1
    generalize hyd : leadOf L X cta w = y at he hy hself ⊢
    have hht : y - laneOf L y + leader < L.threads := by
      unfold laneOf Launch.threads at *
      rw [hb] at *
      omega
    have hsw : SameWarp L y (y - laneOf L y + leader) := by
      refine ⟨⟨hy, hht, ?_⟩, ?_⟩ <;> unfold laneOf <;> rw [hb] <;> omega
    have hlh : laneOf L (y - laneOf L y + leader) = leader := by
      unfold laneOf
      rw [hb]
      omega
    obtain ⟨x, pc0, pc', m0, m', inst', l0, l', h0, hx⟩ :=
      ElectOrd.partner hX hsw he (by rw [hlh]; exact hm)
    have h1 : X.get (y, j) = some ⟨pc0, .elect m0 inst' l0⟩ := h0
    have h2 : X.get (y, j) = some ⟨pc, .elect mask inst leader⟩ := he
    rw [h2] at h1
    simp only [Option.some.injEq, Event.mk.injEq, Kind.elect.injEq] at h1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
    obtain ⟨-, -, rfl, -⟩ := hX.elect.2.1 _ _ _ _ _ _ _ _ _ h0 hx hsw
    obtain ⟨hc, hwp⟩ := leadOf_place (X := X) (cta := cta) hpre hw
    rw [hyd] at hc hwp
    obtain ⟨⟨-, -, hct⟩, hwh⟩ := hsw
    refine absurd ⟨_, hht, ?_, ?_, x + 1, x, by omega, pc', inst, ?_⟩ hex
    · rw [← hc]; exact hct.symm
    · rw [← hwp]; exact hwh.symm
    · rw [hlh, ← elect_full hX hx]; exact hx

/-- **A ring full barrier has a final state** once a thread of its pair has made an event after
the cluster start. -/
theorem full_state (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (hi : InitFacts L X) (htm : TmemFacts L X) (ht : RingFacts L X)
    {b : FBar} (hb : b.isFull) {c g j : Nat} {ev : Event} (he : X.get (g, j) = some ev)
    (hk : ¬ PreKind ev.kind) (hub : ∀ f, ev.kind ≠ .ub f) (hcl : ctaOf L g / 2 = c) :
    ∃ before, stateBefore (X.objects (b.loc L (2 * c))) (X.objects (b.loc L (2 * c))).length =
      some before := by
  obtain ⟨e, pc, n, hinit⟩ := InitFirst.init_exists hpre hX hc hi b (cta := 2 * c) he hk hub
    (by omega)
  have hact : objectAction X X.async (b.loc L (2 * c)) (Ref.thread e) = some (.init n) := by
    simp [objectAction, hinit]
  obtain ⟨r, hr, -⟩ := (hX.tma.2.2.1 (b.loc L (2 * c))).2.2 (Ref.thread e) _ hact
  obtain ⟨r0, h0, ha0, hf0, -⟩ :=
    InitFirst.ringInit hpre hX hc htm hi ht (2 * c) b (isFull_ring hb) r hr
  have hni : NoInval (X.objects (b.loc L (2 * c))) :=
    objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, h⟩ => htm.no_inval h) _
  have hpos : 0 < (X.objects (b.loc L (2 * c))).length := List.length_pos_of_mem hr
  obtain ⟨s, hs, -⟩ := ObjectInit.checked_expected_after_init (X.objects_checked hX _) hni h0 ha0
    hf0 hpos (le_refl _)
  exact ⟨s, hs⟩

/-- **Who blocks the MMA warp's ring full polls.** When the full barrier `b` of pair `c` ends in
a phase of the parity of a number `n` at least the elected MMA lane's commits to the partner
empty barrier, the leader CTA's elected loader lane has made at most `n` arrivals on `b`, or the
elected loader lane of a CTA of the pair has issued fewer than `n + 1` uses' copies on `b`, or a
tensor copy has not completed. -/
def MmaRingBlocked (L : Launch) (X : Execution) : Prop :=
  ∀ c (b : FBar), b.isFull → ∀ {before : State} {n : Nat},
    stateBefore (X.objects (b.loc L (2 * c))) (X.objects (b.loc L (2 * c))).length =
      some before →
    (X.tr (leadOf L X (2 * c) 12)).countP (commitsTo (b.partner.loc L (2 * c))) ≤ n →
    before.phase % 2 = n % 2 →
    arrivals (b.loc L (2 * c)) (X.tr (leadOf L X (2 * c) 14)) ≤ n ∨
      (∃ a : Fin 2, (X.tr (leadOf L X (2 * c + a.val) 14)).countP
        (issuesTo (b.loc L (2 * c))) < b.copies * (n + 1)) ∨
      Descent.Obl L X .tensor

theorem mmaRingBlocked (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : RingFacts L X) (htm : TmemFacts L X) (hinit : RingInit L X) : MmaRingBlocked L X :=
  fun c _ hb _ _ hst hC hpar =>
    PairTmaRing.full_blocked_of_commits hX (hyp hpre hX ht htm hinit hb c) 0 hst hC hpar

end MmaRing

end
end PTX.Kernels.FlashAttn4Fwd.Proof
