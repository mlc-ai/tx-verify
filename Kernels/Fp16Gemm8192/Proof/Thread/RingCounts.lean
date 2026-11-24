-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.RingUsers
public import Kernels.Fp16Gemm8192.Proof.Thread.RingPolls
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderTasks
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaAcc
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerAcc
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleWarp
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcCount
public import Kernels.Fp16Gemm8192.Proof.Thread.SchedulerCount

@[expose] public section

/-! # The ring barriers' polls, arrivals, commits and copies along a thread

`RingEvent` says which role acts on which ring barrier (by the barrier's table); that role's
run then gives the count relation of the act: a poll uses the parity of the thread's successful
polls on the barrier (after them on an empty barrier), and an arrival, commit or copy on a
barrier is preceded by enough successful polls of its partner (`Bar.partner`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The input barriers in the loader's and the MMA thread's own terms. -/
theorem input_empty_bar (L : Launch) (g : Nat) (s : Fin 4) :
    Bar.loc L (g / L.block) ⟨.input, s.val, false⟩ = Loader.emptyOf L g s :=
  (InputRing.emptyLoc_bar L _ s).symm

theorem input_full_bar (L : Launch) (g : Nat) (s : Fin 4) :
    Bar.loc L (2 * (g / L.block / 2)) ⟨.input, s.val, true⟩ = Loader.fullOf L g s :=
  (InputRing.fullLoc_bar L _ s).symm

theorem mma_full_bar (L : Launch) (g : Nat) (s : Fin 4) :
    Bar.loc L (g / L.block) ⟨.input, s.val, true⟩ = Mma.fullOf L g s := by
  simp only [Bar.loc, Bar.off, Mma.fullOf, Loc.mk.injEq, true_and]
  omega

theorem mma_empty_bar (L : Launch) (g : Nat) (s : Fin 4) :
    Bar.loc L (g / L.block) ⟨.input, s.val, false⟩ = emptyAt L g s := by
  simp only [Bar.loc, Bar.off, emptyAt, Loc.mk.injEq, true_and]
  omega

/-- A poll of a ring barrier uses the parity of the thread's own successful polls on it, after
them on an empty barrier. -/
theorem poll_parity (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat}
    {e : Event} {d : ThreadD} {b : Bar} {cta p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hg : g < L.threads) (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k =
      some (some d))
    (hk : e.kind = .wait (b.loc L cta) p ok acq sc) (hb : b.Valid) :
    p % 2 = (okPolls (b.loc L cta) ((X.tr g).take k) + b.pollOffset) % 2 := by
  obtain ⟨hby, rfl⟩ := (ring_event hpre hX hg he hσ).wait _ _ _ _ _ _ hk hb
  obtain ⟨r, s, f⟩ := b
  simp only [Bar.Valid] at hb
  cases r <;> cases f <;> simp only [Ring.slots] at hb
  · obtain ⟨l, rfl⟩ := hby
    rw [input_empty_bar L g ⟨s, hb⟩] at hk ⊢
    exact RingPolls.producer_poll_parity hpre hX hg he hσ hk
  · obtain ⟨mm, rfl⟩ := hby
    rw [mma_full_bar L g ⟨s, hb⟩] at hk ⊢
    exact RingPolls.consumer_poll_parity hpre hX hg he hσ hk
  · obtain ⟨mm, rfl, -⟩ := hby
    exact Mma.acc_poll_parity hpre hX hg he hσ hb hk
  · obtain ⟨⟨cs, rfl⟩, -⟩ := hby
    exact Consumer.acc_poll_parity hpre hX hg he hσ hb hk
  · obtain ⟨sd, rfl⟩ := hby
    obtain rfl : s = 0 := by omega
    exact Scheduler.ack_poll_parity hpre hX hg he hσ hk
  · obtain ⟨r, rfl⟩ := hby
    obtain rfl : s = 0 := by omega
    simp only [Bar.pollOffset, ↓reduceIte, Nat.add_zero]
    exact (clc_counts hpre hX hg he hσ).1 _ _ _ _ hk

/-- An arrival on a ring barrier is preceded by enough successful polls of its gate in the
thread's CTA (`Bar.gate`, `Bar.gateSlack`). -/
theorem arrival_budget (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat}
    {e : Event} {d : ThreadD} {b : Bar} {cta tx c : Nat} {rel : Bool} {sc : MbarScope}
    (hg : g < L.threads) (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k =
      some (some d))
    (hk : e.kind = .arrive (b.loc L cta) tx c rel sc) (hb : b.Valid) :
    arrivals (b.loc L cta) ((X.tr g).take k) + b.gateSlack ≤
      okPolls (b.gate.loc L (g / L.block)) ((X.tr g).take k) := by
  obtain ⟨hby, rfl, -, -⟩ := (ring_event hpre hX hg he hσ).arrive _ _ _ _ _ _ hk hb
  obtain ⟨r, s, f⟩ := b
  simp only [Bar.Valid] at hb
  cases r <;> cases f <;> simp only [Ring.slots, Bar.arriveBy] at hb hby <;>
    simp only [Bar.arriveCta, Bar.arriveLeader, Bar.gate, Bar.gateSlack, ↓reduceIte,
      Bool.false_eq_true] at hk ⊢
  · obtain ⟨⟨l, rfl⟩, -⟩ := hby
    rw [input_full_bar L g ⟨s, hb⟩] at hk ⊢
    rw [input_empty_bar L g ⟨s, hb⟩]
    exact InputRing.arrival_budget hpre hX hg he hσ hk
  · obtain ⟨⟨cs, rfl⟩, -⟩ := hby
    exact Consumer.acc_arrival_budget hpre hX hg he hσ hb hk
  · obtain rfl : s = 0 := by omega
    obtain ⟨r, rfl⟩ : ∃ r, d = .inr r := by
      rcases hby with ⟨l, rfl⟩ | ⟨⟨m, rfl⟩, -⟩ | ⟨s, rfl⟩ | ⟨⟨c, rfl⟩, -⟩ <;> exact ⟨_, rfl⟩
    exact ((clc_counts hpre hX hg he hσ).2 _ _ _ _ hk).1
  · obtain rfl : s = 0 := by omega
    obtain ⟨sd, rfl⟩ := hby
    simpa using Scheduler.response_budget hpre hX hg he hσ hk

/-- A commit to a ring barrier is preceded by more successful polls of its partner than
earlier commits to it. -/
theorem commit_budget (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat}
    {e : Event} {d : ThreadD} {sp : TcCommit.Spec} {rank : Fin 16} {b : Bar} {cta : Nat}
    (hg : g < L.threads) (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k =
      some (some d))
    (hk : e.kind = .tc (.commit sp)) (ht : TcCommit.target sp rank = some (b.loc L cta))
    (hb : b.Valid) :
    ((X.tr g).take k).countP (commitsTo sp.mbar) + 1 ≤
      okPolls (b.partner.loc L (g / L.block)) ((X.tr g).take k) := by
  obtain ⟨hby, -, -, -, hmb⟩ := (ring_event hpre hX hg he hσ).commit _ _ _ _ hk ht hb
  obtain ⟨r, s, f⟩ := b
  simp only [Bar.Valid] at hb
  cases r <;> cases f <;> simp only [Ring.slots, Bar.commitBy] at hb hby
  · obtain ⟨mm, rfl⟩ := hby
    rw [mma_empty_bar L g ⟨s, hb⟩] at hmb
    rw [show Bar.partner ⟨.input, s, false⟩ = ⟨.input, s, true⟩ from rfl, mma_full_bar L g ⟨s, hb⟩,
      hmb]
    exact InputRing.commit_budget hpre hX hg he hσ hk hmb
  · obtain ⟨mm, rfl, -⟩ := hby
    exact Mma.acc_commit_budget hpre hX hg he hσ hb hk hmb

/-- A copy completing on a ring barrier is preceded by fewer earlier such copies than the
barrier's copies per successful poll of its partner. -/
theorem issue_budget (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat}
    {e : Event} {d : ThreadD} {b : Bar} {cta : Nat} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k = some (some d))
    (hi : issuesTo (b.loc L cta) e = true) (hb : b.Valid) :
    ((X.tr g).take k).countP (issuesTo (b.loc L cta)) + 1 ≤
      b.issues * okPolls (b.partner.loc L (g / L.block)) ((X.tr g).take k) := by
  obtain ⟨a, sp, hk, hm⟩ : ∃ a sp, e.kind = .tensorIssue a sp ∧ sp.mbar = b.loc L cta := by
    unfold issuesTo at hi
    split at hi
    · exact ⟨_, _, ‹_›, of_decide_eq_true hi⟩
    · cases hi
  obtain ⟨hby, rfl, -⟩ := (ring_event hpre hX hg he hσ).tensor _ _ _ _ hk hm hb
  obtain ⟨r, s, f⟩ := b
  simp only [Bar.Valid] at hb
  cases r <;> cases f <;> simp only [Ring.slots, Bar.copyBy] at hb hby
  obtain ⟨l, rfl⟩ := hby
  rw [input_full_bar L g ⟨s, hb⟩] at hi ⊢
  rw [show Bar.partner ⟨.input, s, true⟩ = ⟨.input, s, false⟩ from rfl, input_empty_bar L g ⟨s, hb⟩]
  exact InputRing.issue_budget hpre hX hg he hσ hi

/-- A cancellation request completing on a ring barrier is preceded by more successful polls of
its partner than earlier such requests. -/
theorem clc_budget (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat}
    {e : Event} {d : ThreadD} {sp : Clc.Spec} {tg : List Nat} {b : Bar}
    (hg : g < L.threads) (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k =
      some (some d))
    (hk : e.kind = .clcIssue sp tg) (hm : sp.mbar = b.loc L (g / L.block)) (hb : b.Valid) :
    ((X.tr g).take k).countP (clcIssuesTo sp.mbar) + 1 ≤
      b.issues * okPolls (b.partner.loc L (g / L.block)) ((X.tr g).take k) := by
  obtain ⟨b', hb', hby, hm', -, -⟩ := (ring_event hpre hX hg he hσ).clc _ _ hk
  obtain ⟨rfl, -⟩ := Bar.loc_inj hb hb' (hm.symm.trans hm')
  obtain ⟨r, s, f⟩ := b
  simp only [Bar.Valid] at hb
  cases r <;> cases f <;> simp only [Ring.slots, Bar.clcBy] at hb hby
  obtain rfl : s = 0 := by omega
  obtain ⟨⟨sd, rfl⟩, -⟩ := hby
  simpa [Bar.issues, Bar.partner] using Scheduler.cancel_budget hpre hX hg he hσ hk hm

end
end PTX.Kernels.Fp16Gemm8192.Proof
