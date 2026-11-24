-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface

@[expose] public section

/-! # One tile per task of a cluster

A thread of cluster `c` holds tile `(m, n)` as its task `E` (`TaskTile`) when its trace shows it
(`Consumer.TileAt`): the first task is the cluster's own tile, which both CTAs of the pair name
alike (`claim_pair`); a later task is the tile of the CTA the response read after the thread's
successful response poll numbered `E - 1` claims, and two readers of one cluster read the same
response there (`AllResponsesAgree`, the read after a poll being of the response buffer by
`ThreadFacts.poll_read`). So a task has one tile (`taskTile_agree`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Flow

noncomputable section

namespace Result

variable {L : Launch} {X : Execution}

/-- Thread `g'` of cluster `c` shows tile `(m, n)` as its task `E`. -/
def TaskTile (L : Launch) (X : Execution) (c E m n : Nat) : Prop :=
  ∃ g' k', g' < L.threads ∧ g' / L.block / 2 = c ∧ k' ≤ (X.tr g').length ∧
    Consumer.TileAt L g' ((X.tr g').take k') E m n

/-- The two CTAs of a pair claim the same tile. -/
theorem claim_pair {a b : Nat} (h : a / 2 = b / 2) :
    Loader.claimM a = Loader.claimM b ∧ Loader.claimN a = Loader.claimN b := by
  simp only [Loader.claimM, Loader.claimN]
  constructor <;> split_ifs <;> omega

/-- The read of a thread's response after its successful response poll numbered `E`. -/
theorem readClaim_read (ht : ThreadFacts L X) {g k E x : Nat} (hg : g < L.threads)
    (hk : k ≤ (X.tr g).length) (h : Consumer.ReadClaim L g ((X.tr g).take k) E x) :
    ∃ j pc p acq sc pcr src bs rr,
      X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) = E ∧
      X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ ∧
      src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ ∧
      Flow.responseOf bs = some rr ∧ x = (rr.firstCta.map fun c => c.1.toNat).getD Loader.none32 :=
        by
  obtain ⟨j, pc, p, acq, sc, pcr, a, bs, rr, hj, hc, hj1, hr, hx⟩ := h
  have hl1 : j + 1 < ((X.tr g).take k).length := (List.getElem?_eq_some_iff.mp hj1).1
  simp only [List.length_take] at hl1
  rw [List.getElem?_take_of_lt (by omega)] at hj hj1
  rw [List.take_take, Nat.min_eq_left (by omega)] at hc
  obtain ⟨pcr', src, bs', hrd, hfp⟩ := ht.poll_read hg hj (by omega)
  have hj1' : X.get (g, j + 1) = some ⟨pcr, .rd a bs⟩ := hj1
  rw [hj1'] at hrd
  simp only [Option.some.injEq, Event.mk.injEq, Kind.rd.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  exact ⟨j, pc, p, acq, sc, pcr, a, bs, rr, hj, hc, hj1', hfp, hr, hx⟩

/-- **A task of a cluster has one tile.** -/
theorem taskTile_agree (ht : ThreadFacts L X) (hag : AllResponsesAgree L X) {c E m n m' n' : Nat}
    (h1 : TaskTile L X c E m n) (h2 : TaskTile L X c E m' n') : m = m' ∧ n = n' := by
  obtain ⟨g1, k1, hg1, hc1, hk1, ht1⟩ := h1
  obtain ⟨g2, k2, hg2, hc2, hk2, ht2⟩ := h2
  rcases ht1 with ⟨hE, rfl, rfl⟩ | ⟨x1, hE1, hr1, hx1, rfl, rfl⟩ <;>
    rcases ht2 with ⟨hE', rfl, rfl⟩ | ⟨x2, hE2, hr2, hx2, rfl, rfl⟩
  · exact claim_pair (by omega)
  · omega
  · omega
  · obtain ⟨j1, pc1, p1, acq1, sc1, pcr1, src1, bs1, rr1, hw1, hc1', hd1, hf1, hrr1, hx1'⟩ :=
      readClaim_read ht hg1 hk1 hr1
    obtain ⟨j2, pc2, p2, acq2, sc2, pcr2, src2, bs2, rr2, hw2, hc2', hd2, hf2, hrr2, hx2'⟩ :=
      readClaim_read ht hg2 hk2 hr2
    have hbs := hag c g1 g2 j1 j2 pc1 pc2 p1 p2 pcr1 pcr2 acq1 acq2 sc1 sc2 src1 src2 bs1 bs2
      hc1 hc2 hw1 hw2 (hc1'.trans hc2'.symm) hd1 hf1 hd2 hf2
    subst hbs
    rw [hrr1] at hrr2
    obtain rfl := Option.some.inj hrr2
    rw [hx1', ← hx2']
    exact ⟨rfl, rfl⟩

end Result

end
end PTX.Kernels.Fp16Gemm8192.Proof
