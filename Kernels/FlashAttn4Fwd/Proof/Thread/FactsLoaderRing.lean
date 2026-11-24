-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoader
public import Kernels.FlashAttn4Fwd.Proof.Interface.Async

@[expose] public section

/-! # The loader's thread facts: its copies on the ring

A tensor copy is the loader's copy `j` of the use of a copy site (`Loader.copy_origin`). Its
barrier is the use's full barrier in the even CTA of the pair, a ring barrier
(`Loader.bar_isFull`), and the copies before it there number `copies` per earlier round plus
`j < copies` (`CopyId.before`). At the copy site the loader has polled the partner empty barrier
once per round up to the copy's (`Loader.copy_round`, from `Counts.kvPoll`/`qPoll`), and the
copy's round names the item the loader is at (`Loader.use_item`): the facts `RingFacts.issue`,
`RingFacts.issue_use` and `AsyncFacts.copy_started` follow. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow Work

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Loader

theorem bar_isFull (L : Launch) (c : CopyId) : (c.bar L).isFull = true := by
  obtain ⟨u, j, i, t⟩ := c
  cases u <;> rfl

theorem bar_ring (L : Launch) (c : CopyId) : (c.bar L).ring = true := by
  obtain ⟨u, j, i, t⟩ := c
  cases u <;> rfl

/-- **At a copy site** the loader has polled the copy's partner empty barrier once more than
the copy's round, and the copy's index is below its barrier's copies per use. -/
theorem copy_round {g : Nat} {d : D} {u : UseK} {j : Fin 2} {pre : List Event}
    (hs : d.site = .copy u j) (hJ : Counts L g d pre) (hi : Inv L g d) :
    CopyId.round L ⟨u, j, d.i, d.t⟩ + 1 =
        okPolls ((CopyId.bar L ⟨u, j, d.i, d.t⟩).partner.loc L (ctaOf L g)) pre ∧
      j.val < (CopyId.bar L ⟨u, j, d.i, d.t⟩).copies := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  have hj := hi.one u j (.inr rfl)
  have hev := uB_even L i
  cases u <;> simp only [UseK.copies] at hj <;>
    simp only [CopyId.round, CopyId.bar, CopyId.use, FBar.partner, FBar.copies]
  all_goals first
    | (rw [hJ.kvPoll]; simp only [kvPolled]
       exact ⟨by unfold slotCount; omega, by split_ifs <;> omega⟩)
    | (rw [hJ.qPoll]; simp only [qPolled]; exact ⟨by simp, by omega⟩)

/-- The copies before a copy over its barrier's copies per use: its round. -/
theorem before_div {c : CopyId} (hj : c.j.val < (c.bar L).copies) :
    c.before L / (c.bar L).copies = c.round L ∧ c.before L % (c.bar L).copies = c.j.val := by
  have hpos : 0 < (c.bar L).copies := by omega
  unfold CopyId.before
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hj, Nat.add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

/-- `kvBlocks` is the loader's tile count. -/
theorem kvBlocks_eq (hpre : Pre P L mem0) : kvBlocks P = n L := by
  unfold kvBlocks n sk
  rw [skOf_eq hpre]

/-- A use of an item, after its first `r < 2 n`, over the item's uses: the item. -/
theorem uB_div {i r : Nat} (hr : r < 2 * n L) : (uB L i + r) / (2 * n L) = i ∧
    (uB L i + r) % (2 * n L) = r := by
  have hpos : 0 < 2 * n L := by omega
  unfold uB
  rw [Nat.mul_comm (2 * n L) i, Nat.add_comm, Nat.add_mul_div_right _ _ hpos,
    Nat.div_eq_of_lt hr, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  exact ⟨by omega, rfl⟩

/-- **The item and the block of a copy's round**: the state's item, and for a KV copy its
block. -/
theorem use_item (hpre : Pre P L mem0) {g : Nat} {d : D} {u : UseK} {j : Fin 2}
    (hs : d.site = .copy u j) (hi : Inv L g d) :
    useItem P (CopyId.bar L ⟨u, j, d.i, d.t⟩) (CopyId.round L ⟨u, j, d.i, d.t⟩) = d.i ∧
      (∀ s, CopyId.bar L ⟨u, j, d.i, d.t⟩ = .kvFull s →
        useBlock P (CopyId.bar L ⟨u, j, d.i, d.t⟩) (CopyId.round L ⟨u, j, d.i, d.t⟩) =
          CopyId.block L ⟨u, j, d.i, d.t⟩) := by
  have hn1 := (shape hpre).2.2.2.2.2.1
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  have hsix : ∀ U, 6 * (U / 6) + U % 6 = U := fun U => by omega
  cases u <;>
    simp only [CopyId.round, CopyId.bar, CopyId.use, CopyId.block, useItem, useBlock, hsix,
      reduceCtorEq, false_imp_iff, imp_true_iff, and_true, kvBlocks_eq hpre]
  · have := uB_div (L := L) (i := i) (r := 0) (by omega)
    simp only [Nat.add_zero] at this
    exact ⟨this.1, fun _ _ => by rw [this.2]; omega⟩
  · have := uB_div (L := L) (i := i) (r := 1) (by omega)
    exact ⟨this.1, fun _ _ => by rw [this.2]; omega⟩
  · have ht := hi.trip rfl
    have := uB_div (L := L) (i := i) (r := 2 + 2 * tt) (by simp at ht; omega)
    rw [← Nat.add_assoc] at this
    exact ⟨this.1, fun _ _ => by rw [this.2]; omega⟩
  · have ht := hi.trip rfl
    have := uB_div (L := L) (i := i) (r := 3 + 2 * tt) (by simp at ht; omega)
    rw [← Nat.add_assoc] at this
    exact ⟨this.1, fun _ _ => by rw [this.2]; omega⟩

end Loader

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **`RingFacts.issue`**: a copy on a ring barrier is an elected loader lane's, on a full
barrier of the pair's even CTA, of the barrier's copy bytes, within the copies its polls of the
partner empty barrier allow. -/
theorem RingFacts_issue : ∀ {g k pc a c : Nat} {b : FBar} {sp : TensorCopy.Spec}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar = b.loc L c → b.ring →
      b.isFull ∧ c = pairBase L g ∧ warpOf L g = 14 ∧ LeadAt L X g k ∧
      TensorTransfer.bytes sp.descriptor = b.copyBytes ∧
      ((X.tr g).take k).countP (issuesTo (b.loc L c)) + 1 ≤
        b.copies * okPolls (b.partner.loc L (ctaOf L g)) ((X.tr g).take k) := by
  intro g k pc a c b sp _ he hm _
  obtain ⟨d, hw, -, hJ, hi, hlead, u, j, hs, hci, hcnt⟩ := Loader.copy_origin hpre hX ht he
  obtain ⟨hb, hc⟩ := FBar.loc_inj (hm.symm.trans hci.mbar)
  subst hb hc
  obtain ⟨hr, hj⟩ := Loader.copy_round hs hJ hi
  rw [← hm, hcnt, ← hr]
  refine ⟨Loader.bar_isFull L _, rfl, hw, hlead, hci.bytes, ?_⟩
  simp only [Loader.CopyId.before] at hj ⊢
  rw [Nat.mul_succ]
  omega

/-- **`RingFacts.issue_use`**: a copy is of the use of its loader's last poll of the partner
empty barrier. -/
theorem RingFacts_issue_use : ∀ {g k pc a c : Nat} {b : FBar} {sp : TensorCopy.Spec},
    g < L.threads → X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar = b.loc L c → b.ring →
      ((X.tr g).take k).countP (issuesTo (b.loc L c)) / b.copies + 1 =
        okPolls (b.partner.loc L (ctaOf L g)) ((X.tr g).take k) := by
  intro g k pc a c b sp _ he hm _
  obtain ⟨d, -, -, hJ, hi, -, u, j, hs, hci, hcnt⟩ := Loader.copy_origin hpre hX ht he
  obtain ⟨hb, hc⟩ := FBar.loc_inj (hm.symm.trans hci.mbar)
  subst hb hc
  obtain ⟨hr, hj⟩ := Loader.copy_round hs hJ hi
  rw [← hm, hcnt, (Loader.before_div hj).1, hr]

/-- **`AsyncFacts.copy_started`**: a copy loads for an item its loader started. -/
theorem AsyncFacts_copy_started : ∀ {g k pc a c : Nat} {b : FBar} {sp : TensorCopy.Spec},
    g < L.threads → X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar = b.loc L c →
      b.isFull →
      workOf L g (useItem P b (((X.tr g).take k).countP (issuesTo (b.loc L c)) / b.copies)) <
        totOf L := by
  intro g k pc a c b sp _ he hm _
  obtain ⟨d, -, -, hJ, hi, -, u, j, hs, hci, hcnt⟩ := Loader.copy_origin hpre hX ht he
  obtain ⟨hb, hc⟩ := FBar.loc_inj (hm.symm.trans hci.mbar)
  subst hb hc
  obtain ⟨-, hj⟩ := Loader.copy_round hs hJ hi
  rw [← hm, hcnt, (Loader.before_div hj).1, (Loader.use_item hpre hs hi).1, totOf_eq' hpre]
  exact (Work.lt_T_iff hpre).mp (hi.item (by rw [hs]; rfl))

end
end PTX.Kernels.FlashAttn4Fwd.Proof
