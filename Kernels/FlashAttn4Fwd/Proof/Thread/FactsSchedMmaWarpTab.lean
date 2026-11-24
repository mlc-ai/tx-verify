-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedLoaderExit
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedMma

@[expose] public section

/-! # The MMA warp's item table of warp collectives

A thread of warp 12 makes the prologue's four shuffles and its election (before the handshake
barrier's initialization), then the Q descriptor's broadcast `shflQ`, then per item the constant
broadcasts and the elections of its sites: before the trip loop three broadcasts and five
elections in slot 0, per trip six and eight in the trip's slot, after the loop five and seven
in slot `n` (`Mma.shA`, `Mma.elA`: `6 n + 2` and `8 n + 4` per item). The table `tabM` lists
their offsets in the MMA warp's band (`100 + mmaOff`), in program order.

An item site of region `k` has `idxM s` of the region's collectives before it, read off the
count formulas (`shA s + elA s` less the `shflQ` and the eight before the loop); the check over
every site (`check_sitesM`, by evaluation) compares each with the table: a broadcast or an
election is the table's entry, every other site is before it or past the region's last. The
MMAs' offsets are odd (one per MMA after the election), the others even (`check_evenM`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The MMA warp's item table: the offsets of its broadcasts and elections in its band. -/
def tabM : Sched.ItemTab :=
  ⟨[104, 106, 108, 120, 126, 128, 140, 144],
    [104, 106, 108, 110, 124, 126, 136, 142, 144, 146, 160, 164, 174, 178],
    [100, 104, 112, 114, 116, 118, 132, 138, 140, 142, 156, 160]⟩

/-- The prologue's four shuffles and election, the Q descriptor's broadcast. -/
def fixM : List Nat := [0, 2, 4, 6, prologue .shfl3, shflQT]

/-- The tail, past the exit at `+3024`. -/
def tailM (j : Nat) : Nat := 3030 + 2 * j

/-- The warp collectives' schedule of warp 12: on the odd CTA no item. -/
def mmaS (L : Launch) (c : Nat × Nat) (k : Nat) : Nat :=
  tabM.sched slotTime fixM tailM (Work.n L) (if c.1 % 2 = 0 then Tc L c.1 else 0) (Tc L c.1) k

theorem tabM_ok : tabM.Ok span := by unfold tabM Sched.ItemTab.Ok; decide

theorem mmaS_gap (hpre : Pre P L mem0) (c : Nat × Nat) (k : Nat) :
    mmaS L c k + 1 < mmaS L c (k + 1) :=
  Sched.ItemTab.sched_gap slotClock tabM_ok (by decide) (fun j => by unfold tailM; omega)
    (n_pos hpre) (by split_ifs <;> omega) k

theorem mmaS_even (c : Nat × Nat) (k : Nat) : mmaS L c k % 2 = 0 :=
  Sched.ItemTab.sched_even slotClock (by decide) (by decide) (by decide) (by decide)
    (fun j => by unfold tailM; omega) k

theorem tabM_len {n : Nat} (hn : 1 ≤ n) : tabM.len n = 14 * n + 6 := by
  simp only [Sched.ItemTab.len, tabM, List.length_cons, List.length_nil]
  omega

/-! ### The sites of an item -/

/-- The region's collectives before an item site. -/
def idxM (s : Mma.Site) : Nat := Mma.shA s + Mma.elA s - 1 - (if Mma.region s = 1 then 0 else 8)

/-- The offset of an MMA warp site in its slot. -/
def offM (s : Mma.Site) : Nat := 100 + mmaOff s

/-- The check of an item site against the item table. -/
def siteOkM (s : Mma.Site) : Bool :=
  let k := Mma.region s
  let l := tabM.rlist k
  let a := idxM s
  k == 0 ||
    (decide (1 + (if k = 1 then 0 else 8) ≤ Mma.shA s + Mma.elA s) &&
      s.loop == (if k = 1 then 0 else 1) &&
      if mmaKind s == .warp then decide (a < l.length) && l.getD a 0 == offM s
      else (decide (a < l.length) && decide (offM s < l.getD a 0)) || a == l.length)

theorem check_sitesM : Mma.allSites.all siteOkM = true := by decide +kernel

/-- The MMAs' offsets are odd, the other sites' even. -/
theorem check_evenM : Mma.allSites.all (fun s => s.isMma || mmaOff s % 2 == 0) = true := by
  decide +kernel

theorem siteOkM_of (s : Mma.Site) : siteOkM s = true :=
  List.all_eq_true.mp check_sitesM s (Mma.mem_allSites s)

theorem itemSite_region {s : Mma.Site} (h : Mma.ItemSite s) :
    Mma.region s = 1 ∨ Mma.region s = 2 ∨ Mma.region s = 3 := by
  cases s <;> simp only [Mma.ItemSite] at h <;>
    (repeat' (first | revert ‹Fin _› | revert ‹Bool›)) <;> decide

/-- The facts of an item site from the check. -/
theorem siteOkM_spec {s : Mma.Site} (hk : Mma.region s ≠ 0) :
    1 + (if Mma.region s = 1 then 0 else 8) ≤ Mma.shA s + Mma.elA s ∧
    s.loop = (if Mma.region s = 1 then 0 else 1) ∧
    (mmaKind s = .warp → idxM s < (tabM.rlist (Mma.region s)).length ∧
      (tabM.rlist (Mma.region s)).getD (idxM s) 0 = offM s) ∧
    (mmaKind s ≠ .warp →
      (idxM s < (tabM.rlist (Mma.region s)).length ∧
        offM s < (tabM.rlist (Mma.region s)).getD (idxM s) 0) ∨
      idxM s = (tabM.rlist (Mma.region s)).length) := by
  have h := siteOkM_of s
  unfold siteOkM at h
  simp only [show (Mma.region s == 0) = false from by simpa using hk, Bool.false_or,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun hw => ?_, fun hw => ?_⟩
  · simp only [hw, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h3
    exact h3
  · simp only [hw, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at h3
    exact h3

/-- The slot of an item site's region. -/
theorem time_itemM {n T : Nat} {d : Mma.D} (hs : Mma.ItemSite d.site) :
    mma n T d = slotTime n d.i (Sched.ItemTab.rslot n d.t (Mma.region d.site)) (offM d.site) := by
  rw [Mma.time_item_eq d hs]
  unfold mmaAt offM
  rcases itemSite_region hs with h | h | h <;> simp [h, Sched.ItemTab.rslot]

/-- The count of an item site. -/
theorem coll_itemM {d : Mma.D} (hn : 1 ≤ Work.n L) (hs : Mma.ItemSite d.site)
    (htr : Mma.TripOk L d) :
    4 + Mma.cnt L Mma.shA 6 2 d + (1 + Mma.cnt L Mma.elA 8 4 d) =
      fixM.length + (tabM.len (Work.n L) * d.i +
        (Sched.ItemTab.rbase tabM (Work.n L) d.t (Mma.region d.site) + idxM d.site)) := by
  have hk := itemSite_region hs
  obtain ⟨h1, h2, -⟩ := siteOkM_spec (s := d.site) (by omega)
  rw [tabM_len hn]
  have htn : Mma.trips L = Work.n L := rfl
  obtain ⟨n', hn'⟩ : ∃ n', Work.n L = n' + 1 := ⟨Work.n L - 1, by omega⟩
  unfold Mma.TripOk at htr
  unfold Mma.cnt idxM
  rw [h2, htn, hn']
  simp only [fixM, List.length_cons, List.length_nil]
  rw [htn, hn'] at htr
  rcases hk with hk | hk | hk <;> rw [hk] at h1 htr ⊢ <;>
    simp [Sched.ItemTab.rbase, tabM] at h1 htr ⊢
  · ring_nf; omega
  · ring_nf; omega
  · rw [show d.t = n' by omega]; ring_nf; omega

/-- **An item site of the MMA warp against the schedule.** -/
theorem mma_item (hpre : Pre P L mem0) {g : Nat} {d : Mma.D} (hi : Mma.Inv L g d)
    (hs : Mma.ItemSite d.site) :
    (mmaKind d.site = .warp → mma (Work.n L) (Work.T L g) d =
      mmaS L (warpKey L g) (4 + Mma.cnt L Mma.shA 6 2 d + (1 + Mma.cnt L Mma.elA 8 4 d))) ∧
    (mmaKind d.site ≠ .warp → mma (Work.n L) (Work.T L g) d <
      mmaS L (warpKey L g) (4 + Mma.cnt L Mma.shA 6 2 d + (1 + Mma.cnt L Mma.elA 8 4 d))) := by
  have hn := n_pos hpre
  obtain ⟨hw0, hr0⟩ := hi.i hs
  have hiT : d.i < Work.T L g := (Work.mma_work_lt hpre).mp hw0
  have hk := itemSite_region hs
  obtain ⟨-, -, hw, hnw⟩ := siteOkM_spec (s := d.site) (by omega)
  have hreg : Sched.ItemTab.RegOk (Work.n L) d.t (Mma.region d.site) := by
    have htr := hi.trip
    unfold Mma.TripOk at htr
    rcases hk with hk | hk | hk <;> rw [hk] at htr ⊢
    · exact .inl rfl
    · exact .inr (.inl ⟨rfl, htr⟩)
    · exact .inr (.inr rfl)
  have ho : offM d.site < span := by
    have := mmaOff_lt d.site; unfold offM; simp only [span]; omega
  unfold mmaS
  have hc : (warpKey L g).1 % 2 = 0 := hr0
  rw [Sched.ite_yes hc, show Tc L (warpKey L g).1 = Work.T L g from rfl, coll_itemM hn hs hi.trip,
    time_itemM hs]
  refine ⟨fun hk' => ?_, fun hk' => ?_⟩
  · obtain ⟨ha, hget⟩ := hw hk'
    rw [Sched.ItemTab.sched_reg hreg hiT ha, hget]
  · exact Sched.ItemTab.lt_sched_reg slotClock hn hreg hiT le_rfl ho (hnw hk')

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
