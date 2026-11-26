-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Raw.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Lag
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.ObjNe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.TmaLane
public import Lemmas.Protocol.UnitReachBlocker
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar0
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Time

@[expose] public section

/-! # The raw ring's free side: progress row (`raw_free`, wait at 2245)

The TMA lane waits at pc 2245 on `rawFree j` of its CTA with the parity of its successful polls
plus one (the first use of each slot passes). Block `r` of slot `j = r % 2` is released by the 128
dequant lanes' arrivals at `rfArr r` and awaited by the TMA lane in block `r + 2` at
`rfWait (r + 2)` (`rf_lt`). The schedule (`rawFree_lag`, `Sched.LagN`, `δ = 1`):
`τ u = 0` for `u = 0`, else `rfArr (2 (u - 1) + j) + 1`; producers the dequant lanes short of the
CTA's uses of the slot (`deq_rfEarly`, `deq_rfExit`), consumers the lanes whose next event is the
wait (`tma_rfWait`).

At a blocked poll with a successful earlier poll, the final phase is the TMA lane's successful
polls less one and some dequant lane has made no more arrivals (`Unit.Obj.reach_short`, reuse
paths `freeReach` from the ring, `KRing.reachE`). Before its first successful poll the object is
still in phase 0 (`rawFree_first`: an arrival of the slot would follow a dequant lane's
successful poll of `rawReady j`, which observes the TMA lane's arrival, which follows the TMA
lane's successful poll of `rawFree j`), so the poll with parity 1 is not blocked. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section
set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The producers of `rawFree j` of CTA `c` while they lag: its dequant lanes short of the
uses of the slot. -/
def FreeProd (P : Params) (L : Launch) (X : Execution) (c : Nat) (j : Fin 2) (y : Nat) : Prop :=
  (∃ a, y = deqLane L c a) ∧
    arrivals (mbarLoc L c (.rawFree j)) (X.tr y) < ringUses 2 j.val (blocksOf P L c)

/-- Lane `g`'s next event is the wait at 2245 on `rawFree j` of CTA `c`. -/
def FreeCons (L : Launch) (m : Mem0) (X : Execution) (c : Nat) (j : Fin 2) (g : Nat) : Prop :=
  ∃ p ok acq sc, Sched.NextEv L kernel Assumptions.all m X g
    ⟨2245, .wait (mbarLoc L c (.rawFree j)) p ok acq sc⟩

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **The `rawFree` schedule** of slot `j` of CTA `c`. -/
theorem rawFree_lag (hub : ¬ HasUb X) (c : Nat) (j : Fin 2) :
    Sched.LagN (timed P L) X (mbarLoc L c (.rawFree j)) 1 (FreeProd P L X c j)
      (FreeCons L m X c j) (fun u => if u = 0 then 0 else rfArr (2 * (u - 1) + j.val) + 1)
      (ringUses 2 j.val (blocksOf P L c)) (arrivesOn (mbarLoc L c (.rawFree j))) := by
  refine ⟨fun a b h => ?_, fun g hg => ?_, fun y hy hyt => ?_, fun y k pc hy hx => ?_,
    fun g hg => ?_⟩
  · simp only [rfArr, frame, stride, loopBase, deqOff, deqArrF]
    split_ifs <;> omega
  · obtain ⟨p, ok, acq, sc, hn⟩ := hg
    obtain ⟨-, -, hw⟩ := tma_rfWait hp hX hFw hn
    split_ifs with h0
    · exact Nat.zero_le _
    · have := rf_lt (2 * (okPolls (mbarLoc L c (.rawFree j)) (X.tr g) - 1) + j.val)
      have he : 2 * (okPolls (mbarLoc L c (.rawFree j)) (X.tr g) - 1) + j.val + 2 =
          2 * okPolls (mbarLoc L c (.rawFree j)) (X.tr g) + j.val := by omega
      rw [he] at this
      omega
  · obtain ⟨⟨a, rfl⟩, hlt⟩ := hy
    have := deq_rfEarly hp hX hFw hub (deqLane_warp hp c a) hyt (deqLane_cta hp c a) hlt
    simp only [arrivals] at this ⊢
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    omega
  · obtain ⟨⟨a, rfl⟩, -⟩ := hy
    exact deq_rfExit hp hX hFw (deqLane_warp hp c a) (deqLane_cta hp c a) hx
  · obtain ⟨p, ok, acq, sc, hn⟩ := hg
    have := (tma_rfWait hp hX hFw hn).2.1
    omega

variable (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : RawInputs L X)
include hR hI hB hN

/-- **The reuse paths of `rawFree s`** as the TMA lane polls it (`KRing.reachE`). -/
theorem freeReach (c : Nat) (s : Fin 2) :
    Unit.Reach L kernel Assumptions.all X (mbarLoc L c (.rawFree s)) 128 (deqLane L c) 1
      (tmaThread L X c) :=
  fun _ hx _ hj => (rawSlot hp hX hFw hR hI hB hN c s).reachE hX hx 0 (by omega) (by omega)

/-- **Before the TMA lane's first successful poll of `rawFree s` the object is in phase 0.** -/
theorem rawFree_first (c : Nat) (s : Fin 2) {st : MBarrier.State}
    (hst : MBarrier.stateBefore (X.objects (mbarLoc L c (.rawFree s)))
      (X.objects (mbarLoc L c (.rawFree s))).length = some st)
    (h0 : okPolls (mbarLoc L c (.rawFree s)) (X.tr (tmaThread L X c)) = 0) : st.phase = 0 := by
  classical
  by_contra hne
  have O := rawFree_obj hp hX hFw hR hI hB c s
  have hch := X.objects_checked hX (mbarLoc L c (.rawFree s))
  have hU := hch.card_unit_arrivals_phase O.noInval (n := 128) (q := 0)
    (fun p r c tx hr _ ha => (O.arrive_rec hr ha).1)
    (fun p st' _ hs' => PairTmaRing.expected_of_init hX O.init O.noInval hs') O.noIncrement
    le_rfl hst (by omega)
  obtain ⟨p, hp'⟩ := Finset.card_pos.mp (by rw [hU]; decide)
  obtain ⟨-, r, tx, hr, ha, hf, -⟩ := Finset.mem_filter.mp hp'
  obtain ⟨x, hx, -⟩ := O.rec_S hr hf ha
  let R := rawSlot hp hX hFw hR hI hB hN c s
  obtain ⟨i, -, -, hcnt⟩ := R.polE x hx
  have h4 : okPolls R.F ((X.tr (R.cons x.1)).take i) ≤ okPolls R.F (X.tr (R.cons x.1)) :=
    (List.take_sublist i _).countP_le
  have h1 : 0 < okPolls R.F (X.tr (R.cons x.1)) := by omega
  obtain ⟨hS, -⟩ := R.full_observes hX h1 0
  obtain ⟨i', -, -, hc'⟩ := R.polF _ hS
  have h2 : okPolls R.E ((X.tr (R.prod (R.ownF (0, 0).1))).take i') ≤
      okPolls R.E (X.tr (R.prod (R.ownF (0, 0).1))) := (List.take_sublist i' _).countP_le
  have h3 : okPolls R.E (X.tr (R.prod (R.ownF (0, 0).1))) = 0 := h0
  omega

/-- **The TMA lane's wait on `rawFree s` is blocked** by a lagging dequant lane, when the
object's records do not fault. -/
theorem rawFree_blk (hub : ¬ HasUb X) {g q : Nat} {s : Fin 2} {sc : MbarScope}
    (hff : ∀ r ∈ X.objects (MbarRow.loc L g (.rawFree s)), r.fault = none)
    (hq : q = (okPolls (MbarRow.loc L g (.rawFree s)) (X.tr g) + 1) % 2)
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨2245, .wait (MbarRow.loc L g (.rawFree s)) q false true sc⟩) :
    Sched.WaitBlk (timed P L) X g (MbarRow.loc L g (.rawFree s)) q := by
  simp only [MbarRow.loc] at hff hq hn ⊢
  obtain ⟨⟨k, e, he, hu, hon⟩, hlt, -⟩ := tma_rfWait hp hX hFw hn
  have hg := hn.lt
  have hy : g = tmaThread L X (g / L.block) := tma_thread_on hN.tmaOne he hu hon
  have hb0 := bar0_before hp hX hFw he hu (by have := hon.2; omega)
  have O := rawFree_obj hp hX hFw hR hI hB (g / L.block) s
  obtain ⟨st, hst⟩ := Unit.final_of_init hX O.init O.noInval
    (objects_ne hp hX hFw hI hg (.inl (List.getElem?_eq_some_iff.mp he).1) hb0 (.rawFree s))
  refine ⟨st, hst, fun hpar => ?_⟩
  rw [hq, Nat.mod_mod] at hpar
  have hpar' : st.phase % 2 = (okPolls (mbarLoc L (g / L.block) (.rawFree s))
      (X.tr (tmaThread L X (g / L.block))) + 1) % 2 := by
    rw [← hy]
    exact hpar
  by_cases h0 : okPolls (mbarLoc L (g / L.block) (.rawFree s)) (X.tr g) = 0
  · rw [h0] at hpar
    have := rawFree_first hp hX hFw hR hI hB hN (g / L.block) s hst (by rw [← hy]; exact h0)
    omega
  obtain ⟨hph, a, ha⟩ := O.reach_short hX (freeReach hp hX hFw hR hI hB hN (g / L.block) s) hff
    hst (by rw [← hy]; omega) hpar'
  rw [← hy] at hph
  have hcy := deqLane_cta hp (g / L.block) a
  have hyl : deqLane L (g / L.block) a < L.threads := by
    have := a.isLt
    have h := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) (g := 256 + a.val)
      (by rw [hp.block]; omega)
    simp only [deqLane]
    omega
  have hne' : X.tr g ≠ [] := by
    intro h
    simp [Execution.get, h] at he
  exact (rawFree_lag hp hX hFw hub (g / L.block) s).blk hX hub hg ⟨_, _, _, _, hn⟩ hne'
    ⟨⟨a, rfl⟩, by omega⟩ hyl (by rw [hcy]) (by simp only [arrivals] at ha; omega)

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
