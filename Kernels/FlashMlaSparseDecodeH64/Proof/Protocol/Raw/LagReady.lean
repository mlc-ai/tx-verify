-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Raw.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.ObjNe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.TmaLane
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MbarUse.Kinds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Tma
public import Lemmas.Protocol.TmaUnitsReach
public import Lemmas.Kernel.Progress.NextEv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Wait
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Time

@[expose] public section

/-! # The raw ring's ready side: progress row (`raw_ready`, wait at 2677)

A dequant lane waits at pc 2677 on `rawReady j` of its CTA with the parity of its successful polls
(offset 0). Block `r` of slot `j = r % 2` is filled by the TMA lane's arrival at `rrArr r` and its
sixteen loads before it, and awaited by the dequant lanes at `rrWait r` (`rr_lt`).

At a blocked poll the final phase is the waiter's successful polls `u`, and the TMA thread has made
no more than `u` arrivals or fewer than `16 (u + 1)` loads (`TmaUnits.Obj.reach_short`, reuse
paths `readyReach` from the ring, `KRing.reachF`). The blocker is the CTA's TMA producer `y`, the
lane the election chooses (hypothesis `hProd`, the statement of `tma_producer`): it is the TMA
thread, or it has made no event on the object (`rawReady_other`), so it is short of use `u` too.
Then `y` lags behind the waiter (`rawReady_lags`): before its election it has not exited and is no
later than `electSlot`; after its won election it is no later than the arrival slot of its next
arrival (`tma_rrEarly`) or its next load (`tma_riEarly`), `rrArr (2 u + j) < rrWait (2 u + j)`,
and it has not exited (`tma_rrExit`, `tma_riExit`). The schedule is the T note's item 5
(`τ u = rrArr (2 u + j) + 1`, `δ = 0`), used here through `blk_of_lagsN` with both counts. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section
set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The TMA producer of CTA `c`** (the statement of `tma_producer`): a lane of warp 5 of the CTA
that every lane with a `TmaOn` event is, before its election (no exit, time at most `electSlot`)
or with its won election. -/
def TmaProducer (P : Params) (L : Launch) (X : Execution) (c y : Nat) : Prop :=
  y / L.block = c ∧ y < L.threads ∧ MbarRow.warp L y = 5 ∧
    (∀ g k e, g / L.block = c → X.get (g, k) = some e → (∀ f, e.kind ≠ .ub f) →
      TmaOn L g e.pc → g = y) ∧
    (((∀ k pc, X.get (y, k) ≠ some ⟨pc, .exit⟩) ∧
        Sched.threadTime (timed P L) X y ≤ electSlot) ∨
      ∃ k inst, X.get (y, k) = some ⟨2165, .elect (2 ^ 32 - 1) inst (PTX.laneOf L y)⟩)

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **The producer lags behind the waiter**: a TMA producer of CTA `c` with no more than `u`
arrivals on `rawReady j` or fewer than `16 (u + 1)` loads to it, `u` below the CTA's uses of the
slot, has not exited and is earlier than the slot of the waited block's wait. -/
theorem rawReady_lags (hub : ¬ HasUb X) {c y u : Nat} {j : Fin 2} (hy : TmaProducer P L X c y)
    (hu : u < ringUses 2 j.val (blocksOf P L c))
    (hsh : arrivals (mbarLoc L c (.rawReady j)) (X.tr y) ≤ u ∨
      (X.tr y).countP (issuesTo (mbarLoc L c (.rawReady j))) < 16 * (u + 1)) :
    (∀ k pc, X.get (y, k) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (timed P L) X y < rrWait (2 * u + j.val) := by
  obtain ⟨hyc, -, -, -, hst⟩ := hy
  have hrr : ∀ a, a ≤ u → rrArr (2 * a + j.val) < rrWait (2 * u + j.val) := fun a ha => by
    simp only [rrArr, rrWait, frame, stride, loopBase, tmaOff, tmaRa, deqOff, deqWraw]
    omega
  rcases hst with ⟨hnx, ht⟩ | ⟨k, inst, hj⟩
  · exact ⟨hnx, lt_of_le_of_lt ht (elect_lt _ _)⟩
  rcases hsh with ha | hi
  · refine ⟨fun k pc hx => ?_, ?_⟩
    · have := tma_rrExit hp hX hFw hj (s := j) hyc hx
      omega
    · exact lt_of_le_of_lt (tma_rrEarly hp hX hFw hj hub hyc (by omega)) (hrr _ ha)
  · have h16 : 16 * (u + 1) ≤ 16 * ringUses 2 j.val (blocksOf P L c) := by omega
    refine ⟨fun k pc hx => ?_, ?_⟩
    · have := tma_riExit hp hX hFw hj (s := j) hyc hx
      omega
    · exact lt_of_le_of_lt (tma_riEarly hp hX hFw hj hub hyc (by omega))
        (hrr _ (by omega))

variable (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : RawInputs L X)
include hR hI hB hN

/-- **The reuse paths of `rawReady s`** as dequant lane `b` polls it (`KRing.reachF`). -/
theorem readyReach (c : Nat) (s : Fin 2) (b : Fin 128) :
    TmaUnits.Reach L kernel Assumptions.all X (mbarLoc L c (.rawReady s)) (tmaThread L X c) 16
      2304 (deqLane L c b) :=
  fun _ hx _ hj => (rawSlot hp hX hFw hR hI hB hN c s).reachF hX hx b hj

omit hp hFw hI hB in
/-- A lane with an arrival or a load on `rawReady s` of CTA `c` is the CTA's TMA thread. -/
theorem rawReady_lane {c y k : Nat} {s : Fin 2} {e : Event} (hy : y < L.threads)
    (he : X.get (y, k) = some e) (hm : Frame.MbarOf e (mbarLoc L c (.rawReady s)))
    (hw : ∀ p ok acq sc, e.kind ≠ .wait (mbarLoc L c (.rawReady s)) p ok acq sc)
    (hi : ∀ n, e.kind ≠ .mbInit (mbarLoc L c (.rawReady s)) n) : y = tmaThread L X c := by
  rcases rawReady_use hR hy he hm with ⟨n, hk⟩ | ⟨hT, hU, hc, -⟩ | ⟨-, -, ok, hk⟩
  · exact absurd hk (hi n)
  · have := tma_thread_eq hN.tmaOne he (notUb_of_kind (mbar_kind hX hR he hm)) hT hU
    rwa [hc] at this
  · exact absurd hk (hw _ _ _ _)

omit hp hFw hI hB in
/-- **A lane other than the TMA thread has made no event on `rawReady s`.** -/
theorem rawReady_other {c y : Nat} {s : Fin 2} (hy : y < L.threads) (hne : y ≠ tmaThread L X c) :
    arrivals (mbarLoc L c (.rawReady s)) (X.tr y) = 0 ∧
      (X.tr y).countP (issuesTo (mbarLoc L c (.rawReady s))) = 0 := by
  constructor
  · refine List.countP_eq_zero.mpr fun e hmem hpe => hne ?_
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp [arrivesOn, sourceArrive] at hpe
    subst hpe
    exact rawReady_lane hX hR hN hy hk rfl (by simp) (by simp)
  · refine List.countP_eq_zero.mpr fun e hmem hpe => hne ?_
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp [issuesTo] at hpe
    exact rawReady_lane hX hR hN hy hk hpe (by simp) (by simp)

/-- **A dequant lane's wait on `rawReady s` is blocked** by the lagging TMA producer of its CTA
(`hProd`, the statement of `tma_producer`) or an open tensor load, when the object's records do
not fault and the lane is past barrier 0. -/
theorem rawReady_blk (hub : ¬ HasUb X)
    (hProd : ∀ c, c * L.block < L.threads → ∃ y, TmaProducer P L X c y)
    {g q : Nat} {s : Fin 2} {sc : MbarScope} (hb0 : 0 < (X.tr g).countP isBar0)
    (hff : ∀ r ∈ X.objects (MbarRow.loc L g (.rawReady s)), r.fault = none)
    (hq : q = okPolls (MbarRow.loc L g (.rawReady s)) (X.tr g) % 2)
    (hrel : Step.Released L X g)
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨2677, .wait (MbarRow.loc L g (.rawReady s)) q false true sc⟩) :
    Sched.WaitBlk (timed P L) X g (MbarRow.loc L g (.rawReady s)) q := by
  simp only [MbarRow.loc] at hff hq hn ⊢
  obtain ⟨⟨-, hw8, hw12⟩, hlt, hwt⟩ := deq_rrWait hp hX hFw hn
  have hg := hn.lt
  obtain ⟨b, hb⟩ := deq_lane hp (pc := 2677) ⟨hw8, hw12, by decide, by decide⟩
  have O := rawReady_obj hp hX hFw hR hI hB hN.tmaOne (g / L.block) s
  have hb0' : 0 < ((X.tr g).take (X.tr g).length).countP isBar0 := by
    rw [List.take_length]
    exact hb0
  obtain ⟨st, hst⟩ := Unit.final_of_init hX O.init O.noInval
    (objects_ne hp hX hFw hI hg (.inr ⟨rfl, hrel⟩) hb0' (.rawReady s))
  refine ⟨st, hst, fun hpar => ?_⟩
  by_cases htens : Descent.Obl L X .tensor
  · exact .inl ⟨.tensor, .inr (.inr (.inl rfl)), htens⟩
  rw [hq, Nat.mod_mod] at hpar
  have hpar' : st.phase % 2 = okPolls (mbarLoc L (g / L.block) (.rawReady s))
      (X.tr (deqLane L (g / L.block) b)) % 2 := by
    rw [← hb]
    exact hpar
  obtain ⟨hph, hsh⟩ := O.reach_short hX (by decide)
    (readyReach hp hX hFw hR hI hB hN (g / L.block) s b)
    ((rawSlot hp hX hFw hR hI hB hN (g / L.block) s).altF hX b) hff htens hst hpar'
  rw [← hb] at hph
  have hcb : g / L.block * L.block < L.threads := by
    have := Nat.div_mul_le_self g L.block
    omega
  obtain ⟨y, hy⟩ := hProd (g / L.block) hcb
  obtain ⟨hyc, hyt, -⟩ := id hy
  have hsy : arrivals (mbarLoc L (g / L.block) (.rawReady s)) (X.tr y) ≤ st.phase ∨
      (X.tr y).countP (issuesTo (mbarLoc L (g / L.block) (.rawReady s))) <
        16 * (st.phase + 1) := by
    by_cases he : y = tmaThread L X (g / L.block)
    · rw [he]
      exact hsh
    · exact .inl (by rw [(rawReady_other hX hR hN hyt he).1]; exact Nat.zero_le _)
  rw [hph] at hsy
  obtain ⟨hnx, hyl⟩ := rawReady_lags hp hX hFw hub hy hlt hsy
  have hne : X.tr g ≠ [] := by
    intro h
    rw [h] at hb0
    simp at hb0
  exact Sched.blk_of_lagsN hX hub hg hne hyt (by rw [hyc]) fun _ => ⟨hnx, by omega⟩

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
