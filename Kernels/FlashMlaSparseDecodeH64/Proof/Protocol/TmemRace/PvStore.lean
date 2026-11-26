-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Order
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Score.LagQk
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Block
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Block
public import Lemmas.Protocol.StagingHandoff
public import Lemmas.Protocol.UnitHandoff
public import Lemmas.Order.OrderWaits
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Ring

@[expose] public section

/-! # The PV/rescale order (`PvStoreOrder`)

A PV MMA `x` of block `d` (`mma_pvBlock`) and a rescale store `y` of warpgroup 0 of block `r`
(`wg0_stBlock`) of one CTA are ordered by the score ring of slot `j = r % 2`, use `u = r / 2`:

* `r ≤ d` (`store_first`): the store's wait `tcgen05.wait::st` is its next event
  (`wg0_stWait`), before the lane's arrival of use `u` on `soReady j`; the MMA lane polled
  `soReady j` for use `u` before `x` (its polls at `x` are the uses among blocks `0 … d`), and
  that poll observes the arrival (`KRingOff.empty_observes` of `scoreSlot`, `Unit.Obj.wait_obs`).
  So the wait happens before `x` (`Staging.baseCausality_of_handoff`): `StoreDoneBefore y x`.
* `r > d` (`mma_first`): warpgroup 0's lane polled `qkDone j` for use `u` before `y`; that poll
  observes the notification of the MMA lane's commit of use `u` (`Notify.Obj.observes`, reuse
  paths `qkReach`), which comes after `x` in the lane's program order (its commits at `x` are the
  uses among blocks `0 … d`, fewer than `u + 1`). So the commit tracks `x`, and `x` is done
  before `y`: `DoneBefore x y`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow

noncomputable section
set_option maxRecDepth 4000

namespace TmRace

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem ru_lt {r d : Nat} (h : r ≤ d) : r / 2 + 1 ≤ ringUses 2 (r % 2) (d + 1) := by
  unfold ringUses; omega

private theorem ru_le {r d : Nat} (h : d < r) : ringUses 2 (r % 2) (d + 1) ≤ r / 2 := by
  unfold ringUses; omega

private theorem ru_self (r : Nat) : ringUses 2 (r % 2) r = r / 2 := by
  unfold ringUses; omega

private theorem ru_succ (r : Nat) : ringUses 2 (r % 2) (r + 1) = r / 2 + 1 := by
  unfold ringUses; omega

/-- An arrival on an mbarrier of the rows is a release of CTA scope. -/
private theorem arrive_cta (hX : Consistent L kernel Assumptions.all m X) (hR : MbarRows P L X)
    {w : EvId} {pc tx n : Nat} {l : Loc} {rel : Bool} {sc : MbarScope}
    (he : X.get w = some ⟨pc, .arrive l tx n rel sc⟩) : sc = .cta := by
  rcases mbar_kind hX hR he rfl with ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, _, hc⟩ | ⟨_, hc, -⟩ |
    ⟨_, _, _, hc, -⟩
  · cases hc
  · cases hc
    rfl
  · cases hc
  · cases hc
  · cases hc

/-- An MMA with D below column 256 is the MMA lane's PV MMA. -/
theorem pv_on (hR : TmemRows P L X) (hX : Consistent L kernel Assumptions.all m X)
    {x : EvId} {pc b : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hx : X.get x = some ⟨pc, .tc (.mma b s acc mask)⟩) (hb : b < 256) : MmaOn L x.1 pc := by
  rcases tc_role hR (Frame.lt_of_get hX hx) hx rfl with ⟨-, hW⟩ | ⟨hat, hM⟩ | ⟨_, _, _, hc⟩
  · rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;> cases h
  · rcases hM with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨_, k, -, -, h, -⟩ |
      ⟨_, _, k, -, hpc, h, -⟩
    · cases h
    · cases h
    · cases h
    · cases h
      omega
    · refine ⟨hat, ?_⟩
      simp only [TmemRow.pvPc] at hpc
      split at hpc <;> omega
  · cases hc

/-- A `tcgen05.st` is warpgroup 0's. -/
private theorem st_at (hR : TmemRows P L X) (hX : Consistent L kernel Assumptions.all m X)
    {y : EvId} {pc a : Nat} {vals : List Value} {sh : TcShape}
    (hy : X.get y = some ⟨pc, .tc (.st a vals sh)⟩) : Wg0At L y.1 pc := by
  rcases tc_role hR (Frame.lt_of_get hX hy) hy rfl with ⟨hat, -⟩ | ⟨-, hM⟩ | ⟨_, _, _, hc⟩
  · exact hat
  · rcases hM with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨_, _, -, -, h, -⟩ |
      ⟨_, _, _, -, -, h, -⟩ <;> cases h
  · cases hc

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
include hp hX hFw hR hI hB

/-- **The arrival first, any event before it**: a lane `h` of warpgroup 0 with `r / 2` earlier
arrivals on `soReady (r % 2)` has an arrival of that use, and every event of the lane up to the
arrival is before an event of the MMA lane after its poll of that slot for use `r / 2`. -/
theorem soReady_after' {g i h r : Nat} (hh : h < L.threads) (hw : MbarRow.warp L h < 4)
    (hg : g = mmaLane L X (h / L.block)) (hc : g / L.block = h / L.block)
    (hi : i < (X.tr g).length)
    (hpol : r / 2 + 1 ≤ okPolls (mbarLoc L (h / L.block) (.soReady (slot2 r))) ((X.tr g).take i)) :
    ∃ ia pca, X.get (h, ia) = some ⟨pca, .arrive (mbarLoc L (h / L.block) (.soReady (slot2 r)))
        0 1 true .cta⟩ ∧
      arrivals (mbarLoc L (h / L.block) (.soReady (slot2 r))) ((X.tr h).take ia) = r / 2 ∧
      (∀ q, q ≤ r / 2 → ∀ j, arrivals (mbarLoc L (h / L.block) (.soReady (slot2 r)))
        ((X.tr h).take j) = q → j ≤ ia ∨ q < r / 2) ∧
      ∀ e, e ≤ ia → baseCausality L X (h, e) (g, i) := by
  obtain ⟨b, hbq⟩ := wg0_lane hp (pc := 103) ⟨hw, by omega, by omega⟩
  obtain ⟨c, hcd⟩ : ∃ c, c = h / L.block := ⟨_, rfl⟩
  rw [← hcd] at hbq hg hc hpol
  subst hg
  have hn := Poll.nth_lt hpol
  have hlt : r / 2 < okPolls (mbarLoc L c (.soReady (slot2 r))) (X.tr (mmaLane L X c)) := by
    have h2 := Poll.okPolls_mono (mbarLoc L c (.soReady (slot2 r))) (X.tr (mmaLane L X c)) hi.le
    rw [List.take_length] at h2
    omega
  obtain ⟨hS, hub⟩ := (scoreSlot hp hX hFw hR hI hB c (slot2 r)).empty_observes hX
    (a := 0) (u := r / 2) hlt b
  have hS' : (b, r / 2) ∈ Unit.S X (mbarLoc L c (.soReady (slot2 r))) (wg0Lane L c) := hS
  obtain ⟨pcn, p, acq, sc, hget, -⟩ := Poll.nth_spec hlt
  have hub' : MBarrier.UpdateBeforeWait (X.objects (mbarLoc L c (.soReady (slot2 r))))
      (.thread (Unit.it X (mbarLoc L c (.soReady (slot2 r))) (wg0Lane L c) (b, r / 2).1
        (b, r / 2).2))
      (.thread (mmaLane L X c, Poll.nth X (mbarLoc L c (.soReady (slot2 r))) (mmaLane L X c)
        (r / 2))) := hub
  obtain ⟨ia, pca, sca, hga, hca, hobs⟩ :=
    (soReady_obj hp hX hFw hR hI hB c (slot2 r)).wait_obs hS' hget hub'
  dsimp only at hga hca hobs
  rw [← hbq] at hga hca hobs
  obtain ⟨rfl, rfl⟩ := mbarWait_cta hX hR hget
  obtain rfl := arrive_cta hX hR hga
  have hg' : mmaLane L X c < L.threads := Frame.lt_of_get hX hget
  have hsc : ScopesMeet L .cta h .cta (mmaLane L X c) :=
    ⟨⟨hh, hg', by rw [hc, hcd]⟩, hg', hh, by rw [hc, hcd]⟩
  have hga' := hga
  rw [hcd] at hga' hca
  exact ⟨ia, pca, hga', hca, fun q hq j hj => by
      by_cases hqr : q < r / 2
      · exact .inr hqr
      · obtain rfl : q = r / 2 := by omega
        exact .inl (MbarRing.arrival_index_ge hga' (by simp [arrivesOn, sourceArrive]) hca hj.le),
    fun e he => Staging.baseCausality_of_handoff ⟨0, 1, pca, hga⟩ hobs hsc ⟨rfl, he⟩
      ⟨rfl, hn, hi⟩⟩

/-- **The arrival first, any event before it**: `soReady_after'` without the arrival's count. -/
theorem soReady_after {g i h r : Nat} (hh : h < L.threads) (hw : MbarRow.warp L h < 4)
    (hg : g = mmaLane L X (h / L.block)) (hc : g / L.block = h / L.block)
    (hi : i < (X.tr g).length)
    (hpol : r / 2 + 1 ≤ okPolls (mbarLoc L (h / L.block) (.soReady (slot2 r))) ((X.tr g).take i)) :
    ∃ ia pca, X.get (h, ia) = some ⟨pca, .arrive (mbarLoc L (h / L.block) (.soReady (slot2 r)))
        0 1 true .cta⟩ ∧
      (∀ q, q ≤ r / 2 → ∀ j, arrivals (mbarLoc L (h / L.block) (.soReady (slot2 r)))
        ((X.tr h).take j) = q → j ≤ ia ∨ q < r / 2) ∧
      ∀ e, e ≤ ia → baseCausality L X (h, e) (g, i) := by
  obtain ⟨ia, pca, hga, -, hq, hbc⟩ := soReady_after' hp hX hFw hR hI hB hh hw hg hc hi hpol
  exact ⟨ia, pca, hga, hq, hbc⟩

/-- **The store first**: a store of lane `h` with `r / 2` earlier arrivals on `soReady (r % 2)`
is done before an event of the MMA lane after its poll of that slot for use `r / 2`. -/
theorem store_first {g i h k r pc a : Nat} {vals : List Value} {sh : TcShape}
    (hy : X.get (h, k) = some ⟨pc, .tc (.st a vals sh)⟩) (hat : Wg0At L h pc)
    (hg : g = mmaLane L X (h / L.block)) (hc : g / L.block = h / L.block)
    (hi : i < (X.tr g).length)
    (hpol : r / 2 + 1 ≤ okPolls (mbarLoc L (h / L.block) (.soReady (slot2 r))) ((X.tr g).take i))
    (harr : arrivals (mbarLoc L (h / L.block) (.soReady (slot2 r))) ((X.tr h).take k) =
      r / 2) :
    TcMma.StoreDoneBefore L X (h, k) (g, i) := by
  have hh : h < L.threads := Frame.lt_of_get hX hy
  obtain ⟨ia, pca, hga, hq, hbc⟩ := soReady_after hp hX hFw hR hI hB hh hat.1 hg hc hi hpol
  have hki : k ≤ ia := by
    rcases hq _ le_rfl k harr with h1 | h1
    · exact h1
    · omega
  have hki' : k < ia := by
    rcases Nat.lt_or_eq_of_le hki with h1 | rfl
    · exact h1
    · rw [hy] at hga
      cases hga
  obtain ⟨pcw, hw⟩ := wg0_stWait hp hX hFw hy hat hga (fun _ h => by cases h) hki'
  exact ⟨⟨a, vals, sh, pc, hy⟩, .inl ⟨(h, k + 1), ⟨pcw, hw⟩, rfl, Nat.lt_succ_self k,
    .inl (hbc (k + 1) hki')⟩⟩

/-- **The MMA first, observed**: an MMA of the MMA lane with at most `r / 2` earlier commits to
`qkDone (r % 2)` has its completion observed by an acquire wait of a warpgroup-0 lane `h` that is
before an event `(h, k)` after the lane's poll of that slot for use `r / 2`. -/
theorem mma_first_obs {g i h k r pc b : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (hx : X.get (g, i) = some ⟨pc, .tc (.mma b s acc mask)⟩)
    (hh : h < L.threads) (hw : MbarRow.warp L h < 4) (hkl : k < (X.tr h).length)
    (hg : g = mmaLane L X (h / L.block)) (hc : g / L.block = h / L.block)
    (hcm : ((X.tr g).take i).countP
      (PTX.Flow.commitsTo (mbarLoc L (h / L.block) (.qkDone (slot2 r)))) ≤ r / 2)
    (hpol : r / 2 + 1 ≤ okPolls (mbarLoc L (h / L.block) (.qkDone (slot2 r))) ((X.tr h).take k)) :
    ∃ j < k, ∃ ws, AsyncCopy.AsyncObserved X (g, i) .mmaDone (h, j) true ws ∧
      ScopesMeet L .cluster g ws h ∧ baseCausality L X (h, j) (h, k) := by
  obtain ⟨b', hbq⟩ := wg0_lane hp (pc := 103) ⟨hw, by omega, by omega⟩
  obtain ⟨c, hcd⟩ : ∃ c, c = h / L.block := ⟨_, rfl⟩
  rw [← hcd] at hbq hg hc hcm hpol
  subst hg
  obtain ⟨j, pcp, p, acq, sc, hjk, hget, hq⟩ := UnitHandoff.exists_poll hpol
  have O := qkDone_obj hp hX hFw hR hI hB (mmaOne hp hX hFw) c (slot2 r)
  rw [hbq] at hget hq
  obtain ⟨ic, pcc, sp, rank, hcom, hmb, htg, hcnt, hrank, hobs⟩ :=
    O.observes hX (u := r / 2) (qkReach hp hX hFw hR hI hB c (slot2 r) b') hget hq
  rw [← hbq] at hget hobs
  obtain ⟨rfl, rfl⟩ := mbarWait_cta hX hR hget
  have hlt : i < ic := by
    by_contra hle
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hle) with h1 | rfl
    · have e1 := countP_take_succ (p := PTX.Flow.commitsTo (mbarLoc L c (.qkDone (slot2 r))))
        hcom (by simp [PTX.Flow.commitsTo, hmb])
      have e2 := countP_take_mono (PTX.Flow.commitsTo (mbarLoc L c (.qkDone (slot2 r))))
        (X.tr (mmaLane L X c)) (show ic + 1 ≤ i by omega)
      omega
    · rw [hx] at hcom
      cases hcom
  have hg' : mmaLane L X c < L.threads := Frame.lt_of_get hX hx
  have hsc : ScopesMeet L .cluster (mmaLane L X c) .cta h :=
    ⟨⟨hg', hh, by rw [hc, hcd]⟩, hh, hg', by rw [hc, hcd]⟩
  exact ⟨j, hjk, .cta, ⟨_, _, ⟨(mmaLane L X c, ic), sp, rank, rfl,
    ⟨rfl, hlt, .inl ⟨b, s, acc, mask, pc, hx⟩, sp, pcc, hcom⟩, ⟨pcc, hcom⟩, htg, hrank⟩, hobs⟩,
    hsc, .single (.inl (po_of_source_not_access rfl hjk hkl (by rw [hget]; rfl)))⟩

/-- **The MMA first**: an MMA of the MMA lane with at most `r / 2` earlier commits to
`qkDone (r % 2)` is done before an event of a warpgroup-0 lane after its poll of that slot for
use `r / 2`. -/
theorem mma_first {g i h k r pc pc' b a : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {vals : List Value} {sh : TcShape}
    (hx : X.get (g, i) = some ⟨pc, .tc (.mma b s acc mask)⟩)
    (hy : X.get (h, k) = some ⟨pc', .tc (.st a vals sh)⟩) (hat : Wg0At L h pc')
    (hg : g = mmaLane L X (h / L.block)) (hc : g / L.block = h / L.block)
    (hcm : ((X.tr g).take i).countP
      (PTX.Flow.commitsTo (mbarLoc L (h / L.block) (.qkDone (slot2 r)))) ≤ r / 2)
    (hpol : r / 2 + 1 ≤ okPolls (mbarLoc L (h / L.block) (.qkDone (slot2 r))) ((X.tr h).take k)) :
    TcMma.DoneBefore L X (g, i) (h, k) := by
  obtain ⟨j, -, ws, ho, hs, hb⟩ := mma_first_obs hp hX hFw hR hI hB hx (Frame.lt_of_get hX hy)
    hat.1 (List.getElem?_eq_some_iff.mp hy).1 hg hc hcm hpol
  exact .inl ⟨(h, j), ws, ho, hs, hb⟩

/-- **The PV/rescale order with the blocks**: a PV MMA `x` (block `d`, its polls of `soReady` are
the uses among blocks `0 … d`) and a store `y` of warpgroup 0 of one CTA (block `r`) are ordered:
the store is done before the MMA when `r ≤ d`, the MMA is done before the store when `d < r`. -/
theorem pvStore_blk (hT : TmemRows P L X) {x y : EvId} {pc pc' b a : Nat} {s : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} {vals : List Value}
    (hx : X.get x = some ⟨pc, .tc (.mma b s acc mask)⟩) (hb : b < 256)
    (hy : X.get y = some ⟨pc', .tc (.st a vals .s32x32b)⟩) (hc : x.1 / L.block = y.1 / L.block) :
    ∃ d r, (∀ j : Fin 2, okPolls (mbarLoc L (x.1 / L.block) (.soReady j)) ((X.tr x.1).take x.2) =
        ringUses 2 j (d + 1)) ∧
      (∀ j : Fin 2, okPolls (mbarLoc L (y.1 / L.block) (.qkDone j)) ((X.tr y.1).take y.2) =
        ringUses 2 j (r + 1)) ∧
      ((r ≤ d ∧ TcMma.StoreDoneBefore L X y x) ∨ (d < r ∧ TcMma.DoneBefore L X x y)) := by
  obtain ⟨g, i⟩ := x
  obtain ⟨h, k⟩ := y
  dsimp only at hc ⊢
  have hon := pv_on hT hX hx hb
  have hat := st_at hT hX hy
  have hg : g = mmaLane L X (h / L.block) := by
    rw [← hc]
    exact laneOn_eq (mmaOne hp hX hFw) hx (fun _ h => by cases h) hon
  obtain ⟨d, hd⟩ := mma_pvBlock hp hX hFw hx hon.1 hb
  obtain ⟨r, hr⟩ := wg0_stBlock hp hX hFw hy hat
  obtain ⟨hdP, hdC⟩ := hd (slot2 r)
  obtain ⟨hrP, hrA⟩ := hr (slot2 r)
  have hdall : ∀ j : Fin 2, okPolls (mbarLoc L (g / L.block) (.soReady j)) ((X.tr g).take i) =
      ringUses 2 j (d + 1) := fun j => (hd j).1
  rw [hc] at hdP hdC
  have hs : ((slot2 r : Fin 2) : Nat) = r % 2 := rfl
  rw [hs] at hdP hdC hrP hrA
  refine ⟨d, r, hdall, fun j => (hr j).1, ?_⟩
  by_cases hrd : r ≤ d
  · exact .inl ⟨hrd, store_first hp hX hFw hR hI hB hy hat hg hc
      (List.getElem?_eq_some_iff.mp hx).1 (by rw [hdP]; exact ru_lt hrd)
      (by rw [hrA]; exact ru_self r)⟩
  · exact .inr ⟨by omega, mma_first hp hX hFw hR hI hB hx hy hat hg hc
      (by rw [hdC]; exact ru_le (by omega)) (by rw [hrP, ru_succ])⟩

/-- **The PV/rescale order**: a PV MMA and a store of warpgroup 0 of one CTA are ordered. -/
theorem pvStore_order (hT : TmemRows P L X) : PvStoreOrder L X := by
  intro x y pc pc' b s acc mask a vals hx hb hy hc
  obtain ⟨d, r, -, -, h1 | h1⟩ := pvStore_blk hp hX hFw hR hI hB hT hx hb hy hc
  · exact .inr h1.2
  · exact .inl h1.2

end

end TmRace

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
