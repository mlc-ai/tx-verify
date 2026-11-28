-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Tma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots
public import Lemmas.Flow.NotTensor
public import Lemmas.Kernel.Progress.NextEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.ObjCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Won

@[expose] public section

/-! # The TMA lane's counts the channels take

For a lane `y` of warp 5 in CTA `c` (the CTA's TMA lane; a lane that lost the election makes none
of these events): its arrival on `rawReady s` follows more successful polls of `rawFree s` than
its earlier arrivals on `rawReady s` (`tma_rawArr`), its gather on `rawReady s` more than a
sixteenth of its earlier gathers on it (`tma_rawIss`), and its arrival on `coordFree s` more
successful polls of `coordReady s` than its earlier arrivals on `coordFree s` (`tma_coordArr`):
block `r` uses slot `r % 2` of the tile and `r % 4` of the ring, after its two polls and before
its arrivals, and gathers sixteen times. These are `RawInputs.{tmaArr,tmaIss}`
(`Protocol/Raw/Observe.lean`) and `CoordInputs.tmaArr` (`Protocol/Coord/Observe.lean`) for the
CTA's TMA thread, a lane of warp 5 of the CTA. A TMA lane waiting at 2205 is no earlier than the
slot of `bar_q_utccp` (`tma_query_slot`: `QueryTime.tmaSlot`, `Protocol/Query/Lag.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y i : Nat}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hw : warp L y = 5)
include hp hX hFw hw

/-- A synchronizing event of the lane is fired from a TMA state of the loop with the reference
counts at the lane's prefix. -/
private theorem tma_sync_at {e : Event} (he : X.get (y, i) = some e) (hk : PollCommit e)
    (hub : ∀ f, e.kind ≠ .ub f) :
    ∃ d, Tma.RefCore L y d (fun c => ((X.tr y).take i).countP (Tma.cls c)) ∧ Tma.Ev L y d e ∧
      ∀ j, d.site ≠ .leave j := by
  have hin := lane5_inRole hp hX hFw hw he hk
  simp only [Tma.inRole, decide_eq_true_eq] at hin
  obtain ⟨d, hR, -, hev, hl, -⟩ := tma_at hp hX hFw he hub ⟨by omega, by omega⟩
  exact ⟨d, hR (lane5_take_noUb hX he), hev, hl⟩

/-- **The TMA lane's arrival on `rawReady s`** follows more successful polls of `rawFree s` than
its earlier arrivals on `rawReady s`. -/
theorem tma_rawArr {c pc tx cnt : Nat} {s : Fin 2} {rel : Bool} {sc : MbarScope}
    (hc : y / L.block = c)
    (he : X.get (y, i) = some ⟨pc, .arrive (mbarLoc L c (.rawReady s)) tx cnt rel sc⟩) :
    arrivals (mbarLoc L c (.rawReady s)) ((X.tr y).take i) <
      okPolls (mbarLoc L c (.rawFree s)) ((X.tr y).take i) := by
  subst hc
  obtain ⟨d, hR, hev, hl⟩ := tma_sync_at hp hX hFw hw he
    (.inr (.inr (.inr ⟨_, _, _, _, _, rfl⟩))) (fun _ h => by cases h)
  have hP := lane5_okPolls hp hX hFw hw i
  have hA := lane5_arrivals hp hX hFw hw i
  rcases Tma.ev_arrive hl hev rfl with hs | hs
  · obtain ⟨⟨-, -, -, -, -, hbuf, -, -, -, -⟩, hn⟩ := (Tma.core_loop (by rw [hs]; rfl)).mp hR
    obtain ⟨-, hK⟩ := hev
    simp only [Tma.EvK, hs, Kind.arrive.injEq] at hK
    have hl' : loc L y (.rawReady s) = loc L y (.rawReady (slot2 d.cnt.toNat)) :=
      hK.1.trans ((Tma.raw_of hbuf).trans (Tma.raw_loc hp (slot2 d.cnt.toNat)))
    have hs' : s = slot2 d.cnt.toNat := by
      have := (Tma.loc_eq_iff.mp hl')
      cases this
      rfl
    show arrivals (loc L y (.rawReady s)) _ < okPolls (loc L y (.rawFree s)) _
    rw [hA, hP, hn _ (by simp), hn _ (by simp), Tma.tcnt_raw hp, Tma.tcnt_free hp, hs']
    simp [Tma.useAt, Tma.ind, hs, Tma.Site.stage, slot2]
  · obtain ⟨⟨-, -, -, -, -, -, hslot, -, -, -⟩, -⟩ := (Tma.core_loop (by rw [hs]; rfl)).mp hR
    obtain ⟨-, hK⟩ := hev
    simp only [Tma.EvK, hs, Kind.arrive.injEq] at hK
    have hl' : loc L y (.rawReady s) = loc L y (.coordFree (slot4 d.cnt.toNat)) :=
      hK.1.trans ((Tma.cfree_of hslot).trans (Tma.cfree_loc hp (slot4 d.cnt.toNat)))
    nomatch Tma.loc_eq_iff.mp hl'

/-- **The TMA lane's gather on `rawReady s`** follows more than a sixteenth of its earlier gathers
on `rawReady s` successful polls of `rawFree s`. -/
theorem tma_rawIss {c pc al : Nat} {s : Fin 2} {sp : TensorCopy.Spec} (hc : y / L.block = c)
    (he : X.get (y, i) = some ⟨pc, .tensorIssue al sp⟩)
    (hm : sp.mbar = mbarLoc L c (.rawReady s)) :
    ((X.tr y).take i).countP (issuesTo (mbarLoc L c (.rawReady s))) <
      16 * okPolls (mbarLoc L c (.rawFree s)) ((X.tr y).take i) := by
  subst hc
  obtain ⟨d, hR, hev, hl⟩ := tma_sync_at hp hX hFw hw he
    (.inr (.inr (.inl ⟨_, _, rfl⟩))) (fun _ h => by cases h)
  have hP := lane5_okPolls hp hX hFw hw i
  have hI := lane5_issues hp hX hFw hw i
  obtain ⟨k, hs⟩ := Tma.ev_gather hl hev rfl
  obtain ⟨⟨-, -, -, -, -, hbuf, -, -, -, -⟩, hn⟩ := (Tma.core_loop (by rw [hs]; rfl)).mp hR
  obtain ⟨-, hK⟩ := hev
  simp only [Tma.EvK, hs] at hK
  obtain ⟨a, s', hK, hmb⟩ | ⟨f, hK⟩ := hK
  · simp only [Kind.tensorIssue.injEq] at hK
    obtain ⟨-, rfl⟩ := hK
    have hl' : loc L y (.rawReady s) = loc L y (.rawReady (slot2 d.cnt.toNat)) :=
      hm.symm.trans (hmb.trans ((Tma.raw_of hbuf).trans (Tma.raw_loc hp (slot2 d.cnt.toNat))))
    have hs' : s = slot2 d.cnt.toNat := by
      have := (Tma.loc_eq_iff.mp hl')
      cases this
      rfl
    show ((X.tr y).take i).countP (issuesTo (loc L y (.rawReady s))) <
      16 * okPolls (loc L y (.rawFree s)) _
    rw [hI, hP, hn _ (by simp), hn _ (by simp), Tma.tcnt_gather hp, Tma.tcnt_free hp, hs']
    have hk := k.isLt
    simp [Tma.useAt, Tma.ind, hs, Tma.Site.stage, Tma.Site.gN, slot2]
    omega
  · cases hK

/-- **The TMA lane's arrival on `coordFree s`** follows more successful polls of `coordReady s`
than its earlier arrivals on `coordFree s`. -/
theorem tma_coordArr {c pc : Nat} {s : Fin 4} {sc : MbarScope} (hc : y / L.block = c)
    (he : X.get (y, i) = some ⟨pc, .arrive (mbarLoc L c (.coordFree s)) 0 1 true sc⟩) :
    arrivals (mbarLoc L c (.coordFree s)) ((X.tr y).take i) <
      okPolls (mbarLoc L c (.coordReady s)) ((X.tr y).take i) := by
  subst hc
  obtain ⟨d, hR, hev, hl⟩ := tma_sync_at hp hX hFw hw he
    (.inr (.inr (.inr ⟨_, _, _, _, _, rfl⟩))) (fun _ h => by cases h)
  have hP := lane5_okPolls hp hX hFw hw i
  have hA := lane5_arrivals hp hX hFw hw i
  rcases Tma.ev_arrive hl hev rfl with hs | hs
  · obtain ⟨⟨-, -, -, -, -, hbuf, -, -, -, -⟩, -⟩ := (Tma.core_loop (by rw [hs]; rfl)).mp hR
    obtain ⟨-, hK⟩ := hev
    simp only [Tma.EvK, hs, Kind.arrive.injEq] at hK
    have hl' : loc L y (.coordFree s) = loc L y (.rawReady (slot2 d.cnt.toNat)) :=
      hK.1.trans ((Tma.raw_of hbuf).trans (Tma.raw_loc hp (slot2 d.cnt.toNat)))
    nomatch Tma.loc_eq_iff.mp hl'
  · obtain ⟨⟨-, -, -, -, -, -, hslot, -, -, -⟩, hn⟩ := (Tma.core_loop (by rw [hs]; rfl)).mp hR
    obtain ⟨-, hK⟩ := hev
    simp only [Tma.EvK, hs, Kind.arrive.injEq] at hK
    have hl' : loc L y (.coordFree s) = loc L y (.coordFree (slot4 d.cnt.toNat)) :=
      hK.1.trans ((Tma.cfree_of hslot).trans (Tma.cfree_loc hp (slot4 d.cnt.toNat)))
    have hs' : s = slot4 d.cnt.toNat := by
      have := (Tma.loc_eq_iff.mp hl')
      cases this
      rfl
    show arrivals (loc L y (.coordFree s)) _ < okPolls (loc L y (.coordReady s)) _
    rw [hA, hP, hn _ (by simp), hn _ (by simp), Tma.tcnt_cfree hp, Tma.tcnt_ready hp, hs']
    simp [Tma.useAt, Tma.ind, hs, Tma.Site.stage, slot4]
end

/-- **`QueryTime.tmaSlot`**: the TMA lane at its wait on `bar_q_utccp` is no earlier than the
slot. -/
theorem tma_query_slot (hp : Pre P L m) (hFw : Follow P L X) {g c p : Nat} {ok acq : Bool}
    {sc : MbarScope} (_hat : MbarRow.TmaAt L g 2205)
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨2205, .wait (mbarLoc L c .qUtccp) p ok acq sc⟩) :
    qUtccpSlot ≤ Sched.threadTime (timed P L) X g :=
  (tma_slot_wait hp hFw hn).ge

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
