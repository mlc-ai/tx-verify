-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Descent
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LiveState
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingArrivalRelease
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressIndexRendezvous
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressIndexShuffle
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1IndexRendezvous

public section

/-! # Index butterflies descend to lanes at earlier stages -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow
open _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem peer_stage_or_earlier {g h : Nat} {d z : Wg1Index.D} {extra second : Bool}
    (hw : SameWarp L g h) (hi : Wg1Index.Inv P L g d) (hz : Wg1Index.Inv P L h z)
    (hSite : d.site = (if second then .quad2 extra else .quad1 extra))
    (hn : z.site ≠ .barrier)
    (hCount : Wg1Index.shuffleCount z = Wg1Index.shuffleCount d) :
    z.site = d.site ∨ priority P L h (.index z) < priority P L g (.index d) := by
  cases second <;> cases hZ : z.site
  all_goals simp only [Wg1Index.shuffleCount, hZ, hSite, Bool.false_eq_true, ↓reduceIte]
    at hCount
  case false.quad1 ex =>
    have hEq := Wg1Index.same_cache_of_block hw hi hz
      (by rw [hSite]; rfl) (by rw [hZ]; rfl) (by omega)
    exact .inl (by simp [hSite, hEq])
  case true.quad2 ex =>
    have hEq := Wg1Index.same_cache_of_block hw hi hz
      (by rw [hSite]; rfl) (by rw [hZ]; rfl) (by omega)
    exact .inl (by simp [hSite, hEq])
  all_goals try exact (hn hZ).elim
  all_goals try omega
  case' false.pair ex first high => cases first <;> cases high
  case' false.coord ex high => cases high
  all_goals
    right
    simp only [priority, indexTime, blockTime, hSite, hZ, Bound.indexOrdinal, Bool.false_eq_true,
      ↓reduceIte]
    omega

/-- A pending index butterfly either has an earlier warp peer or can execute the whole warp. -/
theorem pending_index_shuffle_earlier {g : Nat} {d : Wg1Index.D} {extra second : Bool}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X) (hp : PendingState P L X g (.index d))
    (hSite : d.site = (if second then .quad2 extra else .quad1 extra)) :
    ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g (.index d) := by
  have hX := hmax.1
  let sound := fun h hh => (hs h hh).machine
  have hPeers := index_shuffle_peers hpre hs hX hub hp.1 hp.2 hSite
  have hwg : warpOf L g = 7 := RingRoleGeometry.of_trace hX hp.1.1 (sound g hp.1.1) hp.2
  obtain ⟨tg, hRunG⟩ := Frame.run_some hX hub hp.1
  obtain ⟨ug, _, _, _, hIG, _, _⟩ := Frame.end_at hs hp.1.1 hRunG hp.2
  change Wg1Index.Inv P L g d at hIG
  have hBound : Wg1Index.shuffleCount d < 3 + 2 * totalBlocks d.len0 d.len1 := by
    have hB := hIG.block
    cases second <;> simp [Wg1Index.shuffleCount, hSite] <;> omega
  by_contra hNoEarlier
  have all (h : Nat) (hw : SameWarp L g h) :
      ∃ z, Frame.Pending L X h ∧ PTX.Step.Released L X h ∧
        Frame.stateAt (Machine.code P L) X h (X.tr h).length = some (some (.index z)) ∧
        z.site = (if second then .quad2 extra else .quad1 extra) := by
    obtain ⟨hPending, hCount⟩ := hPeers h hw
    obtain ⟨q, hQ⟩ := pending_followed hpre hX hs ht hPending
    have hWarp : warpOf L h = 7 := by
      have eq (a : Nat) : warpOf L a = a % L.block / 32 := by
        simp [warpOf, tidOf_eq hpre, hpre.block]
      rw [eq, ← hw.2, ← eq, hwg]
    by_cases hEarly : (X.tr h).length < 5
    · rcases Wg1Index.warp_seven_early_prefix hpre hX sound hWarp hEarly le_rfl with
        ⟨s, hS⟩ | hS
      · apply (hNoEarlier ⟨h, .prologue s, ⟨hPending, hS⟩, ?_⟩).elim
        cases second <;> simp [priority, indexTime, hSite, blockTime, Bound.indexOrdinal] <;> omega
      · apply (hNoEarlier ⟨h, .head, ⟨hPending, hS⟩, ?_⟩).elim
        cases second <;> simp [priority, indexTime, hSite, blockTime, Bound.indexOrdinal] <;> omega
    have hRow : Wg1Index.eOf L h = Wg1Index.eOf L g := by
      have hCta : ctaOf L h = ctaOf L g := hw.1.2.2.symm
      simp only [Wg1Index.eOf, ctaidY, hCta]
    rcases Wg1Index.warp_seven_tail_body hpre hX sound hWarp (by omega) hQ with
      ⟨z, rfl, hBar⟩ | ⟨_, hDone⟩
    · have hN := Wg1Index.index_prefix_shuffle_count hpre hX sound hWarp le_rfl hQ
      rw [List.take_length, hCount] at hN
      have hzBar : z.site ≠ .barrier := by
        intro hz
        have hLast := hBar hz
        rw [hRow, ← hIG.len0, ← hIG.len1] at hLast
        have hFinish : Wg1Index.shuffleCount z = 3 + 2 * z.block + 2 := by
          simp only [Wg1Index.shuffleCount, hz]
        rw [hFinish] at hN
        omega
      obtain ⟨t, hRun⟩ := Frame.run_some hX hub hPending
      obtain ⟨u, _, _, _, hI, _, _⟩ := Frame.end_at hs hPending.1 hRun hQ
      rcases peer_stage_or_earlier hw hIG hI hSite hzBar hN.symm with hSame | hEarlier
      · exact ⟨z, hPending, ClosingArrival.index_released_of_tail hQ, hQ, hSame.trans hSite⟩
      · exact (hNoEarlier ⟨h, .index z, ⟨hPending, hQ⟩, hEarlier⟩).elim
    · rw [hCount, hRow, ← hIG.len0, ← hIG.len1] at hDone
      omega
  exact hmax.not_grows (index_shuffle_extension hpre hs hX hp.1.1 hub all)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
