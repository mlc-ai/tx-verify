-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueSelectionReads
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionObservations
public import Lemmas.Flow.WarpScan

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The returning ballot event drives the actual popcount and selects the batch register. -/
theorem selectedGroupPopcountObserved {p : Params} {l : Launch} {m : Mem0} {A : List Assumption}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel A m X)
    {g i ordinal first batch : Nat} (t : TState) (hit : Bool) (word : BitVec 32)
    (hFirst : first ≤ batch) (hGroup : batch < first + 31) (hBatch : batch < p.batch)
    (ht : At t 2887 [(293, .pred hit), (7223, b32 first)])
    (he : X.get (g, i) = some ⟨2887, .vote (2 ^ 32 - 1) hit word⟩)
    (hOrdinal : X.MaskK voteClass (g, i) (2 ^ 32 - 1) ordinal)
    (hPeers : ∀ lane < 32, ∃ j val,
      let e := (g - laneOf l g + lane, j)
      X.get e = some ⟨2887, .vote (2 ^ 32 - 1) (decide (first + lane < batch)) val⟩ ∧
        X.MaskK voteClass e (2 ^ 32 - 1) ordinal) :
    let u := next (setReg t 2352 (b32 word.toNat))
    ∃ v, EStep kernel [] l g t ⟨2887, .vote (2 ^ 32 - 1) hit word⟩ (some u) ∧
      run kernel [] l g 4 u = some v ∧
      At v 2892 [(1208, b32 (batch - first)), (7228, b32 batch),
        (294, .pred (decide (batch = first))), (7225, b32 0)] := by
  let n := batch - first
  have hn : n < 32 := by omega
  have hAdd : first + n = batch := Nat.add_sub_of_le hFirst
  have hBatch31 := hp.shape.2.1
  have hSum : first + n < 2 ^ 31 := by omega
  have hPow : 2 ^ n < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hn
  have hMask := selectedGroupMask hX hFirst he hOrdinal hPeers
  have hMaskBound : 2 ^ n - 1 < 2 ^ 32 :=
    lt_of_le_of_lt (Nat.sub_le _ _) hPow
  have hWord : word.toNat = 2 ^ n - 1 := by
    rw [hMask, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hMaskBound]
  let u := next (setReg t 2352 (b32 word.toNat))
  have hVote := selectedGroupVote hp g t hit ht.1 ht.2.2.2.1
    (holds_mem ht.2.2.2.2 (by simp))
  have hU' : At u 2888 [(2352, b32 word.toNat), (293, .pred hit), (7223, b32 first)] :=
    ht.set (by simp)
  have hU : At u 2888 [(2352, b32 (2 ^ n - 1)), (7223, b32 first)] :=
    hU'.mono ⟨congrArg (fun v => some (b32 v)) hWord ▸ hU'.2.2.2.2.1,
      hU'.2.2.2.2.2.2⟩
  obtain ⟨v, hv, hV⟩ := selectedGroupPopcount l g hn hSum u hU
  have hZero : n = 0 ↔ batch = first := by omega
  exact ⟨v, ⟨_, hVote, word, by rw [ht.1], rfl⟩, hv, by simpa only [hAdd, hZero] using hV⟩

variable {p : Params} {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel A m X) {g i j ordinal first batch peerIndex : Nat} {t : TState}
    {F : List (Nat × Value)} {recv peerRecv : Value} {ok peerOk : Bool}
include hp hX

/-- When the batch follows the first request, the previous lane supplies the exclusive prefix. -/
theorem previousPrefixObserved (hFirst : first < batch) (hGroup : batch < first + 31) :
    let part := fun lane => ∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i
    let source := batch - first - 1
    let ev := ⟨2894, .shfl .idx (b32 (part (laneOf l g))) source 31 recv ok⟩
    At t 2894 F → (2353, b32 source) ∈ F → (7221, b32 (part (laneOf l g))) ∈ F →
    (∀ pair ∈ F, pair.1 ≠ 2354) →
    X.get (g, i) = some ev → X.ShflK (g, i) ordinal →
    X.get (g - laneOf l g + source, j) =
      some ⟨2894, .shfl .idx (b32 (part source)) peerIndex 31 peerRecv peerOk⟩ →
    X.ShflK (g - laneOf l g + source, j) ordinal →
    ¬ ShflExited X (g - laneOf l g + source) ordinal →
    ∃ u, EStep kernel [] l g t ev (some u) ∧
      At u 2895 ((2354,
        b32 (∑ lane ∈ Finset.range (batch - first), groupLaneTiles p first lane)) :: F) := by
  dsimp only
  intro ht hIndexFact hSumFact hFresh he hk hPeer hPeerK hLive
  have hIndex : batch - first - 1 < 32 := by omega
  have hCount : batch - first - 1 + 1 = batch - first := by omega
  have hRecv := (selectedIndexValue hX hIndex he hk hPeer hPeerK hLive).1
  rw [hCount] at hRecv
  have hOut := previousPrefixTemplate hp g t _ _ hIndex ht.1 ht.2.2.2.1
    (holds_mem ht.2.2.2.2 hIndexFact) (holds_mem ht.2.2.2.2 hSumFact)
  let u := next (setReg t 2354 recv)
  refine ⟨u, ⟨_, hOut, recv, ok, by rw [ht.1], rfl⟩, ?_⟩
  rw [show u = next (setReg t 2354
      (b32 (∑ lane ∈ Finset.range (batch - first), groupLaneTiles p first lane))) by
    simp [u, hRecv]]
  exact ht.set hFresh

/-- The observed indexed shuffle at request selection deposits the selected batch's tile count. -/
theorem selectedRequestObserved (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) (ht : At t 2898 F) (hRelative : (1208, b32 (batch - first)) ∈ F)
    (hLaneTiles : (7220, b32 (groupLaneTiles p first (laneOf l g))) ∈ F)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ 2355)
    (he : X.get (g, i) = some ⟨2898, .shfl .idx
      (b32 (groupLaneTiles p first (laneOf l g))) (batch - first) 31 recv ok⟩)
    (hk : X.ShflK (g, i) ordinal)
    (hPeer : X.get (g - laneOf l g + (batch - first), j) =
      some ⟨2898, .shfl .idx (b32 (groupLaneTiles p first (batch - first))) peerIndex 31
        peerRecv peerOk⟩) (hPeerK : X.ShflK (g - laneOf l g + (batch - first), j) ordinal)
    (hLive : ¬ ShflExited X (g - laneOf l g + (batch - first)) ordinal) :
    ∃ u, EStep kernel [] l g t ⟨2898, .shfl .idx
      (b32 (groupLaneTiles p first (laneOf l g))) (batch - first) 31 recv ok⟩ (some u) ∧
      At u 2899 ((2355, b32 (requestTiles p batch)) :: F) := by
  have hIndex : batch - first < 32 := by omega
  have hCount : groupLaneTiles p first (batch - first) = requestTiles p batch := by
    simp [groupLaneTiles, Nat.add_sub_of_le hFirst, hBatch, show batch - first < 31 by omega]
  have hRecv := (selectedIndexValue hX hIndex he hk hPeer hPeerK hLive).1
  rw [hCount] at hRecv
  have hOut := selectedRequestTiles hp g t _ _ hIndex ht.1 ht.2.2.2.1
    (holds_mem ht.2.2.2.2 hRelative) (holds_mem ht.2.2.2.2 hLaneTiles)
  let u := next (setReg t 2355 recv)
  refine ⟨u, ⟨_, hOut, recv, ok, by rw [ht.1], rfl⟩, ?_⟩
  rw [show u = next (setReg t 2355 (b32 (requestTiles p batch))) by simp [u, hRecv]]
  exact ht.set hFresh

/-- The parameter loads feed the observed request shuffle and establish the coordinate inputs. -/
theorem selectedParametersObserved (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) (ht : At t 2896 F) (hRelative : (1208, b32 (batch - first)) ∈ F)
    (hLaneTiles : (7220, b32 (groupLaneTiles p first (laneOf l g))) ∈ F)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ 7155 ∧ pair.1 ≠ 7146 ∧ pair.1 ≠ 2355)
    (he : X.get (g, i) = some ⟨2898, .shfl .idx
      (b32 (groupLaneTiles p first (laneOf l g))) (batch - first) 31 recv ok⟩)
    (hk : X.ShflK (g, i) ordinal)
    (hPeer : X.get (g - laneOf l g + (batch - first), j) =
      some ⟨2898, .shfl .idx (b32 (groupLaneTiles p first (batch - first))) peerIndex 31
        peerRecv peerOk⟩) (hPeerK : X.ShflK (g - laneOf l g + (batch - first), j) ordinal)
    (hLive : ¬ ShflExited X (g - laneOf l g + (batch - first)) ordinal) :
    ∃ u v, run kernel [] l g 2 t = some u ∧ EStep kernel [] l g u ⟨2898, .shfl .idx
      (b32 (groupLaneTiles p first (laneOf l g))) (batch - first) 31 recv ok⟩ (some v) ∧
      At v 2899
        ((2355, b32 (requestTiles p batch)) :: (7146, b32 p.batch) :: (7155, b32 800) :: F) := by
  obtain ⟨u, hRun, hU⟩ := selectionParameters hp g ht
    (fun pair hm => ⟨(hFresh pair hm).1, (hFresh pair hm).2.1⟩)
  have hFree : ∀ pair ∈ (7146, b32 p.batch) :: (7155, b32 800) :: F, pair.1 ≠ 2355 := by
    intro pair hm
    rcases List.mem_cons.mp hm with rfl | hm
    · change (7146 : Nat) ≠ 2355
      decide
    rcases List.mem_cons.mp hm with rfl | hm
    · change (7155 : Nat) ≠ 2355
      decide
    exact (hFresh pair hm).2.2
  obtain ⟨v, hStep, hV⟩ := selectedRequestObserved hp hX hFirst hGroup hBatch hU
    (by simp [hRelative]) (by simp [hLaneTiles]) hFree he hk hPeer hPeerK hLive
  exact ⟨u, v, hRun, hStep, hV⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
