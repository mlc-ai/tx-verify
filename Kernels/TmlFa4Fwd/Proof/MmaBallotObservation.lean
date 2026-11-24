-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaSelectionPath
import Kernels.TmlFa4Fwd.Proof.MmaModel
import Kernels.TmlFa4Fwd.Proof.EpilogueSelectionObservations

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue

/-- Registers retained by the MMA ballot and relative index calculation. -/
def voteFrameRegs : List Nat := [7199, 7196, 7197, 1186, 1072, 7139, 7502, 7503, 2535]

/-- Registers needed after the ballot enters its decoded vote site. -/
def groupInputRegs : List Nat := [7199, 7196, 7197, 1072, 7139, 7502, 7503, 2535]

/-- The selected group computes the decoded vote predicate and the preceding group's work
before the warp ballot. -/
theorem prepareMmaGroupVote {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g first batch : Nat} {t : TState} {F : List (Nat × Value)}
    (hFirst : first ≤ batch) (hGroup : batch < first + 31) (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hFrame : ∀ pair ∈ F, pair.1 ∈ groupInputRegs) :
    let args := [(7198, b32 (∑ i ∈ Finset.range 32, groupLaneTiles p first i)),
      (7197, b32 (∑ i ∈ Finset.range (laneOf l g + 1), groupLaneTiles p first i)),
      (7200, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)),
      (7139, b32 p.heads), (1072, b32 (g / l.block))]
    At t 2042 ([(7199, b32 first), (7203, b32 p.batch)] ++ args ++ F) →
    ∃ u, run kernel Assumptions.all l g 8 t = some u ∧
      At u 2050 ([(362, .pred (decide (first + laneOf l g < batch))),
        (1186, b32 (tilePrefix p first * p.heads))] ++ F) := by
  dsimp only
  intro ht
  let args := [(7198, b32 (∑ i ∈ Finset.range 32, groupLaneTiles p first i)),
    (7197, b32 (∑ i ∈ Finset.range (laneOf l g + 1), groupLaneTiles p first i)),
    (7200, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)),
    (7139, b32 p.heads), (1072, b32 (g / l.block))]
  let saved := groupInputRegs ++ [7198, 7200]
  have hpBatch := hp.shape.2.1
  obtain ⟨v, hStart, hv⟩ := selectedGroupAvailable l g (show first < p.batch by omega) hpBatch t
    (ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, trivial⟩)
  have hWrites : ((kernel.code.drop 2042).take 4).all
      (fun ins => saved.all (fun r => !(writesRegs ins.op).contains r)) = true := by decide +kernel
  have hFalls : ((kernel.code.drop 2042).take 3).all
      (fun ins => schedulerFallsThrough ins.op) = true := by decide +kernel
  have hArgs : ∀ pair ∈ args ++ F, pair.1 ∈ saved := by
    intro pair hm
    rcases List.mem_append.mp hm with hm | hm
    · simp only [args, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl
    · exact List.mem_append.mpr (.inl (hFrame pair hm))
  have hStartKeep := holdsSchedulerFrame ht.2.2.2.2.2.2
    (fun _ hr => schedulerLocalFrame hWrites hFalls hStart ht.1.ge (by rw [ht.1]) hr) hArgs
  obtain ⟨u, hVote, hu⟩ := selectedGroupBallot hp g hFirst hGroup hBatch
    (Nat.mod_lt _ (by decide)) hLo hHi v (hv.mono ((holds_append ..).mp hStartKeep).1)
  have hWritesVote : ((kernel.code.drop 2046).take 4).all
      (fun ins => groupInputRegs.all (fun r => !(writesRegs ins.op).contains r)) = true := by
    decide +kernel
  have hFallsVote : ((kernel.code.drop 2046).take 3).all
      (fun ins => schedulerFallsThrough ins.op) = true := by decide +kernel
  have hEndKeep := holdsSchedulerFrame ((holds_append ..).mp hStartKeep).2
    (fun _ hr => schedulerLocalFrame hWritesVote hFallsVote hVote hv.1.ge (by rw [hv.1]) hr)
    hFrame
  have hStartFull := localRun (pc := 2042) (n := 4) (by decide) (by decide) ht.1 hFalls hStart
  have hVoteFull := localRun (pc := 2046) (n := 4) (by decide) (by decide) hv.1 hFallsVote hVote
  exact ⟨u, run_comp hStartFull hVoteFull,
    hu.mono ⟨hu.2.2.2.2.2.1, hu.2.2.2.2.1, hEndKeep⟩⟩

/-- The actual full-mask ballot gives the relative batch index, keeping the coordinates
and startup registers needed for both request shuffles. -/
theorem observedMmaGroupVote {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index ordinal first batch : Nat} {t : TState} {F : List (Nat × Value)}
    {word : BitVec 32} {hit : Bool} (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) (ht : At t 2050 ((362, .pred hit) :: F))
    (hFrame : ∀ pair ∈ F, pair.1 ∈ voteFrameRegs)
    (hGroupIndex : (7199, b32 first) ∈ F)
    (he : X.get (g, index) = some ⟨2050, .vote (2 ^ 32 - 1) hit word⟩)
    (hOrdinal : X.MaskK voteClass (g, index) (2 ^ 32 - 1) ordinal)
    (hPeers : ∀ lane < 32, ∃ j val,
      let e := (g - laneOf l g + lane, j)
      X.get e = some ⟨2050, .vote (2 ^ 32 - 1) (decide (first + lane < batch)) val⟩ ∧
        X.MaskK voteClass e (2 ^ 32 - 1) ordinal) :
    let u := next (setReg t 2500 (b32 word.toNat))
    ∃ v, EStep kernel Assumptions.all l g t ⟨2050, .vote (2 ^ 32 - 1) hit word⟩ (some u) ∧
      run kernel Assumptions.all l g 4 u = some v ∧
      At v 2055 ([(1187, b32 (batch - first)), (7203, b32 batch),
        (363, .pred (decide (batch - first = 0))), (7201, b32 0)] ++ F) := by
  let n := batch - first
  let u := next (setReg t 2500 (b32 word.toNat))
  have hn : n < 32 := by omega
  have hAdd : first + n = batch := Nat.add_sub_of_le hFirst
  have hSigned := hp.shape.2.1
  have hSum : first + n < 2 ^ 31 := by omega
  have hPow : 2 ^ n < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hn
  have hMaskBound : 2 ^ n - 1 < 2 ^ 32 := (Nat.sub_le _ _).trans_lt hPow
  have hWord : word.toNat = 2 ^ n - 1 := by
    rw [selectedGroupMask hX hFirst he hOrdinal hPeers, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hMaskBound]
  have hVote : out kernel Assumptions.all l g t =
      .ev (.vote (2 ^ 32 - 1) hit (fun mask => next (setReg t 2500 (b32 mask.toNat)))) :=
    (out_eq_core (by rw [ht.1]; decide) (by rw [ht.1]; decide)).trans
      (selectedGroupVote hp g t hit ht.1 ht.2.2.2.1 ht.2.2.2.2.1)
  have hFresh : ∀ pair ∈ F, pair.1 ≠ 2500 := by
    intro pair hm eq
    have hBad : 2500 ∈ voteFrameRegs := eq ▸ hFrame pair hm
    exact (by decide : 2500 ∉ voteFrameRegs) hBad
  have hu : At u 2051 ((2500, b32 word.toNat) :: F) := (ht.mono ht.2.2.2.2.2).set hFresh
  have hInputs : At u 2051 [(2500, b32 (2 ^ n - 1)), (7199, b32 first)] :=
    hu.mono ⟨hWord ▸ hu.2.2.2.2.1, holds_mem hu.2.2.2.2.2 hGroupIndex, trivial⟩
  obtain ⟨v, hRun, hv⟩ := selectedGroupPopcount l g hn hSum u hInputs
  have hWrites : ((kernel.code.drop 2051).take 4).all
      (fun ins => voteFrameRegs.all (fun r => !(writesRegs ins.op).contains r)) = true := by
    decide +kernel
  have hFalls : ((kernel.code.drop 2051).take 3).all
      (fun ins => schedulerFallsThrough ins.op) = true := by decide +kernel
  have hKeep := holdsSchedulerFrame hu.2.2.2.2.2
    (fun _ hr => schedulerLocalFrame hWrites hFalls hRun hu.1.ge (by rw [hu.1]) hr) hFrame
  exact ⟨v, ⟨_, hVote, word, by rw [ht.1], rfl⟩,
    localRun (by decide) (by decide) hu.1 hFalls hRun,
    hv.mono ((holds_append ..).mpr ⟨by simpa only [hAdd] using hv.2.2.2.2, hKeep⟩)⟩

end PTX.Kernels.TmlFa4Fwd.Mma
