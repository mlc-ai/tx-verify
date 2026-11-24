-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueGroup
public import Kernels.TmlFa4Fwd.Proof.SchedulerBallot

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left h]

/-- The decoded ballot comparison marks precisely the lanes preceding the selected batch. -/
theorem selectedGroupBallot {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {first batch lane cta : Nat} (hFirst : first ≤ batch)
    (hGroup : batch < first + 31) (hBatch : batch < p.batch) (hLane : lane < 32)
    (hLo : tilePrefix p batch * p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch + 1) * p.heads) :
    Seg kernel [] l g 4 2883
      [(7222, b32 (∑ i ∈ Finset.range 32, groupLaneTiles p first i)),
       (7221, b32 (∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i)),
       (7224, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)),
       (7138, b32 p.heads), (1072, b32 cta)] 2887
      [(1207, b32 (tilePrefix p first * p.heads)),
       (293, .pred (decide (first + lane < batch)))] := by
  let start := tilePrefix p first * p.heads
  let tail := tilePrefix p (min p.batch (first + 31)) * p.heads
  let total := ∑ i ∈ Finset.range 32, groupLaneTiles p first i
  let part := ∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i
  have hStart : start < 2 ^ 31 := hp.prefixWork_signed (by omega)
  have hTail : tail < 2 ^ 31 := hp.prefixWork_signed (Nat.min_le_left _ _)
  have hPart : part * p.heads + start < 2 ^ 31 := by
    have h := congrArg (fun n => n * p.heads) (groupTiles_eq p (by omega : first ≤ p.batch)
      (by omega : lane + 1 ≤ 32))
    change (tilePrefix p first + part) * p.heads = _ at h
    rw [Nat.add_mul, Nat.add_comm] at h
    exact h ▸ hp.prefixWork_signed (Nat.min_le_left _ _)
  have hTotal : total * p.heads + start = tail := by
    have h := congrArg (fun n => n * p.heads) (groupTiles_eq p (by omega : first ≤ p.batch)
      (by decide : 32 ≤ 32))
    change (tilePrefix p first + total) * p.heads = tail at h
    rw [Nat.add_mul, Nat.add_comm] at h
    exact h
  have hBallot : part * p.heads + start ≤ cta ↔ first + lane < batch := by
    simpa only [Nat.add_mul, Nat.add_comm, start] using
      groupBallot_iff p hFirst hGroup hBatch hLane hLo hHi
  have hHeads := hp.heads_signed
  have hCta : cta < 2 ^ 31 := lt_trans hHi (hp.prefixWork_signed (by omega))
  have hPos : 0 < p.heads := by unfold Params.heads; have := hp.shape.2.2.1; omega
  have hTotal32 : total < 2 ^ 32 := by have := Nat.le_mul_of_pos_right total hPos; omega
  have hPart32 : part < 2 ^ 32 := by have := Nat.le_mul_of_pos_right part hPos; omega
  have hTail32 : tail < 2 ^ 32 := by omega
  have hHeads32 : p.heads < 2 ^ 32 := by omega
  have hCta32 : cta < 2 ^ 32 := by omega
  have hTotalWork32 : total * p.heads < 2 ^ 32 := by omega
  have hStart32 : start < 2 ^ 32 := by omega
  have hPartWork32 : part * p.heads + start < 2 ^ 32 := by omega
  have hSub : tail - total * p.heads = start := by omega
  intro t ht
  change At t 2883
    [(7222, b32 total), (7221, b32 part), (7224, b32 tail), (7138, b32 p.heads), (1072, b32 cta)]
    at ht
  change ∃ u, run kernel [] l g 4 t = some u ∧
    At u 2887 [(1207, b32 start), (293, .pred (decide (first + lane < batch)))]
  seg_fp ht using
    simp only [b32, truncBits_ofNat hTotal32 (by decide), truncBits_ofNat hPart32 (by decide),
      truncBits_ofNat hTail32 (by decide), truncBits_ofNat hHeads32 (by decide),
      truncBits_ofNat hCta32 (by decide), truncBits_ofNat hStart32 (by decide),
      ← BitVec.ofNat_add, ← BitVec.ofNat_mul,
      truncBits_ofNat hTotalWork32 (by decide), truncBits_ofNat hPartWork32 (by decide),
      BitVec.ofNat_sub_ofNat_of_le _ _ (show total * p.heads < 2 ^ 64 by omega)
        (show total * p.heads ≤ tail by omega),
      hSub, compare, Option.getD_some, signedWord hPart, signedWord hCta,
      Int.ofNat_le, hBallot]

theorem selectedGroupVote {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (hit : Bool)
    (hpc : t.pc = 2887) (hf : t.fault = none) (hv : t.regs 293 = some (.pred hit)) :
    out kernel [] l g t = .ev (.vote (2 ^ 32 - 1) hit
      (fun mask => next (setReg t 2352 (b32 mask.toNat)))) := by
  rw [out_event hf (by rw [hpc]; exact Flow.code_2887) rfl rfl]
  change Out.ev (voteTmpl l g t 2352 293 false (.imm (-1))) = _
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  simp [voteTmpl, readPred, readReg, hv, hBlock, bind, Except.bind, pure, Except.pure, b32]
  rfl

theorem selectedGroupPopcount (l : Launch) (g : Nat) {first n : Nat}
    (hn : n < 32) (hbound : first + n < 2 ^ 31) :
    Seg kernel [] l g 4 2888 [(2352, b32 (2 ^ n - 1)), (7223, b32 first)] 2892
      [(1208, b32 n), (7228, b32 (first + n)), (294, .pred (decide (n = 0))),
       (7225, b32 0)] := by
  intro t ht
  have hp : 2 ^ n < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hn
  have hMask : 2 ^ n - 1 < 2 ^ 32 := by omega
  have hMask64 : 2 ^ n - 1 < 2 ^ 64 := by omega
  have hFirst : first < 2 ^ 32 := by omega
  have hSum : first + n < 2 ^ 32 := by omega
  have hn32 : n < 2 ^ 32 := by omega
  have hz : (↑(truncBits 32 (BitVec.ofInt 64 0)).toNat : Int) = 0 := rfl
  have hzMask : 2 ^ n - 1 = 0 ↔ n = 0 := by
    cases n with
    | zero => decide
    | succ n =>
      have hOne := Nat.one_lt_two_pow (Nat.succ_ne_zero n)
      omega
  have hc := ballotPrefixPopcount (Nat.le_of_lt hn)
  seg_fp ht using
    first
    | rfl
    | (simp only [b32, truncBits_ofNat hMask (by decide), truncBits_ofNat hFirst (by decide),
        toNat_ofNat_lt hMask64, hc, truncBits_ofNat hn32 (by decide), ← BitVec.ofNat_add,
        truncBits_ofNat hSum (by decide), Nat.add_comm,
        compare, Option.getD_some, hz, Int.natCast_eq_zero, hzMask])

theorem previousPrefixIndex (l : Launch) (g : Nat) {n : Nat} (hn : 0 < n) (hn32 : n < 32) :
    Seg kernel [] l g 1 2893 [(1208, b32 n)] 2894 [(2353, b32 (n - 1))] := by
  intro t ht
  seg_fp ht using norm_bits

theorem selectedRequestTiles {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (lane count : Nat) (hl : lane < 32)
    (hpc : t.pc = 2898) (hf : t.fault = none)
    (hLane : t.regs 1208 = some (b32 lane)) (hv : t.regs 7220 = some (b32 count)) :
    out kernel [] l g t = .ev (.shfl .idx (b32 count) lane 31
      (fun value _ => next (setReg t 2355 value))) := by
  rw [out_event hf (by rw [hpc]; exact Flow.code_2898) rfl rfl]
  change Out.ev (shflTmpl l g t .idx 2355 none (.reg 7220) (.reg 1208)
    (.imm 31) (.imm (-1))) = _
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have h32 : lane < 2 ^ 32 := by omega
  have h64 : lane < 2 ^ 64 := by omega
  simp [shflTmpl, readValue, readReg, hv, hLane, hBlock, Value.bytes, b32, readBits,
    bind, Except.bind, pure, Except.pure, truncBits_ofNat h32 (by decide), toNat_ofNat_lt h64]
  rfl

/-- Once tile and head are computed, the epilogue guard takes the selected tile's load path. -/
theorem enterSelectedTile {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {batch head tile : Nat} (hb : batch < p.batch) (ht : 256 * tile < p.qLength batch) :
    Seg kernel [] l g 5 2944
      [(7228, b32 batch), (7146, b32 p.batch), (7227, b32 head), (2388, b32 tile)] 2949
      [(7228, b32 batch), (7227, b32 head), (7226, b32 (2 ^ 30 + 256 * tile))] := by
  intro t hAt
  have hBound := lt_of_lt_of_le ht (hp.qLength_fits hb)
  obtain ⟨u, hRun, hu⟩ := selectedTileRegisters l g hb hp.shape.2.1 hBound t hAt
  have hFound : u.regs 782 = some (.pred true) := holds_mem hu.2.2.2.2 (by simp)
  have hBranch := selectedBranch l g u true hu.1 hu.2.2.2.1 hFound
  let v := skip (next (setReg u 306 (.pred false)))
  refine ⟨v, run_comp hRun hBranch, ?_⟩
  have hPc : v.pc = 2949 := by change u.pc + 1 + 1 = 2949; rw [hu.1]
  refine ⟨hPc, rfl, rfl, hu.2.2.2.1, ?_⟩
  simpa [v, skip, next, setReg, Holds] using hu.2.2.2.2.2

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
