-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaSchedulerEntry
public import Kernels.TmlFa4Fwd.Proof.EpilogueSchedule

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue Prologue

noncomputable section

private theorem int32Signed {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left h]

private theorem firstTileGate (l : Launch) (g : Nat) {lane batch begin finish : Nat}
    (hl : lane < 32) (hb : batch < 2 ^ 31) (hb32 : begin < 2 ^ 32) (he32 : finish < 2 ^ 32) :
    Seg kernel [] l g 6 1942
      [(1180, b32 lane), (7203, b32 batch), (7193, b32 begin), (2456, b32 finish)] 1948
      [(1181, .bits 32 (truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin))),
       (7196, b32 0),
       (337, .pred (!decide (laneHasRequest lane batch))), (1180, b32 lane)] := by
  intro t ht
  have hL32 : lane < 2 ^ 32 := by omega
  have hL31 : lane < 2 ^ 31 := by omega
  have hL64 : lane < 2 ^ 64 := by omega
  have hB32 : batch < 2 ^ 32 := by omega
  have hNe : (lane : Int) ≠ 31 ↔ lane < 31 := by omega
  seg_fp ht using
    first
    | rfl
    | simp only [truncBits_ofNat hb32 (by decide), truncBits_ofNat he32 (by decide)]
    | (simp only [compare, Option.getD_some, truncBits_ofNat hL32 (by decide),
        truncBits_ofNat hB32 (by decide), int32Signed hL31, int32Signed hb,
        toNat_ofNat_lt hL64, Int.ofNat_lt, Bool.and_comm]
       have heq : (↑(truncBits 32 (BitVec.ofInt 64 31)).toNat : Int) = 31 := rfl
       simp only [heq, hNe]
       by_cases hcut : lane < batch <;> by_cases hlast : lane < 31 <;>
         simp [laneHasRequest, hcut, hlast])

private theorem roundedTiles (l : Launch) (g : Nat) {len : Nat}
    (hlen : len < 2 ^ 30) :
    Seg kernel [] l g 10 1949 [(1181, b32 len)]
      (1959)
      [(7196, b32 ((len + 255) / 256))] := by
  have h32 : len < 2 ^ 32 := by omega
  have h31 : len < 2 ^ 31 := by omega
  have h64 : len < 2 ^ 64 := by omega
  have hx64 : len < 18446744073709551616 := h64
  have hDiv : len / 256 < 2 ^ 32 := by omega
  have hMask : len / 256 * 256 < 2 ^ 32 := by omega
  have shr31 : (len : Int) / 2 ^ 31 = 0 := by omega
  have shr8 : (len : Int) / 2 ^ 8 = (len / 256 : Nat) := by omega
  have s31 : min (truncBits 32 (BitVec.ofInt 64 31)).toNat 32 = 31 := rfl
  have s8 : min (truncBits 32 (BitVec.ofInt 64 8)).toNat 32 = 8 := rfl
  have s24 : (truncBits 32 (BitVec.ofInt 64 24)).toNat = 24 := rfl
  have z : truncBits 32 (BitVec.ofInt 64 0) = 0 := rfl
  have z32 : truncBits 32 0 = 0 := rfl
  have zShift : (0 : BitVec 64) >>> 24 = 0 := rfl
  have h24 : ¬24 ≥ 32 := by decide
  have hNeg : toSigned 32 (truncBits 32 (BitVec.ofInt 64 (-1))) = -1 := rfl
  have hPos : (-1 : Int) < len := by omega
  have m32 : truncBits 32 (BitVec.ofInt 64 (-256)) = BitVec.ofNat 64 4294967040 := rfl
  have aZero : BitVec.ofNat 64 len + 0 = BitVec.ofNat 64 len := BitVec.add_zero _
  have hFirst : Seg kernel [] l g 8 1949
      [(1181, b32 len)] (1957)
      [(2460, b32 (len / 256)),
       (340, .pred (decide (len ≠ len / 256 * 256)))] := by
    intro t ht
    seg_fp ht using
      simp only [b32, s31, s8, s24, ite_eq_right h24, shr31, shr8, z, z32, zShift,
        aZero, truncBits_ofNat h32 (by decide), m32,
        truncBits_ofNat hDiv (by decide), BitVec.ofInt_natCast, nf_and, compare,
        Option.getD_some, int32Signed h31, hNeg, gt_iff_lt, hPos, decide_true, Bool.true_and,
        toNat_ofNat_lt h64, Int.ofNat_inj, ne_eq]
      all_goals
        simp only [Nat.mod_eq_of_lt hx64, Nat.reduceMod, lowByteMask h32,
          truncBits_ofNat hMask (by decide),
          toNat_ofNat_lt (show len / 256 * 256 < 2 ^ 64 by omega)]
  have hLast : Seg kernel [] l g 2 (1957)
      [(2460, b32 (len / 256)),
       (340, .pred (decide (len ≠ len / 256 * 256)))]
      (1959)
      [(7196, b32 ((len + 255) / 256))] := by
    by_cases h : len = len / 256 * 256
    · have hPad : decide (len ≠ len / 256 * 256) = false := decide_eq_false (fun hn => hn h)
      intro t ht
      simp only [hPad] at ht
      seg_fp ht using norm_bits
    · intro t ht
      simp only [decide_eq_true h] at ht
      seg_fp ht using norm_bits
  exact hFirst.comp hLast

/-- The first tile calculation also keeps the physical CTA id. -/
theorem firstSchedulerTilesWithCta {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {lane : Nat} (hl : lane < 32) {t : TState}
    (ht : At t 1942 [(2456, b32 (drainCuQ p (shflSource .down lane 1 31).1)),
      (7193, b32 (drainCuQ p lane)), (1180, b32 lane), (7203, b32 p.batch)]) :
    ∃ n u, run kernel Assumptions.all l g n t = some u ∧
      At u 1959 [(7196, b32 (groupLaneTiles p 0 lane)), (1180, b32 lane),
        (337, .pred (!decide (laneHasRequest lane p.batch)))] ∧
      u.regs 1072 = t.regs 1072 := by
  let begin := drainCuQ p lane
  let finish := drainCuQ p (shflSource .down lane 1 31).1
  obtain ⟨hBegin, hFinish, hMono, hLength, hTiles⟩ := drainWordTiles hp 0 lane
  simp only [Nat.zero_add] at hBegin hFinish hMono hLength hTiles
  have hAt : At t 1942 [(1180, b32 lane), (7203, b32 p.batch),
      (7193, b32 begin), (2456, b32 finish)] := ht.mono
    ⟨ht.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.1, trivial⟩
  obtain ⟨u, hu, hU⟩ := firstTileGate l g hl hp.shape.2.1 hBegin hFinish t hAt
  have hLocal := localRun (by decide) (by decide) ht.1 (by
    set_option maxRecDepth 100000 in kernel_rfl) hu
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1948 _ hU hU.2.2.2.2.2.2.1 (by simp)
  have hBranch := localRun (by decide) (by decide) hU.1 rfl hv
  have hRun := run_comp hLocal hBranch
  have hCta : v.regs 1072 = t.regs 1072 :=
    schedulerLocalFrame (lo := 1942) (len := 7) (regs := [1072]) (by
      set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (run_comp hu hv) ht.1.ge (by rw [ht.1]) (by decide)
  by_cases ha : laneHasRequest lane p.batch
  · have hPc : v.pc = 1949 := by simpa [ha] using hV.1
    have hVal : truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin) =
        BitVec.ofNat 64 (finish - begin) := by
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (show begin < 2 ^ 64 by omega)
        (hMono (decide_eq_true ha)), truncBits_ofNat (show finish - begin < 2 ^ 32 by omega)
          (by decide)]
    have hReg : v.regs 1181 = some
        (.bits 32 (truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin))) :=
      hV.2.2.2.2.1
    rw [hVal] at hReg
    have hV' : At v 1949 [(1181, b32 (finish - begin))] :=
      ⟨hPc, hV.2.1, hV.2.2.1, hV.2.2.2.1, hReg, trivial⟩
    obtain ⟨w, hw, hW⟩ := roundedTiles l g hLength v hV'
    have hLocal := localRun (by decide) (by decide) hPc (by
      set_option maxRecDepth 100000 in kernel_rfl) hw
    have hKeep : w.regs 1072 = v.regs 1072 :=
      schedulerLocalFrame (lo := 1949) (len := 10) (regs := [1072]) (by
        set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl) hw hPc.ge (by rw [hPc]) (by decide)
    refine ⟨17, w, run_comp hRun hLocal, ?_, hKeep.trans hCta⟩
    rw [← hTiles, decide_eq_true ha]
    have hFrame : w.regs 1180 = v.regs 1180 :=
      schedulerLocalFrame (lo := 1949) (len := 10) (regs := [1180]) (by
        set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hw hPc.ge (by rw [hPc]) (by simp)
    have hs : w.regs 7196 = some (b32 ((finish - begin + 255) / 256)) := hW.2.2.2.2.1
    have hGuard : w.regs 337 = v.regs 337 :=
      schedulerLocalFrame (lo := 1949) (len := 10) (regs := [337]) (by decide +kernel)
        (by decide +kernel) hw hPc.ge (by rw [hPc]) (by simp)
    exact hW.mono ⟨hs, hFrame.trans hV.2.2.2.2.2.2.2.1,
      (by simpa only [decide_eq_true ha] using hGuard.trans hV.2.2.2.2.2.2.1), trivial⟩
  · have hPc : v.pc = 1959 := by simpa [ha] using hV.1
    refine ⟨7, v, hRun, ⟨hPc, hV.2.1, hV.2.2.1, hV.2.2.2.1, ?_,
      hV.2.2.2.2.2.2.2.1, hV.2.2.2.2.2.2.1, trivial⟩, hCta⟩
    have hFalse : decide (laneHasRequest lane p.batch) = false := decide_eq_false ha
    rw [← hTiles]
    simpa only [hFalse, Bool.false_eq_true, ↓reduceIte] using hV.2.2.2.2.2.1

end
end PTX.Kernels.TmlFa4Fwd.Mma
