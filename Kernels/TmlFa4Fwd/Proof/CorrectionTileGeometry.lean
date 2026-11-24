-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionStatsSync
public import Kernels.TmlFa4Fwd.Proof.CorrectionTmemLoads
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
import Kernels.TmlFa4Fwd.Flow.Code.Part123
import Kernels.TmlFa4Fwd.Flow.Code.Part124

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

/-- The shared and Tensor Memory coordinates are derived from the actual CTA-local lane. -/
def correctionTileGeometryFacts (l : Launch) (g : Nat) (live : Bool) : List (Nat × Value) :=
  [(1625, b32 (statsBarrierId l g 0)), (1626, b32 (statsBarrierId l g 1)),
    (1627, b32 (l.sharedBase + 4 * rowOf l g)), (1628, b32 (l.sharedBase + 200)),
    (1629, b32 (outputAddress l g 0 0)), (1633, b32 (outputAddress l g 1 0)),
    (1630, b32 (l.sharedBase + 128 * rowOf l g)),
    (1631, b32 (l.sharedBase + 3072 + 128 * rowOf l g)),
    (1632, b32 (rowOf l g % 2)), (7131, b32 (l.sharedBase + 232)), (7287, b32 1),
    (723, .pred !live)]

private theorem rowBaseBits (tid : Nat) :
    (tid * 128) &&& 3968 = (tid % 32) * 128 := by
  have h (n : Nat) : n <<< 7 = n * 128 := by rw [Nat.shiftLeft_eq]
  rw [← h tid, ← h (tid % 32), show (3968 : Nat) = (2 ^ 5 - 1) <<< 7 by decide,
    ← Nat.shiftLeft_and_distrib, Nat.and_two_pow_sub_one_eq_mod]

private theorem rowColumnBits (warp col : Nat) (hCol : col < 512) :
    (warp * 2097152) ||| col = 65536 * (warp * 32) + col := by
  have h := Nat.two_pow_add_eq_or_of_lt (i := 21) (show col < 2 ^ 21 by omega) warp
  change 2097152 * warp + col = (2097152 * warp) ||| col at h
  rw [Nat.mul_comm warp 2097152, ← h]
  omega


private def geometryTailInput (l : Launch) (g : Nat) (live : Bool) : List (Nat × Value) :=
  let row := rowOf l g
  [(1612, b32 (g % l.block)), (5952, b32 (row / 32)), (5953, b32 ((row / 32) * 2097152)),
    (2535, b32 l.sharedBase), (784, .pred live)]

private def geometryHeadFacts (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(1625, b32 (statsBarrierId l g 0)), (1626, b32 (statsBarrierId l g 1)),
    (1627, b32 (l.sharedBase + 4 * rowOf l g)), (1628, b32 (l.sharedBase + 200)),
    (1629, b32 (outputAddress l g 0 0))]

private theorem correctionGeometryHead {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (live : Bool) :
    Seg kernel [] l g 9 7932
      [(1062, b32 (warpIndex l g)), (1612, b32 (g % l.block)),
        (1613, b32 (rowOf l g)), (2535, b32 l.sharedBase), (784, .pred live)]
      7941 (geometryHeadFacts l g ++ geometryTailInput l g live) := by
  let tid := g % l.block
  let row := rowOf l g
  let warp := warpIndex l g
  have hTid : tid < 512 := by rw [← hp.block]; exact Nat.mod_lt _ (by rw [hp.block]; decide)
  have hRow : row < 128 := Nat.mod_lt _ (by decide)
  have hWarp : warp < 16 := by dsimp only [warp, warpIndex]; omega
  have hPart : row / 32 = warp % 4 := by change (tid % 128) / 32 = (tid / 32) % 4; omega
  have hLaneBase : laneBase l g = (row / 32) * 32 := by
    unfold laneBase
    change warp % 4 * 32 = row / 32 * 32
    rw [hPart]
  have hWarpAnd : warp &&& 3 = warp % 4 := Nat.and_two_pow_sub_one_eq_mod warp 2
  have hShared := hp.shared.2.1
  have hTid32 : tid % 4294967296 = tid := Nat.mod_eq_of_lt (by omega)
  have hRow32 : row % 4294967296 = row := Nat.mod_eq_of_lt (by omega)
  have hWarp32 : warp % 4294967296 = warp := Nat.mod_eq_of_lt (by omega)
  have hTid64 : tid % 18446744073709551616 = tid := Nat.mod_eq_of_lt (by omega)
  have hRow64 : row % 18446744073709551616 = row := Nat.mod_eq_of_lt (by omega)
  have hWarp64 : warp % 18446744073709551616 = warp := Nat.mod_eq_of_lt (by omega)
  have hGroup32 : (row / 32) % 4294967296 = row / 32 := Nat.mod_eq_of_lt (by omega)
  have hGroup64 : (row / 32) % 18446744073709551616 = row / 32 := Nat.mod_eq_of_lt (by omega)
  have hEnc32 : ((row / 32) * 2097152) % 4294967296 = (row / 32) * 2097152 :=
    Nat.mod_eq_of_lt (by omega)
  have hEnc64 : ((row / 32) * 2097152) % 18446744073709551616 = (row / 32) * 2097152 :=
    Nat.mod_eq_of_lt (by omega)
  intro t ht
  change At t 7932 [(1062, b32 warp), (1612, b32 tid), (1613, b32 row),
    (2535, b32 l.sharedBase), (784, .pred live)] at ht
  simp only [geometryHeadFacts, geometryTailInput, List.cons_append, List.nil_append]
  seg_fp ht using
    norm_bits [statsBarrierId, outputAddress, outputColumn, hWarpAnd,
      rowColumnBits (row / 32) 256 (by decide), hLaneBase, hTid32, hWarp32, hRow32,
      hTid64, hWarp64, hRow64, hGroup32, hGroup64, hEnc32, hEnc64]

private def geometryTailFacts (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(1633, b32 (outputAddress l g 1 0)), (1630, b32 (l.sharedBase + 128 * rowOf l g)),
    (1631, b32 (l.sharedBase + 3072 + 128 * rowOf l g)), (1632, b32 (rowOf l g % 2)),
    (7131, b32 (l.sharedBase + 232)), (7287, b32 1)]

private theorem correctionGeometryTail {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (live : Bool) :
    Seg kernel [] l g 10 7941 (geometryTailInput l g live)
      7951 ((784, .pred live) :: geometryTailFacts l g) := by
  let tid := g % l.block
  let row := rowOf l g
  let warp := warpIndex l g
  have hTid : tid < 512 := by rw [← hp.block]; exact Nat.mod_lt _ (by rw [hp.block]; decide)
  have hRow : row < 128 := Nat.mod_lt _ (by decide)
  have hPart : row / 32 = warp % 4 := by change (tid % 128) / 32 = (tid / 32) % 4; omega
  have hParity : tid % 2 = row % 2 := by change tid % 2 = (tid % 128) % 2; omega
  have hLanes : tid % 32 + 32 * (row / 32) = row := by
    change tid % 32 + 32 * ((tid % 128) / 32) = tid % 128
    omega
  have hLaneBase : laneBase l g = (row / 32) * 32 := by
    unfold laneBase
    change warp % 4 * 32 = row / 32 * 32
    rw [hPart]
  have hOr : ((row / 32) * 4096) ||| ((tid % 32) * 128) = row * 128 := by
    rw [lor_4096 (by omega) (by omega)]
    omega
  have hTidAnd : tid &&& 1 = row % 2 :=
    (Nat.and_two_pow_sub_one_eq_mod tid 1).trans hParity
  have hShared := hp.shared.2.1
  have hTid32 : tid % 4294967296 = tid := Nat.mod_eq_of_lt (by omega)
  have hRow32 : row % 4294967296 = row := Nat.mod_eq_of_lt (by omega)
  have hTid64 : tid % 18446744073709551616 = tid := Nat.mod_eq_of_lt (by omega)
  have hRow64 : row % 18446744073709551616 = row := Nat.mod_eq_of_lt (by omega)
  have hGroup32 : (row / 32) % 4294967296 = row / 32 := Nat.mod_eq_of_lt (by omega)
  have hGroup64 : (row / 32) % 18446744073709551616 = row / 32 := Nat.mod_eq_of_lt (by omega)
  have hEnc32 : ((row / 32) * 2097152) % 4294967296 = (row / 32) * 2097152 :=
    Nat.mod_eq_of_lt (by omega)
  have hEnc64 : ((row / 32) * 2097152) % 18446744073709551616 = (row / 32) * 2097152 :=
    Nat.mod_eq_of_lt (by omega)
  have hStridedTid : (tid * 128) % 4294967296 = tid * 128 := Nat.mod_eq_of_lt (by omega)
  have hStridedTid64 : (tid * 128) % 18446744073709551616 = tid * 128 :=
    Nat.mod_eq_of_lt (by omega)
  have hBox32 : ((row / 32) * 4096) % 4294967296 = (row / 32) * 4096 :=
    Nat.mod_eq_of_lt (by omega)
  have hBox64 : ((row / 32) * 4096) % 18446744073709551616 = (row / 32) * 4096 :=
    Nat.mod_eq_of_lt (by omega)
  have hLane32 : ((tid % 32) * 128) % 4294967296 = tid % 32 * 128 :=
    Nat.mod_eq_of_lt (by omega)
  have hLane64 : ((tid % 32) * 128) % 18446744073709551616 = tid % 32 * 128 :=
    Nat.mod_eq_of_lt (by omega)
  intro t ht
  change At t 7941 [(1612, b32 tid), (5952, b32 (row / 32)),
    (5953, b32 ((row / 32) * 2097152)), (2535, b32 l.sharedBase), (784, .pred live)] at ht
  unfold geometryTailFacts
  seg_fp ht using
    norm_bits [outputAddress, outputColumn, hTidAnd, rowBaseBits,
      rowColumnBits (row / 32) 384 (by decide), hLaneBase, hOr, hTid32, hTid64,
      hGroup32, hGroup64, hEnc32, hEnc64, hStridedTid, hStridedTid64,
      hBox32, hBox64, hLane32, hLane64]

private theorem correctionGeometryFlag (l : Launch) (g : Nat) (live : Bool) :
    Seg kernel [] l g 1 7951 ((784, .pred live) :: geometryTailFacts l g)
      7952 (geometryTailFacts l g ++ [(723, .pred !live)]) := by
  intro t ht
  let u := next (setReg t 723 (.pred !live))
  have hReg : t.regs 784 = some (.pred live) := ht.2.2.2.2.1
  have hRun : run kernel [] l g 1 t = some u := by
    apply run_local Flow.code_7951 rfl ht
    rw [execLocalA_nil, execLocal_int rfl]
    simp [execInt, DType.width, readPred, readReg, hReg, bind, Except.bind, pure, Except.pure, u]
  have hFresh : ∀ rv ∈ (784, .pred live) :: geometryTailFacts l g, rv.1 ≠ 723 := by
    intro rv hm he
    have h :=
      List.mem_map_of_mem (f := Prod.fst) hm
    rw [he] at h
    exact (of_decide_eq_true rfl : 723 ∉ [784, 1633, 1630, 1631, 1632, 7131, 7287]) h
  have hu := ht.set (r := 723) (v := .pred !live) hFresh
  exact ⟨u, hRun, hu.mono ((holds_append _ _ _).2
    ⟨hu.2.2.2.2.2.2, hu.2.2.2.2.1, trivial⟩)⟩

/-- The exact post-selection integer segment establishes both named barrier IDs, the row
statistics pointer, and both stage TMEM bases before branching on the live-request predicate. -/
theorem correctionTileGeometry {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (live : Bool) :
    Seg kernel [] l g 20 7932
      [(1062, b32 (warpIndex l g)), (1612, b32 (g % l.block)),
        (1613, b32 (rowOf l g)), (2535, b32 l.sharedBase), (784, .pred live)]
      7952 (correctionTileGeometryFacts l g live) := by
  intro t ht
  obtain ⟨s, hs, hS⟩ := correctionGeometryHead hp g live t ht
  have hOther := ((holds_append _ _ _).1 hS.2.2.2.2).2
  obtain ⟨u, hu, hU⟩ := ((correctionGeometryTail hp g live).comp
    (correctionGeometryFlag l g live)) s (hS.mono hOther)
  have hFrame : ∀ r ∈ [1625, 1626, 1627, 1628, 1629], u.regs r = s.regs r :=
    fun _ hr => schedulerLocalFrame (lo := 7941) (len := 11) (by
      set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hu hS.1.ge (by rw [hS.1]) hr
  have hCarry := hS.2.2.2.2
  refine ⟨u, run_comp hs hu, hU.mono ?_⟩
  exact ⟨(hFrame _ (by decide)).trans hCarry.1, (hFrame _ (by decide)).trans hCarry.2.1,
    (hFrame _ (by decide)).trans hCarry.2.2.1, (hFrame _ (by decide)).trans hCarry.2.2.2.1,
    (hFrame _ (by decide)).trans hCarry.2.2.2.2.1, hU.2.2.2.2⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
