-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderTripCount
public import Kernels.TmlFa4Fwd.Proof.PagedKvGeometry
public import Kernels.TmlFa4Fwd.Flow.Code.Part007

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The first copy starts at the last visible 128-row tile, and the steady loop has
one fewer tile after that priming pair. -/
theorem loaderTripStartFull {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch tile : Nat} (hb : batch < p.batch) (ht : 256 * tile < p.qLength batch) :
    let n := Mma.trips p batch tile
    Seg kernel [] l g 4 477 [(1088, b32 n)] 481
      [(1091, b32 (n - 1)), (1838, b32 (128 * (n - 1))),
       (121, .pred true), (1092, b32 (128 * (n - 1)))] := by
  dsimp only
  let n := Mma.trips p batch tile
  have hBounds := Mma.trips_bounds hp hb ht
  have hLen := (hp.lengths batch hb).2.2
  have hPos : 0 < n := hBounds.1
  have hRow : 128 * (n - 1) < p.kLength batch := by
    have hUpper := hBounds.2.1
    change n ≤ (p.kLength batch + 127) / 128 at hUpper
    omega
  have hN : n < 2 ^ 31 := by omega
  have hn32 : n < 2 ^ 32 := by omega
  have hN' : n - 1 < 2 ^ 32 := by omega
  have hN64 : n < 2 ^ 64 := by omega
  have hRow' : 128 * (n - 1) < 2 ^ 32 := by omega
  have hSlide : truncBits 32
        (BitVec.ofNat 64 n + truncBits 32 (BitVec.ofInt 64 (-1))) =
      BitVec.ofNat 64 (n - 1) := by
    have hM : truncBits 32 (BitVec.ofInt 64 (-1)) = BitVec.ofNat 64 (2 ^ 32 - 1) := rfl
    rw [hM, ← BitVec.ofNat_add]
    have hs : n + (2 ^ 32 - 1) = 2 ^ 32 + (n - 1) := by omega
    rw [hs, truncBits, toNat_ofNat_lt (show 2 ^ 32 + (n - 1) < 2 ^ 64 by omega),
      Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hN']
  have hCmp : toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
    simp only [toSigned, toNat_ofNat_lt hN64, Nat.mod_eq_of_lt hn32, ite_eq_left hN]
  have hZ : toSigned 32 (truncBits 32 (BitVec.ofInt 64 0)) = 0 := rfl
  have hP : (0 : Int) < n := by exact_mod_cast hPos
  have hSh : (truncBits 32 (BitVec.ofInt 64 7)).toNat = 7 := rfl
  have hs : BitVec.ofNat 64 (n - 1) <<< 7 = BitVec.ofNat 64 (128 * (n - 1)) := by
    rw [nf_shl, Nat.mul_comm]
    rfl
  have hTail : Seg kernel [] l g 3 477 [(1088, b32 n)] 480
      [(121, .pred true), (1091, b32 (n - 1)), (1092, b32 (128 * (n - 1)))] := by
    intro t h
    seg_fp h using
      simp only [b32, truncBits_ofNat hn32 (by decide), hSlide,
        truncBits_ofNat hN' (by decide), compare, Option.getD_some, hCmp, hZ,
        gt_iff_lt, hP, decide_true, ↓reduceIte, hSh,
        show ¬ 7 ≥ 32 by decide, hs, truncBits_ofNat hRow' (by decide)]
  have hSelect : Seg kernel [] l g 1 480
      [(121, .pred true), (1091, b32 (n - 1)), (1092, b32 (128 * (n - 1)))] 481
      [(1091, b32 (n - 1)), (1838, b32 (128 * (n - 1))),
       (121, .pred true), (1092, b32 (128 * (n - 1)))] := by
    intro t h
    let u := next (setReg t 1838 (b32 (128 * (n - 1))))
    have hr : run kernel [] l g 1 t = some u := by
      apply run_local Flow.code_480 rfl h
      rw [execLocalA_nil, execLocal_selp rfl]
      simp [execMove, readReg, readValue, h.2.2.2.2.1, h.2.2.2.2.2.2.1,
        DType.width, Value.bytes, b32, bind, Except.bind, pure, Except.pure, u]
    exact ⟨u, hr, by
      simp [u, At, next, setReg, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
        h.2.2.2.2.2.1, h.2.2.2.2.2.2.1]⟩
  exact hTail.comp hSelect

end
end PTX.Kernels.TmlFa4Fwd.Loader
