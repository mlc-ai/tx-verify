-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSource
public import Kernels.TmlFa4Fwd.Proof.LoaderPointerReload
import Lemmas.Flow.SignedBits

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The decoded comparison before the first K pointer reload enables exactly the
rows below the selected request's key length. -/
theorem primingKFirstMaskResidual (l : Launch) (g : Nat) {len tile tid : Nat}
    (hLen : len < 2 ^ 31) (hRow : kvCopyRow tile tid 0 < 2 ^ 31) :
    Seg kernel [] l g 5 538
      [(1062, b32 (tid / 32)), (1081, b32 (tid / 8 % 8)), (1092, b32 (128 * tile)),
       (1086, b32 len), (121, .pred true)] 543
      [(124, .pred (decide (kvCopyRow tile tid 0 < len))),
       (1852, b32 ((len + 2 ^ 32 - kvCopyRow tile tid 0) % 2 ^ 32))] := by
  have hRowEq : 128 * tile + tid / 8 % 8 = kvCopyRow tile tid 0 := by simp [kvCopyRow]
  have hBlock : tid / 8 % 8 < 2 ^ 32 := by omega
  have hTile : 128 * tile < 2 ^ 32 := by omega
  have hLen32 : len < 2 ^ 32 := by omega
  have hRow32 : kvCopyRow tile tid 0 < 2 ^ 32 := by omega
  have hRow64 : kvCopyRow tile tid 0 < 2 ^ 64 := by omega
  have hBlock' : tid / 8 % 8 % 4294967296 = tid / 8 % 8 := Nat.mod_eq_of_lt hBlock
  have hTile' : 128 * tile % 4294967296 = 128 * tile := Nat.mod_eq_of_lt hTile
  have hLen' : len % 4294967296 = len := Nat.mod_eq_of_lt hLen32
  have hRow' : kvCopyRow tile tid 0 % 4294967296 = kvCopyRow tile tid 0 := Nat.mod_eq_of_lt hRow32
  have hRowRev : tid / 8 % 8 + 128 * tile = kvCopyRow tile tid 0 := by omega
  have hRow64' : kvCopyRow tile tid 0 % 18446744073709551616 = kvCopyRow tile tid 0 :=
    Nat.mod_eq_of_lt hRow64
  intro s hs
  seg_fp hs using
    norm_signed [hBlock', hTile', hLen', hRow', hRowRev, hRow64']

/-- The decoded first K reload obtains the first-slot pointer from both scalar
halves of the same eight-byte cell. -/
def primingKPointerReload : SavedPointerReload :=
  ⟨543, 7292, 0, 1853, 1854⟩

/-- Inputs maintained while the actual first K copy mask is computed and the
first pointer is reloaded. -/
def primingKMaskInputs (p : Params) (l : Launch) (batch tile warp lane : Nat) :
    List (Nat × Value) :=
  let tid := 32 * warp + lane
  [(1062, b32 (tid / 32)), (1081, b32 (tid / 8 % 8)), (1092, b32 (128 * tile)),
   (1086, b32 (p.kLength batch)), (121, .pred true), (7292, b64 l.localBase),
   (1082, b32 (kvCopyColumn tid false)),
   (1083, b32 (kvCopyAddress l.sharedBase 0 tid 0 false)),
   (1084, b32 (kvCopyAddress l.sharedBase 0 tid 1 false))]

/-- Compute the first K copy mask and reach the exact pointer reload operands. -/
theorem primingKMaskDecode {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch tile warp lane : Nat} (hb : batch < p.batch) (hTile : 128*tile+7 < 2^31)
    {s : TState} (hs : At s 538 (primingKMaskInputs p l batch tile warp lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 543 (primingKSourceFrame p l batch tile warp lane) := by
  have hLen := (hp.lengths batch hb).2.2
  let tid := 32 * warp + lane
  have hRow : kvCopyRow tile tid 0 < 2 ^ 31 := by
    have hSmall := Nat.mod_lt (tid / 8) (by decide : 0 < 8)
    simp only [kvCopyRow, Nat.mul_zero, Nat.add_zero]
    omega
  obtain ⟨u, hu, hU⟩ := primingKFirstMaskResidual l g (tid := tid)
    (by omega) hRow s (hs.mono ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.1,
      hs.2.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.1, trivial⟩)
  obtain ⟨huA, hFrame⟩ := loaderLinear (regs := [7292, 1082, 1083, 1084]) (by decide) (by decide)
    hs.1 (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  exact ⟨u, run_rtg huA, hU.mono
    ⟨(hFrame 1082 (by simp)).trans hs.2.2.2.2.2.2.2.2.2.2.1, hU.2.2.2.2.1,
     (hFrame 1083 (by simp)).trans hs.2.2.2.2.2.2.2.2.2.2.2.1,
     (hFrame 1084 (by simp)).trans hs.2.2.2.2.2.2.2.2.2.2.2.2.1,
     hU.2.2.2.2.2.1, (hFrame 7292 (by simp)).trans hs.2.2.2.2.2.2.2.2.2.1, trivial⟩⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g batch head tile warp shuffles votes : Nat}
    (hb : batch < p.batch) (hh : head < p.kvHeads) (hTile : 128 * tile + 7 < 2 ^ 31)
    (cur : SchedulerWarpAt l X g 538 (primingKMaskInputs p l batch tile warp) shuffles votes)
    (hStored : ∀ lane < 32, ∃ write < cur.pos lane,
      let thread := warpLane l g lane
      let row := primingLaneRow tile (32 * warp + lane)
      X.Writes (thread, write) (sourceScratchAccess l thread 0)
        (b64 (primingKRowPointer p batch head row)).toBytes ∧
      ∀ byte < 8, ∀ j < cur.pos lane, ∀ acc, X.Access (thread, j) acc true →
        acc.Covers ((sourceScratchAccess l thread 0).loc.at byte) → j ≤ write)
include hp hX hb hh hTile cur hStored

end

end
end PTX.Kernels.TmlFa4Fwd.Loader
