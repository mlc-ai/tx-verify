-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxStats
import Lemmas.Flow.Footprint
import Lemmas.Flow.SegChain
import Lemmas.Flow.OrBits
import Kernels.TmlFa4Fwd.Proof.LoaderEntry
import Kernels.TmlFa4Fwd.Proof.SoftmaxMax

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax

open PTX PTX.Proof PTX.Flow Prologue

noncomputable section

private def terminalWordFrame (warp : Fin 8) (sum maximum : Value) : List (Nat × Value) :=
  [(7257, sum), (7256, maximum), (5127, b32 (3 + warp.val))]

private theorem terminalStageColumn (l : Launch) (g : Nat) (warp : Fin 8) (sum maximum : Value) :
    Seg kernel Assumptions.all l g 2 7607
      ((1062, b32 warp.val) :: (2535, b32 l.sharedBase) :: terminalWordFrame warp sum maximum)
      7609 ((5809, b32 (128 * (warp.val / 4))) :: (2535, b32 l.sharedBase) ::
        terminalWordFrame warp sum maximum) := by
  fin_cases warp <;> intro t ht <;> unfold terminalWordFrame at ht ⊢ <;>
    seg_fp ht using rfl

private theorem terminalThreadColumn {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (g : Nat) (warp : Fin 8) (sum maximum : Value) :
    Seg kernel Assumptions.all l g 1 7609
      ((5809, b32 (128 * (warp.val / 4))) :: (2535, b32 l.sharedBase) ::
        terminalWordFrame warp sum maximum)
      7610 ((5810, b32 (g % l.block)) :: (5809, b32 (128 * (warp.val / 4))) ::
        (2535, b32 l.sharedBase) :: terminalWordFrame warp sum maximum) := by
  intro t ht
  have hTid := (sregValue_oneDim hp.cluster.2.2 g).1
  have hSmall : g % l.block < 2 ^ 32 := by
    rw [hp.block]
    exact (Nat.mod_lt _ (by decide : 0 < 512)).trans (by decide)
  let u := next (setReg t 5810 (b32 (g % l.block)))
  have hu : run kernel Assumptions.all l g 1 t = some u := by
    apply run_local Flow.code_7609 rfl ht
    rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil (by
      rw [ht.1]
      decide) rfl]
    simp [u, execLocalA, execLocalRule, execLocal, Op.rule, MoveInstr.rule, execMove,
      DType.width, readValue, readBits, SReg.width, hTid, bind, Except.bind,
      pure, Except.pure, truncBits_ofNat hSmall (by decide), Value.bytes, b32]
  exact ⟨u, hu, ht.set (by simp [terminalWordFrame])⟩

private theorem terminalStatsAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (warp : Fin 8) (hWarp : warp.val = warpIndex l g) (sum maximum : Value) :
    Seg kernel Assumptions.all l g 4 7610
      ((5810, b32 (g % l.block)) :: (5809, b32 (128 * (warp.val / 4))) ::
        (2535, b32 l.sharedBase) :: terminalWordFrame warp sum maximum)
      7614 ((5814, b32 (statsBase l g warp)) :: terminalWordFrame warp sum maximum) := by
  have hTid : g % l.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hStage := warp.isLt
  have hBase := hp.shared.2.1
  have hPack : 128 * (warp.val / 4) ||| (g % l.block % 128) = 32 * warp.val + laneOf l g := by
    rw [lor_eq_add (k := 7) (x := 128 * (warp.val / 4))
      (y := g % l.block % 128) (by omega) (Nat.mod_lt _ (by decide))]
    rw [hWarp]
    unfold warpIndex laneOf
    omega
  have hIndex : 32 * warp.val + laneOf l g < 256 := by
    have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
    omega
  have hAddress' : l.sharedBase + (32 * warp.val + laneOf l g) * 4 = statsBase l g warp := by
    unfold statsBase
    omega
  have hResult32 : statsBase l g warp < 4294967296 := by rw [← hAddress']; omega
  have hResult64 : statsBase l g warp < 18446744073709551616 := by omega
  intro t ht
  unfold terminalWordFrame at ht ⊢
  seg_fp ht using norm_bits [
    Nat.mod_eq_of_lt (show g % l.block < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show 128 * (warp.val / 4) < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show g % l.block < 4294967296 by omega),
    Nat.mod_eq_of_lt (show 128 * (warp.val / 4) < 4294967296 by omega),
    Nat.mod_eq_of_lt (show g % l.block % 128 < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show g % l.block % 128 < 4294967296 by omega),
    Nat.mod_eq_of_lt (show 32 * warp.val + laneOf l g < 4294967296 by omega),
    Nat.mod_eq_of_lt (show (32 * warp.val + laneOf l g) * 4 < 4294967296 by omega),
    Nat.mod_eq_of_lt (show l.sharedBase < 4294967296 by omega),
    Nat.mod_eq_of_lt (show l.sharedBase + (32 * warp.val + laneOf l g) * 4 < 4294967296 by omega),
    Nat.and_two_pow_sub_one_eq_mod (g % l.block) 7, hPack, hAddress',
    Nat.mod_eq_of_lt hResult32, Nat.mod_eq_of_lt hResult64]

/-- The terminal softmax path derives the address of its statistics words from its warp and lane. -/
theorem terminalStatsReady {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (warp : Fin 8) (hWarp : warp.val = warpIndex l g) {t : TState} {sum maximum : Value}
    (ht : At t 7607 [(1062, b32 warp.val), (2535, b32 l.sharedBase), (7257, sum),
      (7256, maximum), (5127, b32 (3 + warp.val))]) :
    ∃ u, run kernel Assumptions.all l g 7 t = some u ∧
      At u 7614 [(5814, b32 (statsBase l g warp)), (7257, sum), (7256, maximum),
        (5127, b32 (3 + warp.val))] := by
  seg_chain ht [terminalStageColumn l g warp sum maximum,
    terminalThreadColumn hp g warp sum maximum, terminalStatsAddress hp g warp hWarp sum maximum]

/-- The terminal batch check preserves the last round's sum and maximum while preparing
their shared addresses. This cursor is shared by the one-visit and repeated paths. -/
theorem terminalStatsReadyFromDrain {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (warp : Fin 8) (hWarp : warp.val = warpIndex l g)
    {t : TState} {sum maximum : Value}
    (ht : At t 7605 [(1215, b32 (laneOf l g)), (1062, b32 warp.val), (2535, b32 l.sharedBase),
      (7257, sum), (7256, maximum), (5127, b32 (3 + warp.val))]) :
    ∃ u, run kernel Assumptions.all l g 9 t = some u ∧
      At u 7614 [(5814, b32 (statsBase l g warp)), (7257, sum), (7256, maximum),
        (5127, b32 (3 + warp.val))] := by
  let F := [(1062, b32 warp.val), (2535, b32 l.sharedBase), (7257, sum), (7256, maximum),
    (5127, b32 (3 + warp.val))]
  let v := next (setReg t 7151 (b32 p.batch))
  obtain ⟨hWord, hParam⟩ := hp.values (19, p.batch) (by simp [Params.scalarWords])
  change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at hParam
  rw [Loader.loaderParam19Name] at hParam
  have hv : run kernel Assumptions.all l g 1 t = some v := by
    apply run_local Flow.code_7605 rfl ht
    rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil (by
      rw [ht.1]
      decide) rfl, execLocalA_nil, execLocal_mem rfl]
    simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq,
      hParam, DType.width, MemExt.extendBits_same, pure, Except.pure]
    rw [truncBits_ofNat hWord (by decide)]
    rfl
  have hvAt : At v 7606 ((7151, b32 p.batch) :: (1215, b32 (laneOf l g)) :: F) :=
    ht.set (by simp)
  let drained := compare .gt .s 32 (truncBits 32 (BitVec.ofNat 64 (laneOf l g)))
    (truncBits 32 (BitVec.ofNat 64 p.batch))
  have hCmp : Seg kernel Assumptions.all l g 1 7606
      ((7151, b32 p.batch) :: (1215, b32 (laneOf l g)) :: F) 7607 ((652, .pred drained) :: F) := by
    intro s hs
    dsimp only [F] at hs ⊢
    seg_fp hs using rfl
  obtain ⟨w, hw, hwAt⟩ := hCmp.apply hvAt
  obtain ⟨u, hu, hAt⟩ := terminalStatsReady hp warp hWarp (hwAt.mono hwAt.2.2.2.2.2)
  exact ⟨u, run_comp (run_comp hv hw) hu, hAt⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
