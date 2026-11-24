-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxTerminalPublish
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Flow.Code.Part104
import Kernels.TmlFa4Fwd.Flow.Code.Part107
import Lemmas.Flow.OrBits

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof Prologue Softmax

noncomputable section

/-- The repeated and terminal statistics windows that set up a per-lane address. -/
inductive StatisticsAddressWindow where
  | biased | plainSetup | plain | final
  deriving DecidableEq

namespace StatisticsAddressWindow

def start : StatisticsAddressWindow → Nat
  | .biased => 5675
  | .plainSetup => 6661
  | .plain => 6886
  | .final => 7607

def stop : StatisticsAddressWindow → Nat
  | .biased => 5682
  | .plainSetup => 6664
  | .plain => 6890
  | .final => 7614

def selector : StatisticsAddressWindow → Nat
  | .biased => 4566
  | .plainSetup | .plain => 5176
  | .final => 5809

def tid : StatisticsAddressWindow → Nat
  | .biased => 4567
  | .plainSetup | .plain => 5177
  | .final => 5810

def base : StatisticsAddressWindow → Nat
  | .biased => 4571
  | .plainSetup | .plain => 5518
  | .final => 5814

def roots (l : Launch) (w : Fin 8) : List (Nat × Value) :=
  [(1062, b32 w.val), (2535, b32 l.sharedBase)]

def coordinates (l : Launch) (g : Nat) (w : Fin 8) (window : StatisticsAddressWindow) :
    List (Nat × Value) :=
  [(window.tid, b32 (g % l.block)), (window.selector, b32 (128 * (w.val / 4))),
    (2535, b32 l.sharedBase)]

def entry (l : Launch) (g : Nat) (w : Fin 8) : StatisticsAddressWindow → List (Nat × Value)
  | .plain => coordinates l g w .plain
  | _ => roots l w

def result (l : Launch) (g : Nat) (w : Fin 8) (window : StatisticsAddressWindow) :
    List (Nat × Value) :=
  match window with
  | .plainSetup => coordinates l g w .plain
  | _ => [(window.base, b32 (statsBase l g w))]

private theorem selectorRun (l : Launch) (g : Nat) (w : Fin 8)
    (window : StatisticsAddressWindow) (hw : window ≠ .plain) :
    Seg kernel Assumptions.all l g 2 window.start (roots l w) (window.start + 2)
      [(window.selector, b32 (128 * (w.val / 4))), (2535, b32 l.sharedBase)] := by
  cases window
  all_goals try exact (hw rfl).elim
  all_goals
    fin_cases w <;> intro t ht <;>
      (simp only [start, roots, selector] at ht ⊢; seg_fp ht using rfl)

private def tidMove (window : StatisticsAddressWindow) : Instr :=
  ⟨none, .move ⟨.scalar, .int .u 32, [some window.tid], [.sreg (.mk .tid (some .x))]⟩⟩

private theorem tidCode (window : StatisticsAddressWindow) (hw : window ≠ .plain) :
    kernel.code[window.start + 2]? = some window.tidMove := by
  cases window
  · exact Flow.code_5677
  · exact Flow.code_6663
  · exact (hw rfl).elim
  · exact Flow.code_7609

private theorem tidRun {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (w : Fin 8) (window : StatisticsAddressWindow) (hw : window ≠ .plain) :
    Seg kernel Assumptions.all l g 1 (window.start + 2)
      [(window.selector, b32 (128 * (w.val / 4))), (2535, b32 l.sharedBase)]
      (window.start + 3) (window.coordinates l g w) := by
  intro t ht
  have hTid := (sregValue_oneDim hp.cluster.2.2 g).1
  have hSmall : g % l.block < 2 ^ 32 := by
    rw [hp.block]
    exact (Nat.mod_lt _ (by decide : 0 < 512)).trans (by decide)
  let u := next (setReg t window.tid (b32 (g % l.block)))
  have hu : run kernel Assumptions.all l g 1 t = some u := by
    apply run_local (tidCode window hw) rfl ht
    rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil (by
      rw [ht.1]
      cases window <;> decide) rfl]
    simp [u, execLocalA, execLocalRule, execLocal, Op.rule, MoveInstr.rule, execMove,
      DType.width, readValue, readBits, SReg.width, hTid, bind, Except.bind,
      pure, Except.pure, truncBits_ofNat hSmall (by decide), Value.bytes, b32]
  refine ⟨u, hu, ht.set ?_⟩
  cases window <;> simp [tid, selector]

private def combineStart : StatisticsAddressWindow → Nat
  | .plain => 6886
  | window => window.start + 3

private theorem combineRun {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (w : Fin 8) (hWarp : w.val = warpIndex l g)
    (window : StatisticsAddressWindow) (hNotSetup : window ≠ .plainSetup) :
    Seg kernel Assumptions.all l g 4 window.combineStart (window.coordinates l g w)
      window.stop [(window.base, b32 (statsBase l g w))] := by
  have hTid : g % l.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hStage := w.isLt
  have hBase := hp.shared.2.1
  have hPack : 128 * (w.val / 4) ||| (g % l.block % 128) = 32 * w.val + laneOf l g := by
    rw [lor_eq_add (k := 7) (x := 128 * (w.val / 4))
      (y := g % l.block % 128) (by omega) (Nat.mod_lt _ (by decide))]
    rw [hWarp]
    unfold warpIndex laneOf
    omega
  have hIndex : 32 * w.val + laneOf l g < 256 := by
    have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
    omega
  have hAddress : l.sharedBase + (32 * w.val + laneOf l g) * 4 = statsBase l g w := by
    unfold statsBase
    omega
  have hResult32 : statsBase l g w < 4294967296 := by rw [← hAddress]; omega
  have hResult64 : statsBase l g w < 18446744073709551616 := by omega
  cases window
  all_goals try exact (hNotSetup rfl).elim
  all_goals
    intro t ht
    simp only [coordinates, selector, tid, start, stop, combineStart, base] at ht ⊢
    seg_fp ht using norm_bits [
      Nat.mod_eq_of_lt (show g % l.block < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (show 128 * (w.val / 4) < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (show g % l.block < 4294967296 by omega),
      Nat.mod_eq_of_lt (show 128 * (w.val / 4) < 4294967296 by omega),
      Nat.mod_eq_of_lt (show g % l.block % 128 < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (show g % l.block % 128 < 4294967296 by omega),
      Nat.mod_eq_of_lt (show 32 * w.val + laneOf l g < 4294967296 by omega),
      Nat.mod_eq_of_lt (show (32 * w.val + laneOf l g) * 4 < 4294967296 by omega),
      Nat.mod_eq_of_lt (show l.sharedBase < 4294967296 by omega),
      Nat.mod_eq_of_lt (show l.sharedBase + (32 * w.val + laneOf l g) * 4 < 4294967296 by omega),
      Nat.and_two_pow_sub_one_eq_mod (g % l.block) 7, hPack, hAddress,
      Nat.mod_eq_of_lt hResult32, Nat.mod_eq_of_lt hResult64]

/-- The exact decoded address setup reads only the lane coordinates and shared base. -/
theorem replay {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (w : Fin 8) (hw : w.val = warpIndex l g) (window : StatisticsAddressWindow) :
    Seg kernel Assumptions.all l g (window.stop - window.start) window.start
      (window.entry l g w) window.stop (window.result l g w) := by
  cases window
  case biased =>
    intro t ht
    seg_chain ht [selectorRun l g w .biased (by decide), tidRun hp g w .biased (by decide),
      combineRun hp g w hw .biased (by decide)]
  case plainSetup =>
    intro t ht
    seg_chain ht [selectorRun l g w .plainSetup (by decide), tidRun hp g w .plainSetup (by decide)]
  case plain => exact combineRun hp g w hw .plain (by decide)
  case final =>
    intro t ht
    seg_chain ht [selectorRun l g w .final (by decide), tidRun hp g w .final (by decide),
      combineRun hp g w hw .final (by decide)]

end StatisticsAddressWindow
end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
