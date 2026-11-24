-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQRegisters
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainEntry
public import Lemmas.Kernel.ReadValue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue Prologue

noncomputable section

private theorem signedWord {n : Nat} (hn : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left hn]

private theorem firstGate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat) :
    Seg kernel [] l g 2 1935 [(1180, b32 (laneOf l g)), (7203, b32 p.batch),
      (7506, b64 p.cuQBase)] 1937
      [(334, .pred (decide (p.batch < laneOf l g))), (7193, b32 0),
        (1180, b32 (laneOf l g)), (7506, b64 p.cuQBase), (7203, b32 p.batch)] := by
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hBatch := hp.shape.2.1
  have hLane32 : laneOf l g < 2 ^ 32 := by omega
  have hBatch32 : p.batch < 2 ^ 32 := by omega
  intro t ht
  seg_fp ht using first
    | rfl
    | simp only [truncBits_ofNat hLane32 (by decide), truncBits_ofNat hBatch32 (by decide),
        compare, Option.getD_some, signedWord (show laneOf l g < 2 ^ 31 by omega),
        signedWord hBatch, gt_iff_lt, Int.ofNat_lt]

variable {p : Params} {l : Launch} {m : Mem0}

private theorem firstReadAddress (hp : Pre p l m) (g : Nat) (hb : laneOf l g ≤ p.batch) :
    Seg kernel [] l g 2 1938 [(1180, b32 (laneOf l g)), (7506, b64 p.cuQBase)] 1940
      [(7877, b64 (p.cuQBase + 4 * laneOf l g))] := by
  have hRange := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRange
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hLane32 : laneOf l g < 2 ^ 32 := by omega
  have hLane64 : laneOf l g < 2 ^ 64 := by omega
  have hOff : 4 * laneOf l g < 2 ^ 64 := by omega
  have hCuQ : p.cuQBase < 2 ^ 64 := by omega
  have hAddr : p.cuQBase + 4 * laneOf l g < 2 ^ 64 := by omega
  have h4 : (truncBits 32 (BitVec.ofInt 64 4)).toNat = 4 := rfl
  intro t ht
  seg_fp ht using simp only [b64, kind_u_beq_s, Bool.false_eq_true, ↓reduceIte,
    truncBits_ofNat hLane32 (by decide), toNat_ofNat_lt hLane64, h4, Nat.mul_comm (laneOf l g),
    truncBits_ofNat hOff (by decide), truncBits_ofNat hCuQ (by decide),
    ← BitVec.ofNat_add, truncBits_ofNat hAddr (by decide)]

private theorem firstSchedulerBranch (hp : Pre p l m) {g : Nat} {t : TState}
    (ht : At t 1935 [(1180, b32 (laneOf l g)), (7203, b32 p.batch), (7506, b64 p.cuQBase)]) :
    ∃ w, At w (if p.batch < laneOf l g then 1941 else 1938)
        [(334, .pred (decide (p.batch < laneOf l g))), (7193, b32 0),
          (1180, b32 (laneOf l g)), (7506, b64 p.cuQBase), (7203, b32 p.batch)] ∧
      w.regs 1072 = t.regs 1072 ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t w := by
  obtain ⟨v, hv, hV⟩ := firstGate hp g t ht
  have hJ := localRun (by decide) (by decide) ht.1 (by
    set_option maxRecDepth 100000 in kernel_rfl) hv
  obtain ⟨w, hw, hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1937 _ hV hV.2.2.2.2.1 (by simp)
  have hGate := localRun (by decide) (by decide) hV.1 rfl hw
  have hFrame : w.regs 1072 = t.regs 1072 :=
    schedulerLocalFrame (lo := 1935) (len := 3) (regs := [1072]) (by
      set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (run_comp hv hw) ht.1.ge (by rw [ht.1]) (by decide)
  exact ⟨w, by simpa using hW, hFrame, run_rtg (run_comp hJ hGate)⟩

/-- An inactive lane skips the initial CuQ load and gives the shuffle a zero input. -/
theorem firstSchedulerSkipWithFrame (hp : Pre p l m) {g : Nat} {t : TState}
    (hLane : p.batch < laneOf l g)
    (ht : At t 1935 [(1180, b32 (laneOf l g)), (7203, b32 p.batch), (7506, b64 p.cuQBase)]) :
    ∃ u, At u 1941 [(7193, b32 (drainCuQ p (laneOf l g))),
        (1180, b32 (laneOf l g)), (7203, b32 p.batch)] ∧
      u.regs 1072 = t.regs 1072 ∧ Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  obtain ⟨w, hw, hFrame, hLocal⟩ := firstSchedulerBranch hp ht
  have hAt : At w 1941 [(7193, b32 0), (1180, b32 (laneOf l g)), (7203, b32 p.batch)] :=
    ⟨by simpa [hLane] using hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.2.1,
      hw.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.1, trivial⟩
  exact ⟨w, by simpa [drainCuQ, Nat.not_le.mpr hLane] using hAt, hFrame, hLocal⟩

/-- The local route to the first CuQ read also gives its populated operand register. -/
theorem firstSchedulerNextWithFrame (hp : Pre p l m) {g : Nat} {t : TState}
    (hLane : laneOf l g ≤ p.batch)
    (ht : At t 1935 [(1180, b32 (laneOf l g)), (7203, b32 p.batch), (7506, b64 p.cuQBase)]) :
    ∃ s, At s 1940 [(7877, b64 (p.cuQBase + 4 * laneOf l g)),
        (1180, b32 (laneOf l g)), (7203, b32 p.batch)] ∧
      s.regs 1072 = t.regs 1072 ∧ Next kernel Assumptions.all l g t s
        (.read {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4}
          (afterLoad s [7193])) := by
  obtain ⟨w, hW, hCta, hBranch⟩ := firstSchedulerBranch hp ht
  have hPc : w.pc = 1938 := by simpa [Nat.not_lt_of_ge hLane] using hW.1
  have hW' : At w 1938 [(1180, b32 (laneOf l g)), (7506, b64 p.cuQBase)] :=
    ⟨hPc, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.2.2.1,
      hW.2.2.2.2.2.2.2.1, trivial⟩
  obtain ⟨s, hs, hS⟩ := firstReadAddress hp g hLane w hW'
  have hLocal := localRun (by decide) (by decide) hPc (by
    set_option maxRecDepth 100000 in kernel_rfl) hs
  let addr := p.cuQBase + 4 * laneOf l g
  have hRange := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRange
  have hAlign := hp.alignment.2.2.2.2.2.2.2.2.1
  have hAddr : addr < 2 ^ 64 := by dsimp only [addr]; omega
  have hWordAlign : addr % 4 = 0 := by dsimp only [addr]; omega
  have hFrame {r : Nat} (hm : r ∈ [1180, 7203, 1072]) : s.regs r = w.regs r :=
    schedulerLocalFrame (lo := 1938) (len := 2) (by
      set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hs hPc.ge (by rw [hPc]) hm
  have hKeep : At s 1940 [(7877, b64 (p.cuQBase + 4 * laneOf l g)),
      (1180, b32 (laneOf l g)), (7203, b32 p.batch)] :=
    hS.mono ⟨hS.2.2.2.2.1,
      (hFrame (by decide)).trans hW.2.2.2.2.2.2.1,
      (hFrame (by decide)).trans hW.2.2.2.2.2.2.2.2.1, trivial⟩
  refine ⟨s, hKeep, (hFrame (by decide)).trans hCta, hBranch.trans (run_rtg hLocal), ?_⟩
  rw [out_eq_core (by rw [hS.1]; decide) (by rw [hS.1]; decide),
    out_event hS.2.2.2.1 (by rw [hS.1]; exact Flow.code_1940) rfl rfl]
  exact congrArg Out.ev (loadTmpl_global hS.2.1 hS.2.2.2.2.1 hAddr (by decide) hWordAlign)

/-- The initial scheduler exchange is a full-warp down shuffle. -/
theorem firstDownTemplate (hp : Pre p l m) {g : Nat} {t : TState}
    (ht : At t 1941 [(7193, b32 (drainCuQ p (laneOf l g)))]) :
    out kernel Assumptions.all l g t = .ev (.shfl .down (b32 (drainCuQ p (laneOf l g))) 1 31
      (fun v _ => next (setReg t 2456 v))) := by
  rw [out_eq_core (by rw [ht.1]; decide) (by rw [ht.1]; decide),
    out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_1941) rfl rfl]
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  change Out.ev (shflTmpl l g t .down 2456 none (.reg 7193) (.imm 1) (.imm 31) (.imm (-1))) = _
  simp [shflTmpl, readValue, readReg, ht.2.2.2.2.1, hBlock, Value.bytes, b32, readBits,
    pure, Except.pure]
  rfl

/-- The first scheduler shuffle follows the allocation and the lane's optional cuQ load. -/
def firstSchedulerPos (p : Params) (lane : Nat) : Nat :=
  descriptorShufflePos lane + 1 + (if lane ≤ p.batch then 1 else 0)

end
end PTX.Kernels.TmlFa4Fwd.Mma
