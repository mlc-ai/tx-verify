-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalUpScan
import Kernels.TmlFa4Fwd.Flow.Code.Part142
import Kernels.TmlFa4Fwd.Flow.Code.Part143

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

def terminalGroupTotal (p : Params) (first : Nat) : Nat :=
  prefixWindow (groupLaneTiles p first) 32 31

/-- Either correction drain scan broadcasts the exact total of the current request group. -/
theorem terminalGroupTotalOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} (hg : g < l.threads) (later : Bool)
    {ends : Nat → Option TState} {F : Nat → List (Nat × Value)}
    (hFresh : ∀ lane < 32, ∀ x ∈ F lane, x.1 ≠ 7284)
    (cur : SchedulerWarpReached l X g (scanPc later 4+3)
      (fun lane => let t := warpLane l g lane
        (7283,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l t)))::F lane)
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g (scanPc later 4+4)
      (fun lane => let t := warpLane l g lane
        (7284,b32 (terminalGroupTotal p first))::
          (7283,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l t)))::F lane)
      (shuffles+1) votes ends) := by
  let word := fun lane => b32 (prefixWindow (groupLaneTiles p first) 32
    (laneOf l (warpLane l g lane)))
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hCode :
      kernel.code[scanPc later 4+3]? = some ⟨none,.warp
        {kind := .shfl .idx,ty := some (.int .b 32),dsts := [some 7284],
          srcs := [.reg 7283,.imm 31,.imm 31],mask := some (.imm (-1))}⟩ := by
    cases later
    · exact Flow.code_9125
    · exact Flow.code_9182
  obtain ⟨d⟩ := cur.consumeShuffle (dst := 7284) hp hMax hg .idx word
    (fun _ => 31) (fun _ => 31) (fun lane hl x hm => by
      rcases List.mem_cons.mp hm with rfl | hm
      · dsimp only; decide
      · exact hFresh lane hl x hm)
    (by
      intro lane hl
      have ht := cur.checkpoint lane hl
      have hCore := RowDrainRole.correction.drainCore (l := l) (g := warpLane l g lane)
        (s := cur.state lane) (by rw [ht.1]; cases later <;> decide)
        (by rw [ht.1]; cases later <;> decide)
      rw [hCore,out_event ht.2.2.2.1 (ht.1.symm ▸ hCode) rfl rfl]
      change Out.ev (shflTmpl l (warpLane l g lane) (cur.state lane) .idx 7284 none
        (.reg 7283) (.imm 31) (.imm 31) (.imm (-1))) = _
      have hReg : (cur.state lane).regs 7283 = some (word lane) := ht.2.2.2.2.1
      simp [shflTmpl,readValue,readReg,hReg,hBlock,word,b32,Value.bytes,readBits,pure,Except.pure]
      rfl)
  apply d.advanceLocal
  intro lane hl
  have h31 : laneOf l (warpLane l g 31) = 31 :=
    (Step.sameWarp_lane hBlock hg (by decide : 31 < 32)).2
  have hFrom : (shflSource .idx lane 31 31).1 = 31 :=
    congrArg Prod.fst (shflSource_idx lane (by decide : (31 : Nat) < 32))
  have hd := d.checkpoint lane hl
  exact ⟨_,.refl,by simpa only [word,hFrom,h31,terminalGroupTotal,Nat.add_assoc] using hd⟩

theorem terminalFirstTotal (p : Params) :
    terminalGroupTotal p 0 = tilePrefix p (min p.batch 31) := by
  unfold terminalGroupTotal
  rw [prefixWindow_warp _ (by decide : 31 < 32)]
  have h := groupTiles_eq p (Nat.zero_le p.batch) (by decide : 32 ≤ 32)
  simpa [tilePrefix] using h

end PTX.Kernels.TmlFa4Fwd.Correction
