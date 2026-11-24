-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalRequestGuard
import Kernels.TmlFa4Fwd.Flow.Code.Part119

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

/-- The first terminal rescan broadcasts the exact number of request tiles in its group. -/
theorem terminalDrainFirstTotalOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7657
      (fun lane => let t := warpLane l g lane
        [(7263,b32 (prefixWindow (groupLaneTiles p 0) 32 (laneOf l t))),(7141,b32 p.heads)] ++
          RowDrainRole.softmax.roots p l t) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 7658
      (fun lane => let t := warpLane l g lane
        [(7264,b32 (tilePrefix p (min p.batch 31))),
          (7263,b32 (prefixWindow (groupLaneTiles p 0) 32 (laneOf l t))),(7141,b32 p.heads)] ++
          RowDrainRole.softmax.roots p l t) (shuffles+1) votes ends) := by
  let part := prefixWindow (groupLaneTiles p 0) 32
  let word := fun lane => b32 (part (laneOf l (warpLane l g lane)))
  have hb : l.block%32 = 0 := by rw [hp.block]
  obtain ⟨after⟩ := cur.consumeShuffle (dst := 7264) hp hMax hg .idx word
    (fun _ => 31) (fun _ => 31) (by
      intro lane _ pair hm
      simp only [List.cons_append,List.nil_append,RowDrainRole.roots,RowDrainRole.batchReg,
        RowDrainRole.frame,RowDrainRole.laneReg,RowDrainRole.ctaReg,
        List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide)
    (by
      intro lane hl
      have ht := cur.checkpoint lane hl
      have hCore := RowDrainRole.softmax.drainCore (l := l) (g := warpLane l g lane)
        (s := cur.state lane) (by rw [ht.1]; decide) (by rw [ht.1]; decide)
      rw [hCore,out_event ht.2.2.2.1 (ht.1.symm ▸ Flow.code_7657) rfl rfl]
      change Out.ev (shflTmpl l (warpLane l g lane) (cur.state lane) .idx 7264 none
        (.reg 7263) (.imm 31) (.imm 31) (.imm (-1))) = _
      have hReg : (cur.state lane).regs 7263 = some (word lane) := ht.2.2.2.2.1
      simp [shflTmpl,readValue,readReg,hReg,hb,word,b32,Value.bytes,readBits,pure,Except.pure]
      rfl)
  apply after.advanceLocal
  intro lane hl
  have ht := after.checkpoint lane hl
  have h31 : laneOf l (warpLane l g 31) = 31 :=
    (Step.sameWarp_lane hb hg (by decide : 31 < 32)).2
  have hCount : part 31 = tilePrefix p (min p.batch 31) := by
    change prefixWindow (groupLaneTiles p 0) 32 31 = _
    rw [prefixWindow_warp _ (by decide : (31 : Nat) < 32)]
    have h := groupTiles_eq p (Nat.zero_le p.batch) (show (32 : Nat) ≤ 32 by decide)
    simpa [tilePrefix] using h
  have hFrom : (shflSource .idx lane 31 31).1 = 31 := by
    rw [shflSource_idx lane (by decide : (31 : Nat) < 32)]
  exact ⟨_,.refl,by simpa only [word,hFrom,h31,hCount,List.cons_append,List.nil_append] using ht⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
