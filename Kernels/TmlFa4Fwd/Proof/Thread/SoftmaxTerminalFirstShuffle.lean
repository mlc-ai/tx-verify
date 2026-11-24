-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalDrainStart
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
import Kernels.TmlFa4Fwd.Flow.Code.Part119

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

/-- The first scheduler shuffle carries the exact protected CuQ endpoint of each
lane and advances the recorded full warp once all lanes are at that collective. -/
theorem terminalDrainConsumesFirstShuffle {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7622
      (fun lane => let t := warpLane l g lane
        (7259,b32 (terminalFirstWord p l t))::RowDrainRole.softmax.roots p l t)
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 7623
      (fun lane => let t := warpLane l g lane
        let peer := warpLane l g (shflSource .down lane 1 31).1
        (5815,b32 (terminalFirstWord p l peer)) ::
          (7259,b32 (terminalFirstWord p l t)) :: RowDrainRole.softmax.roots p l t)
      (shuffles+1) votes ends) := by
  apply cur.consumeShuffle hp hMax hg .down
    (fun lane => b32 (terminalFirstWord p l (warpLane l g lane))) (fun _ => 1) (fun _ => 31)
  · intro lane hl item hm
    simp [RowDrainRole.roots,RowDrainRole.batchReg,RowDrainRole.frame,
      RowDrainRole.laneReg,RowDrainRole.ctaReg] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> simp
  · intro lane hl
    let t := cur.state lane
    let thread := warpLane l g lane
    let word := terminalFirstWord p l thread
    have ht := cur.checkpoint lane hl
    have hCore := RowDrainRole.softmax.drainCore (l := l) (g := thread) (s := t)
      (by rw [ht.1]; decide) (by rw [ht.1]; decide)
    rw [hCore,out_event ht.2.2.2.1 (ht.1.symm ▸ Flow.code_7622) rfl rfl]
    change Out.ev (shflTmpl l thread t .down 5815 none (.reg 7259)
      (.imm 1) (.imm 31) (.imm (-1))) = _
    have hb : l.block%32 = 0 := by rw [hp.block]
    have hReg : t.regs 7259 = some (.bits 32 (BitVec.ofNat 64 word)) := ht.2.2.2.2.1
    simp [shflTmpl,readValue,readReg,hReg,hb,Value.bytes,readBits,pure,Except.pure]
    rfl

end PTX.Kernels.TmlFa4Fwd.Softmax
