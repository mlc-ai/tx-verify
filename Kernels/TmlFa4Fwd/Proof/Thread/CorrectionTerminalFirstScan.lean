-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalDrainWarp
import Kernels.TmlFa4Fwd.Flow.Code.Part142
import all Kernels.TmlFa4Fwd.Proof.LoaderSelectedCoordinates
import all Kernels.TmlFa4Fwd.Proof.CorrectionFirstTiles

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

private theorem firstTerminalCounts {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} {t : TState}
    (ht : At t 9091
      ((7082,b32 (drainCuQ p (shflSource .down (laneOf l g) 1 31).1))::
        terminalFirstFrame p l g)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 9104 ((7282,b32 (groupLaneTiles p 0 (laneOf l g)))::
        RowDrainRole.correction.roots p l g) := by
  let lane := laneOf l g
  let begin := drainCuQ p lane
  let finish := drainCuQ p (shflSource .down lane 1 31).1
  let active := decide (laneHasRequest lane p.batch)
  let F := RowDrainRole.correction.roots p l g
  let diff := truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin)
  obtain ⟨hBegin,hFinish,hMono,hLength,hTiles⟩ := drainWordTiles hp 0 lane
  simp only [Nat.zero_add] at hBegin hFinish hMono hLength hTiles
  change begin < 2^32 at hBegin
  change finish < 2^32 at hFinish
  change (if active then (finish-begin+255)/256 else 0) = _ at hTiles
  have hPair : At t 9091 [(7082,b32 finish),(7279,b32 begin)] :=
    ht.mono ⟨ht.2.2.2.2.1,ht.2.2.2.2.2.2.1,trivial⟩
  have hPrep : Seg kernel [] l g 2 9091 [(7082,b32 finish),(7279,b32 begin)] 9093
      [(1657,.bits 32 diff),(7282,b32 0)] := by
    intro t hAt
    seg_fp hAt using
      first
      | rfl
      | simp only [diff,truncBits_ofNat hBegin (by decide),truncBits_ofNat hFinish (by decide)]
  obtain ⟨v,hRun,hV⟩ := hPrep.apply hPair
  let C := (685,Value.pred (!active))::F
  have hRegs : Holds v.regs C := holdsSchedulerFrame
    (show Holds t.regs C from ⟨ht.2.2.2.2.2.1,ht.2.2.2.2.2.2.2⟩)
    (fun r hr => schedulerLocalFrame (lo := 9091) (len := 2)
      (by
        change ((kernel.code.drop 9091).take 2).all
          (fun i => [685,7153,1616,7506,1618].all (fun r => !(writesRegs i.op).contains r)) = true
        decide +kernel)
      (by decide +kernel) hRun ht.1.ge (by rw [ht.1]) hr)
    (fun _ hm => List.mem_map_of_mem hm)
  have hv : At v 9093 ((1657,.bits 32 diff)::(7282,b32 0)::C) :=
    hV.mono ⟨hV.2.2.2.2.1,hV.2.2.2.2.2.1,hRegs⟩
  obtain ⟨w,hBra,hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_9093 (!active) hv hRegs.1 (by simp)
  let role := RowDrainRole.correction
  have hPath :=
    (role.drainLocals (by decide) (by decide) ht.1 (by decide +kernel) hRun).trans
      (role.drainLocals (by decide) (by decide) hv.1 (by simp) hBra)
  by_cases hActive : active = true
  · have hW' : At w 9094 ((1657,b32 (finish-begin))::F) := by
      simp only [hActive,Bool.not_true,Bool.false_eq_true,ite_false] at hW
      have hDiff : diff = BitVec.ofNat 64 (finish-begin) := by
        dsimp [diff]
        rw [BitVec.ofNat_sub_ofNat_of_le _ _ (show begin < 2^64 by omega) (hMono hActive),
          truncBits_ofNat (show finish-begin < 2^32 by omega) (by decide)]
      exact hW.mono ⟨by simpa only [hDiff,b32] using hW.2.2.2.2.1,hW.2.2.2.2.2.2.2⟩
    obtain ⟨u,hu,hU⟩ := (correctionDrainTileCount false l g hLength).apply
      (hW'.mono ⟨hW'.2.2.2.2.1,trivial⟩)
    have hSaved : Holds u.regs F := holdsSchedulerFrame hW'.2.2.2.2.2
      (fun r hr => schedulerLocalFrame (lo := 9094) (len := 10)
        (by
          change ((kernel.code.drop 9094).take 10).all
            (fun i => [7153,1616,7506,1618].all (fun r => !(writesRegs i.op).contains r)) = true
          decide +kernel)
        (by decide +kernel) hu hW'.1.ge (by rw [hW'.1]) hr)
      (fun _ hm => List.mem_map_of_mem hm)
    have hCount : (finish-begin+255)/256 = groupLaneTiles p 0 lane :=
      (ite_eq_left hActive).symm.trans hTiles
    exact ⟨u,hPath.trans (role.drainLocals (by decide) (by decide) hW'.1 (by decide +kernel) hu),
      hU.mono ⟨by
        change u.regs 7282 = some (b32 (groupLaneTiles p 0 lane))
        rw [← hCount]
        exact hU.2.2.2.2.1,hSaved⟩⟩
  · have hFalse : active = false := Bool.eq_false_of_not_eq_true hActive
    simp only [hFalse,Bool.not_false,ite_true] at hW
    have hCount : 0 = groupLaneTiles p 0 lane := (ite_eq_right hActive).symm.trans hTiles
    exact ⟨w,hPath,hW.mono ⟨by
      change w.regs 7282 = some (b32 (groupLaneTiles p 0 lane))
      rw [← hCount]
      exact hW.2.2.2.2.2.1,
      hW.2.2.2.2.2.2.2⟩⟩

private theorem firstTerminalHeads {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} {F : List (Nat × Value)}
    (ht : At t 9104 F) (hFresh : ∀ pair ∈ F, pair.1 ≠ 7143) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 9105 ((7143,b32 p.heads)::F) := by
  obtain ⟨hBits,hParam⟩ := hp.values (17,p.heads) (by simp [Params.scalarWords])
  have hCode : kernel.code[9104]? = some ⟨none,.mem
      {kind := .load, space := some .param, sem := .weak, elem := .int .b 32,
        addr := ⟨.param (param 17) false,0⟩, dsts := [some 7143]}⟩ := by
    rw [headsParameterName]
    exact Flow.code_9104
  have hr := Loader.scalarLoad (g := g) ht hParam hBits hCode
  exact ⟨_,RowDrainRole.correction.drainLocals (by decide) (by decide) ht.1 (by simp) hr,
    ht.set hFresh⟩

/-- The first terminal window's counts and launch operands are ready for its prefix scan. -/
def terminalFirstCountFrame (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  (7143,b32 p.heads)::(7282,b32 (groupLaneTiles p 0 (laneOf l g)))::
    RowDrainRole.correction.roots p l g

theorem terminalFirstCountOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g n votes : Nat} (hg : g < l.threads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 9091
      (fun lane =>
        (7082,b32 (drainCuQ p (shflSource .down lane 1 31).1))::
          terminalFirstFrame p l (warpLane l g lane)) n votes ends) :
    Nonempty (SchedulerWarpReached l X g 9105
      (fun lane => terminalFirstCountFrame p l (warpLane l g lane)) n votes ends) := by
  apply cur.advanceLocal
  intro lane hl
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
  obtain ⟨v,hPath,hV⟩ := firstTerminalCounts hp (by rw [hLane]; exact cur.checkpoint lane hl)
  obtain ⟨u,hHead,hU⟩ := firstTerminalHeads hp hV (fun pair hp => by
    simp only [RowDrainRole.roots,RowDrainRole.batchReg,RowDrainRole.frame,RowDrainRole.laneReg,
      RowDrainRole.ctaReg,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide)
  exact ⟨u,hPath.trans hHead,hU⟩

end PTX.Kernels.TmlFa4Fwd.Correction
