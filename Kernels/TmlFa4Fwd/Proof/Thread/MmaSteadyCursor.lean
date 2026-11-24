-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaTailValueProgress
public import Kernels.TmlFa4Fwd.Proof.MmaReadySegments
public import Kernels.TmlFa4Fwd.Proof.MmaWideCounter
import all Kernels.TmlFa4Fwd.Proof.MmaLoopCounter
import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainTiles
import Kernels.TmlFa4Fwd.Flow.Code.Part035

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open Thread.Allocation (signedWord)

noncomputable section

/-- Shared operands live throughout the recurring QK/PV body. -/
def steadyPorts (l : Launch) : List (Nat × Value) :=
  [(2535,b32 l.sharedBase),(2610,b32 (l.sharedBase+96)),(2614,b32 (l.sharedBase+112)),
    (2615,b32 (l.sharedBase+104)),(2618,b32 (l.sharedBase+120)),(1190,b32 (l.sharedBase+88))]

/-- The recorded warp at a recurring visit carries its remaining trip count,
the ring slot and parity, and the probability parity and accumulation flag. -/
def steadyFrame (l : Launch) (visit remaining : Nat) : List (Nat × Value) :=
  [(7207,b32 (readyStage (2*visit+1)).val),(7208,b32 (readyWord (2*visit+1))),
    (7205,b32 (visit%2)),(7206,b32 (if 0 < visit then 1 else 0)),
    (7204,wideCounterWord remaining)] ++ steadyPorts l

private theorem steadyOpeningOffsets {l : Launch} {g n : Nat}
    (hWidth : l.sharedBase+120 < 2^32) :
    Seg kernel [] l g 4 2275 [(1189,b32 n),(2535,b32 l.sharedBase)] 2279
      [(1189,b32 n),(2535,b32 l.sharedBase),(2610,b32 (l.sharedBase+96)),
        (2614,b32 (l.sharedBase+112)),(2615,b32 (l.sharedBase+104)),
        (2618,b32 (l.sharedBase+120))] := by
  intro t ht
  have h96 : l.sharedBase+96 < 2^32 := by omega
  have h104 : l.sharedBase+104 < 2^32 := by omega
  have h112 : l.sharedBase+112 < 2^32 := by omega
  seg_fp ht using norm_bits [Nat.mod_eq_of_lt h96,Nat.mod_eq_of_lt h104,
    Nat.mod_eq_of_lt h112,Nat.mod_eq_of_lt hWidth]

private theorem openingSteadyBranch {l : Launch} {g n : Nat} {t : TState}
    (hn : 2 ≤ n) (hSigned : n < 2^31)
    (ht : At t 2279 [(1189,b32 n),(2535,b32 l.sharedBase),(2610,b32 (l.sharedBase+96)),
      (2614,b32 (l.sharedBase+112)),(2615,b32 (l.sharedBase+104)),(2618,b32 (l.sharedBase+120))]) :
    ∃ u, run kernel [] l g 6 t = some u ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 2285 ([(1189,b32 n),(2535,b32 l.sharedBase),(2610,b32 (l.sharedBase+96)),
        (2614,b32 (l.sharedBase+112)),(2615,b32 (l.sharedBase+104)),
        (2618,b32 (l.sharedBase+120))]) := by
  have hTwo : toSigned 32 (truncBits 32 (BitVec.ofInt 64 2)) = 2 := rfl
  have hLower : ¬ (n : Int) < 2 := by omega
  have hPred : Seg kernel [] l g 5 2279 [(1189,b32 n)] 2284 [(388,.pred false)] := by
    intro s hs
    seg_fp hs using
      simp only [truncBits_ofNat (show n < 2^32 by omega) (by decide),signedWord hSigned,
        compare,Option.getD_some,hTwo,hLower,decide_false]
  obtain ⟨v,hv,hV⟩ := hPred.apply (ht.mono ⟨ht.2.2.2.2.1,trivial⟩)
  obtain ⟨u,hu,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2284 false hV hV.2.2.2.2.1 (by simp)
  obtain ⟨hPath,hKeep⟩ := activeDrainLocalKeep ht (by decide) (by decide) (by
    change ((kernel.code.drop 2279).take 6).all
      (fun ins => [1189,2535,2610,2614,2615,2618].all
        fun r => !(writesRegs ins.op).contains r) = true
    decide +kernel) (by decide +kernel) (run_comp hv hu)
  exact ⟨u,run_comp hv hu,hPath,hU.mono hKeep⟩

private theorem steadySeed {l : Launch} {g n : Nat} {t : TState}
    (hn : 2 ≤ n) (hSigned : n < 2^31) (hWidth : l.sharedBase+120 < 2^32)
    (ht : At t 2285 [(1189,b32 n),(2535,b32 l.sharedBase),(2610,b32 (l.sharedBase+96)),
      (2614,b32 (l.sharedBase+112)),(2615,b32 (l.sharedBase+104)),(2618,b32 (l.sharedBase+120))]) :
    ∃ u, run kernel [] l g 6 t = some u ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 2291 (steadyFrame l 0 n) := by
  have h88 : l.sharedBase+88 < 2^32 := by omega
  have hFrame : Seg kernel [] l g 6 2285 [(1189,b32 n),(2535,b32 l.sharedBase)] 2291
      [(7207,b32 1),(7208,b32 0),(7205,b32 0),(7206,b32 0),
        (7204,counterWord n),(1190,b32 (l.sharedBase+88))] := by
    intro s hs
    simp only [counterWord]
    seg_fp hs using
      first
      | rfl
      | simp only [b32,truncBits_ofNat (show n < 2^32 by omega) (by decide),
          negativeBits (show 0 < n by omega) (show n < 2^32 by omega),
          truncBits_ofNat (show l.sharedBase < 2^32 by omega) (by decide),
          show truncBits 32 (BitVec.ofInt 64 88) = BitVec.ofNat 64 88 by rfl,
          ← BitVec.ofNat_add,truncBits_ofNat h88 (by decide)]
  obtain ⟨u,hu,hU⟩ := hFrame.apply (ht.mono ⟨ht.2.2.2.2.1,ht.2.2.2.2.2.1,trivial⟩)
  have hKeepAt := ht.mono ht.2.2.2.2.2
  obtain ⟨hPath,hKeep⟩ := activeDrainLocalKeep hKeepAt (by decide) (by decide) (by
    change ((kernel.code.drop 2285).take 6).all
      (fun ins => [2535,2610,2614,2615,2618].all fun r => !(writesRegs ins.op).contains r) = true
    decide +kernel) (by decide +kernel) hu
  have hc : wideCounterWord n = counterWord n :=
    ite_eq_right (show n ≠ 2^32+1 by omega)
  refine ⟨u,hu,hPath,hU.mono ⟨hU.2.2.2.2.1,hU.2.2.2.2.2.1,hU.2.2.2.2.2.2.1,
    hU.2.2.2.2.2.2.2.1,?_,hKeep.1,hKeep.2.1,hKeep.2.2.1,hKeep.2.2.2.1,
    hKeep.2.2.2.2.1,hU.2.2.2.2.2.2.2.2.2.1,trivial⟩⟩
  rw [hc]
  exact hU.2.2.2.2.2.2.2.2.1

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g n shuffles votes : Nat} {ends : Nat → Option TState} {extra : List (Nat × Value)}
    (hn : 2 ≤ n) (hSigned : n < 2^31)
    (cur : SchedulerWarpReached l X g 2275
      (fun _ => [(1189,b32 n),(2535,b32 l.sharedBase)] ++ extra) shuffles votes ends)
    (hKeep : ∀ start count, (start,count) ∈ [(2275,4),(2279,6),(2285,6)] →
      ((kernel.code.drop start).take count).all
        (fun ins => (extra.map Prod.fst).all fun r => !(writesRegs ins.op).contains r) = true)
include hp hn hSigned cur hKeep

/-- The actual entry branch retains the caller's opening operands alongside its trip count. -/
theorem openingSteadyReachedFramedWithPosition :
    ∃ next : SchedulerWarpReached l X g 2291
      (fun _ => steadyFrame l 0 n ++ extra) shuffles votes ends, next.pos = cur.pos := by
  have hWidth : l.sharedBase+120 < 2^32 := by have := hp.shared.2.1; omega
  apply cur.advanceLocalWithPosition
  intro lane hl
  have ht := cur.checkpoint lane hl
  have hf := (holds_append ..).mp ht.2.2.2.2
  obtain ⟨v,hv,hV⟩ := (steadyOpeningOffsets hWidth).apply (ht.mono hf.1)
  obtain ⟨w,hw,_,hW⟩ := openingSteadyBranch (g := warpLane l g lane) hn hSigned hV
  obtain ⟨u,hu,_,hU⟩ := steadySeed (g := warpLane l g lane) hn hSigned hWidth hW
  obtain ⟨pathV,hCarryV⟩ := activeDrainLocalKeep (ht.mono hf.2) (by decide) (by decide)
    (hKeep 2275 4 (by simp)) (by decide +kernel) hv
  obtain ⟨pathW,hCarryW⟩ := activeDrainLocalKeep (hV.mono hCarryV) (by decide) (by decide)
    (hKeep 2279 6 (by simp)) (by decide +kernel) hw
  obtain ⟨pathU,hCarryU⟩ := activeDrainLocalKeep (hW.mono hCarryW) (by decide) (by decide)
    (hKeep 2285 6 (by simp)) (by decide +kernel) hu
  exact ⟨u,pathV.trans (pathW.trans pathU),hU.mono ((holds_append ..).mpr
    ⟨hU.2.2.2.2,hCarryU⟩)⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
