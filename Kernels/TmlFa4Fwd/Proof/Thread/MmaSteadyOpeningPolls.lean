-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyCursor
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaWarpPollProgress
import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainTiles
import Kernels.TmlFa4Fwd.Flow.Code.Part035

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.MBarrier (stateBefore)

noncomputable section

/-- The producer object's final phase can release a poll at the frontier. -/
def MmaProgressPhase (X : Execution) (loc : Loc) (parity : Nat) : Prop :=
  let log := X.objects loc
  ∃ s, stateBefore log log.length = some s ∧ s.phase%2 ≠ parity%2

def steadyValueFrame (l : Launch) (visit remaining : Nat) : List (Nat × Value) :=
  (2568,b32 (readyAddr l (2*visit+1)))::(1191,b32 (l.sharedBase+8*(readyStage (2*visit+1)).val))::
    steadyFrame l visit remaining

private theorem steadyValueAddress {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g visit remaining : Nat} {t : TState}
    (ht : At t 2291 (steadyFrame l visit remaining)) :
    ∃ u, run kernel [] l g 3 t = some u ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 2294 (steadyValueFrame l visit remaining) := by
  let use := 2*visit+1
  let slot := readyStage use
  have hCore (s : Fin 3) : Seg kernel [] l g 3 2291
      [(7207,b32 s.val),(2535,b32 l.sharedBase)] 2294
      [(2568,b32 (l.sharedBase+(8*s.val+32))),(1191,b32 (l.sharedBase+8*s.val))] := by
    have hMax : l.sharedBase+48 < 2^32 := by have := hp.shared.2.1; omega
    have b0 : l.sharedBase < 2^32 := by omega
    have b8 : l.sharedBase+8 < 2^32 := by omega
    have b16 : l.sharedBase+16 < 2^32 := by omega
    have b32' : l.sharedBase+32 < 2^32 := by omega
    have b40 : l.sharedBase+40 < 2^32 := by omega
    fin_cases s <;> intro t ht <;>
      seg_fp ht using norm_bits [Nat.mod_eq_of_lt b0,Nat.mod_eq_of_lt b8,
        Nat.mod_eq_of_lt b16,Nat.mod_eq_of_lt b32',Nat.mod_eq_of_lt b40,
        Nat.mod_eq_of_lt hMax,Nat.add_assoc]
  obtain ⟨u,hu,hU⟩ := (hCore slot).apply
    (ht.mono ⟨holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,trivial⟩)
  obtain ⟨hPath,hF⟩ := activeDrainLocalKeep ht (by decide) (by decide) (by
    change ((kernel.code.drop 2291).take 3).all
      (fun ins => [7207,7208,7205,7206,7204,2535,2610,2614,2615,2618,1190].all
        fun r => !(writesRegs ins.op).contains r) = true
    decide +kernel) (by decide +kernel) hu
  exact ⟨u,hu,hPath,hU.mono ⟨hU.2.2.2.2.1,hU.2.2.2.2.2.1,hF⟩⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

/-- Entry to the recurring V poll retains any proved frame untouched by its address setup. -/
theorem steadyValueWaitReachedFramedWithPosition {g visit remaining shuffles votes : Nat}
    {ends : Nat → Option TState} {extra : List (Nat × Value)}
    (cur : SchedulerWarpReached l X g 2291
      (fun _ => steadyFrame l visit remaining ++ extra) shuffles votes ends)
    (hExtra : ((kernel.code.drop 2291).take 3).all
      (fun ins => (extra.map Prod.fst).all fun r => !(writesRegs ins.op).contains r) = true) :
    ∃ next : SchedulerWarpReached l X g 2294
      (fun _ => steadyValueFrame l visit remaining ++ extra) shuffles votes ends,
      next.pos = cur.pos := by
  apply cur.advanceLocalWithPosition
  intro lane hl
  have ht := cur.checkpoint lane hl
  have hF := (holds_append ..).mp ht.2.2.2.2
  obtain ⟨u,hu,path,hU⟩ := steadyValueAddress hp (g := warpLane l g lane) (ht.mono hF.1)
  obtain ⟨_,hKeep⟩ := activeDrainLocalKeep (ht.mono hF.2) (by decide) (by decide)
    hExtra (by decide +kernel) hu
  exact ⟨u,path,hU.mono ((holds_append ..).mpr ⟨hU.2.2.2.2,hKeep⟩)⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
