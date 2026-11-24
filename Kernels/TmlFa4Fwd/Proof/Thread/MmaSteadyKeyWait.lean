-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyFirstPv
import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainTiles
import Kernels.TmlFa4Fwd.Flow.Code.Part037

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Loader Prologue Epilogue

noncomputable section

def steadyKeyRing (visit : Nat) : List (Nat × Value) :=
  [(1192,b32 (readyStage (2*visit+2)).val),(2572,b32 (readyWord (2*visit+2)))]

def steadyKeyFrame (l : Launch) (visit remaining : Nat) : List (Nat × Value) :=
  [(2571,b32 (readyAddr l (2*visit+2))),
    (1193,b32 (l.sharedBase+8*(readyStage (2*visit+2)).val))] ++
    steadyKeyRing visit ++ steadyValueFrame l visit remaining

private theorem steadyKeyAddress {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g visit remaining : Nat} {t : TState}
    (ht : At t 2344 (steadyValueFrame l visit remaining)) :
    ∃ u, run kernel [] l g 8 t = some u ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 2352 (steadyKeyFrame l visit remaining) := by
  let use := 2*visit+1
  have hAdvance (s : Fin 3) (phase : Bool) : Seg kernel [] l g 5 2344
      [(7207,b32 s.val),(7208,loaderPhaseWord phase)] 2349
      [(1192,b32 ((s.val+1)%3)),(2572,loaderPhaseWord (loaderNextPhase s phase))] := by
    fin_cases s <;> cases phase <;> intro u hu <;>
      dsimp only [loaderPhaseWord,loaderNextPhase] at hu ⊢ <;> seg_fp hu using decide
  have hAdvance' := hAdvance (readyStage use) (readyParity use)
  rw [← readyStage_succ, ← readyParity_succ, loaderPhaseWord_ready, loaderPhaseWord_ready]
    at hAdvance'
  obtain ⟨u,hu,hU⟩ := hAdvance'.apply
    (ht.mono ⟨holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,trivial⟩)
  obtain ⟨hFirst,hKeep⟩ := activeDrainLocalKeep ht (by decide) (by decide) (by
    change ((kernel.code.drop 2344).take 5).all
      (fun ins => [2568,1191,7207,7208,7205,7206,7204,2535,2610,2614,2615,2618,1190].all
        fun r => !(writesRegs ins.op).contains r) = true
    decide +kernel) (by decide +kernel) hu
  have hFrame : At u 2349 (steadyKeyRing visit ++ steadyValueFrame l visit remaining) :=
    hU.mono ((holds_append ..).mpr ⟨hU.2.2.2.2,hKeep⟩)
  have hAddr (s : Fin 3) : Seg kernel [] l g 3 2349
      [(1192,b32 s.val),(2535,b32 l.sharedBase)] 2352
      [(2571,b32 (l.sharedBase+(8*s.val+32))),(1193,b32 (l.sharedBase+8*s.val))] := by
    have hMax : l.sharedBase+48 < 2^32 := by have := hp.shared.2.1; omega
    have b0 : l.sharedBase < 2^32 := by omega
    have b8 : l.sharedBase+8 < 2^32 := by omega
    have b16 : l.sharedBase+16 < 2^32 := by omega
    have b32' : l.sharedBase+32 < 2^32 := by omega
    have b40 : l.sharedBase+40 < 2^32 := by omega
    fin_cases s <;> intro v hv <;>
      seg_fp hv using norm_bits [Nat.mod_eq_of_lt b0,Nat.mod_eq_of_lt b8,
        Nat.mod_eq_of_lt b16,Nat.mod_eq_of_lt b32',Nat.mod_eq_of_lt b40,
        Nat.mod_eq_of_lt hMax,Nat.add_assoc]
  obtain ⟨v,hv,hV⟩ := (hAddr (readyStage (2*visit+2))).apply
    (hFrame.mono ⟨holds_lookup hFrame.2.2.2.2 rfl,holds_lookup hFrame.2.2.2.2 rfl,trivial⟩)
  obtain ⟨hSecond,hKeep'⟩ := activeDrainLocalKeep hFrame (by decide) (by decide) (by
    change ((kernel.code.drop 2349).take 3).all
      (fun ins => [1192,2572,2568,1191,7207,7208,7205,7206,7204,2535,2610,2614,2615,2618,1190].all
        fun r => !(writesRegs ins.op).contains r) = true
    decide +kernel) (by decide +kernel) hv
  exact ⟨v,run_comp hu hv,hFirst.trans hSecond,hV.mono ⟨hV.2.2.2.2.1,hV.2.2.2.2.2.1,hKeep'⟩⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

/-- The first PV packet's retained operands reach the following K wait. -/
theorem steadyKeyWaitReachedFramedWithPosition {g visit remaining shuffles votes : Nat}
    {ends : Nat → Option TState} {extra : List (Nat × Value)}
    (cur : SchedulerWarpReached l X g 2344
      (fun _ => steadyValueFrame l visit remaining ++ extra) shuffles votes ends)
    (hExtra : ((kernel.code.drop 2344).take 8).all
      (fun ins => (extra.map Prod.fst).all fun r => !(writesRegs ins.op).contains r) = true) :
    ∃ next : SchedulerWarpReached l X g 2352
      (fun _ => steadyKeyFrame l visit remaining ++ extra) shuffles votes ends,
      next.pos = cur.pos := by
  apply cur.advanceLocalWithPosition
  intro lane hl
  have ht := cur.checkpoint lane hl
  have hF := (holds_append ..).mp ht.2.2.2.2
  obtain ⟨u,hu,path,hU⟩ := steadyKeyAddress hp (g := warpLane l g lane) (ht.mono hF.1)
  obtain ⟨_,hKeep⟩ := activeDrainLocalKeep (ht.mono hF.2) (by decide) (by decide)
    hExtra (by decide +kernel) hu
  exact ⟨u,path,hU.mono ((holds_append ..).mpr ⟨hU.2.2.2.2,hKeep⟩)⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
