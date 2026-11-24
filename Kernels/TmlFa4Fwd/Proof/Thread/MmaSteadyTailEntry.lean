-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyBackedge
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaTailValueProgress
import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainTiles

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Loader Prologue Epilogue

noncomputable section

def steadyTailValueFrame (l : Launch) (visit : Nat) : List (Nat × Value) :=
  [(2609,b32 (readyAddr l (2*visit+1))),
    (1194,b32 (l.sharedBase+8*(readyStage (2*visit+1)).val))] ++ steadyFrame l visit 1

private theorem steadyTailAddress {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g visit : Nat} {t : TState}
    (ht : At t 2542 (steadyFrame l visit 1)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 2545 (steadyTailValueFrame l visit) := by
  have hAddr (s : Fin 3) : Seg kernel [] l g 3 2542
      [(7207,b32 s.val),(2535,b32 l.sharedBase)] 2545
      [(2609,b32 (l.sharedBase+(8*s.val+32))),(1194,b32 (l.sharedBase+8*s.val))] := by
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
  obtain ⟨v,hv,hV⟩ := (hAddr (readyStage (2*visit+1))).apply
    (ht.mono ⟨holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,trivial⟩)
  obtain ⟨hPath,hKeep⟩ := activeDrainLocalKeep ht (by decide) (by decide) (by
    change ((kernel.code.drop 2542).take 3).all
      (fun ins => [7207,7208,7205,7206,7204,2535,2610,2614,2615,2618,1190].all
        fun r => !(writesRegs ins.op).contains r) = true
    decide +kernel) (by decide +kernel) hv
  exact ⟨v,hPath,hV.mono ⟨hV.2.2.2.2.1,hV.2.2.2.2.2.1,hKeep⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
