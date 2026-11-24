-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Correction.Base
import Kernels.TmlFa4Fwd.Gen.StepCorrection
import Kernels.TmlFa4Fwd.Flow.Code.Part124
import Kernels.TmlFa4Fwd.Flow.Code.Part131
import Lemmas.Flow.AdvanceU
import Lemmas.Flow.ArriveU
import Lemmas.Flow.IssueNext

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow PTX.Proof
open Epilogue (addi scmpi)

set_option maxRecDepth 100000

/-- Only control facts survive at the two endpoints. The straight-line work before either
endpoint computes addresses and compares the round counter. -/
private noncomputable def roundLive (pc : Nat) : List Nat :=
  if pc = 8006 ∨ pc = 8464 then (Flow.live pc).filter controlReg else Flow.live pc

private theorem lift_seg {K A L g a F b G} (h : ∃ n, Seg K A L g n a F b G) :
    SegU K A L g a F b G := by
  obtain ⟨_,h⟩ := h
  exact SegU.of_seg h

variable {p L m g} (hp : Pre p L m)
include hp

theorem stepAt_nb_enterU (v : V) : (code p L g).StepAtU ⟨.nb 1,v,0⟩ := by
  let dn := erase (enterRounds p L g ⟨.nb 1,v.scheduler,0⟩)
  have hk : dn.k = 0 := by
    dsimp only [dn, enterRounds, Correction.D.ite]
    split <;> rfl
  refine Code.advanceU (dn := dn) Flow.code_7988 rfl (fun hf => fires_barSyncN_next hf)
    (fun _ => rfl) rfl rfl (congrArg Fin.val hk) rfl (.inl hk) (lift_seg ?_)
  have hparams := params hp
  dsimp only [dn, code, facts, enterRounds, Correction.D.ite, erase]
  by_cases h : scmpi .lt .s (blocks p L g v.scheduler) 2 = true
  · simp only [h, ↓reduceIte]
    change ∃ n, Seg _ _ _ _ n _ _ 8464 (factsFrom (roundLive 8464) _)
    seg_sym using corr_seg
  · simp only [h]
    change ∃ n, Seg _ _ _ _ n _ _ 8006 (factsFrom (roundLive 8006) _)
    seg_sym using corr_seg

theorem stepAt_round_endU (v : V) : (code p L g).StepAtU ⟨.rarr 1 1,v,0⟩ := by
  let dn := erase (roundEnd ⟨.rarr 1 1,v.scheduler,0⟩)
  have hk : dn.k = 0 := by
    dsimp only [dn, roundEnd, Correction.D.ite]
    split <;> rfl
  refine Code.arriveU (dn := dn) Flow.code_8443 ?_ (fun _ => rfl) rfl rfl
    (congrArg Fin.val hk) rfl (.inl hk) (lift_seg ?_)
  · change 9256 ∉ (factsFrom (liveAt (.rarr 1 1)) _).map Prod.fst
    have keys {rs : List Nat} {val : Nat → Value} : (factsFrom rs val).map Prod.fst = rs := by
      simp only [factsFrom, List.map_map, Function.comp_def]
      exact List.map_id _
    rw [keys]
    decide +kernel
  · have hparams := params hp
    dsimp only [dn, code, facts, roundEnd, Correction.D.ite, erase]
    by_cases h : scmpi .ne .b (addi v.trip 1) (-1) = true
    · simp only [h, ↓reduceIte, V.scheduler]
      change ∃ n, Seg _ _ _ _ n _ _ 8006 (factsFrom (roundLive 8006) _)
      seg_sym using corr_seg
    · simp only [h, V.scheduler]
      change ∃ n, Seg _ _ _ _ n _ _ 8464 (factsFrom (roundLive 8464) _)
      seg_sym using corr_seg

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
