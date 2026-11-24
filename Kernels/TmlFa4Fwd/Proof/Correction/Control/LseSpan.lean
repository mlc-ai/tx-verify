-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine
public import Lemmas.Flow.Havoc
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Ballot
import Kernels.TmlFa4Fwd.Proof.Correction.Havoc
import Kernels.TmlFa4Fwd.Proof.Correction.Base
import Kernels.TmlFa4Fwd.Gen.StepCorrection
import Kernels.TmlFa4Fwd.Flow.Code.Part141
import Lemmas.Flow.BranchU
import Lemmas.Flow.SegCtl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow PTX.Proof
open Epilogue (scmp sub32 shl addi)

noncomputable section
set_option maxRecDepth 100000

def skipRow (p : Params) (L : Launch) (g : Nat) (v : V) (second : Bool) : Bool :=
  let lim := sub32 (sub32 v.sc.c1 v.sc.c0) (shl (rowOff p L g v.sc) 8)
  scmp .ge .s (rowW L g) (if second then addi lim (-128) else lim)

def lateD (p : Params) (L : Launch) (g : Nat) (v : V) : D :=
  erase (passStart p L g true ⟨.lse 1,v.scheduler,0⟩)

def secondD (p : Params) (L : Launch) (g : Nat) (v : V) : D :=
  if skipRow p L g v true then lateD p L g v else ⟨.lse 1,v,0⟩

def firstD (p : Params) (L : Launch) (g : Nat) (v : V) : D :=
  if skipRow p L g v false then secondD p L g v else ⟨.lse 0,v,0⟩

theorem first_compare {p L g} (v : V) : SegU kernel Assumptions.all L g 9057
    (facts p L g ⟨.fdone 1 1,v,0⟩) 9072
    ((741,.pred (skipRow p L g v false)) :: facts p L g ⟨.lse 0,v,0⟩) := by
  seg_ctl rules_frame, hooks_ok using sym_close

theorem second_compare {p L g} (v : V) : SegU kernel Assumptions.all L g 9074
    (facts p L g ⟨.lse 0,v,0⟩) 9081
    ((743,.pred (skipRow p L g v true)) :: facts p L g ⟨.lse 1,v,0⟩) := by
  seg_ctl rules_frame, hooks_ok using sym_close

theorem late_entry {p L m g} (hp : Pre p L m) (v : V) : SegU kernel Assumptions.all L g 9083
    (facts p L g ⟨.lse 1,v,0⟩) (lateD p L g v).site.pc (facts p L g (lateD p L g v)) := by
  suffices h : ∃ n, Seg kernel Assumptions.all L g n 9083 (facts p L g ⟨.lse 1,v,0⟩)
      (lateD p L g v).site.pc (facts p L g (lateD p L g v)) by
    obtain ⟨_,h⟩ := h
    exact SegU.of_seg h
  have hparams := params hp
  dsimp only [lateD, passStart, Correction.D.ite, erase, facts, live, liveAt]
  by_cases h : scmp .gt .s (Epilogue.laneW L g) (Epilogue.paramW p.batch) = true
  · simp only [h, ↓reduceIte]
    change ∃ n, Seg _ _ _ _ n _ _ 9090 (factsFrom (Flow.live 9090) _)
    seg_sym using corr_seg
  · simp only [h, ↓reduceIte]
    change ∃ n, Seg _ _ _ _ n _ _ 9089 (factsFrom (Flow.live 9089) _)
    seg_sym using corr_seg

theorem second_span {p L m g} (hp : Pre p L m) (v : V) : SegU kernel Assumptions.all L g 9074
    (facts p L g ⟨.lse 0,v,0⟩) (secondD p L g v).site.pc (facts p L g (secondD p L g v)) := by
  refine SegU.comp (second_compare v) (SegU.comp (SegU.branch _ Flow.code_9081 bra_rule
    (Epilogue.segFree (by decide))) ?_)
  unfold secondD
  cases skipRow p L g v true with
  | true => exact late_entry hp v
  | false => exact fun t ht => .inl ⟨t,.refl,ht⟩

theorem first_span {p L m g} (hp : Pre p L m) (v : V) : SegU kernel Assumptions.all L g 9057
    (facts p L g ⟨.fdone 1 1,v,0⟩) (firstD p L g v).site.pc (facts p L g (firstD p L g v)) := by
  refine SegU.comp (first_compare v) (SegU.comp (SegU.branch _ Flow.code_9072 bra_rule
    (Epilogue.segFree (by decide))) ?_)
  unfold firstD
  cases skipRow p L g v false with
  | true => exact second_span hp v
  | false => exact fun t ht => .inl ⟨t,.refl,ht⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
