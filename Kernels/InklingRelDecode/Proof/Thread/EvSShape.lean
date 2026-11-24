-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvSSync
public import Kernels.InklingRelDecode.Proof.Thread.EvSTile
public import Kernels.InklingRelDecode.Proof.Thread.EvSBias

@[expose] public section

/-!
# Event shapes of the softmax region: the statement for every site that has one

`Sm.Shape L g d e` is the shape of event `e` at the abstract state `d`, one case per site, in terms
of the state's own fields (`D.e`, `D.i`, `D.n`, `D.pwV`, `D.stg`) and the thread (`g % L.block`,
`g / L.block`). `Sm.shape` proves that every continuing event that fires from `d` has it. The
per-site theorems are in `EvSSync` (register request, barriers, polls, waits, shuffles), `EvSTile`
(the S tile load, the P tile store and the `p_ready` arrival) and `EvSBias` (the bias loads); the
bias loads in the specification's terms are in `EvSBiasSpec`.

**Sites without a shape yet.** The sites after `waitLd` that have no step lemma (the score,
maximum, exponential and sum code's shuffles and barriers, the row sum's shared store and reload,
the `o_done` poll, the O tile's load and store) have the shape `True` here. Adding one is a new
case of `Shape` and a new case of `shape`, with its theorem in the file of its kind; nothing else
changes.

The hypotheses of `shape` are the launch's: `L.block = 256` (the named barrier's count 128 and the
shuffles' whole warps) and `SharedOk L` (the barriers' objects do not wrap in the 32-bit shared
address space, `Pre.sharedAlignment`, `Pre.sharedRange`; `EvSBase.sharedOk_of_pre`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

/-- The shape of the events the softmax region fires from the abstract state `d`. -/
def Shape (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .setMaxReg => ∃ inst, e = ⟨evPc d.site, .setMaxReg true 256 inst⟩
  | .bar0 => e = ⟨evPc d.site, .bar 1 none .sync⟩
  | .pre j => ∃ bs : List (Option Byte), bs.length = 2 ∧
      e = ⟨evPc d.site, .rd (globalAcc (biasAddr d.e (g % L.block) d.n j.val) 2) bs⟩
  | .nxt j => ∃ bs : List (Option Byte), bs.length = 2 ∧
      e = ⟨evPc d.site, .rd (globalAcc
        (biasAddr d.e (g % L.block) (d.n + d.e.splits) j.val) 2) bs⟩
  | .waitS => ∃ ok, e = ⟨evPc d.site, .wait ((sReadyOf d.i).loc L (g / L.block)) (d.i / 2 % 2) ok
      true .cta⟩
  | .shfl4 => ∃ recv ok, e = ⟨evPc d.site, .shfl .idx (b32 (g % L.block / 32)) 0 31 recv ok⟩
  | .ldS => ∃ vals, vals.length = 64 ∧
      e = ⟨evPc d.site, .tc (.ld (tileAddr L g d) vals (.s16x32bx2 64))⟩
  | .waitLd => e = ⟨evPc d.site, .tc .waitLd⟩
  | .shfl12 => ∃ recv ok, e = ⟨evPc d.site, .shfl .bfly d.stg.m2 1 31 recv ok⟩
  | .waitStO => e = ⟨evPc d.site, .tc .waitSt⟩
  | .bar20 => e = ⟨evPc d.site, .bar 0 (some 128) .sync⟩
  | .tmemSt => ∃ vals, vals.length = 32 ∧ (∀ w, w < 32 → vals[w]? = some (d.pwV w)) ∧
      (∀ v ∈ vals, v.bytes = 4) ∧
      e = ⟨evPc d.site, .tc (.st (tileAddr L g d) vals (.s16x32bx2 32))⟩
  | .tmemWait => e = ⟨evPc d.site, .tc .waitSt⟩
  | .bar21 => e = ⟨evPc d.site, .bar 0 (some 128) .sync⟩
  | .arrive => g % L.block = 0 ∧
      e = ⟨evPc d.site, .arrive ((pReadyOf d.i).loc L (g / L.block)) 0 1 true .cta⟩
  | _ => True

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

/-- **Every continuing event of the softmax region has the shape of its state** (for the sites
that have one; the others have the shape `True`). -/
theorem shape (hL : L.block = 256) (hS : SharedOk L) (hF : Fired L g d e (some u)) :
    Shape L g d e := by
  have hb : L.block % 32 = 0 := by rw [hL]
  have hb2 : L.block ≠ 128 := by rw [hL]; decide
  unfold Shape
  split
  · rename_i hs; exact shape_setMaxReg hF hs
  · rename_i hs; exact shape_bar0 hF hs
  · rename_i j hs; exact shape_pre hF hs
  · rename_i j hs; exact shape_nxt hF hs
  · rename_i hs; exact shape_waitS_loc hS hF hs
  · rename_i hs; exact shape_shfl4 hF hs
  · rename_i hs; exact shape_ldS hF hs
  · rename_i hs; exact shape_waitLd hb hF hs
  · rename_i hs; exact shape_shfl12 hF hs
  · rename_i hs; exact shape_waitStO hF hs
  · rename_i hs; exact shape_bar20 hb2 hF hs
  · rename_i hs; exact shape_tmemSt hF hs
  · rename_i hs; exact shape_tmemWait hF hs
  · rename_i hs; exact shape_bar21 hb2 hF hs
  · rename_i hs; exact shape_arrive hS hF hs
  · trivial

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
