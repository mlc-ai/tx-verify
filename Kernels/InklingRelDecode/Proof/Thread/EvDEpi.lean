-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvDEpiMeans

@[expose] public section

/-!
# Event shapes of the epilogue: the statement for every site

`Epi.Shape L g d e` is the shape of event `e` at the abstract state `d`, one case per site of the
machine, in terms of the state's own fields (`Prm`, `D.word`, `D.o`) and the thread's CTA
(`g / L.block`). `Epi.shape` proves that every continuing event that fires from `d` has it. The
per-site theorems are in `EvDEpiSync` (poll, broadcast, load, barriers, register request, table
write, release, return) and `EvDEpiStore` (the 65 output stores); `EvDEpiMeans` relates the
store addresses to the output arrays of `Spec` (`shape_stO_loc`, `shape_stLse_loc`).

The return is the one site whose events never continue: the instruction exits the thread
(`shape_exit`), so `Shape` is empty there (`False`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

/-- The shape of the events the epilogue fires from the abstract state `d`. -/
def Shape (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .wait => ∃ ok, e = ⟨evPc d.site, .wait ⟨.shared, g / L.block, d.pr.mb⟩ 0 ok true .cta⟩
  | .shfl => ∃ recv ok, e = ⟨evPc d.site, .shfl .idx (b32 d.pr.w) 0 31 recv ok⟩
  | .ld => ∃ vals, vals.length = 64 ∧
      e = ⟨evPc d.site, .tc (.ld d.pr.taddr vals (.s16x32bx2 64))⟩
  | .waitLd => e = ⟨evPc d.site, .tc .waitLd⟩
  | .stLse => ∃ v', storeValue 32 d.pr.lseWord = .ok v' ∧
      e = ⟨evPc d.site, .wr (wordAcc ⟨.global, 0, d.pr.lAddr⟩) v'.toBytes⟩
  | .stO k => ∃ v', storeValue 32 (d.word k.val) = .ok v' ∧
      e = ⟨evPc d.site, .wr (wordAcc ⟨.global, 0, (d.pr.oAddr + 4 * k.val) % M64⟩) v'.toBytes⟩
  | .bar1 => e = ⟨evPc d.site, .bar 1 none .sync⟩
  | .setMaxInc => ∃ inst, e = ⟨evPc d.site, .setMaxReg true 256 inst⟩
  | .stTab => ∃ v', storeValue 32 (b32 50529027) = .ok v' ∧
      e = ⟨evPc d.site, .wr (wordAcc ⟨.shared, g / L.block, (L.sharedBase + 213336) % 2 ^ 32⟩)
        v'.toBytes⟩
  | .bar2 => e = ⟨evPc d.site, .bar 1 none .sync⟩
  | .bar3 => e = ⟨evPc d.site, .bar 0 none .sync⟩
  | .dealloc => e = ⟨evPc d.site, .tc (.resource .one none (.dealloc d.pr.tm 512))⟩
  | .exit => False

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

/-- **Every continuing event of the epilogue has the shape of its state.** -/
theorem shape (hb : L.block % 32 = 0) (hF : Fired L g d e (some u)) : Shape L g d e := by
  unfold Shape
  split
  · rename_i hs; exact shape_wait hF hs
  · rename_i hs; exact shape_shfl hF hs
  · rename_i hs; exact shape_ld hF hs
  · rename_i hs; exact shape_waitLd hb hF hs
  · rename_i hs; exact shape_stLse hF hs
  · rename_i k hs; exact shape_stO hF hs
  · rename_i hs; exact shape_bar1 hF hs
  · rename_i hs; exact shape_setMaxInc hF hs
  · rename_i hs; exact shape_stTab hF hs
  · rename_i hs; exact shape_bar2 hF hs
  · rename_i hs; exact shape_bar3 hF hs
  · rename_i hs; exact shape_dealloc hF hs
  · rename_i hs
    exact absurd (shape_exit hF hs).2 (by simp)

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
