-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.EldWin
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StepKinds
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part018

@[expose] public section

/-! # The strict step of the row-sum read (pc 1157)

The peer's row-sum word `v` is the event's; the window after it (`eldWinF`, `eldWinT`) runs under
the conditions of the final sum and, inside the heads, of the logarithm. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m : Mem0}

/-- The condition of the window after the row-sum read of the word `v`. -/
def eldCond (b : Blk) (v : Value) : Prop :=
  Gen.e3_cond (f_ex1 (lookupD (f_car (scX L) b.m b.l b.mx b.sk)) v) ∧
    (scmp .ge .s (Control.r5W L g) (pw 64) = false →
      Gen.e4_cond (lookupD (f_ew (lookupD (f_car (scX L) b.m b.l b.mx b.sk)) v)))

/-- **The strict step at pc 1157**. -/
theorem sk_1157 (hp : Pre P L m) (d : D) (hs : d.c.site = .eld) (hok : d.ok = true) (e : Event)
    (hcd : ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ eldCond (L := L) (g := g)
      d.b v) : (code P L g w).StepFor d e := by
  refine skW_ld1 (pc := 1157) (pc' := (Control.afterEld L g d.c).site.pc) (r := 1728)
    (mk := fun v => { d.b with pe := v }) (Cd := eldCond (L := L) (g := g) d.b) hcd
    (by rw [hs]; rfl) rfl (c' := Control.afterEld L g d.c) (by rw [hs]; decide)
    (by rw [hs]; exact Flow.code_1157) rfl rfl rfl rfl (by rw [hs]; decide) hok
    (fun x bs => by simp [Control.succ, hs, Control.dataRd])
    (by unfold Control.afterEld; split <;> simp [succOk, hs])
    (fun x bs v hv => by simp [record, hs, loadVal_ok hv])
    (fun h => by unfold Control.afterEld; split <;> exact h)
    (fun h => by unfold Control.afterEld; split <;> simp [Control.elems, h])
    (facts_fresh (by rw [hs]) (by decide +kernel) (fun q hq h => by
      rw [hs] at hq
      exact hoff_of (F := wF (scX L) .eld d.b) (ds := [1728]) (by kernel_rfl) q hq
        (by simp [h]))) ?_
  intro v c
  have e1 : wF (scX L) d.c.site d.b =
      f_exit (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) := by
    rw [hs]; rfl
  rw [e1]
  cases hb : scmp .ge .s (Control.r5W L g) (pw 64)
  · have h := eldWinF (w := w) hp d.c hs _ v hb c.1 (c.2 hb)
    simp only [Control.afterEld, hb, Bool.false_eq_true, ↓reduceIte]
    exact h
  · have h := eldWinT (w := w) hp d.c hs _ v hb c.1
    simp only [Control.afterEld, hb, ↓reduceIte]
    exact h

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
