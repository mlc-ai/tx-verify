-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Cross
public import Kernels.InklingRelDecode.Proof.Softmax.Data.LKeep
import Kernels.InklingRelDecode.Proof.Lib.AlphaAt
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The running sum across the update

The row sum is added at pc 2235 (register 1531 from the shuffle's two words) and the running sum
takes its fused update at pc 950 on the way from the round to the barrier of pc 999. The facts are
given by position (as for the maximum, `Data/Phase.lean`): the sum and the round's factor from the
shuffle on, the row sum after the addition, the new sum from pc 951 to pc 999. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Assumption Control Lib

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The registers of the table: the sum, the factor and the row sum's operands or the row sum. -/
def lUKeys (pc : Nat) : List Nat :=
  if pc = 2235 then [1915, 507, 1529, 1530]
  else if 951 ≤ pc ∧ pc ≤ 999 then [1915] else [1915, 507, 1531]

def lUPost (pc : Nat) : Bool := decide (951 ≤ pc ∧ pc ≤ 999)

def lUSpec (pc : Nat) : Bool := decide (pc = 2235 ∨ pc = 950)

/-- The values before the update: the sum, the factor, the row sum's operands and the row sum. -/
def lUV1 (l a s r p : Value) (x : Nat) : Value :=
  if x = 1915 then l else if x = 507 then a else if x = 1529 then s else if x = 1530 then r
  else p

/-- The values after the update. -/
def lUV2 (l a s r p : Value) (x : Nat) : Value :=
  if x = 1915 then lStep l a p else lUV1 l a s r p x

/-- The row sum's addition (pc 2235). -/
def lAddItem : XItem := .base (.add false 1531 1529 1530)

/-- The running sum's update (pc 950). -/
def lFmaItem : XItem :=
  .fn (fOp (fmaI .rn false) 1915 [.reg 1915, .reg 507, .reg 1531]) 1915
    (regsOf [.reg 1915, .reg 507, .reg 1531])
    (fF (floatE (fmaI .rn false)) [.reg 1915, .reg 507, .reg 1531])

theorem ladd_at : OAt kernel Assumptions.all L g 2235 [lAddItem] :=
  ⟨⟨by decide +kernel, Kernels.InklingRelDecode.Proof.segFree (by decide +kernel),
    fun s hs => forms_at (f := .add .f32) (by simp [idealForms]) (pc := 2235)
      (by decide +kernel) (by omega) (by omega) (by omega) s hs⟩, trivial⟩

theorem lfma_at : OAt kernel Assumptions.all L g 950 [lFmaItem] :=
  ⟨⟨by decide +kernel, Kernels.InklingRelDecode.Proof.segFree (by decide +kernel),
    fun s hs => XItem.fma_rule
      (forms_at (f := .fma .f32) (by simp [idealForms]) (pc := 950)
        (by decide +kernel) (by omega) (by omega) (by omega) s hs).1
      (forms_at (f := .fma .f32) (by simp [idealForms]) (pc := 950)
        (by decide +kernel) (by omega) (by omega) (by omega) s hs).2 (by decide)⟩, trivial⟩

theorem ladd_segd (V : Nat → Value) :
    SegD kernel Assumptions.all L g 1 2235 (factsFrom [1915, 507, 1529, 1530] V) 2236
      (factsFrom [1915, 507, 1531] (xFinal V [lAddItem])) (xCond V [lAddItem]) :=
  SegD.xouts (K := kernel) (A := Assumptions.all) (L := L) (g := g) (items := [lAddItem])
    (liveS := [1915, 507, 1529, 1530]) (liveT := [1915, 507, 1531]) (V := V)
    (ladd_at (L := L) (g := g)).code (by decide +kernel)
    (by simp [xReq, lAddItem, XItem.req, OItem.req]) (by decide +kernel)
    (ladd_at (L := L) (g := g)).rules (by decide +kernel)

theorem lfma_segd (V : Nat → Value) :
    SegD kernel Assumptions.all L g 1 950 (factsFrom [1915, 507, 1531] V) 951
      (factsFrom [1915] (xFinal V [lFmaItem])) (xCond V [lFmaItem]) :=
  SegD.xouts (K := kernel) (A := Assumptions.all) (L := L) (g := g) (items := [lFmaItem])
    (liveS := [1915, 507, 1531]) (liveT := [1915]) (V := V)
    (lfma_at (L := L) (g := g)).code (by decide +kernel)
    (by simp [xReq, lFmaItem, XItem.req]) (by decide +kernel)
    (lfma_at (L := L) (g := g)).rules (by decide +kernel)

theorem ladd_val (V : Nat → Value) (r : Nat) :
    xFinal V [lAddItem] r = if r = 1531 then psWord (V 1529) (V 1530) else V r := by
  simp [xFinal, lAddItem, XItem.upd, XItem.vals, OItem.vals, Function.update, psWord, b32]

theorem lfma_val (V : Nat → Value) (r : Nat) :
    xFinal V [lFmaItem] r = if r = 1915 then lStep (V 1915) (V 507) (V 1531) else V r := by
  have h := fF_map (E := floatE (fmaI .rn false)) (os := [.reg 1915, .reg 507, .reg 1531]) (W := V)
  simp only [regsOf, regOf, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.singleton_append, List.map_cons, List.map_nil, fOpnd] at h
  simp [xFinal, lFmaItem, XItem.upd, XItem.vals, Function.update, regsOf, regOf, h, lStep, b32]

theorem lu_spec {ivs : List (Nat × Nat)} (l a s r p : Value)
    (h950 : inIvs ivs 950 = true → inIvs ivs 951 = true)
    (h2235 : inIvs ivs 2235 = true → inIvs ivs 2236 = true ∧ p = psWord s r) :
    ∀ pc, lUSpec pc = true → inIvs ivs pc = true → ∀ t t1 : TState, t.pc = pc →
      TabAt lUKeys lUPost (lUV1 l a s r p) (lUV2 l a s r p) t →
      Tau kernel Assumptions.all L g t t1 →
      ((inIvs ivs t1.pc || evAtB kernel t1.pc) = true ∧
        TabAt lUKeys lUPost (lUV1 l a s r p) (lUV2 l a s r p) t1) ∨
        Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) t1 := by
  intro pc hsp hin t t1 hpc hT ht1
  obtain ⟨hsub, hacc, hH⟩ := hT
  have hfault : t.fault = none := by
    unfold Tau out at ht1
    cases hf : t.fault with
    | none => rfl
    | some f => rw [hf] at ht1; cases ht1
  simp only [lUSpec, decide_eq_true_eq] at hsp
  rcases hsp with rfl | rfl
  · have hF : Holds t.regs (factsFrom [1915, 507, 1529, 1530] (lUV1 l a s r p)) := by
      rw [hpc] at hH
      simpa [phi, lUKeys, lUPost] using hH
    rcases SegD.tau_one (ladd_segd (L := L) (g := g) (lUV1 l a s r p))
      ⟨hpc, hsub, hacc, hfault, hF⟩ ht1 with hu | hd
    · obtain ⟨hp2, hps⟩ := h2235 (hpc ▸ hin)
      have hp : t1.pc = 2236 := hu.1
      refine .inl ⟨by rw [hp]; simp [hp2], hu.2.1, hu.2.2.1, ?_⟩
      show Holds _ (phi lUKeys lUPost _ _ t1.pc)
      rw [hp]
      change Holds t1.regs (factsFrom [1915, 507, 1531] (lUV1 l a s r p))
      refine holds_of_pointwise fun x hx => ?_
      obtain ⟨-, -, -, -, hur⟩ := id hu
      have := holds_mem hur (mem_factsFrom (val := xFinal (lUV1 l a s r p) [lAddItem]) (by
        simpa using hx))
      rw [ladd_val] at this
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simpa [lUV1, hps] using this
    · exact .inr hd
  · have hF : Holds t.regs (factsFrom [1915, 507, 1531] (lUV1 l a s r p)) := by
      rw [hpc] at hH
      simpa [phi, lUKeys, lUPost] using hH
    rcases SegD.tau_one (lfma_segd (L := L) (g := g) (lUV1 l a s r p))
      ⟨hpc, hsub, hacc, hfault, hF⟩ ht1 with hu | hd
    · have hp : t1.pc = 951 := hu.1
      refine .inl ⟨by rw [hp]; simp [h950 (hpc ▸ hin)], hu.2.1, hu.2.2.1, ?_⟩
      show Holds _ (phi lUKeys lUPost _ _ t1.pc)
      rw [hp]
      change Holds t1.regs (factsFrom [1915] (lUV2 l a s r p))
      refine holds_of_pointwise fun x hx => ?_
      obtain ⟨-, -, -, -, hur⟩ := id hu
      have := holds_mem hur (mem_factsFrom (val := xFinal (lUV1 l a s r p) [lFmaItem]) (by
        simpa using hx))
      rw [lfma_val] at this
      simp at hx
      subst hx
      simpa [lUV1, lUV2] using this
    · exact .inr hd

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
