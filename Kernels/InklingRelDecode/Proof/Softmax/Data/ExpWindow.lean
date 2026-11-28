-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpKinds
public import Kernels.InklingRelDecode.Proof.Softmax.Data.SwExp

@[expose] public section

/-! # The exponent window on a register file

From the registers the window reads (`kE0`, under values `V` that satisfy `ExpIn`) the three
stretches of pcs 1847 to 2233 (the shifted scores, the sixteen software instances, the
exponentials and sums) reach pc 2234 with the registers `kE3` under `vE3 V`: the exponentials
packed in pairs (registers 1994 to 2017), the sixteen selected singles (508 to 523) and the row
sum (1529) are numbers. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section
variable {L : Launch} {g : Nat}

/-- A run's value at a register it writes is typed when its facts are. -/
theorem V'_out (r : RunData) (ok : r.Ok) {P : Nat → Value → Prop} {W : Nat → Value}
    (h : ∀ p ∈ r.fs1 W, P p.1 p.2) {x : Nat} (hx : x ∈ r.outs) : P x (r.V' W x) := by
  unfold RunData.V' valueEx
  obtain ⟨v, hv⟩ := lookup_some (F := r.fs1 W) (r := x) (by rw [ok.h1 W]; exact hx)
  rw [hv]
  exact h _ (mem_of_lookupK hv)

theorem swY_fl {v : Value} (h : SK.ni.Has v) : (Kd.s .fl).Has (swY v) := by
  obtain ⟨x, hx, -⟩ := ni_read h
  simp only [swY, hx]
  exact has_float_fl _

/-- The registers the window starts from. -/
def kE0 : List Nat := runE1.live ++ [179, 180]
def vE1 (V : Nat → Value) : Nat → Value := runE1.V' V
def kE1 : List Nat := runE1.K' kE0
def vE2 (V : Nat → Value) : Nat → Value := swVs (vE1 V) 16
def kE2 : List Nat := swKs kE1 16
def vE3 (V : Nat → Value) : Nat → Value := runE2.V' (vE2 V)
def kE3 : List Nat := runE2.K' kE2

theorem kE_ok : runE1.live.all (fun r => kE0.contains r) = true ∧
    (List.range 16).all (fun i => kE1.contains (swX (swPc i))) = true ∧
    runE2.live.all (fun r => kE2.contains r) = true ∧
    (List.range 16).all (fun i => runE1.outs.contains (swX (swPc i))) = true ∧
    xRegs.all (fun r => (List.range 16).all fun j => r != swR (swPc j)) = true ∧
    (List.range 16).all (fun i => swR (swPc i) == 1271 + i) = true := by
  decide +kernel

theorem vE1_has {V : Nat → Value} (h : ExpIn V) {x : Nat} (hx : x ∈ xRegs) :
    (Kd.s .ni).Has (vE1 V x) := V'_out runE1 runE1_ok (P := fun _ => (Kd.s .ni).Has) (e1_has h) hx

theorem vE2_x {V : Nat → Value} (h : ExpIn V) {r : Nat} (hx : r ∈ xRegs) :
    (Kd.s .ni).Has (vE2 V r) := by
  obtain ⟨-, -, -, -, k4, -⟩ := kE_ok
  have hn := List.all_eq_true.mp k4 r hx
  rw [vE2, swVs_other fun j hj => by simpa using List.all_eq_true.mp hn j (by simpa using hj)]
  exact vE1_has h hx

theorem vE2_y {V : Nat → Value} (h : ExpIn V) {r : Nat} (hr : r ∈ swOuts) :
    (Kd.s .fl).Has (vE2 V r) := by
  simp only [swOuts, List.mem_map, List.mem_range] at hr
  obtain ⟨i, hi, rfl⟩ := hr
  obtain ⟨-, -, -, k3, -, k5⟩ := kE_ok
  have e : swR (swPc i) = 1271 + i := by
    simpa using List.all_eq_true.mp k5 i (by simpa using hi)
  rw [← e, vE2, swVs_out hi (le_refl 16)]
  refine swY_fl ?_
  have hx : swX (swPc i) ∈ xRegs := by
    simpa [xRegs] using List.all_eq_true.mp k3 i (by simpa using hi)
  exact vE1_has h hx

/-- **The exponent window on a register file**: from the registers it reads to pc 2234. -/
theorem exp_window {V : Nat → Value} (h : ExpIn V) :
    SegU kernel Assumptions.all L g 1847 (factsFrom kE0 V) 2234 (factsFrom kE3 (vE3 V)) := by
  obtain ⟨k0, k1, k2, k3, -, -⟩ := kE_ok
  have s1 := runE1.adv (L := L) (g := g) (K := kE0) runE1_ok V k0
  have s2 := sw_chain (L := L) (g := g) (K := kE1) (V := vE1 V) (n := 16) le_rfl
    (fun i hi => by simpa using List.all_eq_true.mp k1 i (by simpa using hi))
    (fun i hi => ?_)
  · have s3 := runE2.adv (L := L) (g := g) (K := kE2) runE2_ok (vE2 V) k2
    exact s1.comp (s2.comp s3)
  · refine SK.mono (a := .ni) (b := .ni) (by decide) ?_
    exact vE1_has h (by simpa [xRegs] using List.all_eq_true.mp k3 i (by simpa using hi))

/-- The words the window leaves are numbers (pairs of numbers in the registers 1994 to 2017). -/
theorem exp_typed {V : Nat → Value} (h : ExpIn V) {r : Nat} (hr : r ∈ runE2.outs) :
    ExpTy r (vE3 V r) :=
  V'_out runE2 runE2_ok (P := ExpTy) (e2_has (fun _ hr => vE2_x h hr) (fun _ hr => vE2_y h hr)) hr

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
