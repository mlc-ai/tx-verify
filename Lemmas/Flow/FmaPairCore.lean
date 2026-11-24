-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.MaxCore
public import Lemmas.Flow.FmaRun

@[expose] public section

/-! # The outcome of a packed fused multiply-add on any operand values

A proof tool. Under an ideal-real assumption that names `fma.rn.f32x2` (ASM-IDEAL), the packed
product sum `fma.rn.f32x2 d, a, b, c` reads the two elements of each source pair in the extended
reals: an element without a datum of `.f32` faults, an infinity is that infinity, and a NaN
element (or `0 · ∞`, `∞ - ∞` in a lane) makes the ideal rule decline, so that the Core rule
(THREAD-FLOAT) gives the result, lane by lane. The outcome on the values of the three sources is
one `Exec Value` (`fma2E`): the ideal pair where the ideal rule applies, the Core rule's
(`coreFloat`) where it declines. Its local step writes the outcome's value or faults
(`exec_fma2E`). Every value of the outcome is a pair of four-byte halves (`fma2E_pair4`), and on
pairs of numbers the outcome is the pair of the exact results (`fma2E_fin`). -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

/-- `fma.rn.f32x2`. -/
abbrev fma2I : FloatInstr :=
  { op := .fma, ty := ⟨.f32, 2⟩, rnd := some .rn, dsts := [], srcs := [] }

/-- The ideal-real outcome of `fma.rn.f32x2` on source values, as `execIdealFloat` computes it for
registers that hold them; `none` where the rule declines in a lane. -/
def idealFma2 (va vb vc : Value) : Option (Exec Value) :=
  bindRead (pairRead va) fun (x0, x1) => bindRead (pairRead vb) fun (y0, y1) =>
    bindRead (pairRead vc) fun (z0, z1) =>
      match (mulEReal x0 y0).bind (addEReal · z0), (mulEReal x1 y1).bind (addEReal · z1) with
      | some r0, some r1 => some (pure (.pair (erealValue .f32 r0) (erealValue .f32 r1)))
      | _, _ => none

/-- **The outcome of `fma.rn.f32x2`**: the ideal outcome, or the Core rule's where the ideal rule
declines. -/
@[irreducible] def fma2E (va vb vc : Value) : Exec Value :=
  match idealFma2 va vb vc with
  | some r => r
  | none => coreFloat fma2I [va, vb, vc]

variable {A : List Assumption} {L : Launch} {g : Nat}

theorem fma2Op_eq (d a b c : Nat) :
    fma2Op d a b c = .float { fma2I with dsts := [some d], srcs := [.reg a, .reg b, .reg c] } :=
  rfl

theorem fma2Op_form (d a b c : Nat) :
    FloatForm.ofOp (fma2Op d a b c) = some .fmaRnF32x2 := by
  simp [fma2Op, FloatForm.ofOp]

theorem execLocal_fma2_core {t : TState} {d a b c : Nat} {va vb vc : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) (hc : t.regs c = some vc) :
    execLocal L g t (fma2Op d a b c) =
      (coreFloat fma2I [va, vb, vc]).map fun v => PTX.next (setReg t d v) := by
  rw [fma2Op_eq]
  have hl : FloatInstr.lane { fma2I with dsts := [some d], srcs := [.reg a, .reg b, .reg c] } =
      FloatInstr.lane fma2I := rfl
  have h2 : List.range 2 = [0, 1] := rfl
  cases hxa : classify .f32 (splitValue 64 va).1 with
  | error e => core_float_reg
  | ok xa =>
  cases hxb : classify .f32 (splitValue 64 vb).1 with
  | error e => core_float_reg
  | ok xb =>
  cases hxc : classify .f32 (splitValue 64 vc).1 with
  | error e => core_float_reg
  | ok xc =>
  cases hl0 : FloatInstr.lane fma2I [xa, xb, xc] with
  | none => core_float_reg
  | some o =>
  cases hya : classify .f32 (splitValue 64 va).2 with
  | error e => core_float_reg
  | ok ya =>
  cases hyb : classify .f32 (splitValue 64 vb).2 with
  | error e => core_float_reg
  | ok yb =>
  cases hyc : classify .f32 (splitValue 64 vc).2 with
  | error e => core_float_reg
  | ok yc =>
  cases hl1 : FloatInstr.lane fma2I [ya, yb, yc] with
  | none => core_float_reg
  | some o' => cases o <;> cases o' <;> core_float_reg

theorem execIdeal_fma2 {t : TState} {d a b c : Nat} {va vb vc : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) (hc : t.regs c = some vc) :
    execIdealFloat L g t (fma2Op d a b c) =
      (idealFma2 va vb vc).map (Except.map fun v => PTX.next (setReg t d v)) := by
  simp only [fma2Op, execIdealFloat, idealFma2, readERealPair_reg_val (L := L) (g := g) ha,
    readERealPair_reg_val (L := L) (g := g) hb, readERealPair_reg_val (L := L) (g := g) hc,
    bindRead_map]
  rcases pairRead va with _ | (e | ⟨x0, x1⟩)
  · rfl
  · rfl
  rcases pairRead vb with _ | (e | ⟨y0, y1⟩)
  · rfl
  · rfl
  rcases pairRead vc with _ | (e | ⟨z0, z1⟩)
  · rfl
  · rfl
  simp only [bindRead]
  rcases (mulEReal x0 y0).bind (addEReal · z0) with _ | r0 <;>
    rcases (mulEReal x1 y1).bind (addEReal · z1) with _ | r1 <;> rfl

/-- **The local step of `fma.rn.f32x2 d, a, b, c`** writes the outcome's value or faults. -/
theorem exec_fma2E {t : TState} (hI : IdealAt A .fmaRnF32x2 L g t)
    (hD : DeclineAt A .fmaRnF32x2 L g t) {d a b c : Nat} {va vb vc : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) (hc : t.regs c = some vc) :
    execLocalA A L g t (fma2Op d a b c) =
      (fma2E va vb vc).map fun v => PTX.next (setReg t d v) := by
  have hi := execIdeal_fma2 (L := L) (g := g) (d := d) ha hb hc
  unfold fma2E
  cases hv : idealFma2 va vb vc with
  | none => rw [hD _ (fma2Op_form d a b c) (by rw [hi, hv]; rfl), execLocal_fma2_core ha hb hc]
  | some r => rw [hI _ (fma2Op_form d a b c) _ (by rw [hi, hv]; rfl)]

/-- Every value of the outcome is a pair of four-byte halves. -/
theorem fma2E_pair4 (va vb vc : Value) : Pair4 (fma2E va vb vc) := by
  intro v hv
  unfold fma2E at hv
  split at hv
  · rename_i r hr
    subst hv
    obtain ⟨⟨x0, x1⟩, -, hr⟩ := bindRead_ok hr
    obtain ⟨⟨y0, y1⟩, -, hr⟩ := bindRead_ok hr
    obtain ⟨⟨z0, z1⟩, -, hr⟩ := bindRead_ok hr
    simp only at hr
    split at hr
    · simp only [Option.some.injEq, pure, Except.pure, Except.ok.injEq] at hr
      exact ⟨_, _, hr.symm, erealValue_f32_bytes _, erealValue_f32_bytes _⟩
    · cases hr
  · exact coreFloat_pair4 rfl _ v hv

/-- **A packed fused multiply-add of numbers** is the pair of the exact results. -/
theorem fma2E_fin {va vb vc : Value} {x0 x1 y0 y1 z0 z1 : ℝ}
    (hx0 : valFloat .f32 (splitValue 64 va).1 = .ok x0)
    (hx1 : valFloat .f32 (splitValue 64 va).2 = .ok x1)
    (hy0 : valFloat .f32 (splitValue 64 vb).1 = .ok y0)
    (hy1 : valFloat .f32 (splitValue 64 vb).2 = .ok y1)
    (hz0 : valFloat .f32 (splitValue 64 vc).1 = .ok z0)
    (hz1 : valFloat .f32 (splitValue 64 vc).2 = .ok z1) :
    fma2E va vb vc =
      .ok (.pair (.float .f32 (x0 * y0 + z0)) (.float .f32 (x1 * y1 + z1))) := by
  simp only [fma2E, idealFma2, pairRead_of hx0 hx1, pairRead_of hy0 hy1, pairRead_of hz0 hz1,
    bindRead, mulEReal_coe, Option.bind_some, addEReal_coe, erealValue_coe, pure, Except.pure]

end
end PTX.Flow
