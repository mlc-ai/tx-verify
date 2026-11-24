-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ArithCore
public import Lemmas.Flow.FloatOutcome

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Assumption
noncomputable section

/-- The ideal-real maximum, with the FTZ Core rule as fallback. -/
def peerMaxE (lo hi : Value) : Exec Value :=
  match idealMax [lo, hi] with
  | some out => out
  | none => coreFloat { maxI with ftz := true } [lo, hi]

/-- The two halves of the local maximum each start with an explicit negative infinity. -/
def peerHalfMax (words : Nat → Value) (base : Nat) : Exec Value := do
  let (lo, hi) ← unpackE 64 (words base)
  let m ← peerMaxE lo (b32 4286578688)
  let m ← peerMaxE m hi
  (List.range 7).foldlM (fun acc i => do
    let (l, h) ← unpackE 64 (words (base + i + 1))
    let acc ← peerMaxE acc l
    peerMaxE acc h) m

/-- The local row maximum is reduced in two groups of eight score pairs and then scaled. -/
def peerRowMax (words : Nat → Value) (scale : Value) : Exec Value := do
  let lo ← peerHalfMax words 0
  let hi ← peerHalfMax words 8
  let m ← peerMaxE lo hi
  mulE true m scale

/-- The emitted binary32 maximum, with its operands in PTX order. -/
abbrev peerMaxOp (dst : Nat) (a b : Opnd) : Op :=
  .float { maxI with ftz := true, dsts := [some dst], srcs := [a, b] }

private theorem exec_peerMax_core {L : Launch} {g : Nat} {t : TState} {dst : Nat}
    {a b : Opnd} {va vb : Value}
    (ha : readValue L g t 32 a = .ok va) (hb : readValue L g t 32 b = .ok vb) :
    execLocal L g t (peerMaxOp dst a b) =
      (coreFloat { maxI with ftz := true } [va, vb]).map fun v => PTX.next (setReg t dst v) := by
  cases hxa : classify .f32 va with
  | error e => core_float
  | ok xa =>
    cases hxb : classify .f32 vb with
    | error e => core_float
    | ok xb =>
      let f : FloatInstr := { maxI with ftz := true }
      cases hlane : f.lane [xa, xb] with
      | none =>
        have hl :
            ({ maxI with ftz := true, dsts := [some dst], srcs := [a, b] } : FloatInstr).lane
              [xa, xb] = none := hlane
        have hr : FloatInstr.lane { maxI with ftz := true } [xa, xb] = none := hlane
        core_float
      | some o =>
        have hl :
            ({ maxI with ftz := true, dsts := [some dst], srcs := [a, b] } : FloatInstr).lane
              [xa, xb] = some o := hlane
        have hr : FloatInstr.lane { maxI with ftz := true } [xa, xb] = some o := hlane
        cases o <;> core_float

/-- Exact execution of a binary maximum when the concrete operands are available. -/
theorem exec_peerMaxE {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {dst : Nat} {a b : Opnd} {va vb : Value}
    (hI : IdealAt A (.max .f32) L g t) (hD : DeclineAt A (.max .f32) L g t)
    (ha : readValue L g t 32 a = .ok va) (hb : readValue L g t 32 b = .ok vb)
    (ha' : readERealOpnd t .f32 a = readEReal .f32 va)
    (hb' : readERealOpnd t .f32 b = readEReal .f32 vb) :
    execLocalA A L g t (peerMaxOp dst a b) =
      (peerMaxE va vb).map fun v => PTX.next (setReg t dst v) := by
  have hf : FloatForm.ofOp (peerMaxOp dst a b) = some (.max .f32) := by
    simp [FloatForm.ofOp]
  have hi : execIdealFloat L g t (peerMaxOp dst a b) =
      (idealMax [va, vb]).map (Except.map fun v => PTX.next (setReg t dst v)) := by
    simp only [execIdealFloat, idealMax, ha', hb', bindRead_map,
      beq_self_eq_true, ↓reduceIte, Option.map_some, Except.map, pure, Except.pure]
  unfold peerMaxE
  cases hv : idealMax [va, vb] with
  | none => rw [hD _ hf (by rw [hi, hv]; rfl), exec_peerMax_core ha hb]
  | some r => rw [hI _ hf _ (by rw [hi, hv]; rfl)]

/-- The emitted packed add omits the rounding modifier. -/
abbrev peerAddI : FloatInstr := { add2I with rnd := none }

/-- The packed add's ideal-real result or the exact Core fallback for this instruction. -/
def peerAddE (lo hi : Value) : Exec Value :=
  match idealAdd2 lo hi with
  | some out => out
  | none => coreFloat peerAddI [lo, hi]

private theorem execLocal_peerAdd_core {L : Launch} {g : Nat} {t : TState}
    {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocal L g t (.float { peerAddI with dsts := [some d], srcs := [.reg a, .reg b] }) =
      (coreFloat peerAddI [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { peerAddI with dsts := [some d], srcs := [.reg a, .reg b] } =
      FloatInstr.lane peerAddI := rfl
  have h2 : List.range 2 = [0, 1] := rfl
  cases hxa : classify .f32 (splitValue 64 va).1 with
  | error e => core_float_reg
  | ok xa =>
  cases hxb : classify .f32 (splitValue 64 vb).1 with
  | error e => core_float_reg
  | ok xb =>
  cases hl0 : FloatInstr.lane peerAddI [xa, xb] with
  | none => core_float_reg
  | some o =>
  cases hya : classify .f32 (splitValue 64 va).2 with
  | error e => core_float_reg
  | ok ya =>
  cases hyb : classify .f32 (splitValue 64 vb).2 with
  | error e => core_float_reg
  | ok yb =>
  cases hl1 : FloatInstr.lane peerAddI [ya, yb] with
  | none => core_float_reg
  | some o' => cases o <;> cases o' <;> core_float_reg

/-- **The local step of `add.f32x2 d, a, b`** writes the outcome's value or faults. -/
theorem exec_peerAddE {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    (hI : IdealAt A .addRnF32x2 L g t)
    (hD : DeclineAt A .addRnF32x2 L g t) {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocalA A L g t (.float { peerAddI with dsts := [some d], srcs := [.reg a, .reg b] }) =
      (peerAddE va vb).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp (.float { peerAddI with dsts := [some d], srcs := [.reg a, .reg b] }) =
      some .addRnF32x2 := by simp [FloatForm.ofOp]
  have hi : execIdealFloat L g t
      (.float { peerAddI with dsts := [some d], srcs := [.reg a, .reg b] }) =
      (idealAdd2 va vb).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execIdealFloat, idealAdd2, readERealPair_reg_val (L := L) (g := g) ha,
      readERealPair_reg_val (L := L) (g := g) hb, bindRead_map]
    rcases pairRead va with _ | (e | ⟨x0, x1⟩)
    · rfl
    · rfl
    rcases pairRead vb with _ | (e | ⟨y0, y1⟩)
    · rfl
    · rfl
    simp only [bindRead]
    rcases addEReal x0 y0 with _ | r0 <;> rcases addEReal x1 y1 with _ | r1 <;> rfl
  unfold peerAddE
  cases hv : idealAdd2 va vb with
  | none => rw [hD _ hf (by rw [hi, hv]; rfl), execLocal_peerAdd_core ha hb]
  | some r => rw [hI _ hf _ (by rw [hi, hv]; rfl)]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
