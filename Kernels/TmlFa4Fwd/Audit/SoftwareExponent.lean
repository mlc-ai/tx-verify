-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Lemmas.Flow.Local

@[expose] public section

/-! # The software `exp2` segment as one local step -/

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

private theorem numericSegment {l : Launch} {g : Nat} {t : TState} :
    (Assumptions.numeric.findSome? fun a => a.segmentRule l g t) =
      Assumptions.swExp2.segmentRule l g t := by
  have hI : Assumptions.idealArith.segmentRule l g t = none := rfl
  have hA : Assumptions.approx.segmentRule l g t = none := rfl
  have hL : Assumptions.lg2.segmentRule l g t = none := rfl
  have hB : Assumptions.bf16Convert.segmentRule l g t = none := rfl
  simp only [Assumptions.numeric, List.findSome?_cons, List.findSome?_nil, hI, hA, hL, hB]
  cases Assumptions.swExp2.segmentRule l g t <;> rfl

/-- A recognized software exponent segment is a single actual local transition of the
profile, including the zero produced from its masked negative-infinity inputs. -/
theorem softwareExponentRun {l : Launch} {g pc : Nat} {t u : TState} {ins : Op}
    {F : List (Nat × Value)} {matched : SegMatch CuteSlot}
    (ht : At t pc F) (hSite : pc ∈ Assumptions.swExp2Sites)
    (hCode : kernel.code[pc]? = some ⟨none, ins⟩) (hLocal : ins.isLocal = true)
    (hMatch : cuteExp2.matchAt kernel pc = some matched)
    (hExec : Assumptions.execSwExp2 matched t = .ok u) :
    run kernel Assumptions.all l g 1 t = some u := by
  have hSel : Assumptions.swExp2.segmentRule l g t = some (.ok u) := by
    have hHas : Assumptions.swExp2Sites.contains pc = true := by simpa using hSite
    change (if Assumptions.swExp2Sites.contains t.pc ∧ t.sub = 0 ∧ t.acc.isEmpty then
      (cuteExp2.matchAt kernel t.pc).map fun m => Assumptions.execSwExp2 m t else none) = _
    simp only [ht.1, ht.2.1, ht.2.2.1, hHas, hMatch, hExec, List.isEmpty_nil, and_self,
      ↓reduceIte, Option.map_some]
  rw [Assumptions.run_all_eq_numeric]
  apply run_local hCode hLocal ht
  rw [execLocalA, numericSegment, hSel]

/-- The local continuation of the software exponent uses the matcher-provided input and output
register assignment. Intermediate scratch words are cleared and defining constants are set. -/
def softwareExponentResult (matched : SegMatch CuteSlot) (t : TState)
    (exponents : CuteSlot → ℝ) : TState :=
  let reg := fun slot => (matched.reg.lookup slot).getD 0
  let cleared := matched.shape.writes.foldl (fun rs slot => Function.update rs (reg slot) none)
    t.regs
  let consts := if matched.shape.defines then
      matched.shape.consts.foldl (fun rs (slot, v) => Function.update rs (reg slot) (some v))
        cleared
    else cleared
  let output := matched.shape.io.map fun p => (reg p.2, Value.float .f32 (exponents p.1))
  {t with
    regs := output.foldl (fun rs (d, v) => Function.update rs d (some v)) consts
    pc := matched.stop
    sub := 0
    acc := []}

/-- The software site writes the exponent of every matched input lane and preserves the
matcher-defined continuation PC. The lane outcomes include zero for the negative-infinity mask. -/
theorem softwareExponentValues {l : Launch} {g pc : Nat} {t : TState} {ins : Op}
    {F : List (Nat × Value)} {matched : SegMatch CuteSlot}
    (raw : CuteSlot → Value) (exponents : CuteSlot → ℝ)
    (ht : At t pc F) (hSite : pc ∈ Assumptions.swExp2Sites)
    (hCode : kernel.code[pc]? = some ⟨none, ins⟩) (hLocal : ins.isLocal = true)
    (hMatch : cuteExp2.matchAt kernel pc = some matched)
    (hConsts : matched.shape.defines ∨ ∀ p ∈ matched.shape.consts,
      t.regs ((matched.reg.lookup p.1).getD 0) = some p.2)
    (hInput : ∀ p ∈ matched.shape.io,
      t.regs ((matched.reg.lookup p.1).getD 0) = some (raw p.1))
    (hEval : ∀ p ∈ matched.shape.io, Assumptions.swExp2Lane (raw p.1) = .ok (exponents p.1)) :
    run kernel Assumptions.all l g 1 t = some (softwareExponentResult matched t exponents) := by
  apply softwareExponentRun ht hSite hCode hLocal hMatch
  let reg := fun slot => (matched.reg.lookup slot).getD 0
  let eval := fun p : CuteSlot × CuteSlot => do
    let x ← Assumptions.swExp2Lane (← readReg t (reg p.1))
    pure (reg p.2, Value.float .f32 x)
  let output := fun p : CuteSlot × CuteSlot => (reg p.2, Value.float .f32 (exponents p.1))
  have hEach (p : CuteSlot × CuteSlot) (hp : p ∈ matched.shape.io) :
      eval p = .ok (output p) := by
    have hr := hInput p hp
    have hv := hEval p hp
    simp [eval, output, readReg, reg, hr, hv, bind, Except.bind, pure, Except.pure]
  have hMap : matched.shape.io.mapM eval = .ok (matched.shape.io.map output) := by
    generalize hL : matched.shape.io = items at hEach ⊢
    clear hL
    induction items with
    | nil => rfl
    | cons item rest ih =>
      rw [List.mapM_cons, hEach item (by simp), List.map_cons]
      have hTail := ih (fun p h => hEach p (by simp [h]))
      change ((rest.mapM eval).bind fun xs => .ok (output item :: xs)) = _
      rw [hTail]
      rfl
  unfold Assumptions.execSwExp2 softwareExponentResult
  simp only [hConsts, ↓reduceIte, bind, Except.bind, pure, Except.pure]
  dsimp only [eval, reg, bind, Except.bind, pure, Except.pure] at hMap
  rw [hMap]

end
end PTX.Kernels.TmlFa4Fwd.Softmax
