-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine
public import Lemmas.Flow.MinCore
import Kernels.InklingRelDecode.Proof.Lib.FloatRules
import Kernels.InklingRelDecode.Flow.Code.Part035

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof PTX.Assumption

variable {L : Launch} {g : Nat} {t : TState}

/-- A minimum of two registers outside the software `exp2` sites reads as the ideal minimum. -/
theorem min_at {a b : Value} {src dst dm pc : Nat} (hpc : t.pc = pc)
    (emu : Assumptions.emuSites.contains pc = false) (h1 : pc ≠ 2562) (h2 : pc ≠ 600)
    (h3 : pc ≠ 807) (ha : t.regs src = some a) (hb : t.regs dst = some b) :
    execLocalA Assumptions.all L g t (MinCore.minOp dm [src,dst]) =
      (MinCore.minE [a,b]).map (fun v => PTX.next (setReg t dm v)) := by
  subst hpc
  apply MinCore.exec_minE2 _ _ ha hb
  · exact Lib.ideal_at (by simp [Lib.idealForms]) emu
  · exact Lib.decline_at (by simp [Lib.idealForms]) emu h1 h2 h3

theorem rescale_min {a b : Value} (pc : t.pc = 2256)
    (ha : t.regs 1544 = some a) (hb : t.regs 1545 = some b) :
    execLocalA Assumptions.all L g t (MinCore.minOp 1546 [1544,1545]) =
      (MinCore.minE [a,b]).map (fun v => PTX.next (setReg t 1546 v)) :=
  min_at pc (by decide) (by omega) (by omega) (by omega) ha hb

/-- The first minimum of the rescale decision reads the loaded word and its xor-2 neighbour's. -/
theorem word_min {a b : Value} (pc : t.pc = 2254)
    (ha : t.regs 1542 = some a) (hb : t.regs 1543 = some b) :
    execLocalA Assumptions.all L g t (MinCore.minOp 1544 [1542,1543]) =
      (MinCore.minE [a,b]).map (fun v => PTX.next (setReg t 1544 v)) :=
  min_at pc (by decide) (by omega) (by omega) (by omega) ha hb

abbrev rescaleCmp : Op :=
  .float { setpI (.unord .ge) false with
    dsts := [some 170], srcs := [.reg 1546,.f32imm 1065353216] }

theorem rescale_cmp {m : Value} (pc : t.pc = 2257) (hm : t.regs 1546 = some m) :
    execLocalA Assumptions.all L g t rescaleCmp =
      (setpE (.unord .ge) false m (b32 1065353216)).map
        (fun r => PTX.next (setReg t 170 (.pred r))) := by
  apply exec_setpE _ _ (.inr rfl) rfl rfl (OpndIs.reg hm) OpndIs.imm
  · exact Lib.ideal_at (by simp [Lib.idealForms]) (pc ▸ by decide)
  · exact Lib.decline_at (by simp [Lib.idealForms]) (pc ▸ by decide) (by omega) (by omega)
      (by omega)

/-- The predicate after the shuffle depends only on the sent and received values.
A fault from either local instruction consumes the lane before the branch. -/
theorem skipRescale_eq (a b : Value) :
    skipRescale L g a b =
      ((MinCore.minE [a,b]).bind fun m =>
        setpE (.unord .ge) false m (b32 1065353216)).toOption.getD false := by
  let t : TState := {pc := 2256,regs := fun r =>
    if r = 1544 then some a else if r = 1545 then some b else none}
  unfold skipRescale
  rw [Flow.code_2256,Flow.code_2257]
  have hm := rescale_min (L := L) (g := g) (t := t) rfl (a := a) (b := b) rfl rfl
  change Id.run (match execLocalA Assumptions.all L g t (MinCore.minOp 1546 [1544,1545]) with
    | .ok u => match execLocalA Assumptions.all L g u rescaleCmp with
      | .ok s => pure (decide (s.regs 170 = some (Value.pred true)))
      | _ => pure false
    | _ => pure false) = _
  rw [hm]
  cases h : MinCore.minE [a,b] with
  | error f => rfl
  | ok m =>
    have hc := rescale_cmp (L := L) (g := g) (t := PTX.next (setReg t 1546 m)) (m := m)
      rfl (by simp [PTX.next,setReg])
    simp only [Except.map,Except.bind]
    rw [hc]
    cases setpE (.unord .ge) false m (b32 1065353216) with
    | error _ => rfl
    | ok r => cases r <;> rfl

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
