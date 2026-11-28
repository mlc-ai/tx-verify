-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.QEntry
public import Kernels.InklingRelDecode.Proof.Lib.MoveStep

@[expose] public section

/-! # The strict moves and packs of the query halves -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

variable {L : Launch} {g : Nat}

/-- A move at a pc below 574 that writes a register no tag names is a strict step. -/
theorem move_seg {pc d : Nat} {m : MoveInstr} {v : Value} {F G : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨none, .move m⟩) (hl : (Op.move m).isLocal = true)
    (hr : m.rule = some .threadMove) (hlo : 27 ≤ pc) (hpc : pc < 574)
    (hex : ∀ t : TState, Holds t.regs F → execMove L g t (.move m) = .ok (PTX.next (setReg t d v)))
    (hG : ∀ R, Holds R F → Holds (Function.update R d (some v)) G)
    (hq : ∀ p ∈ proQt (pc + 1), p.1 ≠ d ∧ (proQt pc).lookup p.1 = some p.2) :
    SegQ kernel Assumptions.all L g (QT proQt) pc F (pc + 1) G := by
  intro t ht hQ
  obtain ⟨hp, hsub, hacc, hf, hF⟩ := ht
  have hpl : kernel.code[t.pc]? = some ⟨none, .move m⟩ := hp ▸ hc
  have heval : execLocalA Assumptions.all L g t (.move m) = execMove L g t (.move m) := by
    rw [execLocalA_noSegment (fun a ha => plainSegs_pro (a := 27) (b := 574) le_rfl pc
      (by omega) (by omega) a ha L g t hp), execLocalRule_of_none (Lib.moveNone (by rw [hp]; omega)
      (by rw [hp]; omega) (by rw [hp]; omega) m), execLocal_move hr]
  have htau := tau_of_ok (A := Assumptions.all) (L := L) (g := g) hpl hl hf
    (heval.trans (hex t hF))
  refine ⟨PTX.next (setReg t d v), .single htau,
    ⟨by simp [PTX.next, setReg, hp], hsub, hacc, hf, hG _ hF⟩, ?_⟩
  have hT : Typed (proQt pc) t := by simpa [QT, hp] using hQ
  intro r tg hr'
  have hr1 : (proQt (pc + 1)).lookup r = some tg := by simpa [PTX.next, setReg, hp] using hr'
  obtain ⟨hne, hlk⟩ := hq _ (lookup_mem hr1)
  simpa [PTX.next, setReg, Function.update_of_ne hne] using hT r tg hlk

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

variable {L : Launch} {g : Nat}

theorem hex_mov16 {d s : Nat} {v : Value} {F : List (Nat × Value)} (hs : (s, v) ∈ F)
    (hb : v.bytes = 2) (t : TState) (hF : Holds t.regs F) :
    execMove L g t (.move ⟨.scalar, .int .u 16, [some d], [.reg s]⟩) =
      .ok (PTX.next (setReg t d v)) := by
  simp [execMove, readValue, readReg, holds_mem hF hs, hb, DType.width, bind, Except.bind, pure,
      Except.pure]

theorem hex_pack {d a b : Nat} {x y : Value} {F : List (Nat × Value)} (ha : (a, x) ∈ F)
    (hb : (b, y) ∈ F) (hx : x.bytes = 2) (hy : y.bytes = 2) (t : TState) (hF : Holds t.regs F) :
    execMove L g t (.move ⟨.pack, .int .b 32, [some d], [.reg a, .reg b]⟩) =
      .ok (PTX.next (setReg t d (joinValue x y))) := by
  simp [execMove, readValue, readReg, holds_mem hF ha, holds_mem hF hb, hx, hy, DType.width, bind,
    Except.bind, pure, Except.pure]

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
