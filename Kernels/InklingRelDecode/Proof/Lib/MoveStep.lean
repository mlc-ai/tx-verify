-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.IntStep
public import Kernels.InklingRelDecode.Proof.Lib.FloatRules

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof PTX.Assumption

/-- No assumption has a local rule for a move away from the float sites. -/
theorem moveNone {L : Launch} {g : Nat} {t : TState} (h1 : t.pc ≠ 2562) (h2 : t.pc ≠ 600)
    (h3 : t.pc ≠ 807) (m : MoveInstr) : ∀ a ∈ Assumptions.all, a.localRule L g t (.move m) = none :=
  fun a ha => by
  by_cases hd : a ∈ Assumptions.all.drop 2
  · exact other_rules_none h1 h2 h3 (t := t) (op := .move m) (fun c hc => nomatch hc) a hd
  · simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false, List.drop_succ_cons,
      List.drop_zero] at ha hd
    rcases ha with rfl | rfl | ha'
    · exact idealReal_localRule_none fun f hf => by simp [FloatForm.ofOp] at hf
    · exact approxExact_localRule_none fun f hf => by simp [ApproxForm.ofOp] at hf
    · exact absurd ha' hd

/-- A one-register move. A failed evaluation gives the terminal alternative in `SegU`. -/
theorem moveStepU {L : Launch} {g pc : Nat} {m : MoveInstr} {F G : List (Nat × Value)} {r : Nat}
    {v : Value} (hc : kernel.code[pc]? = some ⟨none, .move m⟩) (hl : (Op.move m).isLocal = true)
    (hr : m.rule = some .threadMove)
    (hs : Assumptions.emuSites.contains pc = false) (h1 : pc ≠ 2562) (h2 : pc ≠ 600)
    (h3 : pc ≠ 807)
    (hex : ∀ t u, Holds t.regs F → execMove L g t (.move m) = .ok u →
      u = PTX.next (setReg t r v))
    (hw : ∀ R, Holds R F → Holds (Function.update R r (some v)) G) :
    SegU kernel Assumptions.all L g pc F (pc + 1) G := by
  intro t ht
  obtain ⟨hp, hsub, hacc, hf, hF⟩ := ht
  have heval : execLocalA Assumptions.all L g t (.move m) = execMove L g t (.move m) := by
    rw [(segFree hs).exec hp, execLocalRule_of_none (moveNone (hp ▸ h1) (hp ▸ h2) (hp ▸ h3) m),
      execLocal_move hr]
  cases he : execMove L g t (.move m) with
  | error fault => exact .inr (dead_of_error (hp ▸ hc) hl hf (heval.trans he))
  | ok u =>
    have htau := tau_of_ok (K := kernel) (hp ▸ hc) hl hf (heval.trans he)
    obtain rfl := hex t u hF he
    exact .inl ⟨_, .single htau, congrArg (· + 1) hp, hsub, hacc, hf, hw _ hF⟩

/-- A scalar `mov` of an operand whose value the facts determine. -/
theorem movScalarStep {L : Launch} {g pc : Nat} {r : Nat} {ty : DType} {a : Opnd}
    {F G : List (Nat × Value)} {v : Value}
    (hc : kernel.code[pc]? = some ⟨none, .move ⟨.scalar, ty, [some r], [a]⟩⟩)
    (hty : ty ≠ .pred) (hl : (Op.move ⟨.scalar, ty, [some r], [a]⟩).isLocal = true)
    (hr : (MoveInstr.mk .scalar ty [some r] [a]).rule = some .threadMove)
    (hs : Assumptions.emuSites.contains pc = false) (h1 : pc ≠ 2562) (h2 : pc ≠ 600)
    (h3 : pc ≠ 807) (hread : ∀ t : TState, Holds t.regs F → readValue L g t ty.width a = .ok v)
    (hb : v.bytes = ty.width / 8)
    (hw : ∀ R, Holds R F → Holds (Function.update R r (some v)) G) :
    SegU kernel Assumptions.all L g pc F (pc + 1) G := by
  refine moveStepU hc hl hr hs h1 h2 h3 (fun t u hF he => ?_) hw
  simp only [execMove, hty, ite_false, hread t hF, bind, Except.bind, hb, ite_true, pure,
    Except.pure] at he
  exact (Except.ok.inj he).symm

/-- A pack of two registers. -/
theorem movPackStep {L : Launch} {g pc : Nat} {r a b : Nat} {ty : DType}
    {F G : List (Nat × Value)} {x y : Value}
    (hc : kernel.code[pc]? = some ⟨none, .move ⟨.pack, ty, [some r], [.reg a, .reg b]⟩⟩)
    (hl : (Op.move ⟨.pack, ty, [some r], [.reg a, .reg b]⟩).isLocal = true)
    (hr : (MoveInstr.mk .pack ty [some r] [.reg a, .reg b]).rule = some .threadMove)
    (hs : Assumptions.emuSites.contains pc = false) (h1 : pc ≠ 2562) (h2 : pc ≠ 600)
    (h3 : pc ≠ 807) (ha : (a, x) ∈ F) (hb : (b, y) ∈ F)
    (hw : ∀ R, Holds R F → Holds (Function.update R r (some (joinValue x y))) G) :
    SegU kernel Assumptions.all L g pc F (pc + 1) G := by
  refine moveStepU hc hl hr hs h1 h2 h3 (fun t u hF he => ?_) hw
  have hxa : t.regs a = some x := holds_mem hF ha
  have hyb : t.regs b = some y := holds_mem hF hb
  simp only [execMove, readValue, readReg, hxa, hyb, bind, Except.bind, pure, Except.pure] at he
  split_ifs at he
  exact (Except.ok.inj he).symm

end PTX.Kernels.InklingRelDecode.Proof.Lib
