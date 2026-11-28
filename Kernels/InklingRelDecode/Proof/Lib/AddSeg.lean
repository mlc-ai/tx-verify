-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.AddBase
public import Kernels.InklingRelDecode.Proof.Lib.IntStep
public import Lemmas.Flow.SegChain
import Lemmas.Flow.Local

@[expose] public section

/-! # A strict `add.s32` of a word with a small constant register

`raw_add` (`AddBase.lean`) says what a successful evaluation writes; here the evaluation succeeds
when the base is a value with integer bits (not a pointer), and the piece is an exact segment. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof Arith32

variable {L : Launch} {g r dst δ : Nat} {t : TState} {w : Value} {op : Opnd}

theorem add_exec (flip : Bool) (hr : t.regs r = some w) (hw : w.regBits.isSome)
    (hv : readValue L g t 32 op = .ok (b32 δ)) (hb : readBits L g t 32 op = .ok (W δ)) :
    ∃ u, execInt L g t ⟨.add, .int .s 32, false, [some dst],
      if flip then [op,.reg r] else [.reg r,op]⟩ = .ok u := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hw
  have hv' : readValue L g t 32 (.reg r) = .ok w := by simp [readValue,readReg,hr]; rfl
  have hrx := readBits_regBits (w := 32) (L := L) (g := g) hr hx
  cases w <;> first
    | (simp [Value.regBits] at hx; done)
    | (cases flip <;>
        simp [execInt, DType.width, hv', hv, hrx, hb, b32, bind, Except.bind, pure, Except.pure])

/-- **The strict `add.s32`**: an exact segment of one instruction. -/
theorem add_seg {K : Kernel} {A : List Assumption} {pc : Nat} {F G : List (Nat × Value)}
    (flip : Bool) (hδ : δ < 2 ^ 31)
    (hc : K.code[pc]? = some ⟨none, .int ⟨.add, .int .s 32, false, [some dst],
      if flip then [op,.reg r] else [.reg r,op]⟩⟩)
    (hx : ∀ t, t.pc = pc → execLocalA A L g t (.int ⟨.add, .int .s 32, false, [some dst],
      if flip then [op,.reg r] else [.reg r,op]⟩) = execInt L g t ⟨.add, .int .s 32, false,
      [some dst], if flip then [op,.reg r] else [.reg r,op]⟩)
    (hl : (Op.int ⟨.add, .int .s 32, false, [some dst],
      if flip then [op,.reg r] else [.reg r,op]⟩).isLocal = true)
    (hw : w.regBits.isSome) (hr : ∀ R, Holds R F → R r = some w)
    (hOp : ∀ t, Holds t.regs F → readValue L g t 32 op = .ok (b32 δ) ∧
      readBits L g t 32 op = .ok (W δ))
    (hG : ∀ R, Holds R F → Holds (Function.update R dst (some (addBase w δ))) G) :
    Seg K A L g 1 pc F (pc + 1) G := by
  intro t ht
  obtain ⟨hp, hsub, hacc, hfl, hF⟩ := ht
  obtain ⟨hv, hb⟩ := hOp t hF
  have hr' := hr _ hF
  obtain ⟨u, he⟩ := add_exec (dst := dst) flip hr' hw hv hb
  have hu := raw_add flip hr' hδ hv hb he
  refine ⟨u, run_local hc hl ⟨hp, hsub, hacc, hfl, hF⟩ ((hx t hp).trans he), ?_⟩
  subst hu
  exact ⟨by simp [PTX.next, setReg, hp], hsub, hacc, hfl, hG _ hF⟩

/-- At a worker `selp` the move evaluator determines the written word. -/
theorem workerSelp {pc : Nat} {ii : IntInstr} (hr : ii.rule = some .threadMove)
    (hp : t.pc = pc) (hs : Assumptions.emuSites.contains pc = false) :
    execLocalA Assumptions.all L g t (.int ii) = execMove L g t (.int ii) := by
  rw [(segFree hs).exec hp, execLocalRule_of_none (fun a ha => intRules a ha), execLocal_selp hr]

end PTX.Kernels.InklingRelDecode.Proof.Lib
