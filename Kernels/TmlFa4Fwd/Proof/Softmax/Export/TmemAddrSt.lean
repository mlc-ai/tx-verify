-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Control
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Shape

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Code
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Kernels.TmlFa4Fwd.Flow.Code.Part101
import Kernels.TmlFa4Fwd.Flow.Code.Part102
import Kernels.TmlFa4Fwd.Flow.Code.Part115
import Kernels.TmlFa4Fwd.Flow.Code.Part116
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemAddr
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # The softmax warps' P stores' Tensor Memory addresses

Every P store (`pst`) is a `.32x32b` store of sixteen registers at the stage's score base `tmS`
or-ed with 64, 80, 96 or 112 (`pst_tc`); in a plain round the address registers are not named
by the round's data table, so their values are the control table's (`pst_plain_mem`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option maxHeartbeats 4000000 in
theorem pst_tc {r : Rd} {q : Fin 4} {v : V} {k : Fin 4} {acc : List Value} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState}
    (hat : (Softmax.code p L g).AtD ⟨.pst r q, v, k, acc⟩ t)
    (hc : kernel.code[(Site.pst r q).pc]? = some ins)
    (hf : Fires (Site.pst r q).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.st a vals sh)) :
    sh = .s32x32b ∧ a % 65536 + vals.length ≤ 512 := by
  cases r <;> fin_cases q <;> dsimp only [Fin.reduceFinMk, Fin.isValue] at hat hc hf ⊢
  · soft_st Mma.ori (tmS L g) 64
  · soft_st Mma.ori (tmS L g) 80
  · soft_st Mma.ori (tmS L g) 96
  · soft_st Mma.ori (tmS L g) 112
  · soft_st Mma.ori (tmS L g) 64
  · soft_st Mma.ori (tmS L g) 80
  · soft_st Mma.ori (tmS L g) 96
  · soft_st Mma.ori (tmS L g) 112
  · soft_st Mma.ori (tmS L g) 64
  · soft_st Mma.ori (tmS L g) 80
  · soft_st Mma.ori (tmS L g) 96
  · soft_st Mma.ori (tmS L g) 112


set_option linter.unusedSimpArgs false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 40000000 in
/-- **Every Tensor Memory load and store of a softmax warp** is a `.32x32b` access below
column 512. -/
theorem soft_tc (hp : Pre p L m) {d : Control.D} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hat : (SmWarp.control p L g).AtD d t)
    (hi : (SmWarp.control p L g).inv d) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    (∀ a vals sh, e.kind = .tc (.ld a vals sh) →
      sh = .s32x32b ∧ a % 65536 + vals.length ≤ 512) ∧
    (∀ a vals sh, e.kind = .tc (.st a vals sh) →
      sh = .s32x32b ∧ a % 65536 + vals.length ≤ 512) := by
  have hev := Control.shapeAt hp d hat hi.1 hc hf
  obtain ⟨s, v, k, acc⟩ := d
  refine ⟨fun a vals sh hk => ?_, fun a vals sh hk => ?_⟩
  · cases s with
    | sld r c =>
      exact sld_tc (p := p) (L := L) (g := g) (r := r) (c := c) (k := k)
        (acc := acc) (v := v.scheduler) hat hc hf hk
    | sldw c =>
      by_cases hk1 : k = 1
      · simp only [Control.Ev, Control.D.scheduler, Ev, hk1] at hev
        simp_all
      · have hk0 : k = 0 := by
          rcases hi.1 with ⟨h, -⟩ | h
          · exact h
          · exact absurd h.1 hk1
        subst hk0
        exact sldw_tc (p := p) (L := L) (g := g) (c := c) (acc := acc) (v := v.scheduler) hat hc
            hf hk
    | _ => (simp only [Control.Ev, Control.D.scheduler, Ev] at hev; simp_all [rdOrUb, tcLdOrUb,
        Epilogue.Ev, Site.toE]) <;>
      (unfold Epilogue.Ev at hev; split at hev <;> simp_all [Epilogue.isStore])
  · cases s with
    | pst r q =>
      exact pst_tc (p := p) (L := L) (g := g) (r := r) (q := q) (k := k)
        (acc := acc) (v := v.scheduler) hat hc hf hk
    | _ => (simp only [Control.Ev, Control.D.scheduler, Ev] at hev; simp_all [rdOrUb, tcLdOrUb,
        Epilogue.Ev, Site.toE]) <;>
      (unfold Epilogue.Ev at hev; split at hev <;> simp_all [Epilogue.isStore])

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
