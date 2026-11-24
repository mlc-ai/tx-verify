-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemCol
import Kernels.TmlFa4Fwd.Flow.Code.Part053
import Kernels.TmlFa4Fwd.Flow.Code.Part054
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Kernels.TmlFa4Fwd.Flow.Code.Part079
import Kernels.TmlFa4Fwd.Flow.Code.Part080
import Kernels.TmlFa4Fwd.Flow.Code.Part101
import Kernels.TmlFa4Fwd.Flow.Code.Part102
import Kernels.TmlFa4Fwd.Flow.Code.Part104
import Kernels.TmlFa4Fwd.Flow.Code.Part105
import Kernels.TmlFa4Fwd.Flow.Code.Part115
import Kernels.TmlFa4Fwd.Flow.Code.Part116
import Lemmas.Flow.ElemAccess
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The addresses of the softmax warps' Tensor Memory accesses -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The address of the columns `n` of the lane's stage. -/
noncomputable def colAddr (L : Launch) (g n : Nat) : Nat :=
  if n = 0 then (tmS L g).toNat else (Mma.ori (tmS L g) (n : Nat)).toNat

set_option hygiene false in
/-- A load site whose address register holds `X`. -/
macro "addr_ld " X:term:max : tactic => `(tactic| (
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  obtain ⟨rfl, rfl, -⟩ := ld_at (a0 := ($X).toNat) hat hc
    (by rw [← b32_toNat]; exact Flow.mem_factsFrom (by lit_mem))
    (by first | exact tmS_lt L g | exact ori_lt _ _) hf hk
  exact ⟨rfl, rfl⟩))

set_option hygiene false in
/-- A store site whose address register holds `X`. -/
macro "addr_st " X:term:max : tactic => `(tactic| (
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  obtain ⟨rfl, rfl, -⟩ := st_at (a0 := ($X).toNat) hat hc
    (by rw [← b32_toNat]; exact Flow.mem_factsFrom (by lit_mem))
    (by first | exact tmS_lt L g | exact ori_lt _ _) hf hk
  exact ⟨rfl, rfl⟩))

set_option maxHeartbeats 4000000 in
/-- **A score load's address.** -/
theorem sld_addr {r : Rd} {c : Fin 4} {v : V} {k : Fin 4} {acc : List Value} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState}
    (hat : (Softmax.code p L g).AtD ⟨.sld r c, v, k, acc⟩ t)
    (hc : kernel.code[(Site.sld r c).pc]? = some ins)
    (hf : Fires (Site.sld r c).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.ld a vals sh)) :
    sh = .s32x32b ∧ a = colAddr L g (32 * c.val) := by
  cases r <;> fin_cases c <;> dsimp only [Fin.reduceFinMk, Fin.isValue] at hat hc hf ⊢
  · addr_ld (tmS L g)
  · addr_ld (Mma.ori (tmS L g) 32)
  · addr_ld (Mma.ori (tmS L g) 64)
  · addr_ld (Mma.ori (tmS L g) 96)
  · addr_ld (tmS L g)
  · addr_ld (Mma.ori (tmS L g) 32)
  · addr_ld (Mma.ori (tmS L g) 64)
  · addr_ld (Mma.ori (tmS L g) 96)
  · addr_ld (tmS L g)
  · addr_ld (Mma.ori (tmS L g) 32)
  · addr_ld (Mma.ori (tmS L g) 64)
  · addr_ld (Mma.ori (tmS L g) 96)

set_option maxHeartbeats 4000000 in
/-- **A P store's address.** -/
theorem pst_addr {r : Rd} {q : Fin 4} {v : V} {k : Fin 4} {acc : List Value} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState}
    (hat : (Softmax.code p L g).AtD ⟨.pst r q, v, k, acc⟩ t)
    (hc : kernel.code[(Site.pst r q).pc]? = some ins)
    (hf : Fires (Site.pst r q).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.st a vals sh)) :
    sh = .s32x32b ∧ a = colAddr L g (64 + 16 * q.val) := by
  cases r <;> fin_cases q <;> dsimp only [Fin.reduceFinMk, Fin.isValue] at hat hc hf ⊢
  · addr_st (Mma.ori (tmS L g) 64)
  · addr_st (Mma.ori (tmS L g) 80)
  · addr_st (Mma.ori (tmS L g) 96)
  · addr_st (Mma.ori (tmS L g) 112)
  · addr_st (Mma.ori (tmS L g) 64)
  · addr_st (Mma.ori (tmS L g) 80)
  · addr_st (Mma.ori (tmS L g) 96)
  · addr_st (Mma.ori (tmS L g) 112)
  · addr_st (Mma.ori (tmS L g) 64)
  · addr_st (Mma.ori (tmS L g) 80)
  · addr_st (Mma.ori (tmS L g) 96)
  · addr_st (Mma.ori (tmS L g) 112)

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
