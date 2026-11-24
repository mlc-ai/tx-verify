-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpOk
import Lemmas.Protocol.CpAsync

@[expose] public section

/-! # The source size of a row copy

The size register of copy row `i` of a packet is a `selp` of 16 and 0 by whether the packet's length
(`lenOf`: the rows of the used length from the lane's first row on) exceeds `8 i`. `size_site`
states and proves it of one copy (one theorem per copy with literal indices, as `cp_site`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

/-- The length word of a packet. -/
def lenOf (L : Launch) (g : Nat) (v : V) : Per → BitVec 64
  | .prime => lenPrime L g v
  | _ => v.len

/-- The source size of copy row `i` of a packet. -/
def cpSize (L : Launch) (g : Nat) (v : V) (per : Per) (i : Fin 16) : Nat :=
  if scmpi .gt .s (lenOf L g v per) (8 * (i.val : Int)) = true then 16 else 0

theorem cp_size {A : List Assumption} {t : TState} {db sb r pc : Nat} {doff soff : Int} {c : Bool}
    {e : Event} {o : Option TState} {sp : AsyncCopy.Spec}
    (hf : Fires pc (eventTmpl A L g t (.cpAsync db doff sb soff 16 (.size (.reg r)) none)) e o)
    (hk : e.kind = .copy sp)
    (hr : t.regs r = some (.bits 32 (Epilogue.sel c (i32 16) (i32 0)))) :
    sp.src.size = if c = true then 16 else 0 := by
  have hz : (truncBits 32 (Epilogue.sel c (i32 16) (i32 0))).toNat =
      if c = true then 16 else 0 := by
    cases c <;> decide
  have hN : cpAsyncSourceSize L g t 16 (.size (.reg r)) =
      .ok (truncBits 32 (Epilogue.sel c (i32 16) (i32 0))).toNat :=
    cpAsyncSourceSize_size (v := truncBits 32 (Epilogue.sel c (i32 16) (i32 0)))
      (by simp [readBits, readReg, hr, bind, Except.bind, pure, Except.pure]) (by
        rw [hz]; cases c <;> decide)
  have hE : eventTmpl A L g t (.cpAsync db doff sb soff 16 (.size (.reg r)) none) =
      cpAsyncTmpl L g t (.cpAsync db doff sb soff 16 (.size (.reg r)) none) := rfl
  rw [hE] at hf
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  simp only [cpAsyncTmpl, hN, bulkPolicy, bind, Except.bind, pure, Except.pure] at hf
  rw [← hz]
  repeat' split at hf
  all_goals simp_all [ofExec, Fires, throw, throwThe, MonadExceptOf.throw]

set_option hygiene false in
/-- The theorem of one row copy. -/
macro "size_site " n:ident per:term:max b:term:max i:num c:num : command => `(
set_option maxHeartbeats 4000000 in
theorem $n {v : V} {kk : Fin 2} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (h : (code p L g w ent).AtD ⟨.cp $per $b $i $c, v, kk⟩ t)
    (hc : kernel.code[(Site.cp $per $b $i $c).pc]? = some ins)
    (hf : Fires (Site.cp $per $b $i $c).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {sp : AsyncCopy.Spec} (hk : e.kind = .copy sp) :
    sp.src.size = cpSize L g v $per $i := by
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  exact cp_size hf hk (lreg h (by lit_mem) rfl))

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
