-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Barriers
public import Kernels.TmlFa4Fwd.Proof.OutputStore

@[expose] public section

/-! # The output warp's tensor stores

A tensor store a state of the output warp fires names the O map, the stage's staging slot and
the operand words its registers hold at the state (`store_kind`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The row word of a store of stage `st` at state `d`. -/
def rowV (p : Params) (L : Launch) (g : Nat) (d : D) (st : Fin 2) : BitVec 64 :=
  let row := sub32 (add32 (coords p L g d).row d.c0) d.c1
  if st = 0 then row else addi row 128

/-- The column word of subbox `b`. -/
def colV (b : Fin 4) : BitVec 64 := [i32 0, i32 32, i32 64, i32 96].getD b.val 0

/-- The operand words of store `(st, b)` at state `d`: the column, the row, the head and the
request's end offset. -/
def storeVals (p : Params) (L : Launch) (g : Nat) (d : D) (st : Fin 2) (b : Fin 4) :
    List (BitVec 64) :=
  [truncBits 32 (colV b), truncBits 32 (rowV p L g d st), truncBits 32 (coords p L g d).head,
    truncBits 32 d.c1]

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

theorem storePc_site (st : Fin 2) (b : Fin 4) : (Site.store st b).pc = Epilogue.storePc st b := by
  fin_cases st <;> fin_cases b <;> rfl

/-- **A store of the output warp** is undefined behaviour or names the O map and the store
specification of the stage's slot and the state's operand words. -/
theorem store_kind (hp : Pre p L m) (hg : g < L.threads) {d : D} {st : Fin 2} {b : Fin 4}
    (hs : d.site = .store st b) {e : Event} {o : Option TState}
    (hf : (code p L g ent).toMachine.Fired (some d) e o) :
    (∃ f, e.kind = .ub f) ∨
      e.kind = .tensorStore p.oMapAddress
        (Epilogue.storeSpec p (Epilogue.sharedSlot L g st b) (storeVals p L g d st b)) := by
  obtain ⟨t, ins, hat, -, hc, hf⟩ := Code.fired_tmpl (stepAt hp hg) hf
  have h : At t d.site.pc (facts p L g ent d) :=
    ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩
  change kernel.code[d.site.pc]? = some ins at hc
  obtain ⟨site, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  simp only at hs
  subst hs
  rw [storePc_site, Epilogue.storeInstr] at hc
  obtain rfl := Option.some.inj hc.symm
  change Fires _ (tensorStoreTmpl L g t (Epilogue.storeOp st b)) e o at hf
  have hreg (r : Nat) (hr : r ∈ Flow.live (Site.store st b).pc) :
      t.regs r = some (valueOf p L g ent ⟨.store st b, w, dn, tl, u1, u2, u4, u8, u16, tot, grp,
        acc, gx, cur, bal, pv, nt, c0, c1⟩ r) :=
    holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hptr : t.regs 7868 = some (.ptr 64 true (.param (param 10)) 0) := by
    rw [hreg 7868 (by fin_cases st <;> fin_cases b <;> lit_mem)]; rfl
  have hbase : t.regs 2535 = some (.bits 32 (BitVec.ofNat 64 L.sharedBase)) := by
    rw [hreg 2535 (by fin_cases st <;> fin_cases b <;> lit_mem)]; rfl
  have hsecond : st = 1 ∧ b = 0 →
      t.regs 1178 = some (.bits 32 (BitVec.ofNat 64 (L.sharedBase + 68608))) := by
    rintro ⟨rfl, rfl⟩
    rw [hreg 1178 (by lit_mem)]; rfl
  have hshared := Epilogue.storeSource_of hp g t st b hbase hsecond
  have hrd (r : Nat) (x : BitVec 64) (hr : r ∈ Flow.live (Site.store st b).pc)
      (hv : valueOf p L g ent ⟨.store st b, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx,
        cur, bal, pv, nt, c0, c1⟩ r = .bits 32 x) :
      readBits L g t 32 (.reg r) = .ok (truncBits 32 x) := by
    simp only [readBits, readReg, hreg r hr, hv, bind, Except.bind, pure, Except.pure]
  have hcoords : (Epilogue.storeCoords st b).mapM (readBits L g t 32) =
      .ok (storeVals p L g ⟨.store st b, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur,
        bal, pv, nt, c0, c1⟩ st b) := by
    have h1 := hrd (Epilogue.columnReg b) (colV b)
      (by fin_cases st <;> fin_cases b <;> lit_mem)
      (by fin_cases st <;> fin_cases b <;> rfl)
    have h2 := hrd (Epilogue.rowReg st) (rowV p L g ⟨.store st b, w, dn, tl, u1, u2, u4, u8, u16,
        tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ st)
      (by fin_cases st <;> fin_cases b <;> lit_mem)
      (by fin_cases st <;> fin_cases b <;> rfl)
    have h3 := hrd 7227 _ (by fin_cases st <;> fin_cases b <;> lit_mem) rfl
    have h4 := hrd 2393 _ (by fin_cases st <;> fin_cases b <;> lit_mem) rfl
    simp only [Epilogue.storeCoords, List.mapM_cons, List.mapM_nil, h1, h2, h3, h4, bind,
      Except.bind, pure, Except.pure]
    rfl
  simp only [tensorStoreTmpl, Epilogue.storeOp] at hf
  cases hsp : tensorStoreSpec L g t (.reg 7868) (Epilogue.storeCoords st b)
      (Epilogue.stageSource st b).1 (Epilogue.stageSource st b).2 (some (.reg 7869)) .tile none
    with
  | error f =>
    simp only [hsp, ofExec, Fires, bind, Except.bind] at hf
    exact .inl ⟨f, by rw [hf.1]⟩
  | ok q =>
    obtain ⟨a, sp⟩ := q
    obtain ⟨rfl, rfl⟩ := Epilogue.storeSpec_of_ok hp st b g t hptr hcoords hshared hsp
    simp only [hsp, ofExec, Fires, bind, Except.bind, pure, Except.pure] at hf
    exact .inr (by rw [hf.1])

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue
