-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TcStLen
public import Lemmas.Flow.TcLdTmpl
public import Lemmas.Flow.NotBulk

@[expose] public section

/-! # A Tensor Memory load comes from a load instruction and returns one word per register

A proof tool. Only a `tcgen05.ld` instruction fires a Tensor Memory load event (`fires_ld_op`):
the data instructions are the only ones firing data events (`fires_tcData_op`), a wait fires its
wait, and a store's template fires no load (`tcTmpl_st_noLd`). So in a consistent execution a load
event at `pc` is of the load instruction at `pc`, and a load of a shape other than `.pack::16b`
returns one word per destination register (`get_tcLd_len`). -/

namespace PTX.Flow
open PTX PTX.EventFrame

noncomputable section

/-- A template that fires no Tensor Memory load. -/
def NoLd : Tmpl → Prop
  | .tc (.ld ..) _ | .tcLd .. => False
  | _ => True

theorem ofExec_noLd {r : Exec Tmpl} (h : AllOk NoLd r) : NoLd (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- **A store's Core template fires no load.** -/
theorem tcTmpl_st_noLd {L : Launch} {g : Nat} {u : TState} {ta : Nat} {ss : List Opnd}
    {sh : TcShape} : NoLd (tcTmpl L g u (.tcSt ta ss sh)) := by
  cases sh
  all_goals simp only [tcTmpl]
  all_goals refine ofExec_noLd ?_
  all_goals generalize List.mapM (readValue L g u 32) ss = r
  all_goals generalize readBits L g u 32 (Opnd.reg ta) = rb
  all_goals cases rb
  all_goals cases r
  all_goals split_ifs <;> simp only [AllOk, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw, pure, Except.pure]
  all_goals try split_ifs
  all_goals simp [NoLd]

/-- **A Tensor Memory load event is fired by a load instruction**, in a block of whole warps. -/
theorem fires_ld_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hb : L.block % 32 = 0)
    (hf : Fires pc (eventTmpl A L g t op) e o) {a : Nat} {vals : List Value} {sh : TcShape}
    (hk : e.kind = .tc (.ld a vals sh)) : ∃ ds ta sh' red, op = .tcLd ds ta sh' red := by
  have hd : tcDataOp op = true := fires_tcData_op hf (by simp only [isTcData, hk])
  cases op <;> simp only [tcDataOp, Bool.false_eq_true] at hd
  · exact ⟨_, _, _, _, rfl⟩
  · rw [fires_tcWaitLd hb hf] at hk
    cases hk
  · rename_i ta ss sh'
    have hm : NoLd (eventTmpl A L g t (.tcSt ta ss sh')) :=
      tcStTmpl_pres (P := NoLd) (fun _ => trivial) trivial fun _ => tcTmpl_st_noLd
    generalize eventTmpl A L g t (.tcSt ta ss sh') = tm at hm hf
    cases tm <;> simp only [NoLd] at hm <;> simp only [Fires] at hf
    all_goals first
      | (obtain ⟨rfl, -⟩ := hf; cases hk; exact (hm : False).elim)
      | (obtain ⟨rfl, -⟩ := hf; cases hk)
      | (obtain ⟨_, rfl, -⟩ := hf; cases hk)
      | (obtain ⟨_, _, rfl, -⟩ := hf; cases hk)
  · simp only [eventTmpl, tcTmpl, hb, ofExec, pure, Except.pure, ↓reduceIte] at hf
    rw [hf.1] at hk
    cases hk

variable {K : Kernel} {A : List Assumption} {L : Launch}

/-- **A Tensor Memory load event of a consistent execution is of the load instruction at its
pc**, and returns one word per destination register unless its shape is `.pack::16b`. -/
theorem get_tcLd_len {mem0 : Mem0} {X : Execution} (hb : L.block % 32 = 0)
    (hX : Consistent L K A mem0 X) {i : EvId} {e : Event} (he : X.get i = some e) {a : Nat}
    {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.ld a vals sh)) :
    ∃ ins ds ta sh' red, K.code[e.pc]? = some ins ∧ ins.op = .tcLd ds ta sh' red ∧
      (red = none → (∀ s, sh' ≠ .packed16 s) → vals.length = ds.length) := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · rw [hf] at hk; cases hk
  · obtain ⟨ds, ta, sh', red, hop⟩ := fires_ld_op hb hf hk
    refine ⟨ins, ds, ta, sh', red, hc, hop, fun hr hs => ?_⟩
    subst hr
    rw [hop] at hf
    exact fires_tcLd_len hs hf hk

end
end PTX.Flow
