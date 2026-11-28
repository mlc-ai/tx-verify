-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TcStLen

@[expose] public section

/-! # An unpacked `tcgen05.st` of any shape stores one word per source register

A proof tool beside `Lemmas/Flow/TcStLen.lean`, which has the `32x32b` shape only: a store event of
a shape that is not `.packed16` has as many values as its instruction has source operands. -/

namespace PTX.Flow
open PTX PTX.EventFrame

noncomputable section

/-- A template whose unpacked store event, if any, stores `n` values. -/
def StLenAny (n : Nat) : Tmpl → Prop
  | .tc (.st _ vals sh) _ => (∀ s, sh ≠ .packed16 s) → vals.length = n
  | _ => True

theorem ofExec_stLenAny {n : Nat} {r : Exec Tmpl} (h : AllOk (StLenAny n) r) :
    StLenAny n (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

theorem tcTmpl_stLenAny {L : Launch} {g : Nat} {u : TState} {ta : Nat} {ss : List Opnd}
    {sh : TcShape} : StLenAny ss.length (tcTmpl L g u (.tcSt ta ss sh)) := by
  by_cases hn : ∀ s, sh ≠ .packed16 s
  · rw [tcTmpl_tcSt_plain hn]
    refine ofExec_stLenAny ?_
    generalize hv : List.mapM (readValue L g u 32) ss = r
    generalize readBits L g u 32 (Opnd.reg ta) = rb
    cases rb
    all_goals cases r with
      | error x => ?_
      | ok vals => ?_
    all_goals try have hl := except_mapM_length hv
    all_goals split_ifs <;> simp only [AllOk, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw, pure, Except.pure]
    all_goals try split_ifs
    all_goals simp [StLenAny, *]
  · push Not at hn
    obtain ⟨s, rfl⟩ := hn
    simp only [tcTmpl]
    refine ofExec_stLenAny ?_
    generalize List.mapM (readValue L g u 32) ss = r
    generalize readBits L g u 32 (Opnd.reg ta) = rb
    cases rb <;> cases r <;> simp [AllOk, StLenAny, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw, pure, Except.pure] <;> split_ifs <;> simp

/-- **An unpacked store event fired by an instruction stores one value per source operand.** -/
theorem fires_tcSt_lenAny {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.st a vals sh))
    (hn : ∀ s, sh ≠ .packed16 s) :
    ∃ ta ss sh', op = .tcSt ta ss sh' ∧ vals.length = ss.length := by
  have hop := fires_tcSt_op hf hk
  cases op <;> simp only [tcStOp, Bool.false_eq_true] at hop
  rename_i ta ss sh'
  refine ⟨ta, ss, sh', rfl, ?_⟩
  have hm : StLenAny ss.length (eventTmpl A L g t (.tcSt ta ss sh')) := by
    exact tcStTmpl_pres (P := StLenAny ss.length) (fun _ => trivial) trivial fun _ =>
      tcTmpl_stLenAny
  generalize eventTmpl A L g t (.tcSt ta ss sh') = tm at hm hf
  cases tm <;> simp only [Fires] at hf
  all_goals first
    | (obtain ⟨rfl, -⟩ := hf; cases hk)
    | (obtain ⟨_, rfl, -⟩ := hf; cases hk)
    | (obtain ⟨_, _, rfl, -⟩ := hf; cases hk)
  exact hm hn

variable {K : Kernel} {A : List Assumption} {L : Launch}

/-- **An unpacked store event of a consistent execution stores one value per source operand of
the instruction at its pc.** -/
theorem get_tcSt_lenAny {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X) {i : EvId}
    {e : Event} (he : X.get i = some e) {a : Nat} {vals : List Value} {sh : TcShape}
    (hk : e.kind = .tc (.st a vals sh)) (hn : ∀ s, sh ≠ .packed16 s) :
    ∃ ins ta ss sh', K.code[e.pc]? = some ins ∧ ins.op = .tcSt ta ss sh' ∧
      vals.length = ss.length := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · rw [hf] at hk; cases hk
  · obtain ⟨ta, ss, sh', hop, hl⟩ := fires_tcSt_lenAny hf hk hn
    exact ⟨ins, ta, ss, sh', hc, hop, hl⟩

end
end PTX.Flow
