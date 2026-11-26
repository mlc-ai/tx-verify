-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotTcSt
public import Lemmas.Flow.NotTcShift
public import Lemmas.Flow.NotBulk

@[expose] public section

/-! # A Tensor Memory store writes one word per source register; no shift without its instruction

A proof tool. A `tcgen05.st` of an unpacked `32x32b` shape fires a store event whose values are
the source registers' words, one per register (`fires_tcSt_len`), so in a consistent execution a
`32x32b` store event at `pc` has as many values as the instruction at `pc` has source operands
(`get_tcSt_len`). A kernel without `tcgen05.shift` fires no shift (`no_shift_of_code`). -/

namespace PTX.Flow
open PTX PTX.EventFrame

noncomputable section

/-- A template whose `32x32b` store event, if any, stores `n` values. -/
def StLen (n : Nat) : Tmpl → Prop
  | .tc (.st _ vals .s32x32b) _ => vals.length = n
  | _ => True

/-- A `mapM` into `Except` that succeeds keeps the length. -/
theorem except_mapM_length {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → r.length = l.length
  | [], r, h => by
    simp only [List.mapM_nil] at h
    cases h
    rfl
  | a :: l, r, h => by
    simp only [List.mapM_cons] at h
    cases hfa : f a with
    | error x =>
      rw [hfa] at h
      cases h
    | ok b =>
      rw [hfa] at h
      cases hl : l.mapM f with
      | error x =>
        rw [hl] at h
        cases h
      | ok rs =>
        rw [hl] at h
        cases h
        simp [except_mapM_length hl]

theorem ofExec_stLen {n : Nat} {r : Exec Tmpl} (h : AllOk (StLen n) r) : StLen n (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- **The store template stores one value per source operand.** -/
theorem tcTmpl_stLen {L : Launch} {g : Nat} {u : TState} {ta : Nat} {ss : List Opnd}
    {sh : TcShape} : StLen ss.length (tcTmpl L g u (.tcSt ta ss sh)) := by
  cases sh
  all_goals simp only [tcTmpl]
  all_goals refine ofExec_stLen ?_
  all_goals generalize hv : List.mapM (readValue L g u 32) ss = r
  all_goals generalize readBits L g u 32 (Opnd.reg ta) = rb
  all_goals cases rb
  all_goals cases r with
    | error x => ?_
    | ok vals => ?_
  all_goals try have hl := except_mapM_length hv
  all_goals split_ifs <;> simp only [AllOk, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw, pure, Except.pure]
  all_goals try split_ifs
  all_goals simp [StLen, *]

/-- **A `32x32b` store fired by an instruction stores one value per source operand of the
instruction.** -/
theorem fires_tcSt_len {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {a : Nat} {vals : List Value} (hk : e.kind = .tc (.st a vals .s32x32b)) :
    ∃ ta ss sh, op = .tcSt ta ss sh ∧ vals.length = ss.length := by
  have hop := fires_tcSt_op hf hk
  cases op <;> simp only [tcStOp, Bool.false_eq_true] at hop
  rename_i ta ss sh
  refine ⟨ta, ss, sh, rfl, ?_⟩
  have hm : StLen ss.length (eventTmpl A L g t (.tcSt ta ss sh)) :=
    tcStTmpl_pres (P := StLen ss.length) (fun _ => trivial) trivial fun _ => tcTmpl_stLen
  generalize eventTmpl A L g t (.tcSt ta ss sh) = tm at hm hf
  cases tm <;> simp only [Fires] at hf
  all_goals first
    | (obtain ⟨rfl, -⟩ := hf; cases hk)
    | (obtain ⟨_, rfl, -⟩ := hf; cases hk)
    | (obtain ⟨_, _, rfl, -⟩ := hf; cases hk)
  exact hm

variable {K : Kernel} {A : List Assumption} {L : Launch}

/-- **A `32x32b` store event of a consistent execution stores one value per source operand of
the instruction at its pc.** -/
theorem get_tcSt_len {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X) {i : EvId}
    {e : Event} (he : X.get i = some e) {a : Nat} {vals : List Value}
    (hk : e.kind = .tc (.st a vals .s32x32b)) :
    ∃ ins ta ss sh, K.code[e.pc]? = some ins ∧ ins.op = .tcSt ta ss sh ∧
      vals.length = ss.length := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · rw [hf] at hk; cases hk
  · obtain ⟨ta, ss, sh, hop, hl⟩ := fires_tcSt_len hf hk
    exact ⟨ins, ta, ss, sh, hc, hop, hl⟩

/-- **A kernel without `tcgen05.shift` fires no shift.** -/
theorem no_shift_of_code {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X)
    (hK : K.code.all (fun ins => !tcShiftOp ins.op) = true) {i : EvId} {e : Event}
    (he : X.get i = some e) (s : TcShift.Spec) : e.kind ≠ .tc (.shift s) := fun h =>
  no_kind_of_code hX tcShiftOp (fun k => ∃ s, k = .tc (.shift s))
    (fun _ ⟨_, hb⟩ => by cases hb) (fun hf ⟨_, hb⟩ => fires_tcShift_op hf hb) hK he ⟨s, h⟩

end
end PTX.Flow
