-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepForQPcP

@[expose] public section

/-! # The strict chain whose invariant at the window's start comes from the run's position

`strictQP_windowPc` (`Lemmas/Flow/StepForQPcP.lean`) needs the invariant `Q` at the first state of
the window for every state the machine's facts allow. A window that starts where the facts do
not fix the lane's tags (the entry of a region whose registers the lane's earlier code tagged)
takes it from the run: `hQ0` may use the position invariant `Pr t es` of the state the run
leaves, and the local steps from it to the state of the machine. -/

namespace PTX.Flow.Code
open PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- **The strict chain after a UB-tolerant prefix**, the invariant at `dk0` taken from the run
position. -/
theorem strictQPR_windowPc (hC : C.SoundU) {Q P : TState → Prop} {Wf : Event → Prop}
    {Ok : C.D → Prop} {Pr : TState → List Event → Prop}
    (hS : ∀ d e, Ok d → C.StepForQP Q P Wf d e)
    (hOk : ∀ d e d', Ok d → Wf e → e.pc = C.pc d → C.next d e = some (some d') → Ok d')
    (hP : PosStep (K := K) (A := A) (L := L) (g := g) Pr P)
    {u : TState} {es : List Event} {o : Option TState} (hr : Run K A L g u es o) :
    Pr u es → ∀ {k0 m : Nat} {d dk0 dn : C.D} {e' : Event}, C.toMachineU.Reach (some d) u →
      C.toMachine.after (some d) (es.take k0) = some (some dk0) → Ok dk0 →
      (∀ t t1 es', Pr t es' → Relation.ReflTransGen (Tau K A L g) t t1 → C.Good (some dk0) t1 →
        Q t1) → (∀ e ∈ (es.drop k0).take (m + 1), Wf e) →
      C.toMachine.after (some dk0) ((es.drop k0).take (m + 1)) = some (some dn) →
      es[k0 + (m + 1)]? = some e' →
      Ok dn ∧ ∃ t1 o', C.Good (some dn) t1 ∧ Q t1 ∧ EStep K A L g t1 e' o' := by
  induction hr with
  | nil t => intro _ k0 m d dk0 dn e' _ _ _ _ _ _ h; simp at h
  | @step t t1 t2 e0 rest o hl he hrest ih =>
    intro hPrt k0 m d dk0 dn e' hreach hafter hOkd hQ0 hW hafter2 hn
    have hg := hreach t1 hl (stops_of_estep he)
    have hgood : C.Good (some d) t1 := good_of_goodU_fires hg he
    cases k0 with
    | zero =>
      rw [List.take_zero] at hafter
      change some (some d) = some (some dk0) at hafter
      obtain rfl := Option.some.inj (Option.some.inj hafter)
      simp only [List.drop_zero, Nat.zero_add] at hW hafter2 hn
      exact strictQP_fromPc hC hS hOk hP (Run.step hl he hrest) hPrt hOkd
        ⟨t1, hl, hgood, hQ0 t t1 _ hPrt hl hgood⟩ hW hafter2 hn
    | succ k =>
      simp only [List.take_succ_cons] at hafter
      change (C.next d e0).bind _ = _ at hafter
      rcases hq : C.next d e0 with _ | _ | d1
      · rw [hq] at hafter; cases hafter
      · rw [hq] at hafter
        change C.toMachine.after none _ = _ at hafter
        rw [after_none_eq] at hafter
        cases hafter
      · rw [hq] at hafter
        change C.toMachine.after (some d1) _ = _ at hafter
        obtain ⟨mm, hm, hf⟩ := he
        have hout := hC.machine.out_eq hg
        have hf' : Fires t1.pc (C.toMachineU.tmpl (some d) t1) e0 (some t2) := by
          have : C.toMachineU.tmpl (some d) t1 = mm := by
            simp only [toMachineU, tmpl, hm]
          rw [this]; exact hf
        rcases hC.machine.step hg hf' with ⟨σ', hn', hreach'⟩ | ⟨hn', -⟩
        · have hn'' : C.next d e0 = some σ' := hn'
          rw [hq] at hn''
          obtain rfl := Option.some.inj hn''
          simp only [List.drop_succ_cons] at hW hafter2
          rw [Nat.succ_add] at hn
          simp only [List.getElem?_cons_succ] at hn
          exact ih (hP hPrt hl ⟨mm, hm, hf⟩).1 hreach' hafter hOkd hQ0 hW hafter2 hn
        · have hn'' : C.next d e0 = none := hn'
          rw [hq] at hn''; cases hn''
  | @last t t1 e hl he =>
    intro _ k0 m d dk0 dn e' hreach hafter hOkd hQ0 hW hafter2 hn
    cases k0 with
    | zero => simp at hn
    | succ k => rw [Nat.succ_add] at hn; simp at hn

end

end PTX.Flow.Code
