-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.OutCoreRules
public import Tests.Gen.Out.ExpoRules

@[expose] public section

/-! # tml-fa4's assumptions read Core's integer forms, for `Tests/Gen/Out/Core.lean`

The lemma `Tools/out_gen.py` names for the Core forms of `Tests/Gen/Out/core.json`: no assumption
of tml-fa4 has a local rule for an instruction that is neither a bias widening nor a probability
pack (`noRule`). -/

namespace PTX.Tests.Gen.CoreRules
open PTX PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

variable {l : Launch} {g : Nat}

/-- No assumption of tml-fa4 has a local rule for an integer instruction. -/
theorem noRuleInt {op : Op} (pc : Nat)
    (hk : (match op with | .int _ => true | _ => false) = true := by exact rfl) :
    NoLocalRule Assumptions.all l g pc op := by
  cases op <;> simp at hk
  intro s _ a ha
  simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- No assumption of tml-fa4 has a local rule for a move. -/
theorem noRuleMove {op : Op} (pc : Nat)
    (hk : (match op with | .move _ => true | _ => false) = true := by exact rfl) :
    NoLocalRule Assumptions.all l g pc op := by
  cases op <;> simp at hk
  exact fun s _ => PTX.Tests.Gen.ExpoRules.moveNone s _

/-- No assumption of tml-fa4 has a local rule for a conversion that is neither a bias widening,
a probability pack, nor an ideal or approximate form. -/
theorem noRuleCvt {op : Op} (pc : Nat)
    (hk : (match op with | .cvt _ => true | _ => false) = true := by exact rfl)
    (hb : Assumptions.biasWidenOperands op = none := by exact rfl)
    (hp : Assumptions.probPackOperands op = none := by exact rfl)
    (hi : FloatForm.ofOp op = none := by exact rfl)
    (ha : ApproxForm.ofOp op = none := by exact rfl) :
    NoLocalRule Assumptions.all l g pc op := by
  cases op <;> simp at hk
  intro s _ a h
  simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact idealReal_localRule_none fun f hf => by rw [hi] at hf; cases hf
  · exact approxExact_localRule_none fun f hf => by rw [ha] at hf; cases hf
  all_goals first
    | rfl
    | simp [Assumptions.bf16Convert, hb, hp, bind, Option.bind]

theorem rule_mov {d a : Nat} (_pc : Nat) :
    ∀ s : TState, s.pc = _pc → (XItem.base (.mov d a)).Rule Assumptions.all l g s :=
  fun s _ => PTX.Tests.Gen.ExpoRules.moveNone s _

end PTX.Tests.Gen.CoreRules
