-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Store
public import Lemmas.Flow.Local
public import Lemmas.Execution.EventFrameSource
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Definitions and helper facts of the store warp's step lemmas: the conclusion of a step
(`Step`), the continuation of an arrival that writes its state register, and the segment
tactic `store_seg`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Store
open PTX PTX.Proof PTX.Flow PTX.EventFrame

noncomputable section
set_option maxRecDepth 100000

/-- The conclusion of a step of this role, under the assumptions `A`: the thread leaves the
role, or steps to `d'` at `t'` by a run of `Tau`. -/
def Step (A : List Assumption) (L : Launch) (g : Nat) (d : D) (e : Event) (u : TState) :
    Prop :=
  next L g d e = some none ∨ ∃ d' t', next L g d e = some (some d') ∧
    Relation.ReflTransGen (Tau kernel A L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
      Inv L g d'

/-- The value of `r` in state `d`, with the registers of `ex` valued as given (predicates
and intermediate values at a checkpoint inside a segment). -/
def valueX (L : Launch) (g : Nat) (d : D) (ex : List (Nat × Value)) (r : Nat) : Value :=
  (ex.lookup r).getD (valueOf L g d r)

/-- The facts at `pc` under `valueX`. -/
def factsX (L : Launch) (g pc : Nat) (d : D) (ex : List (Nat × Value)) :
    List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueX L g d ex)

theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

theorem facts_ne {L : Launch} {g pc : Nat} {d : D} {r : Nat} (hr : r ∉ Flow.live pc) :
    ∀ p ∈ factsAt L g pc d, p.1 ≠ r := by
  intro p hp he
  simp only [factsAt, Flow.factsFrom, List.mem_map] at hp
  obtain ⟨r', hr', rfl⟩ := hp
  exact hr (he ▸ hr')

/-- After an arrival with a state destination the thread is in `next` of the state with the
destination cleared, and the event is an arrival on the object its address evaluates to. -/
theorem fires_arrive_state {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {base : Nat} {off : Int} {tx count : Opnd} {cluster release : Bool} {scope : MbarScope}
    {state : Option Nat} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t
      (.mbarArrive base off tx count cluster release scope state)) e (some u)) :
    u = PTX.next (mbarStateDest t state) ∧
      ∃ m tx' c rel sc, e.kind = .arrive m tx' c rel sc ∧
        ((if cluster then mbarClusterLoc L g t base off else mbarLoc L g t base off) = .ok m) ∧
        ∃ b, readBits L g t 32 tx = .ok b ∧ tx' = b.toNat := by
  simp only [eventTmpl, tmaTmpl, bind, Except.bind, pure, Except.pure] at hf
  cases hm : (if cluster then mbarClusterLoc L g t base off else mbarLoc L g t base off) with
  | error f =>
    cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
      simp only [Bool.false_eq_true, ↓reduceIte, hm, ofExec, widenMbarScope, ite_self,
        Fires] at hf <;> simp at hf
  | ok m =>
    cases hb : readBits L g t 32 tx with
    | error f =>
      cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
        simp only [Bool.false_eq_true, ↓reduceIte, hm, hb, ofExec, widenMbarScope, ite_self,
          Fires] at hf <;> simp at hf
    | ok bytes =>
      cases hn : readBits L g t 32 count with
      | error f =>
        cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
          simp only [Bool.false_eq_true, ↓reduceIte, hm, hb, hn, ofExec, widenMbarScope,
            ite_self, Fires] at hf <;> simp at hf
      | ok n =>
        cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
          simp only [Bool.false_eq_true, ↓reduceIte, hm, hb, hn, ofExec] at hf <;>
          cases release <;> cases scope <;> simp only [widenMbarScope] at hf <;>
          split_ifs at hf <;>
          exact ⟨Option.some.inj hf.2, _, _, _, _, _, by rw [hf.1], by simp,
            bytes, rfl, rfl⟩

/-- A TMA store instruction that continues fired a tensor store, and continues at the next
instruction. -/
theorem fires_tensorStore {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {map : Opnd} {src : Nat} {cs : List Opnd} {off : Int} {policy : Option Opnd} {mode : TensorMode}
    {reduce : Option AtomOp} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.cpTensorStore map cs src off policy mode reduce)) e
      (some u)) :
    u = PTX.next t ∧ ∃ a sp, e.kind = .tensorStore a sp := by
  simp only [eventTmpl, tensorStoreTmpl, bind, Except.bind, pure, Except.pure] at hf
  cases h : tensorStoreSpec L g t map cs src off policy mode reduce with
  | error f => simp [h, ofExec, Fires] at hf
  | ok p =>
    obtain ⟨a, sp⟩ := p
    simp only [h, ofExec, Fires] at hf
    exact ⟨Option.some.inj hf.2, a, sp, by rw [hf.1]⟩

/-- A bulk wait continues at the next instruction and fires its wait. -/
theorem fires_bulkWait {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {mode : BulkGroup.WaitMode} {n pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.bulkWait mode n)) e (some u)) :
    u = PTX.next t ∧ e = ⟨pc, .bulkWait mode n⟩ := by
  simp only [eventTmpl, tensorStoreTmpl, Fires] at hf
  exact ⟨Option.some.inj hf.2, hf.1⟩

/-- A bulk commit continues at the next instruction and fires its commit. -/
theorem fires_bulkCommit' {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {pc : Nat} {e : Event} (hf : Fires pc (eventTmpl A L g t .bulkCommit) e (some u)) :
    u = PTX.next t ∧ e = ⟨pc, .bulkCommit⟩ := by
  simp only [eventTmpl, tensorStoreTmpl, Fires] at hf
  exact ⟨Option.some.inj hf.2, hf.1⟩

/-- Clearing a register no fact names keeps the facts. -/
theorem At.clear {t : TState} {pc r : Nat} {F : List (Nat × Value)} (h : At t pc F)
    (hr : ∀ p ∈ F, p.1 ≠ r) : At (PTX.next (mbarStateDest t (some r))) (pc + 1) F :=
  ⟨congrArg (· + 1) h.1, h.2.1, h.2.2.1, h.2.2.2.1, holds_update h.2.2.2.2 hr⟩

/-- Evaluate a store segment from `h` and close the facts of its end state: by unfolding the
code's terms (`rfl`), the quotient's `mul.hi` operand order, or the normal form of integer
values (shared addresses, bounded by `Pre.sharedRange`). -/
syntax "store_seg" term:max term:max : tactic
macro_rules
  | `(tactic| store_seg $h $hpre) => `(tactic| (
      have hbase := ($hpre).sharedRange
      unfold sharedBytes at hbase
      seg_fp $h using
        try simp only [valueX, valueOf, table, PTX.Flow.lookupLit, Option.getD_some,
          Option.getD_none]
        all_goals (try launch_norm $hpre)
        all_goals first
          | w_rfl_deep [orowW, ctaOf, Work.rank]
          | seg_close [Prologue.sb]))

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Store
