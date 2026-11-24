-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MachineSound

public section

/-! # Launch machine for warpgroup 0

The lane follows the shared prologue, the warpgroup-0 hand-off, and the row-processing role.
Its terminal path follows the same event interfaces as the composed thread machine. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Flow PTX.Proof
open Machine (ThreadD)

noncomputable section

private def onWg0Route : ThreadD → Bool
  | .prologue _ | .wg0 _ | .done => true
  | _ => false

private abbrev LaunchState := { d : ThreadD // onWg0Route d = true }

private def restrictSuccessor (o : Option ThreadD) : Option LaunchState :=
  o.bind fun d => if h : onWg0Route d = true then some ⟨d, h⟩ else none

private theorem route_closed {P : Params} {L : Launch} {g : Nat} {d d' : ThreadD}
    {e : Event} (hwg : wgOf L g = 0) (hd : onWg0Route d = true)
    (hn : Machine.next P L g d e = some (some d')) : onWg0Route d' = true := by
  cases d with
  | prologue s =>
    cases hpre : _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next L g s e with
    | none => simp [Machine.next, hpre] at hn
    | some n =>
      cases n with
      | some s' =>
        simp [Machine.next, hpre] at hn
        subst d'
        rfl
      | none =>
        cases s with
        | handoff w =>
          by_cases hw : wgOf L g = w.val
          · have hw' : w = 0 := Fin.ext (hw.symm.trans hwg)
            subst w
            simp [Machine.next, hpre, hw, Machine.roleStart] at hn
            subst d'
            rfl
          · simp [Machine.next, hpre, hw] at hn
        | _ => simp [Machine.next, hpre] at hn
  | wg0 s =>
    simp only [Machine.next] at hn
    split at hn
    · simp at hn
      subst d'
      rfl
    · split_ifs at hn
      · cases hn
        rfl
      · cases hn
    · cases hn
  | done => cases hn
  | head | tma _ | idle _ | mma _ | index _ | wg2 _ => cases hd

/-- A followed warpgroup-0 lane stays in its prologue, softmax body or return state. -/
theorem state_of_wg {P : Params} {L : Launch} {g i : Nat}
    {es : List Event} {d : ThreadD} (hwg : wgOf L g = 0)
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hd : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some d)) :
    (∃ s, d = .prologue s) ∨ (∃ s, d = .wg0 s) ∨ d = .done := by
  have hRoute := ht.prefix_induction (fun q _ => ∀ z, q = some z → onWg0Route z = true)
    (by rintro z ⟨⟩; rfl) (fun q _ e q' _ h _ hn z hz => by
      subst q'
      cases q with
      | none => cases hn
      | some q => exact route_closed hwg (h q rfl) hn) i (some d) hd d rfl
  cases d <;> simp_all [onWg0Route]

private def launchCode (P : Params) (L : Launch) (g : Nat) :
    PTX.Flow.Code kernel Assumptions.all L g where
  D := LaunchState
  init := ⟨(Machine.code P L g).init, rfl⟩
  pc := fun d => (Machine.code P L g).pc d.val
  sub := fun d => (Machine.code P L g).sub d.val
  acc := fun d => (Machine.code P L g).acc d.val
  facts := fun d => (Machine.code P L g).facts d.val
  inv := fun d => (Machine.code P L g).inv d.val
  next := fun d e => (Machine.next P L g d.val e).map restrictSuccessor

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
