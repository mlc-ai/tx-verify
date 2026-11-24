-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MachineSound

public section

/-! # The launch machine of the index producer warp

Each warp-7 lane follows the shared prologue and dispatch, publishes its index and mask data,
and reaches the final return. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1Index
open PTX PTX.Flow PTX.Proof
open Machine (ThreadD)

noncomputable section

private def onIndexRoute : ThreadD → Bool
  | .prologue _ | .head | .index _ | .done => true
  | _ => false

private abbrev LaunchState := { d : ThreadD // onIndexRoute d = true }

private def restrictSuccessor (o : Option ThreadD) : Option LaunchState :=
  o.bind fun d => if h : onIndexRoute d = true then some ⟨d, h⟩ else none

private theorem route_closed {P : Params} {L : Launch} {g : Nat} {d d' : ThreadD}
    {e : Event} (hwarp : warpOf L g = 7) (hd : onIndexRoute d = true)
    (hn : Machine.next P L g d e = some (some d')) : onIndexRoute d' = true := by
  have hgroup : wgOf L g = 1 := by unfold wgOf warpOf at *; omega
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
          · have hw' : w = 1 := Fin.ext (hw.symm.trans hgroup)
            subst w
            simp [Machine.next, hpre, hw, Machine.roleStart] at hn
            subst d'
            rfl
          · simp [Machine.next, hpre, hw] at hn
        | _ => simp [Machine.next, hpre] at hn
  | head =>
    cases he : e.kind <;> simp [Machine.next, he, Machine.headStart, hwarp] at hn
    exact hn.2 ▸ rfl
  | index d =>
    simp only [Machine.next] at hn
    split at hn
    · simp at hn
      subst d'
      rfl
    · split_ifs at hn
      · simp at hn
        subst d'
        rfl
      · simp at hn
    · cases hn
  | done => cases hn
  | wg0 _ | mma _ | tma _ | idle _ | wg2 _ => cases hd

/-- At any followed prefix, a warp-7 lane stays on its prologue, index or closing route. -/
theorem state_of_warp {P : Params} {L : Launch} {g i : Nat}
    {es : List Event} {d : ThreadD} (hwarp : warpOf L g = 7)
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hd : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some d)) :
    (∃ s, d = .prologue s) ∨ d = .head ∨ (∃ s, d = .index s) ∨ d = .done := by
  have hRoute := ht.prefix_induction (fun q _ => ∀ z, q = some z → onIndexRoute z = true)
    (by rintro z ⟨⟩; rfl) (fun q _ e q' _ h _ hn z hz => by
      subst q'
      cases q with
      | none => cases hn
      | some q => exact route_closed hwarp (h q rfl) hn) i (some d) hd d rfl
  cases d <;> simp_all [onIndexRoute]

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
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1Index
