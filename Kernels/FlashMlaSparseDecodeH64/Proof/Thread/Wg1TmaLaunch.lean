-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MachineSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1TmaLeader

public section

/-! # The route of the TMA producer warp

The warp-5 thread follows the shared prologue and dispatch. An elected lane follows the TMA role
and reaches the final return; it never enters the idle role (`elected_state_of_warp`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1Tma
open PTX PTX.Flow PTX.Proof
open Machine (ThreadD)

noncomputable section

private def onTmaRoute : ThreadD → Bool
  | .prologue _ | .head | .tma _ | .idle _ | .done => true
  | _ => false

private theorem route_closed {P : Params} {L : Launch} {g : Nat} {d d' : ThreadD}
    {e : Event} (hwarp : warpOf L g = 5) (hd : onTmaRoute d = true)
    (hn : Machine.next P L g d e = some (some d')) : onTmaRoute d' = true := by
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
  | tma d =>
    simp only [Machine.next] at hn
    split at hn
    · simp at hn
      subst d'
      rfl
    · split_ifs at hn <;> simp at hn <;> subst d' <;> rfl
    · split_ifs at hn
      simp at hn
      subst d'
      rfl
  | idle s =>
    simp only [Machine.next] at hn
    split at hn
    · simp at hn
      subst d'
      rfl
    · cases hn
    · split_ifs at hn
      simp at hn
      subst d'
      rfl
  | done => cases hn
  | wg0 _ | mma _ | index _ | wg2 _ => cases hd

variable {P : Params} {L : Launch}

private theorem no_idle_next {g : Nat} {d : ThreadD} {e : Event} {s : Thread.Site}
    {o : Option TState} (hw : warpOf L g = 5) (hb : onTmaRoute d = true) (hnIdle : ∀ s, d ≠ .idle s)
    (hKeep : ∀ inst leader, e.kind = .elect 4294967295 inst leader → leader = PTX.laneOf L g)
    (hf : (Machine.machine P L g).Fired (some d) e o)
    (hn : Machine.next P L g d e = some (some (.idle s))) : False := by
  have hGroup : wgOf L g = 1 := by unfold wgOf warpOf at *; omega
  cases d with
  | prologue q =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        by_cases hEq : wgOf L g = w.val
        · have hw' : w = 1 := Fin.ext (hEq.symm.trans hGroup)
          subst w
          simp [hGroup, Machine.roleStart] at hn
        · simp [hEq] at hn
      · cases hn
    · cases hn
  | head =>
    cases he : e.kind <;> simp [Machine.next, he, Machine.headStart, hw] at hn
  | tma q =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · cases hn
      · split at hn
        · rename_i hLost
          have hSite := hLost.1
          have hl := hLost.2
          cases he : e.kind <;> simp only [Machine.lostElection, he, Bool.false_eq_true] at hl
          rename_i mask inst leader
          have hMask := Wg1TmaLeader.full_mask hSite hf he
          rw [hMask] at he
          simp [hKeep inst leader he] at hl
        · cases hn
    · split at hn <;> cases hn
  | idle v => exact hnIdle v rfl
  | done => cases hn
  | wg0 _ | mma _ | index _ | wg2 _ => cases hb

/-- The elected warp-5 lane cannot enter the idle path. -/
theorem elected_state_of_warp {g i : Nat} {es : List Event} {d : ThreadD} (hw : warpOf L g = 5)
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hd : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) = some (some d))
    (hKeep : ∀ e ∈ es, ∀ inst leader, e.kind = .elect 4294967295 inst leader →
      leader = PTX.laneOf L g) :
    (∃ s, d = .prologue s) ∨ d = .head ∨ (∃ q, d = .tma q) ∨ d = .done := by
  let Q (q : Option ThreadD) (pre : List Event) : Prop :=
    (∀ e ∈ pre, ∀ inst leader, e.kind = .elect 4294967295 inst leader →
      leader = PTX.laneOf L g) →
    ∀ z, q = some z → onTmaRoute z = true ∧ ∀ s, z ≠ .idle s
  have hInit : Q (Machine.machine P L g).init [] := by
    rintro _ z ⟨⟩
    exact ⟨rfl, by intro s h; cases h⟩
  have hStep : ∀ q pre e q' o, Q q pre → (Machine.machine P L g).Fired q e o →
      (Machine.machine P L g).next q e = some q' → Q q' (pre ++ [e]) := by
    intro q pre e q' o hQ hf hn hAll z hz
    subst q'
    cases q with
    | none => cases hn
    | some q =>
      obtain ⟨hRoute, hIdle⟩ := hQ (fun f hf => hAll f (List.mem_append_left _ hf)) q rfl
      refine ⟨route_closed hw hRoute hn, fun s he => ?_⟩
      subst z
      exact no_idle_next hw hRoute hIdle (hAll e (by simp)) hf hn
  obtain ⟨hRoute, hIdle⟩ := ht.prefix_induction Q hInit hStep i (some d) hd
    (fun e he => hKeep e (List.mem_of_mem_take he)) d rfl
  cases d <;> simp_all [onTmaRoute]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1Tma
