-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents

@[expose] public section

/-! # Increasing block numbers in the MMA trace -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1Mma

open PTX PTX.Flow

set_option maxHeartbeats 1200000 in
private theorem advancing {P : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : next P L g d e = some (some d')) : d.i ≤ d'.i := by
  cases hs : d.site <;> simp only [next, hs] at h
  all_goals repeat' split at h
  all_goals cases h
  all_goals simp

private def floor (i : Nat) : Option Machine.ThreadD → Prop
  | some (.mma d) => i ≤ d.i
  | some (.idle _) | some .done | none => True
  | _ => False

private theorem floor_step {P : Params} {L : Launch} {g i : Nat}
    {s s' : Option Machine.ThreadD} {e : Event} (h : floor i s)
    (hn : (Machine.machine P L g).next s e = some s') : floor i s' := by
  cases s with
  | none =>
    change some none = some s' at hn
    cases hn
    trivial
  | some s =>
    change Machine.next P L g s e = some s' at hn
    cases s
    case mma d =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i d' hnext
        cases hn
        exact h.trans (advancing hnext)
      · split at hn <;> cases hn <;> trivial
      · split at hn
        all_goals cases hn
        all_goals trivial
    case idle d =>
      simp only [Machine.next] at hn
      repeat' split at hn
      all_goals cases hn
      all_goals trivial
    case done =>
      cases hn
    all_goals exact h.elim

/-- States of one MMA trace at increasing endpoints have nondecreasing block numbers. -/
theorem block_order {P : Params} {L : Launch} {X : Execution}
    {g i j : Nat} {d d' : D} (hij : i ≤ j)
    (hi : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hj : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d'))) : d.i ≤ d'.i := by
  let M := Machine.machine P L g
  change M.after M.init ((X.tr g).take i) = _ at hi
  change M.after M.init ((X.tr g).take j) = _ at hj
  let tail := ((X.tr g).take j).drop i
  have happ : (X.tr g).take i ++ tail = (X.tr g).take j := by
    dsimp [tail]
    simpa only [List.take_take, Nat.min_eq_left hij] using
      List.take_append_drop i ((X.tr g).take j)
  rw [← happ, PTX.Flow.Machine.after_append, hi] at hj
  change M.after (some (.mma d)) tail = _ at hj
  exact PTX.Flow.Machine.after_induction (M := M) (fun s _ => floor d.i s) (Nat.le_refl _)
    (fun _ _ _ _ h hn => floor_step h hn) tail _ hj

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1Mma
