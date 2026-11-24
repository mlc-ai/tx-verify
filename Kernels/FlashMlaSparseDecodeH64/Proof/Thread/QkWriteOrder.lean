-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaBlockOrder

@[expose] public section

/-! # The last QK issue is the last score writer of its block -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QkWriteOrder

open PTX.Flow Wg1Mma

noncomputable section

variable {P : Params} {L : Launch} {X : Execution} {g : Nat}

private def phase : Wg1Mma.Site → Nat
  | .qkMma k => k.val + 1
  | .qkCommit | .soWait | .soFence | .pvMma _ | .pvCommit | .outBar | .exit => 17
  | _ => 0

private def rank (d : D) : Nat := 18 * d.i + phase d.site

set_option maxHeartbeats 1200000 in
private theorem role_rank {d d' : D} {e : Event}
    (hn : Wg1Mma.next P L g d e = some (some d')) : rank d ≤ rank d' := by
  cases hd : d.site <;> simp only [Wg1Mma.next, hd, Wg1Mma.nextSite] at hn
  case qkMma k =>
    have hk := k.isLt
    split at hn <;> cases hn <;> simp [rank, phase, hd]
    all_goals omega
  case pvCommit =>
    split at hn <;> cases hn <;> simp [rank, phase, hd]
    all_goals omega
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp only [rank, phase, hd, Wg1Mma.startSite, Wg1Mma.afterTopk]
  all_goals repeat' split_ifs
  all_goals simp_all

private def floor (n : Nat) : Option (Option Machine.ThreadD) → Prop
  | some (some (.mma d)) => n ≤ rank d
  | some (some (.idle _)) | some (some .done) | some none | none => True
  | _ => False

private theorem next_floor {n : Nat} {s : Machine.ThreadD} {e : Event}
    (h : floor n (some (some s))) : floor n (Machine.next P L g s e) := by
  cases s
  case mma d =>
    simp only [Machine.next]
    split
    · rename_i q hnext
      exact h.trans (role_rank hnext)
    · split_ifs <;> trivial
    · split_ifs <;> trivial
  case idle d =>
    simp only [Machine.next]
    split
    · trivial
    · trivial
    · split_ifs <;> trivial
  case done => trivial
  all_goals exact h.elim

private theorem frame_floor {i j n : Nat} (hij : i ≤ j) (hj : j ≤ (X.tr g).length)
    (h : floor n (Frame.stateAt (Machine.code P L) X g i)) :
    floor n (Frame.stateAt (Machine.code P L) X g j) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => exact h
  | succ d ih =>
    have hlt : i + d < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[i + d]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hp := ih hlt.le
    rw [Nat.add_succ, Frame.stateAt_succ he]
    cases hh : Frame.stateAt (Machine.code P L) X g (i + d) with
    | none => trivial
    | some s =>
      cases s with
      | none => trivial
      | some s =>
        rw [hh] at hp
        exact next_floor hp

/-- Any score-writing stage at or before the last issue of a given block, by block ordinal,
is at or before that actual last issue in the elected issuer's trace. -/
theorem no_later_same_block_writer {i j : Nat} {d q : D} {k : Fin 16} {e : Event}
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.mma q)))
    (hsite : d.site = .qkMma 15) (hother : q.site = .qkMma k)
    (hb : q.i ≤ d.i) (hj : j ≤ (X.tr g).length) : j ≤ i := by
  by_contra hn
  have hlt : i < j := by omega
  have hnxt : Frame.stateAt (Machine.code P L) X g (i + 1) =
      some (some (.mma { d with site := .qkCommit })) := by
    rw [Frame.stateAt_succ he, hd]
    change Machine.next P L g (.mma d) e = _
    rw [Machine.next, Wg1Mma.next, hsite]
    rfl
  have hp : floor (18 * d.i + 17) (Frame.stateAt (Machine.code P L) X g (i + 1)) := by
    rw [hnxt]
    exact Nat.le_refl _
  have hfloor := frame_floor hlt hj hp
  rw [hq] at hfloor
  change 18 * d.i + 17 ≤ rank q at hfloor
  rw [rank, hother] at hfloor
  change 18 * d.i + 17 ≤ 18 * q.i + (k.val + 1) at hfloor
  have hk := k.isLt
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QkWriteOrder
