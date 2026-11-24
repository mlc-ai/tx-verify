-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface
public import Lemmas.Arith.RankItems

@[expose] public section

/-! # The shape of the ranks

A thread's rank bounds the counted events it has left (`Frame.bound_of_rank`). Every role walks
its cluster's items, each made of a fixed part and one block of events per KV trip; the rank of a
role state is `perItem L * (B - i) + 64 + pos` for item `i` of the role's `B` items, with the
position `pos` of the state in its item below `perItem L = 256 (n + 1)` (`n` KV trips): every
role has fewer than `256` counted events per trip and in the fixed part of an item. After its
items a role is in its tail, of rank below `64`; before them, at its entry, of rank below
`cap L`, the rank of the first item plus one block. The prologue's rank is `cap L + 256` minus
its position.

Transitions that move to the next trip or item are guarded by the trip count or the item count,
as the machines' are, so a state out of range steps to the end of the loop or to the tail, of
smaller rank; no invariant is needed. A failed poll leaves the state unchanged and is not
counted (`counts_wait`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Bound
open PTX PTX.Proof

noncomputable section

/-- The KV trips of an item, `⌈sk / 128⌉`, as every role's machine computes them. -/
abbrev trips (L : Launch) : Nat := (skOf L + 127) / 128

/-- The rank of one item: above the counted events of any role in an item. -/
abbrev perItem (L : Launch) : Nat := 256 * (trips L + 1)

/-- A bound on the rank of every role's first state. -/
def cap (L : Launch) : Nat := perItem L * (totOf L + 1) + 64

/-- The uniform bound on the threads' initial ranks. -/
def N (P : Params) : Nat := 256 + 256 * (P.sk / 128 + 1) * (P.items + 1) + 64

theorem perItem_ge (L : Launch) : 256 ≤ perItem L := by
  unfold perItem
  omega

/-- An event counts at most once. -/
theorem counts_le (e : Event) : (if e.counts then 1 else 0) ≤ 1 := by
  split <;> omega

/-- A poll counts exactly when it succeeds. -/
theorem counts_wait {e : Event} {m : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hk : e.kind = .wait m p ok acq sc) : e.counts = ok := by
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  cases ok <;> rfl

/-- A role's item rank is at most `cap` once its items are at most the item count. -/
theorem entry_le {L : Launch} {B x : Nat} (hB : B ≤ totOf L) (hx : x ≤ perItem L + 64) :
    perItem L * B + x ≤ cap L := by
  unfold cap
  have := Nat.mul_le_mul_left (perItem L) hB
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- Under the precondition `cap` is the uniform bound less the prologue's `256`. -/
theorem cap_eq {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    cap L + 256 = N P := by
  have hs := skOf_eq hpre
  have ht := totOf_eq hpre
  have hk := hpre.skDiv128
  have hr := hpre.scheduleRange
  have htr : trips L = P.sk / 128 := by unfold trips; omega
  have hto : totOf L = P.items := by omega
  unfold cap N perItem
  rw [htr, hto]
  omega

/-- Closes a rank step: rewrites a poll's count by its success, splits the conditions of the
successor and compares the ranks (unfolded by the given lemmas), with one block of the role's
item count `B` freed when the step moves to the next item. -/
syntax "rk_close" "[" Lean.Parser.Tactic.simpLemma,* "]" term:max : tactic
macro_rules
  | `(tactic| rk_close [$l,*] $B) => `(tactic| (
      (try rw [counts_wait (by assumption)])
      (try split_ifs) <;>
        simp only [$l,*, Nat.sub_zero, Bool.false_eq_true, ↓reduceIte, Fin.reduceFinMk,
          Fin.zero_eta, Fin.mk_one, Fin.isValue, Nat.reduceAdd, Nat.reduceLT] <;>
        (try have := RankItems.mul_sub_succ (perItem ‹Launch›) (B := $B) (by assumption)) <;>
        (have _hQ := perItem_ge ‹Launch›) <;>
        first | omega | exact absurd trivial ‹¬True›))

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Bound
