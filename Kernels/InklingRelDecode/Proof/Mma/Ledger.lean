-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Machine

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The number of loop blocks after the entry check. -/
def runCount (n : Nat) : Nat := if n ≤ 2147483646 then n else 0

/-- Per-channel positions in the trace of the MMA lane. -/
def polls (d : D) : Nat × Nat :=
  let i := d.i
  let n := d.limit
  match d.site with
  | .setMaxReg | .ldNum | .bar0 => (0, 0)
  | .qkBar | .kvWait => (i, i - 1)
  | .qkShfl | .qkBar2 | .qkSkip | .qkElect | .qk _ | .qkCommit => (i + 1, i - 1)
  | .pvBar | .pWait => (min (i + 1) n, i - 1)
  | .pvShfl | .pvBar2 | .pvSkip | .pvElect | .pv _ | .pvCommit1 | .pvCommit2 =>
    (min (i + 1) n, i)
  | _ => (runCount n, runCount n)

/-- Each successful poll leads directly to a broadcast. -/
def broadcasts (d : D) : Nat :=
  (polls d).1 + (polls d).2 - (match d.site with | .qkShfl | .pvShfl => 1 | _ => 0)

theorem wait_counts (i : Nat) (w : Value) :
    polls ⟨.kvWait,i,w⟩ = (i, i - 1) ∧ polls ⟨.pWait,i,w⟩ = (min (i + 1) (low w), i - 1) :=
  ⟨rfl, rfl⟩

theorem return_counts (i : Nat) (w : Value) :
    broadcasts ⟨.dispatch,i,w⟩ = 2 * runCount (low w) := by
  simp [broadcasts, polls, D.limit, Nat.two_mul]

private theorem polls_iter (d : D) (hi : d.i ≤ d.limit) (hn : d.limit ≤ 2147483646) :
    polls (iterNext d) = (min (d.i + 1) d.limit, d.i) := by
  obtain ⟨s,i,w⟩ := d
  simp only [iterNext, D.limit] at *
  by_cases he : i = low w <;> by_cases hl : i + 1 < low w <;>
    simp [he, hl, polls, D.limit, runCount, hn] <;> omega

private theorem polls_after (d : D) (hi : d.i < d.limit) (hn : d.limit ≤ 2147483646) :
    polls (afterQk d) = (d.i + 1, d.i - 1) := by
  unfold afterQk
  split
  · rw [polls_iter d (by omega) hn]
    congr 1 <;> omega
  · change (min (d.i + 1) d.limit, d.i - 1) = _
    rw [Nat.min_eq_left hi]

/-- Increment the count of a successful poll at one of the two wait PCs. -/
def receipt (s : Site) (e : Event) : Nat × Nat :=
  match s, e.kind with
  | .kvWait, .wait _ _ true _ _ => (1, 0)
  | .pWait, .wait _ _ true _ _ => (0, 1)
  | _, _ => (0, 0)

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem polls_next {d d' : D} {L : Launch} {g : Nat} {e : Event} (hi : Inv d)
    (hz : next L g d e = some (some d')) :
    polls d' = polls d + receipt d.site e := by
  obtain ⟨s,i,v⟩ := d
  cases s
  case ldNum =>
    simp only [next] at hz
    split at hz <;> try contradiction
    rename_i bs _
    cases hw : (rebuild 3 bs).toOption <;> simp [hw] at hz
    subst d'
    rfl
  all_goals simp only [next, Inv, D.limit] at hz hi
  all_goals try (rename_i j; fin_cases j)
  all_goals try (simp only [issueNext, Fin.coe_ofNat_eq_mod, Fin.val_zero, Nat.reduceMod,
    Nat.reduceAdd, Nat.reduceLT, ↓reduceDIte] at hz)
  all_goals repeat' split at hz
  all_goals try contradiction
  all_goals try (simp only [Option.bind] at hz; split at hz <;> try contradiction)
  all_goals cases hz
  all_goals try rfl
  all_goals try (rw [polls_after _ (by exact hi.left) (by exact hi.right)])
  all_goals try (rw [polls_iter _ (by exact hi.right.left) (by exact hi.right.right)])
  all_goals simp_all [startSite, polls, receipt, D.limit, runCount, Prod.ext_iff]
  all_goals try split_ifs
  all_goals by_cases hn : low v ≤ 2147483646 <;>
    (try simp_all [polls, D.limit, runCount]) <;>
    first | omega | exact ite_eq_right_iff.mpr (fun h => by omega)

end
end PTX.Kernels.InklingRelDecode.Proof.Mma
