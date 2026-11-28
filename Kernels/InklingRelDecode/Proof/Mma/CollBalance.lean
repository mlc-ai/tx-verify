-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.ShuffleBalance
public import Lemmas.Kernel.Progress.Warp

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow

/-- The sites at a warp collective: the barriers, the broadcasts and the elections. -/
def Site.coll : Site → Bool
  | .qkBar | .qkShfl | .qkBar2 | .qkSkip | .qkElect | .pvBar | .pvShfl | .pvBar2 | .pvSkip
  | .pvElect | .finBar | .finElect => true
  | _ => false

/-- Warp collectives still owed for the current successful poll. -/
def remain : Site → Nat
  | .qkShfl | .pvShfl => 3
  | .qkBar2 | .pvBar2 => 2
  | .qkSkip | .pvSkip | .qkElect | .pvElect => 1
  | _ => 0

/-- A site past its barrier whose poll has not succeeded. -/
def Site.waiting : Site → Nat
  | .kvWait | .pWait => 1
  | _ => 0

/-- A site entered only after a broadcast of the loop that received no 7. -/
def Site.skipped : Site → Nat
  | .qkSkip | .pvSkip => 1
  | _ => 0

/-- A broadcast of the loop that received no 7. -/
noncomputable def skipEv (e : Event) : Bool :=
  (e.pc == 2464 || e.pc == 2512) && match e.kind with
    | .shfl _ _ _ _ v _ => low v != 7
    | _ => false

private theorem quiet_after (d : D) :
    remain (afterQk d).site = 0 ∧ (afterQk d).site.waiting = 0 ∧
      (afterQk d).site.skipped = 0 := by
  simp only [afterQk, iterNext]; split_ifs <;> exact ⟨rfl, rfl, rfl⟩

private theorem quiet_iter (d : D) :
    remain (iterNext d).site = 0 ∧ (iterNext d).site.waiting = 0 ∧
      (iterNext d).site.skipped = 0 := by
  simp only [iterNext]; split_ifs <;> exact ⟨rfl, rfl, rfl⟩

private theorem quiet_start (n : Nat) :
    remain (startSite n) = 0 ∧ (startSite n).waiting = 0 ∧
      (startSite n).skipped = 0 := by
  simp only [startSite]; split_ifs <;> exact ⟨rfl, rfl, rfl⟩

private theorem quiet_qk (j : Fin 8) :
    remain (issueNext .qk .qkCommit j) = 0 ∧ (issueNext .qk .qkCommit j).waiting = 0 ∧
      (issueNext .qk .qkCommit j).skipped = 0 := by
  simp only [issueNext]; split_ifs <;> exact ⟨rfl, rfl, rfl⟩

private theorem quiet_pv (j : Fin 8) :
    remain (issueNext .pv .pvCommit1 j) = 0 ∧ (issueNext .pv .pvCommit1 j).waiting = 0 ∧
      (issueNext .pv .pvCommit1 j).skipped = 0 := by
  simp only [issueNext]; split_ifs <;> exact ⟨rfl, rfl, rfl⟩

private theorem pc_facts (s : Site) :
    ((s.pc == 2464 || s.pc == 2512) = (s == .qkShfl || s == .pvShfl)) ∧
      (s.pc == 2550) = (s == .finBar) ∧ (s.pc == 2551) = (s == .finElect) := by
  cases s <;> first | decide | (rename_i j; revert j; decide +kernel)

theorem remain_next {d dn : D} {L g ev} (src : Lib.CollectiveAt d.site.pc ev)
    (hc : Sched.isWarpColl ev = d.site.coll) (hn : next L g d ev = some (some dn)) :
    (Sched.isWarpColl ev).toNat + remain dn.site + (skipEv ev).toNat + d.site.waiting =
      remain d.site + 4 * ((receipt d.site ev).1 + (receipt d.site ev).2) +
        (ev.pc == 2550).toNat + (ev.pc == 2551).toNat + dn.site.waiting ∧
    dn.site.skipped ≤ d.site.skipped + (skipEv ev).toNat := by
  rw [hc]
  obtain ⟨s, i, v⟩ := d
  obtain ⟨pc, kd⟩ := ev
  have pc' : pc = s.pc := src.pc_eq
  subst pc'
  obtain ⟨f1, f2, f3⟩ := pc_facts s
  simp only [skipEv, f1, f2, f3]
  clear f1 f2 f3
  cases s
  case ldNum =>
    cases kd with
    | rd ac bs =>
      simp only [next] at hn
      cases h : (rebuild 3 bs).toOption <;> simp [h] at hn
      subst dn
      simp [Site.coll, remain, Site.waiting, Site.skipped, receipt, beq_eq_decide]
    | _ => cases hn
  all_goals simp only [next] at hn
  all_goals repeat' split at hn
  all_goals try contradiction
  all_goals cases hn
  all_goals try simp only [quiet_after, quiet_iter, quiet_start, quiet_qk, quiet_pv]
  all_goals simp [Site.coll, remain, Site.waiting, Site.skipped, receipt, beq_eq_decide, bne, *]

/-- The final collectives (pcs 2550 and 2551) behind a site. -/
def Site.fin : Site → Nat
  | .finElect => 1
  | .finCommit | .bar1 | .setMaxRegInc | .dispatch => 2
  | _ => 0

private theorem fin_iter (d : D) : (iterNext d).site.fin = 0 := by
  simp only [iterNext]; split_ifs <;> rfl

private theorem fin_after (d : D) : (afterQk d).site.fin = 0 := by
  simp only [afterQk]; split_ifs
  · exact fin_iter d
  · rfl

private theorem fin_start (n : Nat) : (startSite n).fin = 0 := by
  simp only [startSite]; split_ifs <;> rfl

private theorem fin_issue (f : Fin 8 → Site) (c : Site) (j : Fin 8)
    (hf : ∀ k, (f k).fin = 0) (hc : c.fin = 0) : (issueNext f c j).fin = 0 := by
  simp only [issueNext]; split_ifs <;> simp [hf, hc]

private theorem fin_pcs (s : Site) :
    (s.pc == 2550).toNat + (s.pc == 2551).toNat =
      (if s = .finBar ∨ s = .finElect then 1 else 0) := by
  cases s <;> first | decide | (rename_i j; revert j; decide +kernel)

/-- The final collectives are counted once each, in order. -/
theorem fin_next {L g} {d dn : D} {ev : Event} (hn : next L g d ev = some (some dn)) :
    dn.site.fin = d.site.fin + (d.site.pc == 2550).toNat + (d.site.pc == 2551).toNat := by
  obtain ⟨s, i, v⟩ := d
  cases s
  case ldNum =>
    obtain ⟨pc, kd⟩ := ev
    cases kd with
    | rd ac bs =>
      simp only [next] at hn
      cases h : (rebuild 3 bs).toOption <;> simp [h] at hn
      subst dn; rfl
    | _ => cases hn
  all_goals simp only [next] at hn
  all_goals repeat' split at hn
  all_goals try contradiction
  all_goals cases hn
  all_goals try simp only [fin_iter, fin_after, fin_start,
    fin_issue .qk .qkCommit _ (fun _ => rfl) rfl, fin_issue .pv .pvCommit1 _ (fun _ => rfl) rfl]
  all_goals simp [Site.fin, Nat.add_assoc, fin_pcs]
