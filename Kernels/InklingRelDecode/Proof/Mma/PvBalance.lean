-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Mma.CoverHist
public import Kernels.InklingRelDecode.Proof.Common.MmaHistory

set_option linter.unusedSimpArgs false

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof

/-- The PV steps the current iteration still owes: step `j` is pending at the sites between the
iteration's poll and its issue. -/
def ppend (d : D) (j : Fin 8) : Nat :=
  match d.site with
  | .pvShfl | .pvBar2 | .pvElect => 1
  | .pv j' => if j'.val ≤ j.val then 1 else 0
  | _ => 0

/-- **The count of PV issues by step**: the issues of step `j` before the state, plus the one the
iteration still owes, are the ready polls of the PV loop. -/
def PvCnt (d : D) (n : Cls → Nat) : Prop :=
  d.site ≠ .pvSkip ∧ ∀ j : Fin 8, n (.atPc (pvPc j)) + ppend d j = (polls d).2

theorem pvCnt_start {n : Cls → Nat} (h : QkZero n) : PvCnt {} n := by
  refine ⟨by decide, fun j => ?_⟩
  simp [ppend, polls, (h j).2]

private theorem pv_site (j : Fin 8) : ∀ s : Site, pvPc j = s.pc → s = .pv j := by
  fin_cases j <;> intro s <;> cases s <;>
    repeat' first | decide +kernel | (rename_i j'; revert j')

private theorem site_pc (s : Site) (j : Fin 8) : (s.pc == pvPc j) = decide (s = .pv j) := by
  by_cases h : s = .pv j
  · subst h; simp [Site.pc]
  · have : s.pc ≠ pvPc j := fun e => h (pv_site j s e.symm)
    simp [h, this]

private theorem seven_low : low (b32 7) = 7 := by decide

private theorem ppend_after (d : D) (j : Fin 8) : ppend (afterQk d) j = 0 := by
  unfold afterQk iterNext
  split_ifs <;> simp [ppend]

private theorem ne_after (d : D) : (afterQk d).site ≠ .pvSkip := by
  unfold afterQk iterNext
  split_ifs <;> simp

private theorem ppend_iter (d : D) (j : Fin 8) : ppend (iterNext d) j = 0 := by
  unfold iterNext
  split_ifs <;> simp [ppend]

private theorem ne_iter (d : D) : (iterNext d).site ≠ .pvSkip := by
  unfold iterNext
  split_ifs <;> simp

private theorem ppend_start (n i : Nat) (v : Value) (j : Fin 8) :
    ppend ⟨startSite n, i, v⟩ j = 0 := by
  unfold startSite
  split_ifs <;> simp [ppend]

private theorem ne_start (n : Nat) : startSite n ≠ .pvSkip := by
  unfold startSite
  split_ifs <;> simp

private theorem issue_pv (f : Fin 8 → Site) (c : Site) (j : Fin 8) (hf : ∀ j', f j' ≠ .pvSkip)
    (hc : c ≠ .pvSkip) : issueNext f c j ≠ .pvSkip := by
  unfold issueNext
  split_ifs
  · exact hf _
  · exact hc

set_option hygiene false in
local macro "mv" : tactic => `(tactic| obtain rfl := Option.some.inj (Option.some.inj move))

set_option hygiene false in
local macro "quiet" : tactic => `(tactic| (
  mv
  refine ⟨by first | exact ne_after _ | exact ne_iter _ | exact ne_start _ | simp,
    fun j => ?_⟩
  (try simp only [ppend_after, ppend_iter, ppend_start])
  simp [ppend, receipt]))

/-- **The pending PV steps move with the sites**: a step adds the issue it makes to the pending
steps of the next site, and the poll it takes to the count. -/
private theorem ppend_step {L : Launch} {g k : Nat} {X : Execution} {d d' : D} {e : Event}
    (hlead : ElectLead L g (X.tr g))
    (seven : ∀ k pc md a b c recv ok, X.get (g,k) = some ⟨pc,.shfl md a b c recv ok⟩ →
      (pc = 2464 ∨ pc = 2512) → recv = b32 7)
    (get : X.get (g,k) = some e) (pc : e.pc = d.site.pc) (hs : d.site ≠ .pvSkip)
    (move : next L g d e = some (some d')) :
    d'.site ≠ .pvSkip ∧ ∀ j : Fin 8,
      ppend d' j + (if d.site = .pv j then 1 else 0) = ppend d j + (receipt d.site e).2 := by
  obtain ⟨s,i,v⟩ := d
  cases s with
  | ldNum =>
    simp only [next] at move
    split at move
    · rename_i bs _
      cases hw : Except.toOption (rebuild 3 bs) with
      | none => simp only [hw] at move; exact absurd move (by simp)
      | some v' =>
        simp only [hw] at move
        mv
        simp [ppend, receipt]
    · exact absurd move (by simp)
  | kvWait =>
    simp only [next] at move
    split at move
    · rename_i x m pr ok ac sc heq
      split at move <;> (mv; simp [ppend, receipt, heq, *])
    · exact absurd move (by simp)
  | qkShfl =>
    simp only [next] at move
    split at move
    · split at move <;> quiet
    · exact absurd move (by simp)
  | qkElect =>
    simp only [next] at move
    split at move
    · split at move <;> quiet
    · exact absurd move (by simp)
  | qk j' =>
    simp only [next] at move
    mv
    refine ⟨issue_pv _ _ _ (fun _ => by simp) (by simp), fun j => ?_⟩
    unfold issueNext
    split_ifs <;> first | contradiction | simp [ppend, receipt]
  | pWait =>
    simp only [next] at move
    split at move
    · rename_i x m pr ok ac sc heq
      split at move <;> (mv; simp [ppend, receipt, heq, *])
    · exact absurd move (by simp)
  | pvShfl =>
    simp only [next] at move
    split at move
    · rename_i md a b c recv ok heq
      obtain ⟨p, kd⟩ := e
      simp only at heq pc
      subst heq
      have h7 := seven k p md a b c recv ok get (.inr (pc.trans rfl))
      simp only [h7, seven_low, ↓reduceIte] at move
      quiet
    · exact absurd move (by simp)
  | pvElect =>
    simp only [next] at move
    split at move
    · rename_i mask inst lead heq
      have win := hlead _ (List.mem_of_getElem? get) mask inst lead heq
      split at move
      · quiet
      · rename_i no
        exact absurd win.symm no
    · exact absurd move (by simp)
  | pv j' =>
    simp only [next] at move
    mv
    refine ⟨issue_pv _ _ _ (fun _ => by simp) (by simp), fun j => ?_⟩
    unfold issueNext
    rcases eq_or_ne j' j with rfl | hne
    · split_ifs <;> simp_all [ppend, receipt]
    · have h1 : ¬ (({ site := .pv j', i := i, word := v } : D).site = .pv j) := by
        simpa using hne
      have h2 := Fin.val_ne_of_ne hne
      simp only [h1, ite_false, Nat.add_zero, receipt]
      split_ifs <;> simp only [ppend, Fin.val_mk] <;> split_ifs <;> omega
  | finElect =>
    simp only [next] at move
    split at move
    · split at move <;> quiet
    · exact absurd move (by simp)
  | dispatch => simp [next] at move
  | pvSkip => exact absurd rfl hs
  | _ =>
    simp only [next] at move
    quiet

/-- **One step keeps the PV count**: the broadcast of the PV loop is a 7 and the elected lane is
the leader, so no iteration skips its issues. -/
theorem pvCnt_step {L : Launch} {g k : Nat} {X : Execution} {d d' : D} {e : Event} {n : Cls → Nat}
    (hlead : ElectLead L g (X.tr g))
    (seven : ∀ k pc md a b c recv ok, X.get (g,k) = some ⟨pc,.shfl md a b c recv ok⟩ →
      (pc = 2464 ∨ pc = 2512) → recv = b32 7)
    (get : X.get (g,k) = some e) (pc : e.pc = d.site.pc) (inv : Inv d) (h : PvCnt d n)
    (move : next L g d e = some (some d')) : PvCnt d' (Code.bump cls n e) := by
  obtain ⟨hs, hc⟩ := h
  obtain ⟨hs', hq⟩ := ppend_step hlead seven get pc hs move
  have hp : (polls d').2 = (polls d).2 + (receipt d.site e).2 := by rw [polls_next inv move]; rfl
  refine ⟨hs', fun j => ?_⟩
  have bump : Code.bump cls n e (.atPc (pvPc j)) =
      n (.atPc (pvPc j)) + if d.site = .pv j then 1 else 0 := by
    have := site_pc d.site j
    simp [Code.bump, cls, pc, this]
  have h1 := hc j
  have h2 := hq j
  rw [bump, hp]
  omega

end PTX.Kernels.InklingRelDecode.Proof.Mma
