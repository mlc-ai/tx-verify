-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Time
public import Kernels.InklingRelDecode.Proof.Softmax.TcCount
public import Kernels.InklingRelDecode.Proof.Softmax.ScratchIteration
public import Kernels.InklingRelDecode.Proof.Lib.TcVec

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow Control

set_option maxRecDepth 100000

private theorem time_loop (s : Site) (i : Nat) (v : Carry) (h1 : s ≠ .setMaxReg) (h2 : s ≠ .bar0)
    (h3 : ∀ j, s ≠ .pre j) (h4 : s ≠ .epilogue) :
    time ⟨s, i, v⟩ = Lib.Slots.softmax i + s.position := by
  unfold time
  split <;> simp_all

private theorem coll_sites (s : Site) (h : s.pc ∈ Lib.loopTcPcs) :
    s = .ldS ∨ s = .waitLd ∨ s = .ldO ∨ s = .waitLdO ∨ s = .stO ∨ s = .waitStO ∨ s = .tmemSt ∨
      s = .tmemWait := by
  simp only [Lib.loopTcPcs, List.mem_cons, List.not_mem_nil, or_false] at h
  cases s <;> simp (config := {decide := true}) [Site.pc] at h ⊢
  all_goals (rename_i j; have := j.isLt; omega)

/-- The comparison of the two sites, with the clash the rescale decision allows. -/
private def LagGoal (sh sE : Site) (ih iE R RE : Nat) (vh vE : Carry) : Prop :=
  (time ⟨sh, ih, vh⟩ ≤ time ⟨sE, iE, vE⟩ ∧ (sh.pc ∉ Lib.loopTcPcs →
    time ⟨sh, ih, vh⟩ < time ⟨sE, iE, vE⟩)) ∨
    (sE = .ldO ∧ (sh = .bar20 ∨ sh = .tmemSt) ∧ ih = iE ∧ R = RE)

private def SameVec (sh sE : Site) (ih iE R RE : Nat) : Prop :=
  softCount sh ih R 1265 = softCount sE iE RE 1265 ∧
  softCount sh ih R 1298 = softCount sE iE RE 1298 ∧
  softCount sh ih R 2260 = softCount sE iE RE 2260 ∧
  softCount sh ih R 2261 = softCount sE iE RE 2261 ∧
  softCount sh ih R 2328 = softCount sE iE RE 2328 ∧
  softCount sh ih R 2329 = softCount sE iE RE 2329 ∧
  softCount sh ih R 1009 = softCount sE iE RE 1009 ∧
  softCount sh ih R 1010 = softCount sE iE RE 1010

private theorem main_a {sh sE : Site} {ih iE R RE : Nat} {vh vE : Carry}
    (hs : sE = .ldS ∨ sE = .waitLd ∨ sE = .ldO ∨ sE = .waitLdO)
    (h1 : ∀ j, sh ≠ .pre j) (h2 : ∀ j, sh ≠ .nxt j) (h3 : sh ≠ .setMaxReg) (h4 : sh ≠ .bar0)
    (h5 : sh ≠ .epilogue) (vec : SameVec sh sE ih iE R RE)
    (vis : visited sh = true → 1 ≤ R) (visE : visited sE = true → 1 ≤ RE)
    (prevE : needsPrevious sE = true → 0 < iE) : LagGoal sh sE ih iE R RE vh vE := by
  unfold LagGoal
  unfold SameVec at vec
  simp only [Lib.loopTcPcs, List.mem_cons, List.not_mem_nil, or_false]
  cases sh
  case pre j => exact absurd rfl (h1 j)
  case nxt j => exact absurd rfl (h2 j)
  case setMaxReg => exact absurd rfl h3
  case bar0 => exact absurd rfl h4
  case epilogue => exact absurd rfl h5
  all_goals
    rcases hs with rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [softCount, afterLdS, afterWaitLd, afterTmemSt,
      afterTmemWait, time, Site.position, Lib.Slots.softmax,
      Lib.Slots.frame, Lib.Slots.stride] at vec vis visE prevE ⊢ <;> omega

private theorem main_b {sh sE : Site} {ih iE R RE : Nat} {vh vE : Carry}
    (hs : sE = .stO ∨ sE = .waitStO ∨ sE = .tmemSt ∨ sE = .tmemWait)
    (h1 : ∀ j, sh ≠ .pre j) (h2 : ∀ j, sh ≠ .nxt j) (h3 : sh ≠ .setMaxReg) (h4 : sh ≠ .bar0)
    (h5 : sh ≠ .epilogue) (vec : SameVec sh sE ih iE R RE)
    (vis : visited sh = true → 1 ≤ R) (visE : visited sE = true → 1 ≤ RE)
    (prevE : needsPrevious sE = true → 0 < iE) : LagGoal sh sE ih iE R RE vh vE := by
  unfold LagGoal
  unfold SameVec at vec
  simp only [Lib.loopTcPcs, List.mem_cons, List.not_mem_nil, or_false]
  cases sh
  case pre j => exact absurd rfl (h1 j)
  case nxt j => exact absurd rfl (h2 j)
  case setMaxReg => exact absurd rfl h3
  case bar0 => exact absurd rfl h4
  case epilogue => exact absurd rfl h5
  all_goals
    rcases hs with rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [softCount, afterLdS, afterWaitLd, afterTmemSt,
      afterTmemWait, time, Site.position, Lib.Slots.softmax,
      Lib.Slots.frame, Lib.Slots.stride] at vec vis visE prevE ⊢ <;> omega

/-- A loop collective is at its round's clock. -/
public theorem time_coll {d : D} (h : d.site.pc ∈ Lib.loopTcPcs) : 1266 ≤ time d := by
  obtain ⟨s, i, v⟩ := d
  simp only [Lib.loopTcPcs, List.mem_cons, List.not_mem_nil, or_false] at h
  cases s <;> simp (config := {decide := true}) [Site.pc, time, Site.position,
    Lib.Slots.softmax, Lib.Slots.frame, Lib.Slots.stride] at h ⊢ <;> omega

private theorem main {sh sE : Site} {ih iE R RE : Nat} {vh vE : Carry}
    (hs : sE.pc ∈ Lib.loopTcPcs)
    (h1 : ∀ j, sh ≠ .pre j) (h2 : ∀ j, sh ≠ .nxt j) (h3 : sh ≠ .setMaxReg) (h4 : sh ≠ .bar0)
    (h5 : sh ≠ .epilogue) (vec : SameVec sh sE ih iE R RE)
    (vis : visited sh = true → 1 ≤ R) (visE : visited sE = true → 1 ≤ RE)
    (prevE : needsPrevious sE = true → 0 < iE) : LagGoal sh sE ih iE R RE vh vE := by
  rcases coll_sites _ hs with h | h | h | h | h | h | h | h <;> subst h
  · exact main_a (by simp) h1 h2 h3 h4 h5 vec vis visE prevE
  · exact main_a (by simp) h1 h2 h3 h4 h5 vec vis visE prevE
  · exact main_a (by simp) h1 h2 h3 h4 h5 vec vis visE prevE
  · exact main_a (by simp) h1 h2 h3 h4 h5 vec vis visE prevE
  all_goals exact main_b (by simp) h1 h2 h3 h4 h5 vec vis visE prevE

/-- **A lane of a CTA with the same earlier collective events as a lane at a loop collective is no
later in the round**, unless it has decided the rescale the other way. -/
public theorem soft_lag {dh dE : D} {R RE : Nat} (hE : dE.site.pc ∈ Lib.loopTcPcs)
    (vec : ∀ P ∈ Lib.dataPcs, softCount dh.site dh.i R P = softCount dE.site dE.i RE P)
    (vis : visited dh.site = true → 1 ≤ R) (visE : visited dE.site = true → 1 ≤ RE)
    (prevE : needsPrevious dE.site = true → 0 < dE.i) (ep : dh.site ≠ .epilogue) :
    (time dh ≤ time dE ∧ (dh.site.pc ∉ Lib.loopTcPcs → time dh < time dE)) ∨
      (dE.site = .ldO ∧ (dh.site = .bar20 ∨ dh.site = .tmemSt) ∧ dh.i = dE.i ∧ R = RE) := by
  have late := time_coll hE
  obtain ⟨sh, ih, vh⟩ := dh
  obtain ⟨sE, iE, vE⟩ := dE
  simp only at hE vec vis visE prevE ep late ⊢
  have sv : SameVec sh sE ih iE R RE := by
    simp only [Lib.dataPcs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at vec
    obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, -⟩ := vec
    exact ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩
  cases sh
  case pre j =>
    left
    have := j.isLt
    simp only [time, Site.pc, Lib.loopTcPcs, List.mem_cons, List.not_mem_nil, or_false] at late ⊢
    omega
  case bar0 | setMaxReg =>
    left
    simp only [time, Lib.Slots.reuse, Lib.Slots.enter, Site.pc, Lib.loopTcPcs, List.mem_cons,
      List.not_mem_nil, or_false] at late ⊢
    omega
  case nxt j =>
    have sw : SameVec .waitS sE ih iE R RE := by
      unfold SameVec at sv ⊢
      simpa [softCount, afterLdS, afterWaitLd, afterTmemSt, afterTmemWait] using sv
    rcases main (vh := vh) (vE := vE) hE (by simp) (by simp) (by simp) (by simp) (by simp) sw
      (by simp [visited]) visE prevE with ⟨l, -⟩ | ⟨-, h, -⟩
    · left
      have := j.isLt
      refine ⟨?_, fun _ => ?_⟩ <;>
        simp only [time, Site.position, Lib.Slots.softmax, Lib.Slots.frame, Lib.Slots.stride]
          at l ⊢ <;> omega
    · simp at h
  case epilogue => exact absurd rfl ep
  all_goals
    rcases main (vh := vh) (vE := vE) hE (by simp) (by simp) (by simp) (by simp) (by simp) sv
      vis visE prevE with h | h
    · exact .inl h
    · exact .inr h

/-- A loop collective has made as many events at pc 1010 as its round. -/
public theorem count_1010 {d : D} (R : Nat) (h : d.site.pc ∈ Lib.loopTcPcs) :
    softCount d.site d.i R 1010 = d.i := by
  rcases coll_sites _ h with h | h | h | h | h | h | h | h <;> simp [softCount, h, afterTmemWait]

/-- A loop collective is in a round of the loop. -/
public theorem coll_i_lt {e t} {d : D} (hi : Inv e t d) (h : d.site.pc ∈ Lib.loopTcPcs) :
    d.i < e.limit := by
  obtain ⟨s, i, v⟩ := d
  have := hi.loop
  rcases coll_sites _ h with h | h | h | h | h | h | h | h <;> subst h <;>
    exact this (by simp) (by simp) (by simp) (by simp)

/-- **Every Softmax clock is at most the epilogue's** in a launch of fewer than `2^31` blocks. -/
public theorem time_le_finish {e t} {d : D} (hi : Inv e t d) :
    time d ≤ Lib.Slots.finish ∧ (d.site ≠ .epilogue → time d < Lib.Slots.finish) := by
  have lim := hi.entry.limitEq
  have bnd := hi.bound
  obtain ⟨s, i, v⟩ := d
  simp only at bnd
  refine ⟨?_, fun hne => ?_⟩ <;>
  cases s <;> simp (config := {decide := true}) only [time, Site.position, Lib.Slots.finish,
    Lib.Slots.softmax, Lib.Slots.frame, Lib.Slots.stride, Lib.Slots.enter, Lib.Slots.reuse] at * <;>
    split at lim <;> omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
