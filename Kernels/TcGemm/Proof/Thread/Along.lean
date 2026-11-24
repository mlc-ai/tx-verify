-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Thread.Events

@[expose] public section

/-! # `tc_gemm`: one step of the run invariant

Every step of the machine fired at a state's site extends the events of `Along` by that site's
event (`along_step`): thread 0's issue, the first barrier and the read, thread 0's polls of
`bar0`, its MMA and commit, the polls of `bar1`, and the tail of `lastE`, one event per step. -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {g : Nat}

theorem take_succ_of {l : List Event} {k : Nat} {x : Event} (h : l[k]? = some x) :
    l.take (k + 1) = l.take k ++ [x] := by
  rw [List.take_add_one, h]; rfl

theorem headE_zero (A B S col : Nat) : headE A B S 0 col =
    [allocE S, tslotE S col, init0E S, init1E S, fenceE, arriveE S, bulkAE A S, bulkBE B S] := by
  simp [headE]

/-- Thread 0's issue, one event further. -/
theorem head_step {A B S col k : Nat} {x : Event} (hx : (headE A B S 0 col)[k]? = some x)
    {pre : List Event} (h : pre = (headE A B S 0 col).take k) :
    pre ++ [x] = (headE A B S 0 col).take (k + 1) := by
  rw [h, take_succ_of hx]

/-- The tail of the run, one event further. -/
theorem last_step {P : List Event} {D S g c : Nat} {vals : List Value} {k : Nat} {x : Event}
    (hx : (lastE D S g c vals)[k]? = some x) {pre : List Event}
    (h : pre = P ++ (lastE D S g c vals).take k) :
    pre ++ [x] = P ++ (lastE D S g c vals).take (k + 1) := by
  rw [h, take_succ_of hx, List.append_assoc]

theorem lastE_st {D S g c : Nat} {vals : List Value} {j : Nat} (hj : j < 8) :
    (lastE D S g c vals)[4 + j]? = some (stE D g vals j) := by
  interval_cases j <;> rfl

theorem lastE_take3 {D S g c : Nat} {vals vals' : List Value} :
    (lastE D S g c vals).take 2 ++ [ldE g c vals'] = (lastE D S g c vals').take 3 := rfl

/-- One step of the run invariant: the event of each site extends `Along`. -/
theorem along_step (hpre : Pre L A B D a b mem0) (hg : g < L.threads) {d d' : ThreadD}
    {pre : List Event} {e : Event} {t : TState} {ins : Instr} {o : Option TState}
    (hJ : Along L A B D g d pre) (hat : (code L A B D g).AtD d t) (hi : Inv g d)
    (hc : kernel.code[d.site.pc]? = some ins) (hf : Fires d.site.pc (eventTmpl [] L g t ins.op) e o)
    (hn : next g d e = some (some d')) : Along L A B D g d' (pre ++ [e]) := by
  have hev := site_event hpre hg hat hi hc hf
  obtain ⟨s, c, vals⟩ := d
  cases s with
  | alloc =>
    obtain ⟨hw, rfl⟩ := hJ
    have hev : e = allocE L.sharedBase := hev
    subst hev
    simp only [next, Option.some.injEq] at hn
    subst hn
    by_cases hg0 : g = 0
    · simp only [hg0, ↓reduceIte]
      exact ⟨rfl, rfl⟩
    · simp only [hg0, ↓reduceIte]
      exact ⟨by simp [hg0], 0, by norm_num, by simp [headE, hg0, hw]⟩
  | allocSt =>
    obtain ⟨hg0, rfl⟩ := hJ
    obtain ⟨col, hcol, rfl⟩ := hev
    simp only [next, Option.some.injEq] at hn
    subst hn
    exact ⟨hg0, col, hcol, by simp [headE_zero]⟩
  | init0 =>
    obtain ⟨hg0, col, hcol, hp⟩ := hJ
    simp only [next, Option.some.injEq] at hn
    subst hn
    exact ⟨hg0, col, hcol, head_step (by rw [headE_zero]; rw [hev]; rfl) hp⟩
  | init1 =>
    obtain ⟨hg0, col, hcol, hp⟩ := hJ
    simp only [next, Option.some.injEq] at hn
    subst hn
    exact ⟨hg0, col, hcol, head_step (by rw [headE_zero]; rw [hev]; rfl) hp⟩
  | fence =>
    obtain ⟨hg0, col, hcol, hp⟩ := hJ
    simp only [next, Option.some.injEq] at hn
    subst hn
    exact ⟨hg0, col, hcol, head_step (by rw [headE_zero]; rw [hev]; rfl) hp⟩
  | arrive =>
    obtain ⟨hg0, col, hcol, hp⟩ := hJ
    simp only [next, Option.some.injEq] at hn
    subst hn
    exact ⟨hg0, col, hcol, head_step (by rw [headE_zero]; rw [hev]; rfl) hp⟩
  | bulkA =>
    obtain ⟨hg0, col, hcol, hp⟩ := hJ
    simp only [next, Option.some.injEq] at hn
    subst hn
    exact ⟨hg0, col, hcol, head_step (by rw [headE_zero]; rw [hev]; rfl) hp⟩
  | bulkB =>
    obtain ⟨rfl, col, hcol, hp⟩ := hJ
    simp only [next, Option.some.injEq] at hn
    subst hn
    refine ⟨rfl, col, hcol, ?_⟩
    rw [head_step (by rw [headE_zero]; rw [hev]; rfl) hp]
    simp [headE_zero]
  | bar0 z =>
    obtain ⟨hz, col, hcol, rfl⟩ := hJ
    simp only [next, Option.some.injEq] at hn
    subst hn
    have hev : e = bar0E := hev
    subst hev
    exact ⟨hz, col, hcol, rfl⟩
  | load z =>
    obtain ⟨hz, col, hcol, rfl⟩ := hJ
    obtain ⟨bs, hbs, rfl⟩ := hev
    simp only [next, rdE] at hn
    cases hb : rdCol bs with
    | none => simp [hb] at hn
    | some c' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hn
      subst hn
      cases z
      · have hg0 : g ≠ 0 := by simpa using hz
        exact ⟨col, bs, 0, 0, hcol, hbs, hb, by simp [preW1, hg0, rdE]⟩
      · have hg0 : g = 0 := by simpa using hz
        subst hg0
        exact ⟨rfl, col, bs, 0, hcol, hbs, hb, by simp [rdE]⟩
  | wait0 =>
    obtain ⟨hg0, col, bs, n, hcol, hbs, hb, rfl⟩ := hJ
    obtain ⟨ok, rfl⟩ := hev
    cases ok
    · simp only [next, wait0E, Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at hn
      subst hn
      exact ⟨hg0, col, bs, n + 1, hcol, hbs, hb, by simp [List.replicate_succ']⟩
    · simp only [next, wait0E, Option.some.injEq, ↓reduceIte] at hn
      subst hn
      exact ⟨hg0, col, bs, n, hcol, hbs, hb, by simp⟩
  | mma =>
    obtain ⟨hg0, col, bs, n, hcol, hbs, hb, rfl⟩ := hJ
    have hev : e = mmaE L.sharedBase c := hev
    subst hev
    simp only [next, Option.some.injEq] at hn
    subst hn
    exact ⟨hg0, col, bs, n, hcol, hbs, hb, by simp⟩
  | commit =>
    obtain ⟨rfl, col, bs, n, hcol, hbs, hb, rfl⟩ := hJ
    have hev : e = commitE L.sharedBase := hev
    subst hev
    simp only [next, Option.some.injEq] at hn
    subst hn
    exact ⟨col, bs, n, 0, hcol, hbs, hb, by simp [preW1, midE]⟩
  | wait1 =>
    obtain ⟨col, bs, n0, n, hcol, hbs, hb, rfl⟩ := hJ
    obtain ⟨ok, rfl⟩ := hev
    cases ok
    · simp only [next, wait1E, Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at hn
      subst hn
      exact ⟨col, bs, n0, n + 1, hcol, hbs, hb, by simp [List.replicate_succ']⟩
    · simp only [next, wait1E, Option.some.injEq, ↓reduceIte] at hn
      subst hn
      exact ⟨col, bs, n0, n, hcol, hbs, hb, by simp [lastE]⟩
  | fence1 =>
    obtain ⟨col, bs, n0, n, hcol, hbs, hb, hp⟩ := hJ
    simp only [next, Option.some.injEq] at hn
    subst hn
    exact ⟨col, bs, n0, n, hcol, hbs, hb, last_step (by rw [hev]; rfl) hp⟩
  | ld =>
    obtain ⟨col, bs, n0, n, hcol, hbs, hb, rfl⟩ := hJ
    obtain ⟨vs, hl, rfl⟩ := hev
    simp only [next, ldE, Option.some.injEq] at hn
    subst hn
    exact ⟨⟨col, bs, n0, n, hcol, hbs, hb, by rw [List.append_assoc, lastE_take3]⟩, hl⟩
  | waitLd =>
    obtain ⟨⟨col, bs, n0, n, hcol, hbs, hb, hp⟩, hl⟩ := hJ
    simp only [next, Option.some.injEq] at hn
    subst hn
    exact ⟨⟨col, bs, n0, n, hcol, hbs, hb, last_step (by rw [hev]; rfl) hp⟩, hl, by omega,
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | st j =>
    obtain ⟨⟨col, bs, n0, n, hcol, hbs, hb, hp⟩, hl, hj, hw⟩ := hJ
    rcases hev with ⟨hbj, rfl⟩ | ⟨-, f, rfl⟩
    · simp only [next, stE, Option.some.injEq] at hn
      subst hn
      have hw' : Words vals (j + 1) := fun i hi => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hw i hi
        · exact hbj
      have hp' := last_step (lastE_st hj) hp
      by_cases h7 : j < 7
      · simp only [h7, ↓reduceIte]
        exact ⟨⟨col, bs, n0, n, hcol, hbs, hb, by rw [hp']; rfl⟩, hl, by omega, hw'⟩
      · obtain rfl : j = 7 := by omega
        simp only [Nat.lt_irrefl, ↓reduceIte]
        exact ⟨⟨col, bs, n0, n, hcol, hbs, hb, hp'⟩, hl, hw'⟩
    · simp [next] at hn
  | fenceB =>
    obtain ⟨⟨col, bs, n0, n, hcol, hbs, hb, hp⟩, hl, hw⟩ := hJ
    simp only [next, Option.some.injEq] at hn
    subst hn
    exact ⟨⟨col, bs, n0, n, hcol, hbs, hb, last_step (by rw [hev]; rfl) hp⟩, hl, hw⟩
  | bar1 =>
    obtain ⟨⟨col, bs, n0, n, hcol, hbs, hb, hp⟩, hl, hw⟩ := hJ
    simp only [next, Option.some.injEq] at hn
    subst hn
    exact ⟨⟨col, bs, n0, n, hcol, hbs, hb, last_step (by rw [hev]; rfl) hp⟩, hl, hw⟩
  | fence2 =>
    obtain ⟨⟨col, bs, n0, n, hcol, hbs, hb, hp⟩, hl, hw⟩ := hJ
    simp only [next, Option.some.injEq] at hn
    subst hn
    have hp' := last_step (x := e) (by rw [hev]; rfl) hp
    by_cases h0 : g / 32 = 0
    · simp only [h0, ↓reduceIte]
      exact ⟨h0, ⟨col, bs, n0, n, hcol, hbs, hb, hp'⟩, hl, hw⟩
    · simp only [h0, ↓reduceIte]
      exact ⟨⟨col, bs, n0, n, hcol, hbs, hb, by rw [hp']; simp [h0]⟩, hl, hw⟩
  | dealloc =>
    obtain ⟨h0, ⟨col, bs, n0, n, hcol, hbs, hb, hp⟩, hl, hw⟩ := hJ
    simp only [next, Option.some.injEq] at hn
    subst hn
    refine ⟨⟨col, bs, n0, n, hcol, hbs, hb, ?_⟩, hl, hw⟩
    simp only [h0, ↓reduceIte]
    exact last_step (by rw [hev]; simp [lastE, h0, storesE]) hp
  | exit => simp [next] at hn

end
end PTX.Kernels.TcGemm.Proof
