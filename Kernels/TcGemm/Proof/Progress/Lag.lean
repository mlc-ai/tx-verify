-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Progress.Rank

@[expose] public section

/-! # `tc_gemm` progress: threads that lag behind

In a safe execution every thread's trace is a prefix of its whole trace (`len_eq`). A thread that
has not made an event of its whole trace is pending (`pending_of`), and earlier in time than a
thread past that event: one without its first barrier has time at most 9 (`time_le_9`), thread
0 before its commit at most 13 (`time_le_13`), a thread before its load at most 16
(`time_le_16`), before the load's wait at most 17 (`time_le_17`), before its second barrier at
most 27 (`time_le_27`) and a thread of warp 0 before its deallocation at most 29
(`time_le_29`): past the time it would have crossed the event (`crossing`). The load, its wait
and the deallocation, once made, are the thread's warp-collective `tcgen05` events of their
ordinals (`tcK_ld`, `tcK_wld`, `tcK_dealloc`). -/

namespace PTX.Kernels.TcGemm.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}

section
variable (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
  (hW : Wit A B D L.sharedBase X P m u)
include hpre hX hW

/-- A thread's trace is its prefix of the whole trace. -/
theorem len_eq {g : Nat} (hg : g < 128) : (X.tr g).length = m g := by
  rw [hW.length g hg, u_nil hpre hX hW hg, List.length_nil, Nat.add_zero]

omit hpre hX hW in
/-- Two threads of one warp. -/
theorem warp_eq (hB : L.block = 128) {g h : Nat} (hs : SameWarp L g h) (hg : g < 128)
    (hh : h < 128) : g / 32 = h / 32 := by
  have := hs.2
  rw [hB, Nat.mod_eq_of_lt hg, Nat.mod_eq_of_lt hh] at this
  exact this

/-- **A thread that has not made its exit is pending.** -/
theorem pending_of {h : Nat} (hh : h < 128) (hm : m h ≤ ldIdx h (P h) + 13) :
    Frame.Pending L X h := by
  refine ⟨by rw [threads_eq hpre]; exact hh, not_canceled hW hX, fun pc hl => ?_⟩
  have hlen : 0 < (X.tr h).length := by
    rcases hx : X.tr h with _ | ⟨x, xs⟩
    · rw [hx] at hl; cases hl
    · simp
  have hget : X.get (h, (X.tr h).length - 1) = some ⟨pc, .exit⟩ := by
    change (X.tr h)[_]? = _
    rw [← List.getLast?_eq_getElem?]
    exact hl
  obtain ⟨-, hj, hpos⟩ := hW.exit hget
  split_ifs at hpos <;> omega

end

section
variable (hW : Wit A B D L.sharedBase X P m u)
include hW

/-- The load of a thread that made it is its warp-collective event of its ordinal. -/
theorem tcK_ld {h : Nat} (hh : h < 128) (hm : ldIdx h (P h) < m h) :
    X.TcK (h, ldIdx h (P h)) (if h / 32 = 0 then 1 else 0) := by
  have hget : X.get (h, ldIdx h (P h)) = some (ldE h (P h).c (P h).vals) := by
    rw [hW.get_of_lt hh hm, fullAt_ld]
  refine ⟨⟨_, hget, rfl⟩, ?_⟩
  simp only
  rw [hW.take hh hm.le, fullE_preLd, List.take_append_of_le_length (by rw [preLd_length]),
    List.take_of_length_le (by rw [preLd_length]), preLd_tc]

/-- The wait of a thread that made it is its warp-collective event of its ordinal. -/
theorem tcK_wld {h : Nat} (hh : h < 128) (hm : ldIdx h (P h) + 1 < m h) :
    X.TcK (h, ldIdx h (P h) + 1) (if h / 32 = 0 then 2 else 1) := by
  have hget : X.get (h, ldIdx h (P h) + 1) = some wldE := by
    rw [hW.get_of_lt hh hm, show ldIdx h (P h) + 1 = ldIdx h (P h) + 1 + 0 from rfl, fullAt_post]
    rfl
  refine ⟨⟨_, hget, rfl⟩, ?_⟩
  simp only
  rw [hW.take hh hm.le, show ldIdx h (P h) + 1 = ldIdx h (P h) + 1 + 0 from rfl, take_post]
  have hl : isTcColl (ldE h (P h).c (P h).vals) = true := rfl
  simp only [List.countP_append, List.countP_cons, preLd_tc, List.take_zero, List.countP_nil, hl,
    ↓reduceIte]
  split_ifs <;> rfl

/-- The deallocation of a thread of warp 0 that made it is its fourth warp-collective event. -/
theorem tcK_dealloc {h : Nat} (hh : h < 128) (h32 : h / 32 = 0) (hm : ldIdx h (P h) + 13 < m h) :
    X.TcK (h, ldIdx h (P h) + 13) 3 := by
  have hget : X.get (h, ldIdx h (P h) + 13) = some (deallocE (P h).c) := by
    rw [hW.get_of_lt hh hm, show ldIdx h (P h) + 13 = ldIdx h (P h) + 1 + 12 by omega, fullAt_post]
    simp [postAt, h32]
  refine ⟨⟨_, hget, rfl⟩, ?_⟩
  simp only
  rw [hW.take hh hm.le, show ldIdx h (P h) + 13 = ldIdx h (P h) + 1 + 12 by omega, take_post,
    post_take12]
  simp only [List.countP_append, List.countP_cons, preLd_tc, h32, ↓reduceIte,
    storesE_count isTcColl (fun j => by simp [stE, isTcColl])]
  simp [isTcColl, ldE, wldE, fbE, bar1E, fa2E]

end

section
variable (hpre : Pre L A B D a b mem0) (ht : ThreadFacts L A B D X)
  (hW : Wit A B D L.sharedBase X P m u)
include hpre ht hW

/-- A thread without its first barrier has time at most 9. -/
theorem time_le_9 {h : Nat} (hh : h < 128) (hm : m h < hd h) : timeOf L A B D X h ≤ 9 := by
  by_contra hlt
  obtain ⟨k, d, e, d', -, -, he, hev, hn, h1, h2⟩ :=
    crossing ht (by rw [threads_eq hpre]; exact hh) le_rfl (by omega)
  rw [cross_9 hev hn h1 h2] at he
  obtain ⟨-, hk, -, hpos⟩ := hW.bar he
  have := ldIdx_eq (g := h) (P h)
  have := tl_ge (g := h) (P h)
  omega

/-- Thread 0 before its commit has time at most 13. -/
theorem time_le_13 (hm : m 0 ≤ hd 0 + 3 + (P 0).n0) : timeOf L A B D X 0 ≤ 13 := by
  have h0 : 0 < L.threads := by rw [threads_eq hpre]; decide
  by_contra hlt
  obtain ⟨k, d, e, d', hk, hs, he, hev, hn, h1, h2⟩ :=
    crossing ht h0 (T := 13) (by decide) (by omega)
  have hz : d.site ≠ .load false := by
    intro hsite
    have hJ := ht.along h0 hk.le hs
    simp only [Along, hsite] at hJ
    simp at hJ
  rw [cross_13 hev hn hz h1 h2] at he
  obtain ⟨-, hj, -, hpos, -⟩ := hW.commit he
  omega

/-- A thread before its load has time at most 16. -/
theorem time_le_16 {h : Nat} (hh : h < 128) (hm : m h ≤ ldIdx h (P h)) :
    timeOf L A B D X h ≤ 16 := by
  by_contra hlt
  obtain ⟨k, d, e, d', -, -, he, hev, hn, h1, h2⟩ :=
    crossing ht (by rw [threads_eq hpre]; exact hh) (T := 16) (by decide) (by omega)
  obtain ⟨vs, -, rfl⟩ := cross_16 hev hn h1 h2
  obtain ⟨-, hk, hpos, -⟩ := hW.tld he
  omega

/-- A thread before the wait of its load has time at most 17. -/
theorem time_le_17 {h : Nat} (hh : h < 128) (hm : m h ≤ ldIdx h (P h) + 1) :
    timeOf L A B D X h ≤ 17 := by
  by_contra hlt
  obtain ⟨k, d, e, d', -, -, he, hev, hn, h1, h2⟩ :=
    crossing ht (by rw [threads_eq hpre]; exact hh) (T := 17) (by decide) (by omega)
  rw [cross_17 hev hn h1 h2] at he
  obtain ⟨-, hk, hpos⟩ := hW.waitLd he
  omega

/-- A thread before its second barrier has time at most 27. -/
theorem time_le_27 {h : Nat} (hh : h < 128) (hm : m h ≤ ldIdx h (P h) + 11) :
    timeOf L A B D X h ≤ 27 := by
  by_contra hlt
  obtain ⟨k, d, e, d', -, -, he, hev, hn, h1, h2⟩ :=
    crossing ht (by rw [threads_eq hpre]; exact hh) (T := 27) (by decide) (by omega)
  rw [cross_27 hev hn h1 h2] at he
  obtain ⟨-, hk, -, hpos⟩ := hW.bar he
  rcases hpos with hpos | hpos
  · have hb := hW.get_of_lt hh hk
    rw [he, show k = hd h - 1 by omega, fullAt_bar0] at hb
    simp [bar1E, bar0E] at hb
  · omega

/-- A thread of warp 0 before its deallocation has time at most 29. -/
theorem time_le_29 {h : Nat} (hh : h < 128) (h32 : h / 32 = 0) (hm : m h ≤ ldIdx h (P h) + 13) :
    timeOf L A B D X h ≤ 29 := by
  by_contra hlt
  obtain ⟨k, d, e, d', -, -, he, hev, hn, h1, h2⟩ :=
    crossing ht (by rw [threads_eq hpre]; exact hh) (T := 29) (by decide) (by omega)
  rw [cross_29 hev hn h32 h1 h2] at he
  obtain ⟨-, hk, -, hpos, -⟩ := hW.tdealloc he
  omega

end

end

end PTX.Kernels.TcGemm.Proof
