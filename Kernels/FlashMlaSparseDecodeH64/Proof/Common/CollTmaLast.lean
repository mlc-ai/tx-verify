-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollCls
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollWg1
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Ev
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollIdle
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowHead
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowSub
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # The collectives of warp 5: after a blocking event

`tmaCls`: the `CollCls` of the lanes of warp 5 (`Common/CollTma.lean` has its facts). -/

/-! # The collectives of warp 5 (the TMA warp)

`tmaCls`: the `CollCls` of the lanes of warp 5: four collectives, the startup's shuffles at pcs
6 and 9, the head's shuffle at pc 1843 and the election at pc 2165, the TMA code's first site,
which no later site returns to (`succ_ne_elect`). A lane that loses the election walks into the
idle code. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {x : Nat}

/-- The lanes of warp 5. -/
def TmaLane (L : Launch) (y : Nat) : Prop := y < L.threads ∧ warpOf L y = 5

theorem collList_five : collList 5 = [6, 9, 1843, 2165] := by decide

theorem ncW_five (pc : Nat) : ncW 5 pc = (if 6 < pc then 1 else 0) + (if 9 < pc then 1 else 0) +
    (if 1843 < pc then 1 else 0) + (if 2165 < pc then 1 else 0) := by
  unfold ncW
  rw [collList_five]
  simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]
  repeat' split
  all_goals simp_all

/-- The slots of warp 5's collectives. -/
def tmaSlot (n : Nat) : Nat :=
  if n < 2 then (([6, 9] : List Nat)[n]?).getD 0 + 2 else if n = 2 then 101 else 132

/-- No successor of the TMA code is at its election. -/
theorem tma_succ_ne_elect {d d' : Tma.D} {e : Event}
    (h : Tma.succ P L x d e = some (some d')) : d'.site ≠ .elect := by
  obtain ⟨s, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ := d
  cases s <;> simp only [Tma.succ, Tma.afterTopk, Tma.lensD, Tma.leadNext, Tma.loopEntry,
    Tma.loopEnd, Tma.ncWord, Tma.word32, Tma.rdAny, Tma.afterQuad, Tma.poll, Tma.electNext,
    Tma.afterCoord,
    Tma.afterGather] at h <;>
    (repeat' split at h) <;> first | (simp at h; subst h; simp) | simp_all

theorem tma_pc_cases (s : Tma.Site) : (s = .elect ∧ s.pc = 2165) ∨
    (s ≠ .elect ∧ 2165 < s.pc ∧ (s.pc ≤ 2330 ∨ 2596 ≤ s.pc)) := by
  cases s <;> simp [Tma.Site.pc] <;> first
    | omega
    | (rename_i k; have := k.isLt; split_ifs <;> omega)
    | (rename_i k; have := k.isLt; simp only [Tma.coordPc]; split_ifs <;> omega)
    | (rename_i i; have := idle_pc_ge i; omega)

theorem tma_succ_ne {d : Tma.D} {e : Event} (hev : Tma.Ev L x d e)
    (hb : ¬ Sched.Unblocking e.kind) : Tma.succ P L x d e ≠ none := by
  obtain ⟨-, hk⟩ := hev
  obtain ⟨s, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ := d
  cases s <;> simp only [Tma.EvK] at hk <;> first
    | (simp [Tma.succ]; done)
    | (exfalso; apply hb
       try simp only [Tma.Poll, RdAt] at hk
       first
        | (rw [hk]; simp [Sched.Unblocking])
        | (rcases hk with ⟨a, hk⟩ | ⟨f, hk⟩ <;> rw [hk] <;> simp [Sched.Unblocking])
        | (rcases hk with ⟨a, b, hk⟩ | ⟨f, hk⟩ <;> rw [hk] <;> simp [Sched.Unblocking])
        | (rcases hk with ⟨a, b, hk, -⟩ | ⟨f, hk⟩ <;> rw [hk] <;> simp [Sched.Unblocking]))

/-- The state of the TMA code. -/
abbrev tmaS (P : Params) (L : Launch) (x : Nat) (d : Tma.D) (n : Cls → Nat) : (thread P L x).D :=
  (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n)

theorem pc_tma (d : Tma.D) (n : Cls → Nat) : (thread P L x).pc (tmaS P L x d n) = d.site.pc :=
  rfl

theorem ncT_five (hw : warpOf L x = 5) (σ : (thread P L x).D) : ncT P L x σ =
    (if 6 < (thread P L x).pc σ then 1 else 0) + (if 9 < (thread P L x).pc σ then 1 else 0) +
      (if 1843 < (thread P L x).pc σ then 1 else 0) +
      (if 2165 < (thread P L x).pc σ then 1 else 0) := by
  unfold ncT
  rw [hw, ncW_five]

theorem ncT_tma (hw : warpOf L x = 5) (d : Tma.D) (n : Cls → Nat) :
    ncT P L x (tmaS P L x d n) = if d.site = .elect then 3 else 4 := by
  rw [ncT_five hw, pc_tma]
  rcases tma_pc_cases d.site with ⟨h, hp⟩ | ⟨h, hp, -⟩
  · rw [hp]
    simp only [h, ite_true]
    norm_num
  · simp only [h, ite_false, show 6 < d.site.pc by omega, show 9 < d.site.pc by omega,
      show 1843 < d.site.pc by omega, hp, ite_true]

theorem tma_coll (d : Tma.D) (n : Cls → Nat) :
    (thread P L x).pc (tmaS P L x d n) ∈ collPcs ↔ d.site = .elect := by
  rw [pc_tma]
  rcases tma_pc_cases d.site with ⟨h, hp⟩ | ⟨h, hp, hq⟩
  · exact ⟨fun _ => h, fun _ => by rw [hp]; simp [collPcs]⟩
  · simp only [h, iff_false]
    intro hc
    simp only [collPcs, List.mem_cons, List.not_mem_nil, or_false] at hc
    omega

theorem ncT_five_late (hw : warpOf L x = 5) {σ : (thread P L x).D}
    (h : 2596 ≤ (thread P L x).pc σ) : ncT P L x σ = 4 := by
  rw [ncT_five hw]
  simp only [show 6 < (thread P L x).pc σ by omega, show 9 < (thread P L x).pc σ by omega,
    show 1843 < (thread P L x).pc σ by omega, show 2165 < (thread P L x).pc σ by omega,
    ite_true]

/-- **A state of a lane of warp 5.** -/
theorem tmaw_state (hFw : Follow P L X) (hx : x < L.threads) (hw : warpOf L x = 5) {k : Nat}
    {σ : (thread P L x).D} (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) :
    (∃ d n, σ = (.inl d, n) ∧ Startup.RefW L x d (n .shfl) ∧ Startup.exitOf d = none) ∨
    (∃ s n, σ = (.inr ⟨.inl .wg1, .inl s⟩, n) ∧ (s = .smr ∨ s = .hsh)) ∨
    (∃ d n, σ = tmaS P L x d n) ∨
      ∃ d n, σ = (.inr ⟨.inl .wg1, .inr ⟨.inl .idle, d⟩⟩, n) := by
  rcases wg1_cls hFw hx (by omega) hσ with h | h | ⟨i, d, n, rfl, hok⟩
  · exact .inl h
  · exact .inr (.inl h)
  · cases i
    · simp [subOk, hw] at hok
    · exact .inr (.inr (.inl ⟨d, n, rfl⟩))
    · simp [subOk, hw] at hok
    · exact .inr (.inr (.inr ⟨d, n, rfl⟩))

/-- **After a step of the TMA code** the lane is in the TMA code past its election, or in the
idle code. -/
theorem tmaw_after (hw : warpOf L x = 5) {d : Tma.D} {n : Cls → Nat} {e : Event}
    {σ' : (thread P L x).D} (hn : (thread P L x).next (tmaS P L x d n) e = some (some σ')) :
    Tma.succ P L x d e ≠ none ∧ 2165 < (thread P L x).pc σ' ∧
      ((thread P L x).pc σ' ≤ 2330 ∨ 2596 ≤ (thread P L x).pc σ') := by
  rw [next_sub] at hn
  have hs : (subFrag P L x .tma).next d e = Tma.succ P L x d e := rfl
  rcases hsu : Tma.succ P L x d e with _ | _ | d'
  · rw [hs, hsu] at hn; cases hn
  · rw [hs, hsu] at hn; cases hn
  · rw [hs, hsu] at hn
    simp only [Option.map_some, Option.some.injEq] at hn
    subst hn
    refine ⟨by simp, ?_⟩
    by_cases hl : d'.site = .leave (idleFirst P L x)
    · rw [Code.backEnter_some (p := Wg1.Site.idle)
        (by show subBack P L x .tma d' = some Wg1.Site.idle; simp [subBack, hl]),
        Code.enter_some (gate_idle ⟨by omega, by omega⟩)]
      have := pc_idleLate (P := P) (L := L) (x := x) (idleFirst P L x) (Code.bump cls n e)
      exact ⟨lt_of_lt_of_le (by norm_num) this, .inr this⟩
    · rw [Code.backEnter_none
        (by show subBack P L x .tma d' = none; simp [subBack, hl])]
      have hne := tma_succ_ne_elect hsu
      rcases tma_pc_cases d'.site with ⟨h, -⟩ | ⟨-, h1, h2⟩
      · exact absurd h hne
      · exact ⟨h1, h2⟩

theorem ncT_five_gt (hw : warpOf L x = 5) {σ : (thread P L x).D}
    (h : 2165 < (thread P L x).pc σ) : ncT P L x σ = 4 := by
  rw [ncT_five hw]
  simp only [show 6 < (thread P L x).pc σ by omega, show 9 < (thread P L x).pc σ by omega,
    show 1843 < (thread P L x).pc σ by omega, h, ite_true]

/-- **A step of a lane of warp 5 keeps the pc count.** -/
theorem tmaw_step (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hx : x < L.threads) (hw : warpOf L x = 5)
    {k : Nat} {σ σ' : (thread P L x).D} {e : Event}
    (he : X.get (x, k) = some e) (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (hn : (thread P L x).next σ e = some (some σ')) :
    ncT P L x σ' = ncT P L x σ + if (thread P L x).pc σ ∈ collPcs then 1 else 0 := by
  rcases tmaw_state hFw hx hw hσ with ⟨d, n, rfl, -, -⟩ | ⟨s, n, rfl, hs⟩ | ⟨d, n, rfl⟩ |
    ⟨d, n, rfl⟩
  · exact startup_nc_step hp hX hFw hub hx he hσ hn
  · rcases hs with rfl | rfl
    · rw [smr_next hn, ncT_headS (by omega) (.inl rfl), ncT_headS (by omega) (.inr rfl), pc_smr]
      simp [collPcs]
    · rw [(hsh_next hp hX hFw (noUbBefore_of_noUb hub) hx (by omega) he hσ hn).2.1 hw,
        ncT_headS (by omega) (.inr rfl), pc_hsh]
      show ncT P L x (tmaS P L x Tma.init _) = _
      rw [ncT_tma hw]
      simp [collPcs, Tma.init]
  · obtain ⟨-, h1, h2⟩ := tmaw_after hw hn
    rw [ncT_five_gt hw h1, ncT_tma hw]
    by_cases hel : d.site = .elect
    · have hc := (tma_coll (P := P) (L := L) (x := x) d n).mpr hel
      simp only [hc, ite_true]
      simp only [hel, ite_true]
    · have : (thread P L x).pc (tmaS P L x d n) ∉ collPcs := fun h => hel ((tma_coll d n).mp h)
      simp [this, hel]
  · obtain ⟨d', rfl⟩ := idleD_next hn
    have h1 : 2596 ≤ (thread P L x).pc (idleS P L x d n) := pc_idleLate d n
    have h2 : 2596 ≤ (thread P L x).pc (idleS P L x d' (Code.bump cls n e)) := pc_idleLate d' _
    have h3 : (thread P L x).pc (idleS P L x d n) ∉ collPcs := fun h =>
      absurd (lt_of_le_of_lt h1 (collPcs_lt _ h)) (by norm_num)
    rw [ncT_five_late hw h1, ncT_five_late hw h2]
    simp [h3]

/-- **The pc of a collective state of warp 5 is one of the list.** -/
theorem tmaw_reach (hFw : Follow P L X) (hx : x < L.threads) (hw : warpOf L x = 5) {k : Nat}
    {σ : (thread P L x).D} (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (hc : (thread P L x).pc σ ∈ collPcs) :
    (thread P L x).pc σ ∈ ([6, 9, 1843, 2165] : List Nat) := by
  rcases tmaw_state hFw hx hw hσ with ⟨d, n, rfl, hW, -⟩ | ⟨s, n, rfl, hs⟩ | ⟨d, n, rfl⟩ |
    ⟨d, n, rfl⟩
  · rw [pc_startup] at hc ⊢
    obtain ⟨j, hj⟩ := sh_site (by omega) hW hc
    rw [hj]; fin_cases j <;> simp [Startup.Site.pc]
  · rcases hs with rfl | rfl
    · rw [pc_smr] at hc; simp [collPcs] at hc
    · rw [pc_hsh]; simp
  · have := (tma_coll d n).mp hc
    rw [pc_tma, this]
    simp [Tma.Site.pc]
  · have := collPcs_lt _ hc
    have := pc_idleLate (P := P) (L := L) (x := x) d n
    omega

theorem tmaw_at (hFw : Follow P L X) (hx : x < L.threads) (hw : warpOf L x = 5) {k : Nat}
    {σ : (thread P L x).D} (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) :
    CollAt P L x σ ↔
      ([6, 9, 1843, 2165] : List Nat)[ncT P L x σ]? = some ((thread P L x).pc σ) := by
  rw [collAt_iff]
  unfold ncT
  rw [hw, ← collList_five, getElem_ncW_coll, collList_five]
  refine ⟨tmaw_reach hFw hx hw hσ, fun h => ?_⟩
  generalize (thread P L x).pc σ = p at h ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem tmaw_time_at (hFw : Follow P L X) (hx : x < L.threads) (hw : warpOf L x = 5) {k : Nat}
    {σ : (thread P L x).D} (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (hc : CollAt P L x σ) : time P L x σ = tmaSlot (ncT P L x σ) := by
  have hc' := collAt_iff.mp hc
  rcases tmaw_state hFw hx hw hσ with ⟨d, n, rfl, hW, -⟩ | ⟨s, n, rfl, hs⟩ | ⟨d, n, rfl⟩ |
    ⟨d, n, rfl⟩
  · rw [pc_startup] at hc'
    obtain ⟨j, hj⟩ := sh_site (by omega) hW hc'
    show Startup.time d = _
    rw [Startup.time_of_ne (by rw [hj]; simp), ncT_five hw, pc_startup, hj]
    fin_cases j <;> simp [Startup.Site.pc, tmaSlot]
  · rcases hs with rfl | rfl
    · rw [pc_smr] at hc'; simp [collPcs] at hc'
    · rw [ncT_headS (by omega) (.inr rfl)]
      simp [time, fragTime, wg1Time, Wg1.time, roleBase, tmaSlot]
  · have hel := (tma_coll d n).mp hc'
    rw [ncT_tma hw]
    simp only [hel, ite_true]
    have h0 : Tma.time d = 0 := by
      unfold Tma.time Tma.place
      rw [hel]
      simp [Tma.Site.ord, Tma.Site.inLoop]
    show idleBase + 29 + Tma.time d = _
    rw [h0]
    simp [idleBase, roleBase, tmaSlot]
  · have := collPcs_lt _ hc'
    have := pc_idleLate (P := P) (L := L) (x := x) d n
    omega

theorem tmaw_time_lt (hFw : Follow P L X) (hx : x < L.threads) (hw : warpOf L x = 5) {k : Nat}
    {σ : (thread P L x).D} (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (hc : ¬ CollAt P L x σ) {n : Nat}
    (hn : (([6, 9, 1843, 2165] : List Nat)[n]?).isSome = true) (hle : ncT P L x σ ≤ n) :
    time P L x σ < tmaSlot n := by
  have hn4 : n < 4 := by
    by_contra h
    have : ([6, 9, 1843, 2165] : List Nat)[n]? = none := List.getElem?_eq_none (by simp; omega)
    simp [this] at hn
  rcases tmaw_state hFw hx hw hσ with ⟨d, n0, rfl, hW, hxd⟩ | ⟨s, n0, rfl, hs⟩ | ⟨d, n0, rfl⟩ |
    ⟨d, n0, rfl⟩
  · have hc' : (thread P L x).pc (.inl d, n0) ∉ collPcs := fun h => hc (collAt_iff.mpr h)
    have h6 : (thread P L x).pc (.inl d, n0) ≠ 6 := fun h => hc' (h ▸ by decide)
    have h9 : (thread P L x).pc (.inl d, n0) ≠ 9 := fun h => hc' (h ▸ by decide)
    have ht : Startup.time d ≤ d.site.pc + 2 := Startup.time_le d
    have hlt := Startup.time_lt hxd
    rw [pc_startup] at h6 h9
    rw [ncT_five hw, pc_startup] at hle
    show Startup.time d < _
    interval_cases n <;> simp only [tmaSlot] <;> simp <;> split_ifs at hle <;> omega
  · rcases hs with rfl | rfl
    · rw [ncT_headS (by omega) (.inl rfl)] at hle
      have : n = 2 ∨ n = 3 := by omega
      rcases this with rfl | rfl <;>
        simp [time, fragTime, wg1Time, Wg1.time, roleBase, tmaSlot]
    · exact absurd (collAt_iff.mpr (by rw [pc_hsh]; simp [collPcs])) hc
  · by_cases hel : d.site = .elect
    · exact absurd (collAt_iff.mpr ((tma_coll d n0).mpr hel)) hc
    · have := ncT_tma (P := P) (L := L) hw d n0
      simp only [hel, ↓reduceIte] at this
      rw [this] at hle
      omega
  · rw [ncT_five_late hw (pc_idleLate d n0)] at hle
    omega

theorem tmaw_exit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : warpOf L x = 5) {k pc : Nat} {σ : (thread P L x).D}
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (he : X.get (x, k) = some ⟨pc, .exit⟩) {n : Nat}
    (hn : (([6, 9, 1843, 2165] : List Nat)[n]?).isSome = true) : n < ncT P L x σ := by
  have hn4 : n < 4 := by
    by_contra h
    have : ([6, 9, 1843, 2165] : List Nat)[n]? = none := List.getElem?_eq_none (by simp; omega)
    simp [this] at hn
  have hpc := Frame.event_pcU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ
    (fun f h => by cases h)
  have h3 := exit_event_pc hX he
  rw [ncT_five hw, ← hpc, h3]
  simp only [show 6 < 3611 by omega, show 9 < 3611 by omega, show 1843 < 3611 by omega,
    show 2165 < 3611 by omega, ite_true]
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {x : Nat}

/-- **A lane of warp 5 at its head's shuffle has made its register request.** -/
theorem tmaw_req (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hx : x < L.threads) (hw : warpOf L x = 5)
    {σ : (thread P L x).D}
    (hσ : Frame.stateAt (thread P L) X x (X.tr x).length = some (some σ))
    (hc : CollAt P L x σ) (hn : ncT P L x σ = 2) :
    ∃ j pc inc n i, X.get (x, j) = some ⟨pc, .setMaxReg inc n i⟩ := by
  have hc' := collAt_iff.mp hc
  rcases tmaw_state hFw hx hw hσ with ⟨d, n, rfl, hW, -⟩ | ⟨s, n, rfl, hs⟩ | ⟨d, n, rfl⟩ |
    ⟨d, n, rfl⟩
  · rw [pc_startup] at hc'
    obtain ⟨j, hj⟩ := sh_site (by omega) hW hc'
    rw [ncT_five hw, pc_startup, hj] at hn
    fin_cases j <;> simp [Startup.Site.pc] at hn
  · rcases hs with rfl | rfl
    · rw [pc_smr] at hc'; simp [collPcs] at hc'
    · exact hsh_req hp hX hFw hub hx hσ
  · have := ncT_tma (P := P) (L := L) hw d n
    split_ifs at this <;> omega
  · have h1 : 2596 ≤ (thread P L x).pc (idleS P L x d n) := pc_idleLate d n
    exact absurd (lt_of_le_of_lt h1 (collPcs_lt _ hc')) (by norm_num)

/-- **After a blocking event of a lane of warp 5** the machine runs on, at no collective, or
(after its `setmaxnreg`) at the head's shuffle, at which every lane of the warp that is at it has
made its request. -/
theorem tmaw_last (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hx : x < L.threads) (hw : warpOf L x = 5)
    {k : Nat} {σ : (thread P L x).D} {e : Event}
    (he : X.get (x, k) = some e) (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (hb : ¬ Sched.Unblocking e.kind) :
    (thread P L x).next σ e ≠ none ∧ ∀ σ', (thread P L x).next σ e = some (some σ') →
      ¬ CollAt P L x σ' ∨ ((∃ inc n i, e.kind = .setMaxReg inc n i) ∧
        ∀ y σy, TmaLane L y → SameWarp L y x →
          Frame.stateAt (thread P L) X y (X.tr y).length = some (some σy) → CollAt P L y σy →
          ncT P L y σy = ncT P L x σ' → ∃ j pc inc n i,
            X.get (y, j) = some ⟨pc, .setMaxReg inc n i⟩) := by
  have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(x, k), e.pc, f, by
    rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  rcases tmaw_state hFw hx hw hσ with ⟨d, n, rfl, -, -⟩ | ⟨s, n, rfl, hs⟩ | ⟨d, n, rfl⟩ |
    ⟨d, n, rfl⟩
  · obtain ⟨h1, h2⟩ := startup_last hp hX hFw hub he hσ hb
    exact ⟨h1, fun σ' h => .inl fun hc => h2 σ' h (collAt_iff.mp hc)⟩
  · exact head_last hp hX hFw hub (by omega) (fun y => TmaLane L y) he hs hσ hb
      fun y σy hy hσy hcy hny => tmaw_req hp hX hFw hub hy.1 hy.2 hσy hcy hny
  · obtain ⟨σ0, hσ0, -, hi, hev⟩ := ev_state hp hX hFw he hne
    rw [hσ] at hσ0
    obtain rfl := Option.some.inj (Option.some.inj hσ0)
    have hev' : Tma.Ev L x d e := hev
    refine ⟨?_, fun σ' hn => .inl fun hc => ?_⟩
    · rw [next_sub]
      have hs : (subFrag P L x .tma).next d e = Tma.succ P L x d e := rfl
      rw [hs]
      rcases hsu : Tma.succ P L x d e with _ | _ | d'
      · exact absurd hsu (tma_succ_ne hev' hb)
      · simp
      · simp
    · obtain ⟨-, h1, h2⟩ := tmaw_after hw hn
      have h3 := collAt_iff.mp hc
      generalize (thread P L x).pc σ' = p at h1 h2 h3
      simp only [collPcs, List.mem_cons, List.not_mem_nil, or_false] at h3
      omega
  · obtain ⟨σ0, hσ0, -, hi, hev⟩ := ev_state hp hX hFw he hne
    rw [hσ] at hσ0
    obtain rfl := Option.some.inj (Option.some.inj hσ0)
    obtain ⟨h1, h2⟩ := idleD_blocking hp hX hFw hub he hσ hb
    exact ⟨h1, fun σ' hn => .inl fun hc =>
      absurd (lt_of_le_of_lt (h2 σ' hn) (collPcs_lt _ (collAt_iff.mp hc))) (by norm_num)⟩

/-- **The collectives of the lanes of warp 5.** -/
def tmaCls (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
    (hub : ¬ HasUb X) : CollCls P L X (TmaLane L) (collS P L) where
  cn n := ([6, 9, 1843, 2165] : List Nat)[n]?
  slot := tmaSlot
  nc := ncT P L
  count := fun {y k σ} hA hσ =>
    ncT_count hp hX hub (x := y) (fun {_ _ _ _} he hσ' hn =>
      tmaw_step hp hX hFw hub hA.1 hA.2 he hσ' hn) k σ hσ
  at_ := fun {y k σ} hA hσ => tmaw_at hFw hA.1 hA.2 hσ
  isP := fun hA hσ he hc => coll_isP hp hX hσ he hc
  slot_mono := fun {a b} hab hb => by
    have : b < 4 := by
      by_contra h
      have : ([6, 9, 1843, 2165] : List Nat)[b]? = none := List.getElem?_eq_none (by simp; omega)
      simp [this] at hb
    interval_cases b <;> interval_cases a <;> simp [tmaSlot]
  time_at := fun hA hσ hc => tmaw_time_at hFw hA.1 hA.2 hσ hc
  time_lt := fun hA hσ hc n hn hle => tmaw_time_lt hFw hA.1 hA.2 hσ hc hn hle
  static := fun {y z k k' σ σ'} hA hB hσ hσ' hc hc' hn => by
    have h1 := (tmaw_at hFw hA.1 hA.2 hσ).mp hc
    have h2 := (tmaw_at hFw hB.1 hB.2 hσ').mp hc'
    have hn' : ncT P L y σ = ncT P L z σ' := hn
    rw [hn', h2] at h1
    have := Option.some.inj h1
    show pcShape _ = pcShape _
    rw [this]
  exit := fun {y k pc σ} hA hσ he n hn => tmaw_exit hp hX hA.2 hσ he hn
  last := fun {y k σ e} hA he hσ hb =>
    ⟨(tmaw_last hp hX hFw hub hA.1 hA.2 he hσ hb).1,
      fun σ' h => ((tmaw_last hp hX hFw hub hA.1 hA.2 he hσ hb).2 σ' h).imp_right .inl⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
