-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollCls
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollSite
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollWg1
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollStep0
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowHead
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowSub
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View

@[expose] public section

/-! # The collectives of warp 6

`idleCls`: the `CollCls` of the lanes of warp 6: three collectives, the startup's shuffles at
pcs 6 and 9, then warpgroup 1's head shuffle at pc 1843, whose word sends the lane to the idle
code, which has none. The head's `setmaxnreg` before the shuffle is the register request every
lane of the warp makes (`last`, with `released_of_setMax`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {x : Nat}

/-- The lanes of warp 6. -/
def IdleLane (L : Launch) (y : Nat) : Prop := y < L.threads ∧ warpOf L y = 6

theorem collList_six : collList 6 = [6, 9, 1843] := by decide

theorem ncW_idle (pc : Nat) : ncW 6 pc =
    (if 6 < pc then 1 else 0) + (if 9 < pc then 1 else 0) + (if 1843 < pc then 1 else 0) := by
  unfold ncW
  rw [collList_six]
  simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]
  repeat' split
  all_goals simp_all

/-- The slots of warp 6's collectives: the startup's, then the head's shuffle. -/
def idleSlot (n : Nat) : Nat := if n < 2 then (([6, 9] : List Nat)[n]?).getD 0 + 2 else 101

/-- **A state of a lane of warp 6** is a startup state before its hand-over, a state of the
head, or a state of the idle code. -/
theorem idle_state (hFw : Follow P L X) (hx : x < L.threads) (hw : warpOf L x = 6) {k : Nat}
    {σ : (thread P L x).D} (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) :
    (∃ d n, σ = (.inl d, n) ∧ Startup.RefW L x d (n .shfl) ∧ Startup.exitOf d = none) ∨
    (∃ s n, σ = (.inr ⟨.inl .wg1, .inl s⟩, n) ∧ (s = .smr ∨ s = .hsh ∨ s = .idle)) ∨
      ∃ d n, σ = (.inr ⟨.inl .wg1, .inr ⟨.inl .idle, d⟩⟩, n) := by
  rcases wg1_cls hFw hx (by omega) hσ with h | ⟨s, n, rfl, hs⟩ | ⟨i, d, n, rfl, hok⟩
  · exact .inl h
  · exact .inr (.inl ⟨s, n, rfl, by tauto⟩)
  · cases i
    · simp [subOk, hw] at hok
    · simp [subOk, hw] at hok
    · simp [subOk, hw] at hok
    · exact .inr (.inr ⟨d, n, rfl⟩)

theorem pc_head (s : Wg1.Site) (n : Cls → Nat) :
    (thread P L x).pc (.inr ⟨.inl .wg1, .inl s⟩, n) = Wg1.Site.pc P L x s := rfl

theorem ncT_idle (hw : warpOf L x = 6) (σ : (thread P L x).D) : ncT P L x σ =
    (if 6 < (thread P L x).pc σ then 1 else 0) + (if 9 < (thread P L x).pc σ then 1 else 0) +
      (if 1843 < (thread P L x).pc σ then 1 else 0) := by
  unfold ncT
  rw [hw, ncW_idle]

theorem ncT_smr (hw : warpOf L x = 6) (n : Cls → Nat) :
    ncT P L x (.inr ⟨.inl .wg1, .inl .smr⟩, n) = 2 := by
  rw [ncT_idle hw, pc_head]
  simp [Wg1.Site.pc]

theorem ncT_hsh (hw : warpOf L x = 6) (n : Cls → Nat) :
    ncT P L x (.inr ⟨.inl .wg1, .inl .hsh⟩, n) = 2 := by
  rw [ncT_idle hw, pc_head]
  simp [Wg1.Site.pc]

theorem ncT_late (hw : warpOf L x = 6) {σ : (thread P L x).D}
    (h : 2596 ≤ (thread P L x).pc σ) : ncT P L x σ = 3 := by
  rw [ncT_idle hw]
  simp only [show 6 < (thread P L x).pc σ by omega, show 9 < (thread P L x).pc σ by omega,
    show 1843 < (thread P L x).pc σ by omega, ite_true]

theorem pc_headIdle (n : Cls → Nat) :
    2596 ≤ (thread P L x).pc (.inr ⟨.inl .wg1, .inl .idle⟩, n) := by
  change 2596 ≤ (idleFirst P L x).pc
  exact idle_pc_ge _

theorem pc_idleLate (d : IdleSite) (n : Cls → Nat) :
    2596 ≤ (thread P L x).pc (.inr ⟨.inl .wg1, .inr ⟨.inl .idle, d⟩⟩, n) := idle_pc_ge d

/-- The dispatch's successors are exits of the head. -/
theorem succ_hsh_exit {e : Event} {s' : Wg1.Site} (h : Wg1.succ .hsh e = some (some s')) :
    Wg1.exitOf s' ≠ none := by
  simp only [Wg1.succ] at h
  split at h
  · simp only [Wg1.dispatch] at h
    split at h
    · split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> simp [Wg1.exitOf]
    · cases h
  · cases h

theorem idle_gate_hsh : Code.gatedExit (wg1Enter P L x) (subSel P L x) Wg1.Site.hsh = none :=
  Code.gatedExit_none.mpr (by simp [wg1Enter, Wg1.exitOf])

/-- **A step of a lane of warp 6 keeps the pc count.** -/
theorem idw_step (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hx : x < L.threads) (hw : warpOf L x = 6)
    {k : Nat} {σ σ' : (thread P L x).D} {e : Event}
    (he : X.get (x, k) = some e) (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (hn : (thread P L x).next σ e = some (some σ')) :
    ncT P L x σ' = ncT P L x σ + if (thread P L x).pc σ ∈ collPcs then 1 else 0 := by
  have hσ' : Frame.stateAt (thread P L) X x (k + 1) = some (some σ') := by
    rw [Frame.stateAt_succ (C := thread P L) (show (X.tr x)[k]? = some e from he), hσ]
    exact hn
  rcases idle_state hFw hx hw hσ with ⟨d, n, rfl, -, -⟩ | ⟨s, n, rfl, hs⟩ | ⟨d, n, rfl⟩
  · exact startup_nc_step hp hX hFw hub hx he hσ hn
  · rw [next_head] at hn
    rcases hs with rfl | rfl | rfl
    · simp only [Wg1.succ, Option.map_some, Option.some.injEq] at hn
      subst hn
      simp only [Code.enter, idle_gate_hsh]
      rw [ncT_smr hw, ncT_hsh hw]
      simp [Wg1.Site.pc, collPcs]
    · rcases hsu : Wg1.succ .hsh e with _ | _ | s'
      · rw [hsu] at hn; cases hn
      · rw [hsu] at hn; cases hn
      · rw [hsu] at hn
        simp only [Option.map_some, Option.some.injEq] at hn
        subst hn
        have hne : Code.gatedExit (wg1Enter P L x) (subSel P L x) s' ≠ none := fun h => by
          have := Code.gatedExit_none.mp h
          simp only [wg1Enter, Option.map_eq_none_iff] at this
          exact succ_hsh_exit hsu this
        obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hne
        rw [Code.enter_some hi] at hσ' ⊢
        rcases idle_state hFw hx hw hσ' with ⟨d, n', h, -⟩ | ⟨s2, n', h, -⟩ | ⟨d, n', h⟩
        · cases h
        · cases h
        · rw [h, ncT_late hw (pc_idleLate d n'), ncT_hsh hw, pc_head]
          simp [Wg1.Site.pc, collPcs]
    · simp [Wg1.succ] at hn
  · rw [next_sub] at hn
    rcases hs : Wg1.isucc P d e with _ | _ | d'
    · have : (subFrag P L x .idle).next d e = none := hs
      rw [this] at hn; cases hn
    · have : (subFrag P L x .idle).next d e = some none := hs
      rw [this] at hn; cases hn
    · have : (subFrag P L x .idle).next d e = some (some d') := hs
      rw [this] at hn
      simp only [Option.map_some, Option.some.injEq] at hn
      subst hn
      change ncT P L x (.inr ⟨.inl .wg1, .inr ⟨.inl .idle, d'⟩⟩, Code.bump cls n e) = _
      rw [ncT_late hw (pc_idleLate d' _), ncT_late hw (pc_idleLate d _)]
      have : (thread P L x).pc (.inr ⟨.inl .wg1, .inr ⟨.inl .idle, d⟩⟩, n) ∉ collPcs :=
        fun h => by
          have := collPcs_lt _ h
          have := pc_idleLate (P := P) (L := L) (x := x) d n
          omega
      simp [this]

/-- **The pc of a collective state of warp 6 is one of the list.** -/
theorem idw_reach (hFw : Follow P L X) (hx : x < L.threads) (hw : warpOf L x = 6) {k : Nat}
    {σ : (thread P L x).D} (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (hc : (thread P L x).pc σ ∈ collPcs) : (thread P L x).pc σ ∈ ([6, 9, 1843] : List Nat) := by
  rcases idle_state hFw hx hw hσ with ⟨d, n, rfl, hW, -⟩ | ⟨s, n, rfl, hs⟩ | ⟨d, n, rfl⟩
  · rw [pc_startup] at hc ⊢
    obtain ⟨j, hj⟩ := sh_site (by omega) hW hc
    rw [hj]; fin_cases j <;> simp [Startup.Site.pc]
  · rcases hs with rfl | rfl | rfl
    · simp [Wg1.Site.pc, collPcs] at hc
    · simp [Wg1.Site.pc]
    · have := collPcs_lt _ hc
      have := pc_headIdle (P := P) (L := L) (x := x) n
      omega
  · have := collPcs_lt _ hc
    have := pc_idleLate (P := P) (L := L) (x := x) d n
    omega

/-- **A state of warp 6 is at a collective exactly when its pc is the list's entry at its
count.** -/
theorem idw_at (hFw : Follow P L X) (hx : x < L.threads) (hw : warpOf L x = 6) {k : Nat}
    {σ : (thread P L x).D} (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) :
    CollAt P L x σ ↔ ([6, 9, 1843] : List Nat)[ncT P L x σ]? = some ((thread P L x).pc σ) := by
  rw [collAt_iff]
  unfold ncT
  rw [hw, ← collList_six, getElem_ncW_coll, collList_six]
  refine ⟨idw_reach hFw hx hw hσ, fun h => ?_⟩
  generalize (thread P L x).pc σ = p at h ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> decide

theorem idw_time_at (hFw : Follow P L X) (hx : x < L.threads) (hw : warpOf L x = 6) {k : Nat}
    {σ : (thread P L x).D} (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (hc : CollAt P L x σ) : time P L x σ = idleSlot (ncT P L x σ) := by
  have hc' := collAt_iff.mp hc
  rcases idle_state hFw hx hw hσ with ⟨d, n, rfl, hW, -⟩ | ⟨s, n, rfl, hs⟩ | ⟨d, n, rfl⟩
  · rw [pc_startup] at hc'
    obtain ⟨j, hj⟩ := sh_site (by omega) hW hc'
    show Startup.time d = _
    rw [Startup.time_of_ne (by rw [hj]; simp), ncT_idle hw, pc_startup, hj]
    fin_cases j <;> simp [Startup.Site.pc, idleSlot]
  · rcases hs with rfl | rfl | rfl
    · simp [Wg1.Site.pc, collPcs] at hc'
    · rw [ncT_hsh hw]
      simp [time, fragTime, wg1Time, Wg1.time, roleBase, idleSlot]
    · have := collPcs_lt _ hc'
      have := pc_headIdle (P := P) (L := L) (x := x) n
      omega
  · have := collPcs_lt _ hc'
    have := pc_idleLate (P := P) (L := L) (x := x) d n
    omega

theorem idw_time_lt (hFw : Follow P L X) (hx : x < L.threads) (hw : warpOf L x = 6) {k : Nat}
    {σ : (thread P L x).D} (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (hc : ¬ CollAt P L x σ) {n : Nat} (hn : (([6, 9, 1843] : List Nat)[n]?).isSome = true)
    (hle : ncT P L x σ ≤ n) : time P L x σ < idleSlot n := by
  have hn3 : n < 3 := by
    by_contra h
    have : ([6, 9, 1843] : List Nat)[n]? = none := List.getElem?_eq_none (by simp; omega)
    simp [this] at hn
  rcases idle_state hFw hx hw hσ with ⟨d, n0, rfl, hW, hxd⟩ | ⟨s, n0, rfl, hs⟩ | ⟨d, n0, rfl⟩
  · have hc' : (thread P L x).pc (.inl d, n0) ∉ collPcs := fun h => hc (collAt_iff.mpr h)
    have h6 : (thread P L x).pc (.inl d, n0) ≠ 6 := fun h => hc' (h ▸ by decide)
    have h9 : (thread P L x).pc (.inl d, n0) ≠ 9 := fun h => hc' (h ▸ by decide)
    have ht : Startup.time d ≤ d.site.pc + 2 := Startup.time_le d
    have hlt := Startup.time_lt hxd
    rw [pc_startup] at h6 h9
    rw [ncT_idle hw, pc_startup] at hle
    show Startup.time d < _
    interval_cases n <;> simp only [idleSlot] <;> simp <;> split_ifs at hle <;> omega
  · rcases hs with rfl | rfl | rfl
    · rw [ncT_smr hw] at hle
      have : n = 2 := by omega
      subst this
      simp [time, fragTime, wg1Time, Wg1.time, roleBase, idleSlot]
    · rw [ncT_hsh hw] at hle
      exact absurd (collAt_iff.mpr (by simp [Wg1.Site.pc, collPcs])) hc
    · rw [ncT_late hw (pc_headIdle n0)] at hle
      omega
  · rw [ncT_late hw (pc_idleLate d n0)] at hle
    omega

theorem idw_exit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : warpOf L x = 6) {k pc : Nat} {σ : (thread P L x).D}
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (he : X.get (x, k) = some ⟨pc, .exit⟩) {n : Nat}
    (hn : (([6, 9, 1843] : List Nat)[n]?).isSome = true) : n < ncT P L x σ := by
  have hn3 : n < 3 := by
    by_contra h
    have : ([6, 9, 1843] : List Nat)[n]? = none := List.getElem?_eq_none (by simp; omega)
    simp [this] at hn
  have hpc := Frame.event_pcU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ
    (fun f h => by cases h)
  have h3 := exit_event_pc hX he
  rw [ncT_idle hw, ← hpc, h3]
  simp only [show 6 < 3611 by omega, show 9 < 3611 by omega, show 1843 < 3611 by omega, ite_true]
  omega

/-- **A lane of warp 6 at its head's shuffle has made its register request.** -/
theorem idw_req (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hx : x < L.threads) (hw : warpOf L x = 6)
    {σ : (thread P L x).D}
    (hσ : Frame.stateAt (thread P L) X x (X.tr x).length = some (some σ))
    (hc : CollAt P L x σ) (hn : ncT P L x σ = 2) :
    ∃ j pc inc n i, X.get (x, j) = some ⟨pc, .setMaxReg inc n i⟩ := by
  have hc' := collAt_iff.mp hc
  rcases idle_state hFw hx hw hσ with ⟨d, n, rfl, hW, -⟩ | ⟨s, n, rfl, hs⟩ | ⟨d, n, rfl⟩
  · rw [pc_startup] at hc'
    obtain ⟨j, hj⟩ := sh_site (by omega) hW hc'
    rw [ncT_idle hw, pc_startup, hj] at hn
    fin_cases j <;> simp [Startup.Site.pc] at hn
  · rcases hs with rfl | rfl | rfl
    · simp [Wg1.Site.pc, collPcs] at hc'
    · have hlr := low_or_req hp hX hFw hub hx (X.tr x).length le_rfl _ hσ
      have hm : measure P L x (.inr ⟨.inl .wg1, .inl .hsh⟩, n) = fragBase + 1 := rfl
      rw [hm] at hlr
      rw [List.take_length] at hlr
      have hpos : 0 < (X.tr x).countP SetMaxNReg.isRequest := by
        rcases hlr with h | h
        · omega
        · exact h
      obtain ⟨a, ha, hra⟩ := List.countP_pos_iff.mp hpos
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ha
      obtain ⟨pc, kd⟩ := a
      cases kd <;> simp [SetMaxNReg.isRequest] at hra
      rename_i inc n' i
      exact ⟨j, pc, inc, n', i, hj⟩
    · have := collPcs_lt _ hc'
      have := pc_headIdle (P := P) (L := L) (x := x) n
      omega
  · have := collPcs_lt _ hc'
    have := pc_idleLate (P := P) (L := L) (x := x) d n
    omega

/-- **After a blocking event of a lane of warp 6** the machine runs on, at no collective, or
(after its `setmaxnreg`) at the head's shuffle, at which every lane of the warp that is at it has
made its request. -/
theorem idw_last (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hx : x < L.threads) (hw : warpOf L x = 6)
    {k : Nat} {σ : (thread P L x).D} {e : Event}
    (he : X.get (x, k) = some e) (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (hb : ¬ Sched.Unblocking e.kind) :
    (thread P L x).next σ e ≠ none ∧ ∀ σ', (thread P L x).next σ e = some (some σ') →
      ¬ CollAt P L x σ' ∨ ((∃ inc n i, e.kind = .setMaxReg inc n i) ∧
        ∀ y σy, IdleLane L y → SameWarp L y x →
          Frame.stateAt (thread P L) X y (X.tr y).length = some (some σy) → CollAt P L y σy →
          ncT P L y σy = ncT P L x σ' → ∃ j pc inc n i,
            X.get (y, j) = some ⟨pc, .setMaxReg inc n i⟩) := by
  rcases idle_state hFw hx hw hσ with ⟨d, n, rfl, -, -⟩ | ⟨s, n, rfl, hs⟩ | ⟨d, n, rfl⟩
  · obtain ⟨h1, h2⟩ := startup_last hp hX hFw hub he hσ hb
    exact ⟨h1, fun σ' h => .inl fun hc => h2 σ' h (collAt_iff.mp hc)⟩
  · have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(x, k), e.pc, f, by
      rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
    obtain ⟨σ0, hσ0, -, hi, hev⟩ := ev_state hp hX hFw he hne
    rw [hσ] at hσ0
    obtain rfl := Option.some.inj (Option.some.inj hσ0)
    rcases hs with rfl | rfl | rfl
    · have hev' : Wg1.Ev L x .smr e := hev
      obtain ⟨inst, hk⟩ := hev'
      refine ⟨by rw [next_head]; simp [Wg1.succ], fun σ' hn => .inr ⟨⟨_, _, _, hk⟩, ?_⟩⟩
      rw [next_head] at hn
      simp only [Wg1.succ, Option.map_some, Option.some.injEq] at hn
      subst hn
      intro y σy hy _ hσy hcy hny
      simp only [Code.enter, idle_gate_hsh] at hny
      rw [ncT_hsh hw] at hny
      exact idw_req hp hX hFw hub hy.1 hy.2 hσy hcy hny
    · have hev' : Wg1.Ev L x .hsh e := hev
      obtain ⟨r, ok, hk⟩ := hev'
      rw [hk] at hb
      simp [Sched.Unblocking] at hb
    · exfalso
      have hx2 := hi.2
      have := Code.gatedExit_none.mp hx2
      simp [wg1Enter, Wg1.exitOf] at this
  · have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(x, k), e.pc, f, by
      rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
    obtain ⟨σ0, hσ0, -, hi, hev⟩ := ev_state hp hX hFw he hne
    rw [hσ] at hσ0
    obtain rfl := Option.some.inj (Option.some.inj hσ0)
    obtain ⟨h1, h2⟩ := idleD_last (P := P) (L := L) (x := x) (n := n) (show Wg1.IEv d e from hev) hb
    refine ⟨h1, fun σ' hn => .inl fun hc => ?_⟩
    obtain ⟨d', rfl⟩ := h2 σ' hn
    have h3 : 2596 ≤ (thread P L x).pc (idleS P L x d' (Code.bump cls n e)) := pc_idleLate d' _
    exact absurd (lt_of_le_of_lt h3 (collPcs_lt _ (collAt_iff.mp hc))) (by norm_num)

/-- **The collectives of the lanes of warp 6.** -/
def idleCls (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
    (hub : ¬ HasUb X) : CollCls P L X (IdleLane L) (collS P L) where
  cn n := ([6, 9, 1843] : List Nat)[n]?
  slot := idleSlot
  nc := ncT P L
  count := fun {y k σ} hA hσ =>
    ncT_count hp hX hub (x := y) (fun {_ _ _ _} he hσ' hn =>
      idw_step hp hX hFw hub hA.1 hA.2 he hσ' hn) k σ hσ
  at_ := fun {y k σ} hA hσ => idw_at hFw hA.1 hA.2 hσ
  isP := fun hA hσ he hc => coll_isP hp hX hσ he hc
  slot_mono := fun {a b} hab hb => by
    have : b < 3 := by
      by_contra h
      have : ([6, 9, 1843] : List Nat)[b]? = none := List.getElem?_eq_none (by simp; omega)
      simp [this] at hb
    interval_cases b <;> interval_cases a <;> simp [idleSlot]
  time_at := fun hA hσ hc => idw_time_at hFw hA.1 hA.2 hσ hc
  time_lt := fun hA hσ hc n hn hle => idw_time_lt hFw hA.1 hA.2 hσ hc hn hle
  static := fun {y z k k' σ σ'} hA hB hσ hσ' hc hc' hn => by
    have h1 := (idw_at hFw hA.1 hA.2 hσ).mp hc
    have h2 := (idw_at hFw hB.1 hB.2 hσ').mp hc'
    have hn' : ncT P L y σ = ncT P L z σ' := hn
    rw [hn', h2] at h1
    have := Option.some.inj h1
    show pcShape _ = pcShape _
    rw [this]
  exit := fun {y k pc σ} hA hσ he n hn => idw_exit hp hX hA.2 hσ he hn
  last := fun {y k σ e} hA he hσ hb =>
    ⟨(idw_last hp hX hFw hub hA.1 hA.2 he hσ hb).1,
      fun σ' h => ((idw_last hp hX hFw hub hA.1 hA.2 he hσ hb).2 σ' h).imp_right .inl⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
