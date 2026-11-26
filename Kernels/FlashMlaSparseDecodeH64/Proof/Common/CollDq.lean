-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollCls
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollSite
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollStep0
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View

@[expose] public section

/-! # The collectives of warps 8-11

`dqCls`: the `CollCls` of the lanes of warpgroup 2: two collectives, the startup's shuffles at
pcs 6 and 9, then warpgroup 2's code, which has none. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {x : Nat}

/-- The lanes of warps 8-11. -/
def DqLane (L : Launch) (y : Nat) : Prop := y < L.threads ∧ 8 ≤ warpOf L y ∧ warpOf L y < 12

/-- **A state of a lane of warps 8-11** is a startup state before its hand-over or a
warpgroup-2 state. -/
theorem dq_state (hFw : Follow P L X) (hx : x < L.threads)
    (hw : 8 ≤ warpOf L x ∧ warpOf L x < 12) {k : Nat} {σ : (thread P L x).D}
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) :
    (∃ d n, σ = (.inl d, n) ∧ Startup.RefW L x d (n .shfl) ∧ Startup.exitOf d = none) ∨
      ∃ d n, σ = (.inr ⟨.inl .dequant, d⟩, n) := by
  have hJ := (follow_iff.mp hFw x hx k).2 σ hσ
  obtain ⟨s, n⟩ := σ
  rcases s with d | ⟨e | r, d⟩
  · obtain ⟨-, hW, -⟩ := hJ
    exact .inl ⟨d, n, rfl, hW, by simpa [startupEnter] using glue_gate hσ⟩
  · cases e with
    | dequant => exact .inr ⟨d, n, rfl⟩
    | wg0 | wg1 =>
      obtain ⟨-, -, -, h⟩ := hJ
      simp only [Entry.wg, wgOf, tidOf] at h
      simp only [warpOf, tidOf] at hw
      omega
  · exact hJ.elim

/-- A warpgroup-2 state is past every collective pc. -/
theorem dq_pc_ge (d : (frag P L x .dequant).D) (n : Cls → Nat) :
    2606 ≤ (thread P L x).pc (.inr ⟨.inl .dequant, d⟩, n) := by
  change 2606 ≤ (d : Dequant.Control.D).site.pc
  rcases dequant_pc (d : Dequant.Control.D).site with h | ⟨-, h⟩
  · exact h.1
  · omega

theorem ncT_dq (hw : 8 ≤ warpOf L x ∧ warpOf L x < 12) (d : (frag P L x .dequant).D)
    (n : Cls → Nat) : ncT P L x (.inr ⟨.inl .dequant, d⟩, n) = 2 := by
  have := dq_pc_ge (P := P) (L := L) (x := x) d n
  unfold ncT
  rw [ncW_dq hw.1 hw.2]
  simp only [show 6 < (thread P L x).pc (.inr ⟨.inl .dequant, d⟩, n) by omega,
    show 9 < (thread P L x).pc (.inr ⟨.inl .dequant, d⟩, n) by omega, ite_true]

theorem dq_noColl (d : (frag P L x .dequant).D) (n : Cls → Nat) :
    (thread P L x).pc (.inr ⟨.inl .dequant, d⟩, n) ∉ collPcs := fun h => by
  have := collPcs_lt _ h
  have := dq_pc_ge (P := P) (L := L) (x := x) d n
  omega

/-- **A step of a lane of warps 8-11 keeps the pc count.** -/
theorem dq_step (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hx : x < L.threads)
    (hw : 8 ≤ warpOf L x ∧ warpOf L x < 12) {k : Nat} {σ σ' : (thread P L x).D} {e : Event}
    (he : X.get (x, k) = some e) (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (hn : (thread P L x).next σ e = some (some σ')) :
    ncT P L x σ' = ncT P L x σ + if (thread P L x).pc σ ∈ collPcs then 1 else 0 := by
  rcases dq_state hFw hx hw hσ with ⟨d, n, rfl, -, -⟩ | ⟨d, n, rfl⟩
  · exact startup_nc_step hp hX hFw hub hx he hσ hn
  · rw [next_frag] at hn
    cases hs : (frag P L x .dequant).next d e with
    | none => rw [hs] at hn; cases hn
    | some o =>
      cases o with
      | none => rw [hs] at hn; cases hn
      | some d' =>
        rw [hs] at hn
        simp only [Option.map_some, Option.some.injEq] at hn
        subst hn
        rw [ncT_dq hw, ncT_dq hw]
        simp only [dq_noColl d n, ite_false, Nat.add_zero]

/-- **The pc of a collective state of warps 8-11 is one of the list**: a startup shuffle. -/
theorem dq_reach (hFw : Follow P L X) (hx : x < L.threads)
    (hw : 8 ≤ warpOf L x ∧ warpOf L x < 12) {k : Nat} {σ : (thread P L x).D}
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (hc : (thread P L x).pc σ ∈ collPcs) : (thread P L x).pc σ ∈ ([6, 9] : List Nat) := by
  rcases dq_state hFw hx hw hσ with ⟨d, n, rfl, hW, -⟩ | ⟨d, n, rfl⟩
  · rw [pc_startup] at hc ⊢
    rcases startup_coll_site hW hc with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [hj]; fin_cases j <;> simp [Startup.Site.pc]
    · exfalso
      obtain ⟨site, x1, x2⟩ := d
      simp only at hj
      subst hj
      obtain ⟨-, -, -, this⟩ := hW
      simp only [warpOf, tidOf] at this hw
      omega
  · exact absurd hc (dq_noColl d n)

/-- **A state of warps 8-11 is at a collective exactly when its pc is the list's entry at its
count.** -/
theorem dq_at (hFw : Follow P L X) (hx : x < L.threads)
    (hw : 8 ≤ warpOf L x ∧ warpOf L x < 12) {k : Nat} {σ : (thread P L x).D}
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) :
    CollAt P L x σ ↔ ([6, 9] : List Nat)[ncT P L x σ]? = some ((thread P L x).pc σ) := by
  rw [collAt_iff]
  unfold ncT
  rw [← collList_dq hw.1 hw.2, getElem_ncW_coll, collList_dq hw.1 hw.2]
  refine ⟨dq_reach hFw hx hw hσ, fun h => ?_⟩
  generalize (thread P L x).pc σ = p at h ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide

theorem dq_time_at (hFw : Follow P L X) (hx : x < L.threads)
    (hw : 8 ≤ warpOf L x ∧ warpOf L x < 12) {k : Nat} {σ : (thread P L x).D}
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) (hc : CollAt P L x σ) :
    time P L x σ = (([6, 9] : List Nat)[ncT P L x σ]?).getD 0 + 2 := by
  rcases dq_state hFw hx hw hσ with ⟨d, n, rfl, hW, -⟩ | ⟨d, n, rfl⟩
  · have hc' := collAt_iff.mp hc
    rw [pc_startup] at hc'
    obtain ⟨j, hj⟩ := sh_site (by simp only [warpOf, tidOf] at hw ⊢; omega) hW hc'
    show Startup.time d = _
    rw [Startup.time_of_ne (by rw [hj]; simp)]
    unfold ncT
    rw [pc_startup, hj]
    fin_cases j <;> simp [Startup.Site.pc, ncW_six, ncW_nine]
  · exact absurd (collAt_iff.mp hc) (dq_noColl d n)

theorem dq_time_lt (hFw : Follow P L X) (hx : x < L.threads)
    (hw : 8 ≤ warpOf L x ∧ warpOf L x < 12) {k : Nat} {σ : (thread P L x).D}
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) (hc : ¬ CollAt P L x σ) {n : Nat}
    (hn : (([6, 9] : List Nat)[n]?).isSome = true) (hle : ncT P L x σ ≤ n) :
    time P L x σ < (([6, 9] : List Nat)[n]?).getD 0 + 2 := by
  have hn2 : n < 2 := by
    by_contra h
    have : ([6, 9] : List Nat)[n]? = none := List.getElem?_eq_none (by simp; omega)
    simp [this] at hn
  rcases dq_state hFw hx hw hσ with ⟨d, n0, rfl, hW, -⟩ | ⟨d, n0, rfl⟩
  · have hc' : (thread P L x).pc (.inl d, n0) ∉ collPcs := fun h => hc (collAt_iff.mpr h)
    have h6 : (thread P L x).pc (.inl d, n0) ≠ 6 := fun h => hc' (h ▸ by decide)
    have h9 : (thread P L x).pc (.inl d, n0) ≠ 9 := fun h => hc' (h ▸ by decide)
    have ht : time P L x (.inl d, n0) ≤ d.site.pc + 2 := Startup.time_le d
    rw [pc_startup] at h6 h9
    unfold ncT at hle
    rw [ncW_dq hw.1 hw.2, pc_startup] at hle
    interval_cases n <;> simp <;> split_ifs at hle <;> omega
  · rw [ncT_dq hw] at hle
    omega

theorem dq_exit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : 8 ≤ warpOf L x ∧ warpOf L x < 12) {k pc : Nat} {σ : (thread P L x).D}
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (he : X.get (x, k) = some ⟨pc, .exit⟩) {n : Nat}
    (hn : (([6, 9] : List Nat)[n]?).isSome = true) : n < ncT P L x σ := by
  have hn2 : n < 2 := by
    by_contra h
    have : ([6, 9] : List Nat)[n]? = none := List.getElem?_eq_none (by simp; omega)
    simp [this] at hn
  have hpc := Frame.event_pcU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ
    (fun f h => by cases h)
  have h3 := exit_event_pc hX he
  unfold ncT
  rw [← hpc, h3, ncW_dq hw.1 hw.2]
  simp only [show 6 < 3611 by omega, show 9 < 3611 by omega, ite_true]
  omega

/-- A blocking event of warpgroup 2 is at its `setmaxnreg` or its barrier. -/
theorem dq_blocking_site {d : Dequant.Control.D} {e : Event} (hev : Dequant.Ev L x d e)
    (hb : ¬ Sched.Unblocking e.kind) : d.site = .smr ∨ d.site = .bar := by
  obtain ⟨-, hk⟩ := hev
  cases h : d.site <;> simp only [Dequant.EvK, h] at hk
  · exact .inl rfl
  all_goals try exact .inr rfl
  all_goals exfalso
  all_goals first
    | (rcases hk with ⟨a, bs, hk⟩ | ⟨f, hk⟩ <;> rw [hk] at hb <;> simp [Sched.Unblocking] at hb)
    | (rcases hk with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩ <;> rw [hk] at hb <;> simp [Sched.Unblocking] at hb)
    | (rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩ <;> rw [hk] at hb <;> simp [Sched.Unblocking] at hb)
    | (rw [hk] at hb; simp [Sched.Unblocking] at hb)

/-- **After a blocking event of a lane of warps 8-11** the machine runs on, at no collective. -/
theorem dq_last (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hx : x < L.threads)
    (hw : 8 ≤ warpOf L x ∧ warpOf L x < 12) {k : Nat} {σ : (thread P L x).D} {e : Event}
    (he : X.get (x, k) = some e) (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (hb : ¬ Sched.Unblocking e.kind) :
    (thread P L x).next σ e ≠ none ∧ ∀ σ', (thread P L x).next σ e = some (some σ') →
      ¬ CollAt P L x σ' := by
  rcases dq_state hFw hx hw hσ with ⟨d, n, rfl, -, -⟩ | ⟨d, n, rfl⟩
  · obtain ⟨h1, h2⟩ := startup_last hp hX hFw hub he hσ hb
    exact ⟨h1, fun σ' h hc => h2 σ' h (collAt_iff.mp hc)⟩
  · have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(x, k), e.pc, f, by
      rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
    obtain ⟨σ0, hσ0, -, -, hev⟩ := ev_state hp hX hFw he hne
    rw [hσ] at hσ0
    obtain rfl := Option.some.inj (Option.some.inj hσ0)
    have hev' : Dequant.Ev L x d e := hev
    refine ⟨?_, fun σ' hn hc => ?_⟩
    · rw [next_frag]
      rcases dq_blocking_site hev' hb with hs | hs <;>
        simp [frag, dequantCode, Dequant.Control.code, Dequant.Control.succ, hs]
    · rw [next_frag] at hn
      cases hs : (frag P L x .dequant).next d e with
      | none => rw [hs] at hn; cases hn
      | some o =>
        cases o with
        | none => rw [hs] at hn; cases hn
        | some d' =>
          rw [hs] at hn
          simp only [Option.map_some, Option.some.injEq] at hn
          subst hn
          exact dq_noColl d' _ (collAt_iff.mp hc)

/-- **The collectives of the lanes of warps 8-11.** -/
def dqCls (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
    (hub : ¬ HasUb X) : CollCls P L X (DqLane L) (collS P L) where
  cn n := ([6, 9] : List Nat)[n]?
  slot n := (([6, 9] : List Nat)[n]?).getD 0 + 2
  nc := ncT P L
  count := fun {y k σ} hA hσ =>
    ncT_count hp hX hub (x := y) (fun {_ _ _ _} he hσ' hn =>
      dq_step hp hX hFw hub hA.1 hA.2 he hσ' hn) k σ hσ
  at_ := fun {y k σ} hA hσ => dq_at hFw hA.1 hA.2 hσ
  isP := fun hA hσ he hc => coll_isP hp hX hσ he hc
  slot_mono := fun {a b} hab hb => by
    have : b < 2 := by
      by_contra h
      have : ([6, 9] : List Nat)[b]? = none := List.getElem?_eq_none (by simp; omega)
      simp [this] at hb
    interval_cases b
    · omega
    · interval_cases a
      simp
  time_at := fun hA hσ hc => dq_time_at hFw hA.1 hA.2 hσ hc
  time_lt := fun hA hσ hc n hn hle => dq_time_lt hFw hA.1 hA.2 hσ hc hn hle
  static := fun {y z k k' σ σ'} hA hB hσ hσ' hc hc' hn => by
    have h1 := (dq_at hFw hA.1 hA.2 hσ).mp hc
    have h2 := (dq_at hFw hB.1 hB.2 hσ').mp hc'
    have hn' : ncT P L y σ = ncT P L z σ' := hn
    rw [hn', h2] at h1
    have := Option.some.inj h1
    show pcShape _ = pcShape _
    rw [this]
  exit := fun {y k pc σ} hA hσ he n hn => dq_exit hp hX hA.2 hσ he hn
  last := fun {y k σ e} hA he hσ hb =>
    ⟨(dq_last hp hX hFw hub hA.1 hA.2 he hσ hb).1,
      fun σ' h => .inl ((dq_last hp hX hFw hub hA.1 hA.2 he hσ hb).2 σ' h)⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
