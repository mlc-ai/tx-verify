-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollCls
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollSite
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollWg1
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollIxN
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollIdle
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowHead
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowSub
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLive
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View

@[expose] public section

/-! # The shuffles of warp 7 (the index warp), from the ghost count

The collectives of warp 7 are shuffles only. The number of them a lane has made is the thread
machine's ghost count `σ.2 .shfl` (`ix_count`: the prefix count of warp collectives), and an
index state's count is the role's (`ixN`, `ix_inv`). The states of a lane of warp 7 are the
startup's, the head's and the index code's (`ix_cls`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {x : Nat}

/-- The lanes of warp 7 of CTA `c`. -/
def IxLane (L : Launch) (c y : Nat) : Prop := y < L.threads ∧ warpOf L y = 7 ∧ y / L.block = c

/-- An index state of the thread machine. -/
abbrev ixS (P : Params) (L : Launch) (x : Nat) (d : Index.D) (n : Cls → Nat) : (thread P L x).D :=
  (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n)

/-- **A state of a lane of warp 7** is a startup state before its hand-over, a state of the
head, or an index state. -/
theorem ix_cls (hFw : Follow P L X) (hx : x < L.threads) (hw : warpOf L x = 7) {k : Nat}
    {σ : (thread P L x).D} (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) :
    (∃ d n, σ = (.inl d, n) ∧ Startup.RefW L x d (n .shfl) ∧ Startup.exitOf d = none) ∨
    (∃ s n, σ = (.inr ⟨.inl .wg1, .inl s⟩, n) ∧ (s = .smr ∨ s = .hsh)) ∨
      ∃ d n, σ = ixS P L x d n := by
  rcases wg1_cls hFw hx (by omega) hσ with h | h | ⟨i, d, n, rfl, hok⟩
  · exact .inl h
  · exact .inr (.inl h)
  · cases i
    · simp [subOk, hw] at hok
    · simp [subOk, hw] at hok
    · exact .inr (.inr ⟨d, n, rfl⟩)
    · simp [subOk, hw] at hok

theorem isShfl_of_kind {e : Event} {md : ShflMode} {a : Value} {b c : Nat} {r : Value} {ok : Bool}
    (h : e.kind = .shfl md a b c r ok) : Execution.isShfl e = true := by
  obtain ⟨pc, kd⟩ := e
  simp only at h
  subst h
  rfl

theorem isShfl_coll {e : Event} (h : Execution.isShfl e = true) : Sched.isWarpColl e = true := by
  obtain ⟨pc, kd⟩ := e
  cases kd <;> simp_all [Execution.isShfl, Sched.isWarpColl]

/-- **A warp collective of warp 7 is a shuffle.** -/
theorem ix_coll_shfl (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hx : x < L.threads) (hw : warpOf L x = 7) {k : Nat}
    {e : Event} (he : X.get (x, k) = some e) (hne : ∀ f, e.kind ≠ .ub f)
    (hc : Sched.isWarpColl e = true) : Execution.isShfl e = true := by
  have hpcs := (coll_iff_pc hX he hne).mp hc
  obtain ⟨σ, hσ, -, -, hev⟩ := ev_state hp hX hFw he hne
  have hpc := Frame.event_pcU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ hne
  rw [hpc] at hpcs
  rcases ix_cls hFw hx hw hσ with ⟨d, n, rfl, hW, -⟩ | ⟨s, n, rfl, hs⟩ | ⟨d, n, rfl⟩
  · rw [pc_startup] at hpcs
    obtain ⟨j, hj⟩ := sh_site (by omega) hW hpcs
    have hev' : Startup.Ev L x d e := hev
    obtain ⟨site, x1, x2⟩ := d
    simp only at hj
    subst hj
    fin_cases j <;> obtain ⟨r, ok, hk⟩ := hev' <;> exact isShfl_of_kind hk
  · rcases hs with rfl | rfl
    · rw [pc_smr] at hpcs; simp [collPcs] at hpcs
    · have hev' : Wg1.Ev L x .hsh e := hev
      obtain ⟨r, ok, hk⟩ := hev'
      exact isShfl_of_kind hk
  · have hev' : Index.Ev P L x d e := hev
    obtain ⟨-, hK⟩ := hev'
    obtain ⟨site, el, ac, c⟩ := d
    have hpcd : (thread P L x).pc (ixS P L x ⟨site, el, ac, c⟩ n) = site.pc := rfl
    rw [hpcd] at hpcs
    cases site <;> simp [IxSite.pc, collPcs] at hpcs <;>
      (unfold Index.EvK at hK; simp only [Index.ShflEv] at hK
       rcases hK with ⟨a, b, c', r, ok, hk⟩ | ⟨f, hk⟩
       · exact isShfl_of_kind hk
       · exact absurd hk (hne f))

/-- **The prefix count of the collectives of warp 7 is its ghost count of shuffles.** -/
theorem ix_count (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hx : x < L.threads) (hw : warpOf L x = 7) :
    ∀ k σ, Frame.stateAt (thread P L) X x k = some (some σ) →
      ((X.tr x).take k).countP Sched.isWarpColl = σ.2 .shfl := by
  refine Frame.count_closed (C := thread P L) Sched.isWarpColl (fun σ => σ.2 .shfl) rfl ?_
  intro k e σ σ' he hσ _ hn
  obtain ⟨d0, n0⟩ := σ
  obtain ⟨-, h2⟩ := Code.counted_next_some (C := Code.glue (startupCode P L x)
    (Code.withStubs (frag P L x) Entry.pc) (Code.gatedExit (startupEnter P L x) (sel P L x)))
    (cls := cls) hn
  have hge : X.get (x, k) = some e := he
  have hc : Sched.isWarpColl e = Execution.isShfl e := by
    by_cases h : Execution.isShfl e = true
    · rw [h, isShfl_coll h]
    · have hne := (noUbBefore_of_noUb (x := x) (K := k + 1) hub).ne (Nat.lt_succ_self k) hge
      have : Sched.isWarpColl e ≠ true := fun hc =>
        h (ix_coll_shfl hp hX hFw hx hw hge hne hc)
      simp [h, this]
  rw [h2, hc]
  rfl

/-- **No state with no undefined behaviour before it has counted any.** -/
theorem state_noUb {k : Nat} (hub : NoUbBefore X x k) {σ : (thread P L x).D}
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) : σ.2 .ub = 0 := by
  rw [state_count hσ .ub]
  refine List.countP_eq_zero.mpr fun f hf hcl => ?_
  obtain ⟨j, hj, hfj⟩ := List.getElem_of_mem hf
  have hjk : j < k := by simp only [List.length_take] at hj; omega
  have hget : X.get (x, j) = some f := by
    show (X.tr x)[j]? = some f
    rw [← List.getElem?_take_of_lt hjk, List.getElem?_eq_getElem hj, hfj]
  obtain ⟨pc, kd⟩ := f
  cases kd <;> simp [cls] at hcl
  rename_i fl
  exact hub j hjk pc fl hget

/-- **No state with no undefined behaviour before it has counted an index one.** -/
theorem state_noUbIx {k : Nat} (hub : NoUbBefore X x k) {σ : (thread P L x).D}
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) : σ.2 (.index .ub) = 0 := by
  rw [state_count hσ (.index .ub)]
  refine List.countP_eq_zero.mpr fun f hf hcl => ?_
  obtain ⟨j, hj, hfj⟩ := List.getElem_of_mem hf
  have hjk : j < k := by simp only [List.length_take] at hj; omega
  have hget : X.get (x, j) = some f := by
    show (X.tr x)[j]? = some f
    rw [← List.getElem?_take_of_lt hjk, List.getElem?_eq_getElem hj, hfj]
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | ub fl => exact hub j hjk pc fl hget
  | wait l q ok a sc => cases ok <;> simp [cls, Index.cls, Index.kindOf] at hcl
  | _ => simp [cls, Index.cls, Index.kindOf] at hcl

/-- **A step of the index code stays in it.** -/
theorem ixD_next {d : Index.D} {n : Cls → Nat} {e : Event} {σ' : (thread P L x).D}
    (hn : (thread P L x).next (ixS P L x d n) e = some (some σ')) :
    ∃ d', Index.succ P L x d e = some (some d') ∧ σ' = ixS P L x d' (Code.bump cls n e) := by
  rw [next_sub] at hn
  have hs : (subFrag P L x .index).next d e = Index.succ P L x d e := rfl
  rcases hq : Index.succ P L x d e with _ | _ | d'
  · rw [hs, hq] at hn; cases hn
  · rw [hs, hq] at hn; cases hn
  · rw [hs, hq] at hn
    simp only [Option.map_some, Option.some.injEq] at hn
    subst hn
    refine ⟨d', rfl, ?_⟩
    rw [Code.backEnter_none (by show subBack P L x .index d' = none; rfl)]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
