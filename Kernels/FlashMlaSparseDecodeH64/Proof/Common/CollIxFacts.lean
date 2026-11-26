-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollIxCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowHead
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowSub
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLive
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # The collectives of an index lane, by its CTA's blocks

A CTA's index warp makes three shuffles before its blocks (the startup's two and the head's) and
two per block: the main cache's blocks (`nMin` of its length words, at the sites `sA1`, `sA2`,
pcs 2464 and 2467), then the extra cache's (`sB1`, `sB2`, pcs 2553 and 2556), to the CTA's block
count (`blocksOf`). `ixCn` is this list, `ixFacts` what an index state's position in it is. -/

/-! # The ghost count of shuffles at the states of warp 7

An index state's ghost count of shuffles is the role's (`ix_inv`): the head's shuffle makes it
three, with no index event before, and each step of the index code keeps it equal to `ixN`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {x : Nat}

/-- **A step from a startup state keeps the ghost count of shuffles at most two.** -/
theorem startup_shfl_le (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : warpOf L x = 7) {k : Nat}
    {d : Startup.D} {n : Cls → Nat} {e : Event} (he : X.get (x, k) = some e)
    (hne : ∀ f, e.kind ≠ .ub f)
    (hσ : Frame.stateAt (thread P L) X x k = some (some (.inl d, n)))
    (hW : Startup.RefW L x d (n .shfl)) :
    n .shfl + (if Execution.isShfl e then 1 else 0) ≤ 2 := by
  have hpc := Frame.event_pcU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ hne
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | sh j =>
    obtain ⟨h1, -⟩ := hW
    have := j.isLt
    split_ifs <;> omega
  | _ =>
    all_goals
      have h2 : n .shfl = 2 := hW.1
      have hn : ¬ Execution.isShfl e = true := fun h => by
        have hc := (coll_iff_pc hX he hne).mp (isShfl_coll h)
        rw [hpc, pc_startup] at hc
        obtain ⟨j, hj⟩ := sh_site (by omega) hW hc
        simp at hj
      simp [hn, h2]

/-- A step of the thread machine bumps the ghost counts. -/
theorem next_snd {σ σ' : (thread P L x).D} {e : Event}
    (hn : (thread P L x).next σ e = some (some σ')) : σ'.2 = Code.bump cls σ.2 e := by
  obtain ⟨d0, n0⟩ := σ
  exact (Code.counted_next_some (C := Code.glue (startupCode P L x)
    (Code.withStubs (frag P L x) Entry.pc) (Code.gatedExit (startupEnter P L x) (sel P L x)))
    (cls := cls) hn).2

/-- **The invariant**: an index state's ghost count of shuffles is `ixN`, and the states before
have counted no index event. -/
theorem ix_inv (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {K : Nat} (hub : NoUbBefore X x K) (hx : x < L.threads)
    (hw : warpOf L x = 7) :
    ∀ k σ, k ≤ K → k ≤ (X.tr x).length → Frame.stateAt (thread P L) X x k = some (some σ) →
      (∀ d n, σ = ixS P L x d n → n .shfl = Index.ixN L x d (fun c => n (.index c))) ∧
      ((¬ ∃ d n, σ = ixS P L x d n) → ∀ c, σ.2 (.index c) = 0) := by
  intro k0 σ0 hkK hk0 hst0
  refine Frame.stateAt_inv (C := thread P L) (X := X) (g := x) (fun k σ => k ≤ K →
    (∀ d n, σ = ixS P L x d n → n .shfl = Index.ixN L x d (fun c => n (.index c))) ∧
      ((¬ ∃ d n, σ = ixS P L x d n) → ∀ c, σ.2 (.index c) = 0)) ?_ ?_ k0 σ0 hk0 hst0 hkK
  · intro _
    refine ⟨fun d n h => ?_, fun _ c => rfl⟩
    cases h
  · intro k e s s' he hσ hI' hn hK1
    have hI := hI' (by omega)
    have hge : X.get (x, k) = some e := he
    have hne : ∀ f, e.kind ≠ .ub f := hub.ne (by omega) hge
    obtain ⟨σ0, hσ0, hJ, hi, hev⟩ := ev_state hp hX hFw hge hne
    rw [hσ] at hσ0
    obtain rfl := Option.some.inj (Option.some.inj hσ0)
    have hst : Frame.stateAt (thread P L) X x (k + 1) = some (some s') := by
      rw [Frame.stateAt_succ (C := thread P L) he, hσ]
      exact hn
    have hJ' := (follow_iff.mp hFw x hx (k + 1)).2 s' hst
    have hpc := Frame.event_pcU (C := thread P L) (fun _ _ => thread_sound hp) hX hge hσ hne
    have h2 := next_snd hn
    rcases ix_cls hFw hx hw hσ with ⟨d, n, rfl, hW, -⟩ | ⟨sh, n, rfl, hs⟩ | ⟨d, n, rfl⟩
    · have hsh := startup_shfl_le hp hX hw hge hne hσ hW
      have hlt := startup_pc hi
      refine ⟨fun d' m' hs' => ?_, fun _ c => ?_⟩
      · exfalso
        rw [hs'] at hJ'
        obtain ⟨-, ⟨h3, -, -⟩, -, -⟩ := hJ'
        have hm : m' = Code.bump cls n e := by rw [hs'] at h2; exact h2
        rw [hm] at h3
        have : Code.bump cls n e .shfl = n .shfl + if Execution.isShfl e then 1 else 0 := rfl
        omega
      · rw [h2]
        have hz : n (.index c) = 0 := hI.2 (by rintro ⟨d', n', h⟩; cases h) c
        have hq : Index.cls c e = false := Index.cls_outside (by
          unfold Index.inRole
          simp only [decide_eq_false_iff_not]
          rw [hpc]
          omega) c
        show n (.index c) + (if cls (.index c) e then 1 else 0) = 0
        simp [hz, cls, hq]
    · rcases hs with rfl | rfl
      · have hs' := smr_next hn
        refine ⟨fun d' m' h => ?_, fun _ c => ?_⟩
        · rw [hs'] at h; cases h
        · rw [h2]
          have hz : n (.index c) = 0 := hI.2 (by rintro ⟨d', n', h⟩; cases h) c
          have hq : Index.cls c e = false := Index.cls_outside (by
            unfold Index.inRole
            simp only [decide_eq_false_iff_not]
            rw [hpc, pc_smr]
            omega) c
          show n (.index c) + (if cls (.index c) e then 1 else 0) = 0
          simp [hz, cls, hq]
      · obtain ⟨-, -, -, h7⟩ := hsh_next hp hX hFw (hub.mono hK1) hx (by omega) hge hσ hn
        have hh := h7 hw
        refine ⟨fun d' m' hs' => ?_, fun hne => absurd ⟨_, _, hh⟩ hne⟩
        rw [hh] at hs'
        simp only [ixS, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and]
          at hs'
        obtain ⟨rfl, rfl⟩ := hs'
        obtain ⟨-, hR, -, -⟩ := hJ
        have hn2 : n .shfl = 2 := (show Wg1.HRef L x .hsh (n .shfl) from hR).1
        have hev' : Wg1.Ev L x .hsh e := hev
        obtain ⟨r, ok, hk⟩ := hev'
        have hsf := isShfl_of_kind hk
        have hz : (fun c => (Code.bump cls n e) (.index c)) = fun _ => 0 := by
          funext c
          have hz : n (.index c) = 0 := hI.2 (by rintro ⟨d', n', h⟩; cases h) c
          have hq : Index.cls c e = false := Index.cls_outside (by
            unfold Index.inRole
            simp only [decide_eq_false_iff_not]
            rw [hpc, pc_hsh]
            omega) c
          show n (.index c) + (if cls (.index c) e then 1 else 0) = 0
          simp [hz, cls, hq]
        obtain ⟨-, -, hz0⟩ := Index.zero_first P L x
        have hso : Index.soff (subFrag P L x .index).init.site = 0 := Index.soff_of_incW hz0
        show Code.bump cls n e .shfl = Index.ixN L x _ _
        rw [Index.ixN, hz, hso]
        have : Code.bump cls n e .shfl = n .shfl + if Execution.isShfl e then 1 else 0 := rfl
        simp [Index.blockOf, this, hsf, hn2]
    · obtain ⟨d', hsu, hs'⟩ := ixD_next hn
      refine ⟨fun d'' m'' h => ?_, fun hne => absurd ⟨_, _, hs'⟩ hne⟩
      rw [hs'] at h
      simp only [ixS, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨-, hR, -, -⟩ := hJ
      obtain ⟨-, -, hR'⟩ : 3 ≤ n .shfl ∧ subOk L x .index = true ∧
          (n .ub = 0 → Index.Ref P L x d (fun c => n (.index c))) := hR
      have hub0 : n (.index .ub) = 0 :=
        (state_count hσ (.index .ub)).trans (ix_take_noUb hX hge)
      have hb := hR' (state_noUb (hub.mono (by omega)) hσ) hub0
      have hev' : Index.Ev P L x d e := hev
      have hstep := Index.ixN_step hp hb hev' hne hsu
      have hs1 : Code.bump cls n e .shfl = n .shfl + if Execution.isShfl e then 1 else 0 := rfl
      rw [hs1, hI.1 d n rfl]
      exact hstep.symm

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {x : Nat}

/-- The main loop's block count of CTA `c`. -/
def ixM (P : Params) (L : Launch) (c : Nat) : Nat :=
  Index.nMin (lenWA P L c) (lenWB P L c)

/-- **The pc of the index warp's `n`-th collective** in CTA `c`. -/
def ixCn (P : Params) (L : Launch) (c n : Nat) : Option Nat :=
  if n < 3 then ([6, 9, 1843] : List Nat)[n]?
  else if (n - 3) / 2 < blocksOf P L c then
    some ((if (n - 3) / 2 < ixM P L c then 2464 else 2553) + 3 * ((n - 3) % 2))
  else none

theorem ixCn_blk (c b r : Nat) (hr : r < 2) :
    ixCn P L c (3 + 2 * b + r) = if b < blocksOf P L c then
      some ((if b < ixM P L c then 2464 else 2553) + 3 * r) else none := by
  have h1 : (3 + 2 * b + r - 3) / 2 = b := by omega
  have h2 : (3 + 2 * b + r - 3) % 2 = r := by omega
  have h3 : ¬ (3 + 2 * b + r < 3) := by omega
  simp only [ixCn, h1, h2, h3, ite_false]

theorem ixCn_val {c n p : Nat} (h : ixCn P L c n = some p) :
    (n < 3 ∧ p ∈ ([6, 9, 1843] : List Nat)) ∨ p = 2464 ∨ p = 2467 ∨ p = 2553 ∨ p = 2556 := by
  unfold ixCn at h
  split_ifs at h with h1 h2 h3
  · exact .inl ⟨h1, List.mem_of_getElem? h⟩
  · simp only [Option.some.injEq] at h
    have : (n - 3) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    right
    rcases (by omega : (n - 3) % 2 = 0 ∨ (n - 3) % 2 = 1) with h4 | h4 <;> simp [h4] at h <;> omega
  · simp only [Option.some.injEq] at h
    have : (n - 3) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    right
    rcases (by omega : (n - 3) % 2 = 0 ∨ (n - 3) % 2 = 1) with h4 | h4 <;> simp [h4] at h <;> omega

theorem ixCn_none {c n : Nat} (h : (ixCn P L c n).isSome = true) (hn : 3 ≤ n) :
    (n - 3) / 2 < blocksOf P L c := by
  by_contra hc
  have h1 : ¬ n < 3 := by omega
  simp [ixCn, h1, hc] at h

/-- **What an index state's ghost count is**: three, two per block of the counts and its own
block's shuffles before its site, the block against the CTA's main and total counts. -/
theorem ix_facts (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k : Nat} (hub : NoUbBefore X x k) {d : Index.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X x k = some (some (ixS P L x d n)))
    (hx : x < L.threads) (hw : warpOf L x = 7) :
    ∃ b, n .shfl = 3 + 2 * b + Index.soff d.site ∧
      Index.blockOf L x (fun c => n (.index c)) = b ∧ d.el < d.site.elems ∧
      ((d.site = .sA1 ∨ d.site = .sA2) → b < ixM P L (x / L.block) ∧
        b < blocksOf P L (x / L.block)) ∧
      ((d.site = .sB1 ∨ d.site = .sB2) → ixM P L (x / L.block) ≤ b ∧
        b < blocksOf P L (x / L.block)) ∧
      ((d.site = .bar ∨ d.site = .exit) → b = blocksOf P L (x / L.block)) := by
  have hinv : n .shfl = Index.ixN L x d (fun c => n (.index c)) := by
    by_cases hk : k ≤ (X.tr x).length
    · exact (ix_inv hp hX hFw hub hx hw k _ le_rfl hk hσ).1 d n rfl
    · have hσ2 := hσ
      rw [Frame.stateAt_of_le (by omega)] at hσ2
      exact (ix_inv hp hX hFw (hub.mono (show (X.tr x).length ≤ k by omega)) hx hw _ _
        (by omega) le_rfl hσ2).1 d n rfl
  obtain ⟨hok, hel, -⟩ := ix_ok hp hX hσ d n rfl
  have hJ := (follow_iff.mp hFw x hx k).2 _ hσ
  obtain ⟨-, hR, -, -⟩ := hJ
  obtain ⟨-, -, hR'⟩ : 3 ≤ n .shfl ∧ subOk L x .index = true ∧
      (n .ub = 0 → Index.Ref P L x d (fun c => n (.index c))) := hR
  obtain ⟨i, -, -, -, hc, hct, -⟩ := hR' (state_noUb hub hσ) (state_noUbIx hub hσ)
  have hbl : Index.blockOf L x (fun c => n (.index c)) = i := Index.blockOf_eq' hc
  refine ⟨i, by rw [hinv, Index.ixN, hbl], hbl, hel, ?_, ?_, ?_⟩
  all_goals intro hs
  · have hA : d.site ≠ .lenA := by rcases hs with h | h <;> rw [h] <;> simp
    have hB : d.site ≠ .lenB := by rcases hs with h | h <;> rw [h] <;> simp
    obtain ⟨h0, h1⟩ := ix_words_of hA hB hok
    have hm : Index.MainW P L x d.c i := by rcases hs with h | h <;> rw [h] at hct <;> exact hct
    have hlt := hm.1
    rw [h0, h1] at hlt
    exact ⟨hlt, lt_of_lt_of_le hlt (min_le_right _ _)⟩
  · have hA : d.site ≠ .lenA := by rcases hs with h | h <;> rw [h] <;> simp
    have hB : d.site ≠ .lenB := by rcases hs with h | h <;> rw [h] <;> simp
    obtain ⟨h0, h1⟩ := ix_words_of hA hB hok
    have hr := ix_rounds hp hX hσ hA hB
    have hm : Index.XW L x d.c i := by rcases hs with h | h <;> rw [h] at hct <;> exact hct
    obtain ⟨-, hge, hlt, -⟩ := hm
    rw [h0] at hge
    rw [hr] at hlt
    exact ⟨le_trans (min_le_left _ _) hge, hlt⟩
  · have hA : d.site ≠ .lenA := by rcases hs with h | h <;> rw [h] <;> simp
    have hB : d.site ≠ .lenB := by rcases hs with h | h <;> rw [h] <;> simp
    have hr := ix_rounds hp hX hσ hA hB
    have : i = roundsOf d.c.l0 d.c.l1 := by rcases hs with h | h <;> rw [h] at hct <;> exact hct
    rw [this]
    exact hr

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
