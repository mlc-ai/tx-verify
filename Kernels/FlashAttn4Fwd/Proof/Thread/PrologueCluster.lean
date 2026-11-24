-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.PrologueSteps
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # The second fence, the cluster barrier and the dispatch

Every thread fences the barrier initializations, arrives on and waits at the cluster barrier,
reads its cluster index and passes the role tests (lines 244-249, 709, 1523, 1615, 4516) to its
role's `setmaxnreg` (`dispatch`); every role but the idle warp first loads the item count
(`param_13`). The tests are evaluated with the warp index as a number, one case per warp. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Prologue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState} {e : Event}
  {ins : Instr}

/-- The local instructions from the cluster wait to the role's entry, without the item-count
load before it. -/
def dispatchLen (w : Nat) : Nat :=
  if w = 14 then 3 else if w = 15 then 5 else if w = 12 then 7 else if w = 13 then 9
  else if w < 8 then 11 else 14

/-- Where the dispatch tests lead warp `w`: its role's entry for the idle warp, the item-count
load before it for the others. -/
def dispatchEnd (w : Nat) : Nat :=
  if RoleKind.ofWarp w = .idle then (RoleKind.ofWarp w).entry else (RoleKind.ofWarp w).entry - 1

set_option maxHeartbeats 20000000 in
/-- The role tests, evaluated for warp `w`. -/
theorem dispatch_seg (hpre : Pre P L mem0) (hg : g < L.threads) (w : Nat) (hw : w < 16)
    {u : TState} (h : At u (Site.clWait.pc + 1) (factsAt L g w (rankOf L g) Site.clWait.pc)) :
    ∃ t', run kernel asms L g (dispatchLen w) u = some t' ∧
      At t' (dispatchEnd w) (factsAt L g w (rankOf L g) (dispatchEnd w)) := by
  have hcl := clusterOf_lt hpre hg
  have hcs := clusters_le hpre
  have hct : truncBits 32 (BitVec.ofNat 64 (L.clusterOfCta (g / L.block))) =
      BitVec.ofNat 64 (clusterOf L g) :=
    truncBits_ofNat (by simp only [clusterOf, ctaOf] at hcl; omega) (by decide)
  interval_cases w <;> pro_seg h hpre [sreg_cluster hpre, hct]

/-- The item-count load before a role's `setmaxnreg`: `ld.param.b32 dst, [param 13]`. -/
def ldTot (dst : Nat) : Op :=
  .mem { kind := .load, space := some .param, sem := .weak, elem := .int .b 32,
         addr := ⟨.param (param "13") false, 0⟩, dsts := [some dst] }

/-- The item-count load before a role's `setmaxnreg`. -/
theorem ld_tot (hpre : Pre P L mem0) {w rk pc dst : Nat} {t : TState}
    (hc : kernel.code[pc]? = some ⟨none, ldTot dst⟩)
    (h : At t pc (factsAt L g w rk pc)) (hv : valueOf L g w rk dst = b32 (totOf L))
    (hl : ∀ x ∈ Flow.live (pc + 1), x ∈ [dst] ∨ x ∈ Flow.live pc)
    (hsf : Assumption.SegFreePc asms pc) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' (pc + 1) (factsAt L g w rk (pc + 1)) :=
  ⟨_, run_local hc rfl h
    (exec_ldParam (w := 32) (params_tot hpre) (Assumption.SegFreePc.of_eq h.1 hsf)
      asms_localRule_none), at_set h
    (by rw [hv, b32, truncBits_ofNat (by have := totOf_lt hpre; omega) (by decide)]) hl⟩

/-- The code before each role's entry loads the item count. -/
theorem code_tot (w : Nat) (hw : w < 16) (hi : RoleKind.ofWarp w ≠ .idle) :
    ∃ dst, kernel.code[dispatchEnd w]? = some ⟨none, ldTot dst⟩ ∧
      dispatchEnd w + 1 = (RoleKind.ofWarp w).entry ∧
      (∀ x ∈ Flow.live (dispatchEnd w + 1), x ∈ [dst] ∨ x ∈ Flow.live (dispatchEnd w)) ∧
      Assumption.SegFreePc asms (dispatchEnd w) ∧
      ∀ rk, valueOf L g w rk dst = b32 (totOf L) := by
  have hs : ∀ pc dst, kernel.code[pc]? = some ⟨none, ldTot dst⟩ →
      dispatchEnd w = pc → dispatchEnd w + 1 = (RoleKind.ofWarp w).entry →
      (∀ x ∈ Flow.live (pc + 1), x ∈ [dst] ∨ x ∈ Flow.live pc) →
      (∀ rk, valueOf L g w rk dst = b32 (totOf L)) → Assumption.SegFreePc asms pc →
      ∃ dst, kernel.code[dispatchEnd w]? = some ⟨none, ldTot dst⟩ ∧
        dispatchEnd w + 1 = (RoleKind.ofWarp w).entry ∧
        (∀ x ∈ Flow.live (dispatchEnd w + 1), x ∈ [dst] ∨ x ∈ Flow.live (dispatchEnd w)) ∧
        Assumption.SegFreePc asms (dispatchEnd w) ∧
        ∀ rk, valueOf L g w rk dst = b32 (totOf L) := by
    rintro pc dst hc rfl he hl hv hsf
    exact ⟨dst, hc, he, hl, hsf, hv⟩
  interval_cases w
  · exact hs _ _ Flow.code_1205 rfl rfl (by table_decide) (fun _ => rfl) (by seg_free_pc)
  · exact hs _ _ Flow.code_1205 rfl rfl (by table_decide) (fun _ => rfl) (by seg_free_pc)
  · exact hs _ _ Flow.code_1205 rfl rfl (by table_decide) (fun _ => rfl) (by seg_free_pc)
  · exact hs _ _ Flow.code_1205 rfl rfl (by table_decide) (fun _ => rfl) (by seg_free_pc)
  · exact hs _ _ Flow.code_1205 rfl rfl (by table_decide) (fun _ => rfl) (by seg_free_pc)
  · exact hs _ _ Flow.code_1205 rfl rfl (by table_decide) (fun _ => rfl) (by seg_free_pc)
  · exact hs _ _ Flow.code_1205 rfl rfl (by table_decide) (fun _ => rfl) (by seg_free_pc)
  · exact hs _ _ Flow.code_1205 rfl rfl (by table_decide) (fun _ => rfl) (by seg_free_pc)
  · exact hs _ _ Flow.code_3753 rfl rfl (by table_decide) (fun _ => rfl) (by seg_free_pc)
  · exact hs _ _ Flow.code_3753 rfl rfl (by table_decide) (fun _ => rfl) (by seg_free_pc)
  · exact hs _ _ Flow.code_3753 rfl rfl (by table_decide) (fun _ => rfl) (by seg_free_pc)
  · exact hs _ _ Flow.code_3753 rfl rfl (by table_decide) (fun _ => rfl) (by seg_free_pc)
  · exact hs _ _ Flow.code_540 rfl rfl (by table_decide) (fun _ => rfl) (by seg_free_pc)
  · exact hs _ _ Flow.code_1129 rfl rfl (by table_decide) (fun _ => rfl) (by seg_free_pc)
  · exact hs _ _ Flow.code_193 rfl rfl (by table_decide) (fun _ => rfl) (by seg_free_pc)
  · exact absurd rfl hi

/-- **Routing.** From the cluster wait, local steps reach the entry of the thread's role (by its
warp index), with the prologue's registers live there. -/
theorem dispatch (hpre : Pre P L mem0) (hg : g < L.threads) {u : TState}
    (h : At u (Site.clWait.pc + 1) (factsAt L g (warpOf L g) (rankOf L g) Site.clWait.pc)) :
    ∃ k t', run kernel asms L g k u = some t' ∧
      At t' (RoleKind.ofWarp (warpOf L g)).entry
        (factsAt L g (warpOf L g) (rankOf L g) (RoleKind.ofWarp (warpOf L g)).entry) := by
  have hw := warpOf_lt hpre g
  obtain ⟨t1, hr1, h1⟩ := dispatch_seg hpre hg _ hw h
  by_cases hi : RoleKind.ofWarp (warpOf L g) = .idle
  · refine ⟨_, t1, hr1, ?_⟩
    simpa [dispatchEnd, hi] using h1
  · obtain ⟨dst, hc, he, hl, hsf, hv⟩ := code_tot (L := L) (g := g) _ hw hi
    obtain ⟨t2, hr2, h2⟩ := ld_tot hpre hc h1 (hv _) hl hsf
    rw [he] at h2
    exact ⟨_, t2, run_comp hr1 hr2, h2⟩

/-- The second fence, then the cluster arrival. -/
theorem step_fence1 (hs : d.site = .fence1) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceMbarInit_1)
  obtain rfl := fires_next (show AdvancesOp .fenceMbarInit from trivial) hf
  right
  exact ⟨.inl ⟨.clArrive⟩, _, by simp [next], .refl,
    good_inl (At.mono (At.next h) (holds_factsFrom_mono h.2.2.2.2 (by table_decide)))
      (inv_of (by simp) (by simp) (by simp) (by simp))⟩

/-- The cluster arrival, then the wait. -/
theorem step_clArrive (hs : d.site = .clArrive) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_0)
  obtain rfl := fires_next (show AdvancesOp (.cluster _) from trivial) hf
  right
  exact ⟨.inl ⟨.clWait⟩, _, by simp [next], .refl,
    good_inl (At.mono (At.next h) (holds_factsFrom_mono h.2.2.2.2 (by table_decide)))
      (inv_of (by simp) (by simp) (by simp) (by simp))⟩

/-- The cluster wait, then the dispatch to the thread's role. -/
theorem step_clWait (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .clWait)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_0)
  obtain rfl := fires_next (show AdvancesOp (.cluster _) from trivial) hf
  right
  obtain ⟨k, t', hr, ht⟩ := dispatch hpre hg (At.next h)
  exact ⟨.inr (RoleKind.ofWarp (warpOf L g)), t', by simp [next], run_rtg hr, ht⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Prologue
