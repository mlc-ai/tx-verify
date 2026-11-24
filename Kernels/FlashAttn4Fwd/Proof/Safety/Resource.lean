-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Tmem
public import Lemmas.Execution.ShapeExecution

@[expose] public section

/-! # The source, assumption, register and CLC branches of `Unsafe`

* The kernel's `tcgen05` instructions use one CTA group (`tc_group_uniform`, a fact of the
  program text).
* None of the kernel's assumptions declares an execution undefined (`no_assumption_ub`).
* No register request is unsafe (`no_reg_unsafe`). Every thread makes one request, the
  `setmaxnreg` of its warpgroup (`regOf`: warpgroups 0 and 1 raise to 176, warpgroup 2 lowers
  to 88, warpgroup 3 to 72) at its warp's site (`regPc`), before any other request and before
  its exit (`RegFacts`). So no request has a previous count, every request is of a whole
  warpgroup inside the block, a warpgroup's requests agree on direction and count, and no thread
  of the warpgroup exits before them. The lanes of a warp request at one site; the warps of a
  warpgroup need not (warpgroup 3's four warps, MMA, store, loader and idle, use four sites;
  EXT-BAR-PARTICIPANTS).
* The kernel makes no CLC request (`TmemFacts.no_clc`), so no CLC branch applies
  (`no_clcUnsafe`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Safety

open PTX PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The kernel's `tcgen05` instructions agree on their CTA group. -/
theorem tc_group_uniform : kernel.TcGroupUniform := kernel_groupUniform

/-! ### Assumptions -/

/-- **The kernel's assumptions declare no execution undefined.** -/
theorem no_assumption_ub : ¬ ∃ a ∈ asms, a.ub L mem0 X := by
  rintro ⟨a, ha, hu⟩
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact (show False from hu)

/-! ### Register requests -/

/-- The register request of warp `w`'s warpgroup: direction (`true`: increase) and count. -/
def regOf (w : Nat) : Bool × Nat :=
  if w < 8 then (true, 176) else if w < 12 then (false, 88) else (false, 72)

/-- The site of warp `w`'s register request: one per warp role. Warpgroup 3's four warps (MMA,
store, loader, idle) each make theirs at their own instruction. -/
def regPc (w : Nat) : Nat :=
  if w < 8 then Flow.setMaxReg_4 else if w < 12 then Flow.setMaxReg_5
  else if w = 12 then Flow.setMaxReg_2 else if w = 13 then Flow.setMaxReg_3
  else if w = 14 then Flow.setMaxReg_1 else Flow.setMaxReg_0

/-- The thread layer's facts for the register requests. -/
structure RegFacts (L : Launch) (X : Execution) : Prop where
  /-- A thread's register request is its first, at its warp's site, with its warpgroup's
  direction and count. -/
  request : ∀ {g k pc n inst : Nat} {inc : Bool}, g < L.threads →
    SetMaxNReg.Request X (g, k) pc inc n inst →
      SetMaxNReg.ordinal X (g, k) = 0 ∧ pc = regPc (warpOf L g) ∧
        (inc, n) = regOf (warpOf L g)
  /-- A thread exits after its request. -/
  exit : ∀ {g k pc : Nat}, g < L.threads → X.get (g, k) = some ⟨pc, .exit⟩ →
    1 ≤ SetMaxNReg.ordinal X (g, k)

/-- A request with no request before it has no previous count. -/
theorem prior_none {e : EvId} (h : SetMaxNReg.ordinal X e = 0) : SetMaxNReg.prior X e = none := by
  unfold SetMaxNReg.prior
  unfold SetMaxNReg.ordinal at h
  generalize (X.tr e.1).take e.2 = l at h ⊢
  induction l with
  | nil => rfl
  | cons ev l ih =>
    rw [List.countP_cons] at h
    have hl : l.countP SetMaxNReg.isRequest = 0 := by split at h <;> omega
    have hev : SetMaxNReg.isRequest ev = false := by
      cases hq : SetMaxNReg.isRequest ev
      · rfl
      · simp [hq] at h
    rw [List.foldl_cons]
    obtain ⟨pc, k⟩ := ev
    cases k
    case setMaxReg => simp [SetMaxNReg.isRequest] at hev
    all_goals exact ih hl

/-- **No register request is unsafe.** -/
theorem no_reg_unsafe (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hr : RegFacts L X) : ¬ SetMaxNReg.Unsafe L X := by
  rintro ⟨⟨g, k⟩, pc, inc, n, inst, hreq, hu⟩
  have hg : g < L.threads := event_thread_lt hX hreq
  obtain ⟨hord, hpc, hrq⟩ := hr.request hg hreq
  have hblock := hpre.block
  rcases hu with ⟨m, hm, -⟩ | hgrp | ⟨f, pc', inc', n', inst', hsg, hreq', hof, hne⟩ | ⟨hpos, -⟩
  · rw [prior_none hord] at hm
    cases hm
  · rw [hblock] at hgrp
    omega
  · obtain ⟨-, hpc', hrq'⟩ := hr.request (event_thread_lt hX hreq') hreq'
    obtain ⟨-, hwg⟩ := hsg
    have hwl := warpOf_lt hpre g
    have hwl' := warpOf_lt hpre f.1
    have hgrp : warpOf L g / 4 = warpOf L f.1 / 4 := by
      unfold warpOf
      rw [hblock] at hwg ⊢
      omega
    have hw : regOf (warpOf L g) = regOf (warpOf L f.1) := by
      unfold regOf
      have h8 : warpOf L g < 8 ↔ warpOf L f.1 < 8 := by omega
      have h12 : warpOf L g < 12 ↔ warpOf L f.1 < 12 := by omega
      simp only [h8, h12]
    rw [← hrq, ← hrq', Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rcases hne with hne | hne <;> exact hne rfl
  · omega

/-! ### Cluster launch control -/

/-- **No CLC branch applies**: the kernel makes no CLC request. -/
theorem no_clcUnsafe (ht : TmemFacts L X) : ¬ ClcUnsafe L X := by
  rintro ⟨i, s, tg, -, -, -, ⟨pc, he⟩, -⟩
  exact ht.no_clc he

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Safety
