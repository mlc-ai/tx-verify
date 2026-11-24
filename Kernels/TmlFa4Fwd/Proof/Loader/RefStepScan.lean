-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.RefBase
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's reference invariant across the scheduler and the request's reads

The scheduler's reads, shuffles and ballots and the request's reads are counted by no class; the
first pass stays in its class or enters the drain with no packet (`A = 0`: slot 0, parity 1),
the second pass keeps the ring words and enters the drain with them. The used-K read enters the
first block's page loop. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {g w : Nat}

set_option maxHeartbeats 4000000 in
theorem step_setmax : StepRef p L g w .setmax := by
  intro v kk n e d' k A hJ hC hev hub hn
  simp only [Ev] at hev
  obtain ⟨_, _, _, hk⟩ := hev
  have hq := cls_setmax (L := L) (g := g) hk
  sc_split
  all_goals sc_close

set_option maxHeartbeats 4000000 in
theorem step_word (sk : Epilogue.Scan) : StepRef p L g w (.word sk) := by
  intro v kk n e d' k A hJ hC hev hub hn
  simp only [Ev, Epilogue.Ev, Site.toE] at hev
  rcases hev with ⟨_, hk⟩ | ⟨f, hk⟩
  swap; exact absurd hk (hub f)
  have hq := cls_rd (L := L) (g := g) hk
  cases sk <;> sc_split
  all_goals sc_close

set_option maxHeartbeats 4000000 in
theorem step_down (sk : Epilogue.Scan) : StepRef p L g w (.down sk) := by
  intro v kk n e d' k A hJ hC hev hub hn
  simp only [Ev, Epilogue.Ev, Site.toE] at hev
  obtain ⟨_, _, hk⟩ := hev
  have hq := cls_shfl (L := L) (g := g) hk
  cases sk <;> sc_split
  all_goals sc_close

set_option maxHeartbeats 4000000 in
theorem step_up (sk : Epilogue.Scan) (j : Fin 5) : StepRef p L g w (.up sk j) := by
  intro v kk n e d' k A hJ hC hev hub hn
  simp only [Ev, Epilogue.Ev, Site.toE] at hev
  obtain ⟨_, _, hk⟩ := hev
  have hq := cls_shfl (L := L) (g := g) hk
  cases sk <;> fin_cases j <;> sc_split
  all_goals sc_close

set_option maxHeartbeats 4000000 in
theorem step_total (sk : Epilogue.Scan) : StepRef p L g w (.total sk) := by
  intro v kk n e d' k A hJ hC hev hub hn
  simp only [Ev, Epilogue.Ev, Site.toE] at hev
  obtain ⟨_, _, hk⟩ := hev
  have hq := cls_shfl (L := L) (g := g) hk
  cases sk <;> sc_split
  all_goals sc_close

set_option maxHeartbeats 4000000 in
theorem step_vote (l : Bool) : StepRef p L g w (.vote l) := by
  intro v kk n e d' k A hJ hC hev hub hn
  simp only [Ev, Epilogue.Ev, Site.toE] at hev
  obtain ⟨_, hk⟩ := hev
  have hq := cls_vote (L := L) (g := g) hk
  cases l <;> sc_split
  all_goals sc_close

set_option maxHeartbeats 4000000 in
theorem step_pre (l : Bool) : StepRef p L g w (.pre l) := by
  intro v kk n e d' k A hJ hC hev hub hn
  simp only [Ev, Epilogue.Ev, Site.toE] at hev
  obtain ⟨_, _, hk⟩ := hev
  have hq := cls_shfl (L := L) (g := g) hk
  cases l <;> sc_split
  all_goals sc_close

set_option maxHeartbeats 4000000 in
theorem step_tiles (l : Bool) : StepRef p L g w (.tiles l) := by
  intro v kk n e d' k A hJ hC hev hub hn
  simp only [Ev, Epilogue.Ev, Site.toE] at hev
  obtain ⟨_, _, hk⟩ := hev
  have hq := cls_shfl (L := L) (g := g) hk
  cases l <;> sc_split
  all_goals sc_close

set_option maxHeartbeats 4000000 in
/-- The request's reads. -/
theorem step_req (s : Site) (hs : s = .q0 ∨ s = .q1 ∨ s = .uk) : StepRef p L g w s := by
  intro v kk n e d' k A hJ hC hev hub hn
  rcases hs with rfl | rfl | rfl <;> simp only [Ev] at hev <;>
    rcases hev with ⟨_, hk⟩ | ⟨f, hk⟩
  all_goals first | exact absurd hk (hub f) | skip
  all_goals have hq := cls_rd (L := L) (g := g) hk
  all_goals sc_split
  all_goals sc_close

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
