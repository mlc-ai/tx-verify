-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.RouteN
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.BiasN
import Kernels.InklingRelDecode.Proof.Softmax.Strict.Vals
import Kernels.InklingRelDecode.Flow.Code
@[expose] public section
/-! # The loop's route past the loop's loads: the guard is false, pcs 1124 to 1257 -/
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt
set_option maxRecDepth 100000
variable {e : Control.Entry} {L : Launch} {g : Nat}

theorem nxt_sat :
    ∀ j < 63, tagsSatF (lateQt (1124 + 2 * j + 1)) (lateQt (1124 + 2 * j)) = true := by
  decide +kernel

theorem nxt_sat' : tagsSatF (lateQt 1251) (lateQt 1250) = true := by decide +kernel

/-- **A load and the move after it** under a false guard keep the facts. -/
theorem skip_pair {F : List (Nat × Value)} (j : Nat) (hj : j < 63) (hg : (92, Value.pred false) ∈ F)
    (hw : ∀ q ∈ F, q.1 < 334 ∨ 396 < q.1) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) (1124 + 2 * j) F
      (1124 + 2 * j + 2) F := by
  obtain ⟨a, hc, -⟩ := ldOk_sound (nxt_ld j hj)
  refine SegQ.comp (b := 1124 + 2 * j + 1) (SegQ.tauAll _ (SegQF.skipGS (qt := lateQt) hc
    (fun _ hR => holds_mem hR hg) rfl (fun _ h => h) (nxt_sat j hj))) ?_
  refine mv_seg (p := 1124 + 2 * j) (r := 334 + j) (by omega)
    ((fp3_of (a := 1125) (b := 1251) (by decide +kernel)).mono (by omega) (by omega))
    (nxt_mv j hj) (fun q hq => ?_) (fun _ h => h)
  have := hw q hq
  omega

/-- The loads of the loop under a false guard, as far as the `k`-th. -/
theorem skip_upto {F : List (Nat × Value)} (hg : (92, Value.pred false) ∈ F)
    (hw : ∀ q ∈ F, q.1 < 334 ∨ 396 < q.1) :
    ∀ k ≤ 63, SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 1124 F
      (1124 + 2 * k) F := by
  intro k
  induction k with
  | zero => exact fun _ => SegQ.weaken fun _ h => h
  | succ k ih => exact fun hk => (ih (by omega)).comp (skip_pair k (by omega) hg hw)

/-- **All the loads of the loop under a false guard**: the span to the poll's address. -/
theorem skip_all {F : List (Nat × Value)} (hg : (92, Value.pred false) ∈ F)
    (hw : ∀ q ∈ F, q.1 < 334 ∨ 396 < q.1) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 1124 F 1251 F := by
  refine (skip_upto hg hw 63 le_rfl).comp ?_
  obtain ⟨a, hc, -⟩ := ldOk_sound nxt_last_ld
  exact SegQ.tauAll _ (SegQF.skipGS (qt := lateQt) hc (fun _ hR => holds_mem hR hg) rfl
    (fun _ h => h) nxt_sat')

/-- **The route past the loop's loads**: the next block has no bias load, the poll follows. -/
theorem route_wait {j : Nat} {v : Control.Carry} (m : Value) (ok : e.Ok) (hj : j ≤ e.limit)
    (hne : Control.nextEnabled e (g % L.block) j = false) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 1051
      (RF e L g m j v 1051) 1257 (RF e L g m j v 1257) := by
  have hg : (92, Value.pred false) ∈ RF e L g m j v 1124 := by
    have : Control.valueOf e L g ⟨.arrive, j, v⟩ 92 = .pred false := by
      simp [Control.valueOf, Control.scalarValue, hne]
    exact List.mem_append_right _ (this ▸ mem_factsFrom (by decide +kernel))
  have hw : ∀ q ∈ RF e L g m j v 1124, q.1 < 334 ∨ 396 < q.1 := by
    intro q hq
    rcases List.mem_append.mp hq with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> simp
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
      exact (by decide +kernel : ∀ r ∈ Control.ctlLive 1124, r < 334 ∨ 396 < r) r hr
  refine (route_nxt m ok hj).comp ((skip_all hg hw).comp ?_)
  refine SegQ.fromFacts (F' := RF e L g m j v 1251) (sub_facts (fun _ h => h)
    (by decide +kernel)) ?_
  refine SegQ.tauAll _ ?_
  simp only [RF, List.cons_append, List.nil_append]
  late_ctl 1251, 1257 using late_vals2
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
