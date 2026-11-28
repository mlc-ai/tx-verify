-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.RouteW
@[expose] public section
/-! # The loop's route: the test at pc 1050 sends the state to the epilogue, the loads, the poll -/
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt
set_option maxRecDepth 100000
variable {e : Control.Entry} {L : Launch} {g : Nat}

/-- The test of pc 1050 fails: the branch falls through, the facts of pc 1051 are kept. -/
theorem route_fall {j : Nat} {v : Control.Carry} (m : Value) (hz : j ≠ e.limit) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 1050
      (RF e L g m j v 1050) 1051 (RF e L g m j v 1051) := by
  have h91 : (91, Value.pred false) ∈ factsFrom (Control.ctlLive 1050)
      (Control.valueOf e L g ⟨.arrive, j, v⟩) := by
    have : Control.valueOf e L g ⟨.arrive, j, v⟩ 91 = .pred false := by
      simp [Control.valueOf, Control.scalarValue, hz]
    exact this ▸ mem_factsFrom (by decide +kernel)
  refine SegQ.comp (SegQ.tauAll _ (SegQF.braPS (qt := lateQt) false Flow.code_1050
    (fun _ hR => holds_mem hR (List.mem_append_right _ h91)) (fun t _ ha => Lib.bra_rule t _ ha)
    (segFree (by decide)) (by decide +kernel))) ?_
  exact SegQ.weaken fun _ h => holds_of_forall fun p hp => holds_mem h
    (sub_facts (fun _ h => h) (by decide +kernel) p hp)

/-- **The last block**: the span from the test to the epilogue's first poll. -/
theorem route_to_epi {j : Nat} {v : Control.Carry} (m : Value) (ok : e.Ok) (hz : j = e.limit) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 1050
      (RF e L g m j v 1050) 2565 (RF e L g m j v 2565) :=
  (route_branch m hz).comp (SegQ.fromFacts (sub_facts (fun _ h => h) (by decide +kernel))
    (route_epi m ok.blockWord))

/-- **A next block with bias loads**: the span from the test to the first load. -/
theorem route_to_nxt {j : Nat} {v : Control.Carry} (m : Value) (ok : e.Ok) (hj : j ≤ e.limit)
    (hz : j ≠ e.limit) : SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g))
      1050 (RF e L g m j v 1050) 1124 (RF e L g m j v 1124) :=
  (route_fall m hz).comp (route_nxt m ok hj)

/-- **A next block without them**: the span from the test to the poll. -/
theorem route_to_wait {j : Nat} {v : Control.Carry} (m : Value) (ok : e.Ok) (hj : j ≤ e.limit)
    (hz : j ≠ e.limit) (hne : Control.nextEnabled e (g % L.block) j = false) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 1050
      (RF e L g m j v 1050) 1257 (RF e L g m j v 1257) :=
  (route_fall m hz).comp (route_wait m ok hj hne)
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
