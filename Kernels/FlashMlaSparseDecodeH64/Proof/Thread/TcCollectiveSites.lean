-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ResourceEvents
import Lemmas.Flow.NotTcData
import Lemmas.Flow.OpPcsFast

public section

/-! # Tensor Memory warp-collective sources in the followed thread machine -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TcCollectiveSites

open PTX PTX.Flow

variable {P : Params} {L : Launch} {g : Nat}

/-- The Tensor Memory data sites in the softmax warpgroup. -/
inductive DataSite : Wg0.Site → Prop
  | scoreLoad (a k : Fin 2) : DataSite (.scoreLoad a k)
  | scoreWait : DataSite .scoreWait
  | rescaleLoad (j : Fin 4) : DataSite (.rescaleLoad j)
  | rescaleWait (j : Fin 4) : DataSite (.rescaleWait j)
  | rescaleStore (j : Fin 4) : DataSite (.rescaleStore j)
  | rescaleWaitSt (j : Fin 4) : DataSite (.rescaleWaitSt j)
  | outputLoad (j : Fin 4) : DataSite (.oLoad j)
  | outputWait (j : Fin 4) : DataSite (.oWait j)

private def dataLocations : List Nat :=
  [278, 280, 283, 285, 286, 716, 717, 814, 815, 817, 818, 915, 916, 918, 919, 1016,
    1017, 1019, 1020, 1117, 1118, 1201, 1202, 1361, 1362, 1519, 1520, 1676, 1677]

set_option maxRecDepth 100000 in
private theorem cover : OpPcsFast kernel.code tcDataOp dataLocations = true := by
  decide +kernel

local macro "exclude_data " h:ident : tactic => `(tactic| (
  exfalso
  revert $h
  first
  | decide
  | rename_i a; revert a; decide
  | rename_i a b; revert a b; decide
  | rename_i a b c; revert a b c; decide
  ))

private theorem dataSite_of_location {d : Machine.ThreadD}
    (h : (Machine.code P L g).pc d ∈ dataLocations) :
    ∃ q, d = .wg0 q ∧ DataSite q.site := by
  cases d
  case prologue s =>
    change s.pc ∈ dataLocations at h
    cases s <;> exclude_data h
  case wg0 d =>
    change d.site.pc ∈ dataLocations at h
    refine ⟨d, rfl, ?_⟩
    generalize d.site = s at h ⊢
    clear d
    cases s <;> first | constructor | exclude_data h
  case mma d =>
    exfalso
    change d.site.pc ∈ dataLocations at h
    generalize d.site = s at h
    clear d
    cases s <;> exclude_data h
  case tma d =>
    exfalso
    change d.site.pc ∈ dataLocations at h
    generalize d.site = s at h
    clear d
    cases s <;> exclude_data h
  case index d =>
    exfalso
    change d.site.pc ∈ dataLocations at h
    generalize d.site = s at h
    clear d
    cases s <;> exclude_data h
  case wg2 d =>
    exfalso
    change d.site.pc ∈ dataLocations at h
    generalize d.site = s at h
    clear d
    cases s <;> exclude_data h
  case idle s =>
    change s.pc ∈ dataLocations at h
    cases s <;> exclude_data h
  case head =>
    change 1843 ∈ dataLocations at h
    exclude_data h
  case done =>
    change 3611 ∈ dataLocations at h
    exclude_data h

/-- A Tensor Memory load, store or wait fires only at a typed WG0 data site. -/
private theorem data_of_fired {d : Machine.ThreadD} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some d) e o) (hk : isTcData e = true) :
    ∃ q, d = .wg0 q ∧ DataSite q.site := by
  obtain ⟨t, _, hf⟩ := hf
  change Fires t.pc (match kernel.code[(Machine.code P L g).pc d]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  cases hc : kernel.code[(Machine.code P L g).pc d]? with
  | none =>
    rw [hc] at hf
    rw [hf.1] at hk
    cases hk
  | some ins =>
    rw [hc] at hf
    exact dataSite_of_location (OpPcsFast.mem cover hc (fires_tcData_op hf hk))

/-- Every warp-collective Tensor Memory firing is a typed data site or a resource request. -/
theorem of_fired {mem0 : Mem0} {d : Machine.ThreadD} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hf : (Machine.machine P L g).Fired (some d) e o)
    (hk : isTcColl e = true) :
    (∃ q, d = .wg0 q ∧ DataSite q.site) ∨
    ∃ grp dst req, e.kind = .tc (.resource grp dst req) ∧
      ResourceEvents.Emits L g grp dst req d := by
  obtain ⟨tag, k⟩ := e
  obtain ⟨a, rfl⟩ := isTcColl_kind hk
  cases a <;> simp only [isTcColl, Bool.false_eq_true] at hk
  case resource grp dst req =>
    exact .inr ⟨grp, dst, req, rfl, ResourceEvents.emits hpre hf rfl⟩
  all_goals exact .inl (data_of_fired hf rfl)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TcCollectiveSites
