-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.RegLedger
import Kernels.InklingRelDecode.Flow.Code.Part044

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

/-- The direction and count of the request at a position, as a table. -/
def requestSched (p : Nat) : Bool × Nat :=
  if p == 2333 || p == 2344 || p == 2422 then (false,24) else (true,256)

theorem requestAt_sched {p} (h : p ∈ requestPcs) : requestAt p = some (requestSched p) := by
  simp only [requestPcs,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

/-- Every request of the kernel is `inc 256` or `dec 24`. -/
theorem requestAt_cases {p inc n} (h : requestAt p = some (inc,n)) :
    (inc = true ∧ n = 256) ∨ (inc = false ∧ n = 24) := by
  have mem : p ∈ requestPcs := by
    by_contra no
    have key : ∀ q, q ∉ requestPcs → requestAt q = none := by
      intro q hq
      unfold requestAt
      cases hc : kernel.code[q]? with
      | none => rfl
      | some ins =>
        have := List.all_eq_true.mp reqChecked (ins,q) (List.mem_zipIdx_iff_getElem?.mpr hc)
        cases hop : ins.op <;> simp_all [reqCheckSite]
    rw [key p no] at h
    cases h
  rw [requestAt_sched mem] at h
  have := Option.some.inj h
  simp only [requestSched] at this
  split at this <;> simp_all

theorem dataReq_mem {p} (h : dataReq p = true) : p ∈ requestPcs := by
  simp only [dataReq,Bool.or_eq_true,beq_iff_eq] at h
  rcases h with (rfl|rfl)|rfl <;> decide

theorem workerReq_mem {p} (h : workerReq p = true) : p ∈ requestPcs := by
  simp only [workerReq,List.contains_cons,List.contains_nil,Bool.or_false,
    Bool.or_eq_true,beq_iff_eq] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem dataReq_sched {p} (h : dataReq p = true) : requestSched p = (true,256) := by
  simp only [dataReq,Bool.or_eq_true,beq_iff_eq] at h
  rcases h with (rfl|rfl)|rfl <;> decide

/-- Requests of equal ordinal made by workers have one direction and count. -/
theorem worker_class {p q c d r} (hp : workerReq p = true) (hq : workerReq q = true)
    (hl : ledgerOk p c r = true) (hm : ledgerOk q d r = true) :
    requestSched p = requestSched q := by
  simp only [workerReq,List.contains_cons,List.contains_nil,Bool.or_false,
    Bool.or_eq_true,beq_iff_eq] at hp hq
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp_all [ledgerOk,requestSched,requestPcs,barOneSites]

/-- A request that is not the loop head's and has a predecessor follows one barrier-1 event and
one request, or three and two. -/
theorem ledger_request {p c r} (h : ledgerOk p c r = true) (hp : p ∈ requestPcs) (ne : p ≠ 2337)
    (pos : 0 < r) : (c = 1 ∧ r = 1) ∨ (c = 3 ∧ r = 2) := by
  have h1 := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1
  simp only [hp,decide_true,Bool.not_true,Bool.false_or,Bool.or_eq_true,Bool.and_eq_true,
    beq_iff_eq] at h1
  simp only [requestPcs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all

/-- A barrier-1 event after none or two barrier-1 events follows one or two requests. -/
theorem ledger_barrier {p c r} (h : ledgerOk p c r = true) (hb : p ∈ barOneSites) :
    (c = 0 → 1 ≤ r) ∧ (c = 2 → 2 ≤ r) := by
  have h1 := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  simp only [hb,decide_true,Bool.not_true,Bool.false_or,Bool.and_eq_true,Bool.or_eq_true,
    bne_iff_ne,ne_eq,decide_eq_true_eq] at h1
  omega

/-- The request at the head of the dispatch loop is the one the assumption exempts. -/
theorem head_exempt : ¬ (Assumptions.all.all (fun a => !a.regSyncExempt 2337) = true) := by
  decide +kernel

/-- The position of the request of a warp with `r` requests before it: the default partition's by
the ordinal, a worker's by the round's phase and its warp (4 and 5 idle, 6 loader, 7 MMA). -/
def reqPcOf (w r : Nat) : Nat :=
  if w < 4 then (if r = 0 then 27 else if r = 1 then 574 else 2847)
  else if r % 3 = 0 then 2337
  else if r % 3 = 1 then (if w = 6 then 2344 else if w = 7 then 2422 else 2333)
  else (if w = 6 then 2420 else if w = 7 then 2555 else 2336)

end PTX.Kernels.InklingRelDecode.Proof.Lib
