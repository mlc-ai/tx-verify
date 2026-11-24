-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ClcCount
public import Lemmas.Flow.OpPcsFast

@[expose] public section

/-! # The response a CLC query reports

Every role reads its CTA's CLC response right after a successful poll of its response barrier
and queries the response it read: along a role's run, at the read, the queries and between them
(`Prologue.Role.clcStage`), the thread holds the response decoded from its read
(`QueryRel`). A query event is at a role's query site (decided on the code), so it reports the
response the thread read right after its latest successful response poll (`clc_query`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The kernel's queries are at its query sites (decided on the code). -/
theorem kernel_query_pcs : OpPcs kernel.code queryOp Flow.clcQuery.toList = true :=
  OpPcsFast.opPcs (by decide +kernel)

theorem query_pc {pc : Nat} {ins : Instr} (hc : kernel.code[pc]? = some ins)
    (hq : queryOp ins.op = true) : pc ∈ Flow.clcQuery.toList :=
  OpPcs.mem kernel_query_pcs hc hq

/-- The response buffer of thread `g`'s CTA. -/
abbrev respLoc (L : Launch) (g : Nat) : Loc := ⟨.shared, g / L.block, L.sharedBase + 144⟩

/-- At stage 1 the thread has just polled its response barrier successfully; at stage `n ≥ 2`
it read the response `n - 1` events ago, right after that poll, and holds it. -/
def QueryRel (L : Launch) (g : Nat) (n : Nat) (v : Value) (es : List Event) : Prop :=
  (n = 1 → ∃ pc p acq sc, es.getLast? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩) ∧
  (2 ≤ n → ∃ j pc p acq sc pcr, ∃ a : Acc, ∃ bs rr, j + n = es.length ∧
    es[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ ∧ es[j + 1]? = some ⟨pcr, .rd a bs⟩ ∧
    a.loc = respLoc L g ∧ a.size = 16 ∧ Flow.responseOf bs = some rr ∧ v = .clc rr)

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

theorem QueryRel.zero {v : Value} {es : List Event} : QueryRel L g 0 v es :=
  ⟨(fun h => nomatch h), fun h => by omega⟩

theorem QueryRel.poll {v' : Value} {es : List Event} {pc p : Nat} {acq : Bool} {sc : MbarScope} :
    QueryRel L g 1 v' (es ++ [⟨pc, .wait (clcResp L g) p true acq sc⟩]) :=
  ⟨fun _ => ⟨pc, p, acq, sc, by simp⟩, fun h => by omega⟩

theorem QueryRel.read {v : Value} {es : List Event} (h : QueryRel L g 1 v es) {pcr : Nat}
    {a : Acc} {bs : List (Option Byte)} {rr : ClcResponse} (ha : a.loc = respLoc L g)
    (hs : a.size = 16) (hr : Flow.responseOf bs = some rr) :
    QueryRel L g 2 (.clc rr) (es ++ [⟨pcr, .rd a bs⟩]) := by
  obtain ⟨pc, p, acq, sc, hl⟩ := h.1 rfl
  refine ⟨(fun h => nomatch h), fun _ => ?_⟩
  obtain ⟨es', rfl⟩ : ∃ es', es = es' ++ [⟨pc, .wait (clcResp L g) p true acq sc⟩] := by
    rw [List.getLast?_eq_some_iff] at hl
    exact hl
  refine ⟨es'.length, pc, p, acq, sc, pcr, a, bs, rr, by simp, by simp, by simp, ha, hs, hr, rfl⟩

/-- An acquire load of the response buffer's sixteen bytes, decoded as a response, is the read
that the thread's stage 2 holds. -/
theorem QueryRel.readOf {v : Value} {pre : List Event} {e : Event} {pc : Nat} {t : TState}
    {o : Option TState} {dst base : Nat} (hq : QueryRel L g 1 v pre)
    (hf : Fires pc (eventTmpl Prod L g t (.mem
      { kind := .load, space := some (.shared .cta), sem := .acquire, scope := some .cta,
        elem := .int .b 128, addr := ⟨.reg base 32, 0⟩, dsts := [some dst] })) e o)
    (hsub : t.sub = 0) (hb : L.sharedBase + 144 < 2 ^ 32)
    (hr : t.regs base = some (b32 (L.sharedBase + 144))) {a : Acc} {bs : List (Option Byte)}
    {rr : ClcResponse} (hk : e.kind = .rd a bs) (hrr : Flow.responseOf bs = some rr) :
    QueryRel L g 2 (.clc rr) (pre ++ [e]) := by
  obtain ⟨ha, hs⟩ := (fires_ldAcquire128 (effAddr_b32 hr hb) hsub hf) a bs hk
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  exact QueryRel.read hq ha hs hrr

theorem QueryRel.next {v : Value} {es : List Event} (h : QueryRel L g 2 v es) (e : Event) :
    QueryRel L g 3 v (es ++ [e]) := by
  refine ⟨(fun h => nomatch h), fun _ => ?_⟩
  obtain ⟨j, pc, p, acq, sc, pcr, a, bs, rr, hj, hw, hr, ha, hs, hres, hv⟩ := h.2 (le_refl _)
  have hl : j + 1 < es.length := by omega
  refine ⟨j, pc, p, acq, sc, pcr, a, bs, rr, by simp; omega, ?_, ?_, ha, hs, hres, hv⟩
  · rw [List.getElem?_append_left (by omega)]; exact hw
  · rw [List.getElem?_append_left hl]; exact hr

namespace Loader

/-- The role's stage of a CLC response. -/
def D.clcStage (d : D) : Nat :=
  match d.site with | .clcLoad => 1 | .clcStatus => 2 | .clcFirst => 3 | _ => 0

set_option maxHeartbeats 8000000 in
theorem query_step (hpre : Pre P L mem0) {d d' : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {pre : List Event} (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : QueryRel L g d.clcStage d.resp pre) :
    QueryRel L g d'.clcStage d'.resp (pre ++ [e]) := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  obtain ⟨site, m, n, q, cp, resp, x⟩ := d
  cases site
  case clcWait =>
    obtain ⟨p, ok, acq, sc, -, rfl⟩ := clcWait_event hpre rfl hat hc hf
    simp only [next] at hn
    cases ok <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn <;>
      subst hn <;> simp only [D.clcStage]
    · exact QueryRel.zero
    · exact QueryRel.poll
  case clcLoad =>
    code_at hc
    subst hc
    have hr : t.regs 814 = some (b32 (L.sharedBase + 144)) :=
      (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by loader_values))
    rcases fires_ldAcquire_kind hf with ⟨a, bs, hk⟩ | ⟨f, hk⟩
    · simp only [next, hk, Option.map_eq_some_iff, Option.some.injEq] at hn
      obtain ⟨rr, hrr, rfl⟩ := hn
      exact QueryRel.readOf hq hf hat.2.1 (by omega) hr hk hrr
    · simp [next, hk] at hn
  case clcStatus =>
    simp only [next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      split_ifs <;> simp only [D.clcStage]
      · exact QueryRel.next hq _
      · exact QueryRel.zero
    · cases hn
  all_goals clear hat hc hf
  all_goals simp only [next, endOfTrip] at hn
  clc_sweep hn
  all_goals simp only [D.clcStage]
  all_goals exact QueryRel.zero

/-- A query is at the clcStatus or clcFirst site, and reports the response in the role's
response register. -/
theorem query_site {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) {q : ClcQuery} {rr : ClcResponse}
    (hk : e.kind = .clcQuery q rr) :
    (d.clcStage = 2 ∨ d.clcStage = 3) ∧ ∀ r0, d.resp = .clc r0 → rr = r0 := by
  have hpc := query_pc hc (fires_query_op hf hk)
  obtain ⟨site, m, n, q, cp, resp, x⟩ := d
  cases site
  case clcStatus =>
    code_at hc
    subst hc
    have hR : t.regs 973 = some resp :=
      (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by loader_values))
    exact ⟨.inl rfl, fun r0 hres => by
      simp only at hres; subst hres; exact fires_clcQuery_value hR hf _ _ hk⟩
  case clcFirst =>
    code_at hc
    subst hc
    have hR : t.regs 973 = some resp :=
      (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by loader_values))
    exact ⟨.inr rfl, fun r0 hres => by
      simp only at hres; subst hres; exact fires_clcQuery_value hR hf _ _ hk⟩
  all_goals exfalso
  all_goals clear hat hc hf hk
  all_goals revert hpc
  all_goals simp only [Site.pc]
  all_goals decide +revert

end Loader

namespace Mma

/-- The role's stage of a CLC response. -/
def D.clcStage (d : D) : Nat :=
  match d.site with | .clcLoad => 1 | .clcStatus => 2 | .clcFirst => 3 | _ => 0

set_option maxHeartbeats 8000000 in
theorem query_step (hpre : Pre P L mem0) {d d' : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {pre : List Event} (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : QueryRel L g d.clcStage d.resp pre) :
    QueryRel L g d'.clcStage d'.resp (pre ++ [e]) := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := d
  cases site
  case clcWait =>
    obtain ⟨p, ok, acq, sc, -, rfl⟩ := clcWait_event hpre rfl hat hc hf
    simp only [next] at hn
    cases ok <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn <;>
      subst hn <;> simp only [D.clcStage]
    · exact QueryRel.zero
    · exact QueryRel.poll
  case clcLoad =>
    code_at hc
    subst hc
    have hr : t.regs 851 = some (b32 (L.sharedBase + 144)) :=
      (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by mma_values))
    rcases fires_ldAcquire_kind hf with ⟨a, bs, hk⟩ | ⟨f, hk⟩
    · simp only [next, hk, Option.map_eq_some_iff, Option.some.injEq] at hn
      obtain ⟨rr, hrr, rfl⟩ := hn
      exact QueryRel.readOf hq hf hat.2.1 (by omega) hr hk hrr
    · simp [next, hk] at hn
  case clcStatus =>
    simp only [next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      split_ifs <;> simp only [D.clcStage]
      · exact QueryRel.next hq _
      · exact QueryRel.zero
    · cases hn
  all_goals clear hat hc hf
  all_goals simp only [next, endOfTrip] at hn
  clc_sweep hn
  all_goals simp only [D.clcStage]
  all_goals exact QueryRel.zero

/-- A query is at the clcStatus or clcFirst site, and reports the response in the role's
response register. -/
theorem query_site {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) {q : ClcQuery} {rr : ClcResponse}
    (hk : e.kind = .clcQuery q rr) :
    (d.clcStage = 2 ∨ d.clcStage = 3) ∧ ∀ r0, d.resp = .clc r0 → rr = r0 := by
  have hpc := query_pc hc (fires_query_op hf hk)
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := d
  cases site
  case clcStatus =>
    code_at hc
    subst hc
    have hR : t.regs 975 = some resp :=
      (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by mma_values))
    exact ⟨.inl rfl, fun r0 hres => by
      simp only at hres; subst hres; exact fires_clcQuery_value hR hf _ _ hk⟩
  case clcFirst =>
    code_at hc
    subst hc
    have hR : t.regs 975 = some resp :=
      (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by mma_values))
    exact ⟨.inr rfl, fun r0 hres => by
      simp only at hres; subst hres; exact fires_clcQuery_value hR hf _ _ hk⟩
  all_goals exfalso
  all_goals clear hat hc hf hk
  all_goals revert hpc
  all_goals simp only [Site.pc]
  all_goals decide +revert

end Mma

namespace Scheduler

/-- The role's stage of a CLC response. -/
def D.clcStage (d : D) : Nat :=
  match d.site with | .clcLoad => 1 | .clcStatus => 2 | .clcFirst => 3 | _ => 0

set_option maxHeartbeats 8000000 in
theorem query_step (hpre : Pre P L mem0) {d d' : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {pre : List Event} (hi : Inv d) (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : QueryRel L g d.clcStage d.resp pre) :
    QueryRel L g d'.clcStage d'.resp (pre ++ [e]) := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  obtain ⟨site, ap, cp, resp, x⟩ := d
  cases site
  case clcWait =>
    obtain ⟨ok, acq, sc, rfl⟩ := clcWait_event hpre hi rfl hat hc hf
    simp only [next] at hn
    cases ok <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn <;>
      subst hn <;> simp only [D.clcStage]
    · exact QueryRel.zero
    · exact QueryRel.poll
  case clcLoad =>
    code_at hc
    subst hc
    have hr : t.regs 640 = some (b32 (L.sharedBase + 144)) :=
      (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by sched_values))
    rcases fires_ldAcquire_kind hf with ⟨a, bs, hk⟩ | ⟨f, hk⟩
    · simp only [next, hk, Option.map_eq_some_iff, Option.some.injEq] at hn
      obtain ⟨rr, hrr, rfl⟩ := hn
      exact QueryRel.readOf hq hf hat.2.1 (by omega) hr hk hrr
    · simp [next, hk] at hn
  case clcStatus =>
    simp only [next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      split_ifs <;> simp only [D.clcStage]
      · exact QueryRel.next hq _
      · exact QueryRel.zero
    · cases hn
  all_goals clear hat hc hf
  all_goals simp only [next, loopHead] at hn
  clc_sweep hn
  all_goals simp only [D.clcStage]
  all_goals exact QueryRel.zero

/-- A query is at the clcStatus or clcFirst site, and reports the response in the role's
response register. -/
theorem query_site {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) {q : ClcQuery} {rr : ClcResponse}
    (hk : e.kind = .clcQuery q rr) :
    (d.clcStage = 2 ∨ d.clcStage = 3) ∧ ∀ r0, d.resp = .clc r0 → rr = r0 := by
  have hpc := query_pc hc (fires_query_op hf hk)
  obtain ⟨site, ap, cp, resp, x⟩ := d
  cases site
  case clcStatus =>
    code_at hc
    subst hc
    have hR : t.regs 971 = some resp :=
      (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by sched_values))
    exact ⟨.inl rfl, fun r0 hres => by
      simp only at hres; subst hres; exact fires_clcQuery_value hR hf _ _ hk⟩
  case clcFirst =>
    code_at hc
    subst hc
    have hR : t.regs 971 = some resp :=
      (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by sched_values))
    exact ⟨.inr rfl, fun r0 hres => by
      simp only at hres; subst hres; exact fires_clcQuery_value hR hf _ _ hk⟩
  all_goals exfalso
  all_goals clear hat hc hf hk
  all_goals revert hpc
  all_goals simp only [Site.pc]
  all_goals decide +revert

end Scheduler

namespace Consumer

/-- The role's stage of a CLC response. -/
def D.clcStage (d : D) : Nat :=
  match d.site with | .clcLoad => 1 | .clcStatus => 2 | .clcFirst => 3 | _ => 0

set_option maxHeartbeats 8000000 in
theorem query_step (hpre : Pre P L mem0) {d d' : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {pre : List Event} (hat : (code L g).AtD (.inr (.cons d)) t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : QueryRel L g d.clcStage d.resp pre) :
    QueryRel L g d'.clcStage d'.resp (pre ++ [e]) := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases site
  case clcWait =>
    obtain ⟨p, ok, acq, sc, -, rfl⟩ := clcWait_event hpre rfl hat.2.2.2.2 hc hf
    simp only [next] at hn
    cases ok <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn <;>
      subst hn <;> simp only [D.clcStage]
    · exact QueryRel.zero
    · exact QueryRel.poll
  case clcLoad =>
    code_at hc
    subst hc
    have hr : t.regs 142 = some (b32 (L.sharedBase + 144)) :=
      (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by cons_values))
    rcases fires_ldAcquire_kind hf with ⟨a, bs, hk⟩ | ⟨f, hk⟩
    · simp only [next, hk, Option.map_eq_some_iff, Option.some.injEq] at hn
      obtain ⟨rr, hrr, rfl⟩ := hn
      exact QueryRel.readOf hq hf hat.2.1 (by omega) hr hk hrr
    · simp [next, hk] at hn
  case clcStatus =>
    simp only [next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      split_ifs <;> simp only [D.clcStage]
      · exact QueryRel.next hq _
      · exact QueryRel.zero
    · cases hn
  all_goals clear hat hc hf
  all_goals simp only [next] at hn
  clc_sweep hn
  all_goals simp only [D.clcStage]
  all_goals exact QueryRel.zero

/-- A query is at the clcStatus or clcFirst site, and reports the response in the role's
response register. -/
theorem query_site {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : (code L g).AtD (.inr (.cons d)) t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) {q : ClcQuery} {rr : ClcResponse}
    (hk : e.kind = .clcQuery q rr) :
    (d.clcStage = 2 ∨ d.clcStage = 3) ∧ ∀ r0, d.resp = .clc r0 → rr = r0 := by
  have hpc := query_pc hc (fires_query_op hf hk)
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases site
  case clcStatus =>
    code_at hc
    subst hc
    have hR : t.regs 969 = some resp :=
      (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by cons_values))
    exact ⟨.inl rfl, fun r0 hres => by
      simp only at hres; subst hres; exact fires_clcQuery_value hR hf _ _ hk⟩
  case clcFirst =>
    code_at hc
    subst hc
    have hR : t.regs 969 = some resp :=
      (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by cons_values))
    exact ⟨.inr rfl, fun r0 hres => by
      simp only at hres; subst hres; exact fires_clcQuery_value hR hf _ _ hk⟩
  all_goals exfalso
  all_goals clear hat hc hf hk
  all_goals revert hpc
  all_goals simp only [Site.pc]
  all_goals decide +revert

end Consumer

/-- Each role's stage of a CLC response. -/
def Prologue.Role.clcStage : Prologue.Role → Nat
  | .loader l => l.clcStage
  | .mma m => m.clcStage
  | .sched s => s.clcStage
  | .cons c => c.clcStage

/-- The response a role holds. -/
def Prologue.Role.resp : Prologue.Role → Value
  | .loader l => l.resp
  | .mma m => m.resp
  | .sched s => s.resp
  | .cons c => c.resp

/-- The response relation along a thread's run: nothing in the prologue. -/
def QueryInv (L : Launch) (g : Nat) : ThreadD → List Event → Prop
  | .inl _, _ => True
  | .inr r, es => QueryRel L g r.clcStage r.resp es

/-- A role's first state holds no response. -/
theorem Prologue.clc_stage_start {p : Prologue.D} {e : Event} {r : Prologue.Role}
    (hn : Prologue.next L g p e = some (some (.inr r))) : r.clcStage = 0 := by
  cases r with
  | loader l => rcases Prologue.next_loader hn with rfl | rfl <;>
      simp [Prologue.Role.clcStage, Loader.D.clcStage, Prologue.loaderStart, Prologue.loaderIdle]
  | mma m => rcases Prologue.next_mma hn with h | h <;>
      simp [Prologue.Role.clcStage, Mma.D.clcStage, h]
  | sched s => rw [Prologue.next_sched hn]; simp [Prologue.Role.clcStage, Scheduler.D.clcStage,
      Prologue.schedStart]
  | cons c => rw [Prologue.next_cons hn]; simp [Prologue.Role.clcStage, Consumer.D.clcStage,
      Prologue.consStart]

/-- Along a thread's run each role relates its stage and response to its trace (`QueryInv`). -/
theorem queryInv (hpre : Pre P L mem0) (hg : g < L.threads) {es : List Event}
    (htr : (code L g).toMachine.Trace (some (code L g).init) es) :
    ∀ j d, (code L g).toMachine.after (some (code L g).init) (es.take j) = some (some d) →
      QueryInv L g d (es.take j) := by
  refine Code.run_inv (sound hpre hg) htr (QueryInv L g) trivial ?_
  intro d d' pre e t ins o hq hat hinv hc hf hn
  rcases d with p | (l | m | sd | cs)
  · change Prologue.next L g p e = some (some d') at hn
    rcases d' with p' | r'
    · trivial
    · change QueryRel L g r'.clcStage r'.resp (pre ++ [e])
      rw [Prologue.clc_stage_start hn]
      exact QueryRel.zero
  · obtain ⟨l', hl, rfl⟩ := next_of_loader hn
    exact Loader.query_step hpre hat hc hf hl hq
  · obtain ⟨m', hm, rfl⟩ := next_of_mma hn
    exact Mma.query_step hpre hat hc hf hm hq
  · obtain ⟨s', hs, rfl⟩ := next_of_sched hn
    exact Scheduler.query_step hpre hinv.1 hat hc hf hs hq
  · obtain ⟨c', hc', rfl⟩ := next_of_cons hn
    exact Consumer.query_step hpre hat hc hf hc' hq

/-- A role's query reports the response its thread read from its CTA's response buffer right
after its latest successful poll of the response barrier, two or three events before. -/
theorem clc_query {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {e : Event} (he : X.get (g, k) = some e) {r : Prologue.Role}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
    some (some (.inr r)))
    {q : ClcQuery} {rr : ClcResponse} (hk : e.kind = .clcQuery q rr) :
    ∃ j pc p acq sc pcr, ∃ a : Acc, ∃ bs, k ≤ j + 3 ∧ j + 2 ≤ k ∧
      X.get (g, j) = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ ∧
      X.get (g, j + 1) = some ⟨pcr, .rd a bs⟩ ∧
      a.loc = respLoc L g ∧ a.size = 16 ∧ Flow.responseOf bs = some rr := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hrel : QueryRel L g r.clcStage r.resp ((X.tr g).take k) := queryInv hpre hg htr k _ hσ
  have hsite : (r.clcStage = 2 ∨ r.clcStage = 3) ∧ ∀ r0, r.resp = .clc r0 → rr = r0 := by
    rcases r with l | m | sd | cs
    · exact Loader.query_site hat hc hfire hk
    · exact Mma.query_site hat hc hfire hk
    · exact Scheduler.query_site hat hc hfire hk
    · exact Consumer.query_site hat hc hfire hk
  obtain ⟨j, pc, p, acq, sc, pcr, a, bs, rr0, hj, hw, hr, ha, hs, hres, hv⟩ :=
    hrel.2 (by rcases hsite.1 with h | h <;> omega)
  have hk' : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  simp only [List.length_take, Nat.min_eq_left hk'] at hj
  have hrr := hsite.2 rr0 hv
  subst hrr
  refine ⟨j, pc, p, acq, sc, pcr, a, bs, by rcases hsite.1 with h | h <;> omega,
    by rcases hsite.1 with h | h <;> omega, ?_, ?_, ha, hs, hres⟩
  · rw [List.getElem?_take_of_lt (by omega)] at hw
    exact hw
  · rw [List.getElem?_take_of_lt (by omega)] at hr
    exact hr

/-- Only a role queries a response: the prologue has no query site. -/
theorem query_role {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {e : Event} (he : X.get (g, k) = some e) {d : ThreadD}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) = some (some d))
    {q : ClcQuery} {rr : ClcResponse} (hk : e.kind = .clcQuery q rr) : ∃ r, d = .inr r := by
  obtain ⟨o, hf⟩ := (Frame.trace (fun _ => sound hpre) hX hg).fired_at he hσ
  obtain ⟨t, ins, -, -, hc, hfire⟩ := Code.fired_site (sound hpre hg) hf
  rcases d with ⟨site, w⟩ | r
  · exfalso
    have hpc := query_pc hc (fires_query_op hfire hk)
    clear hc hfire hf hσ
    change site.pc ∈ Flow.clcQuery.toList at hpc
    revert hpc
    cases site <;> simp only [Prologue.Site.pc] <;> decide +revert
  · exact ⟨r, rfl⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof
