-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Lemmas.Flow.Run
public import Lemmas.Flow.SegFree

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Assumptions

open PTX.Assumption

/-- The instruction forms whose local rules are supplied entirely by Core. -/
def coreOp : Op → Bool
  | .float _ => false
  | .cvt c => c.dst.kind?.isSome && c.src.kind?.isSome
  | _ => true

theorem numeric_segSites : SegSites numeric swExp2Sites := by
  intro a ha _ _ t hpc
  simp only [numeric, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | simp [swExp2, hpc]

private theorem coreOp_withSregValues {op : Op} (h : coreOp op = true) (vals : List Nat) :
    coreOp (op.withSregValues vals) = true := by
  cases op <;> exact h

private theorem selectors_of_coreOp {op : Op} (h : coreOp op = true) :
    FloatForm.ofOp op = none ∧ ApproxForm.ofOp op = none ∧ lg2Operands op = none ∧
      biasWidenOperands op = none ∧ probPackOperands op = none := by
  cases op <;> first
    | exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | (exfalso; have : false = true := h; contradiction)
    | (rename_i c; cases hd : c.dst <;> cases hs : c.src <;>
        simp_all [coreOp, DType.kind?, FloatForm.ofOp, CvtInstr.widenF16?, CvtInstr.packF16?,
          ApproxForm.ofOp, lg2Operands, biasWidenOperands, probPackOperands])

/-- Outside the software exponentiation sites, Core's integer, address and memory instructions
keep their local rule. -/
theorem execLocalA_eq_nil {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hpc : t.pc ∉ swExp2Sites) (hop : coreOp op = true) :
    execLocalA numeric L g t op = execLocalA [] L g t op := by
  rw [((numeric_segSites.pc hpc).at (L := L) (g := g) rfl).exec]
  obtain ⟨hi, he, hl, hw, hp⟩ := selectors_of_coreOp hop
  have hlocal : ∀ a ∈ numeric, a.localRule L g t op = none := by
    intro a ha
    simp only [numeric, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · simp only [idealArith, idealReal, hi]
    · simp only [approx, approxExact, he]
    · simp [lg2, hl]
    · simp [bf16Convert, hw, hp]
    · rfl
  rw [execLocalRule_of_none hlocal]
  rfl

private theorem localSregTmpl_eq_nil {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hpc : t.pc ∉ swExp2Sites) (hop : coreOp op = true) (rule : RuleId) :
    localSregTmpl numeric L g t rule op = localSregTmpl [] L g t rule op := by
  have h vals := execLocalA_eq_nil (L := L) (g := g) hpc (coreOp_withSregValues hop vals)
  cases rule <;> first | rfl | simp only [localSregTmpl, sregTmpl, h]

/-- Event continuations also use Core on these instruction forms. Numerical assumptions
neither admit cache-incoherent loads nor change atomic, mbarrier or TMEM load templates. -/
theorem eventTmpl_eq_nil {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hpc : t.pc ∉ swExp2Sites) (hop : coreOp op = true) :
    eventTmpl numeric L g t op = eventTmpl [] L g t op := by
  cases op <;> first
    | rfl
    | (simp only [eventTmpl]; split <;> first | rfl | exact localSregTmpl_eq_nil hpc hop _)

/-- The numerical assumptions do not affect the outcome at a Core instruction off the
software exponentiation sites, including skipped instructions and pending faults. -/
theorem out_eq_nil {L : Launch} {g : Nat} {t : TState} {ins : Instr}
    (hpc : t.pc ∉ swExp2Sites) (hc : kernel.code[t.pc]? = some ins)
    (hop : coreOp ins.op = true) : out kernel numeric L g t = out kernel [] L g t := by
  simp only [out, hc, execLocalA_eq_nil hpc hop, eventTmpl_eq_nil hpc hop]

theorem tauStep_eq_nil {L : Launch} {g : Nat} {t : TState} {ins : Instr}
    (hpc : t.pc ∉ swExp2Sites) (hc : kernel.code[t.pc]? = some ins)
    (hop : coreOp ins.op = true) : tauStep kernel numeric L g t = tauStep kernel [] L g t := by
  rw [tauStep, out_eq_nil hpc hc hop, tauStep]


/-- The full list selects exactly the checked uniform branch sites. -/
theorem all_uniPoll (pc : Nat) : all.any (·.uniPoll pc) = pollAgreeSites.contains pc := by
  change (pollAgreeSites.contains pc || false) = _
  simp

theorem all_commitInOrder (pc : Nat) :
    all.any (·.commitInOrder pc) = commitOrderSites.contains pc := by
  change (commitOrderSites.contains pc || false) = _
  simp

theorem all_tcLdWait (pc : Nat) :
    all.any (·.tcLdWait pc) = (tcLdDataflowSites.contains pc && ldConsumedAt kernel pc) := by
  change ((tcLdDataflowSites.contains pc && ldConsumedAt kernel pc) || false) = _
  simp

theorem all_tcStWaitLd (pc : Nat) :
    all.any (·.tcStWaitLd pc) = delayedTmemSites.contains pc := by
  change (delayedTmemSites.contains pc || false) = _
  simp

/-- Synchronization interpretation adds no segment or local-instruction rule. -/
theorem execLocalA_all_eq_numeric (L : Launch) (g : Nat) (t : TState) (op : Op) :
    execLocalA all L g t op = execLocalA numeric L g t op := by
  have hs : (synchronization.findSome? fun a => a.segmentRule L g t) = none := rfl
  have hl : (synchronization.findSome? fun a => a.localRule L g t op) = none := rfl
  have hi : ([inputReadOnly].findSome? fun a => a.segmentRule L g t) = none := rfl
  have hj : ([inputReadOnly].findSome? fun a => a.localRule L g t op) = none := rfl
  simp only [execLocalA, execLocalRule, all, List.findSome?_append, hs, hl, hi, hj,
    Option.or_none]

/-- The synchronization assumptions affect templates only at the selected TMEM loads
and the first P stores of the biased rounds. -/
theorem eventTmpl_all_eq_numeric {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hload : all.any (·.tcLdWait t.pc) = false)
    (hstore : all.any (·.tcStWaitLd t.pc) = false) :
    eventTmpl all L g t op = eventTmpl numeric L g t op := by
  cases op
  case tcLd =>
    have hn : numeric.any (·.tcLdWait t.pc) = false := rfl
    simp only [eventTmpl, tcLdTmpl, hload, hn, Bool.false_eq_true, ↓reduceIte]
  case tcSt =>
    have hn : numeric.any (·.tcStWaitLd t.pc) = false := rfl
    rw [eventTmpl_tcSt_noWait hstore, eventTmpl_tcSt_noWait hn]
  all_goals rfl

/-- Outside those TMEM sites, synchronization interpretation preserves the outcome. -/
theorem out_all_eq_numeric {L : Launch} {g : Nat} {t : TState}
    (hload : all.any (·.tcLdWait t.pc) = false)
    (hstore : all.any (·.tcStWaitLd t.pc) = false) :
    out kernel all L g t = out kernel numeric L g t := by
  simp only [out, execLocalA_all_eq_numeric, eventTmpl_all_eq_numeric hload hstore]

/-- A selected TMEM instruction still performs an event, so local steps are entirely unchanged. -/
theorem tauStep_all_eq_numeric (L : Launch) (g : Nat) (t : TState) :
    tauStep kernel all L g t = tauStep kernel numeric L g t := by
  simp only [tauStep, out, execLocalA_all_eq_numeric]
  cases t.fault <;> try rfl
  cases kernel.code[t.pc]? <;> try rfl
  rename_i ins
  cases hGuard : guardHolds t ins.guard with
  | error _ => simp only [hGuard]
  | ok guard =>
    cases guard with
    | false => simp only [hGuard]
    | true => cases hLocal : ins.op.isLocal <;> simp [hGuard, hLocal]

/-- Each finite segment of local execution is unchanged by synchronization assumptions. -/
theorem run_all_eq_numeric (L : Launch) (g n : Nat) (t : TState) :
    run kernel all L g n t = run kernel numeric L g n t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [run, tauStep_all_eq_numeric L g, ih]

/-- Core-only prologue and output sites use the same outcome under the full assumption list. -/
theorem out_all_eq_nil {L : Launch} {g : Nat} {t : TState} {ins : Instr}
    (hseg : t.pc ∉ swExp2Sites) (hload : t.pc ∉ tcLdDataflowSites)
    (hstore : t.pc ∉ delayedTmemSites) (hc : kernel.code[t.pc]? = some ins)
    (hop : coreOp ins.op = true) :
    out kernel all L g t = out kernel [] L g t :=
  (out_all_eq_numeric (by simp [all_tcLdWait, hload])
    (by simp [all_tcStWaitLd, hstore])).trans (out_eq_nil hseg hc hop)

theorem tauStep_all_eq_nil {L : Launch} {g : Nat} {t : TState} {ins : Instr}
    (hseg : t.pc ∉ swExp2Sites) (hc : kernel.code[t.pc]? = some ins)
    (hop : coreOp ins.op = true) :
    tauStep kernel all L g t = tauStep kernel [] L g t :=
  (tauStep_all_eq_numeric L g t).trans (tauStep_eq_nil hseg hc hop)

end PTX.Kernels.TmlFa4Fwd.Assumptions
