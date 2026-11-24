-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.NamedBarrierSites
public import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
public import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Lemmas.Flow.NotClc
public import Lemmas.Step.CtaBar
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
public import Kernels.TmlFa4Fwd.Proof.RoleDispatch
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
public import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
public import Lemmas.Flow.NotTcData
import Lemmas.Flow.NotTcMma

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Prologue

/-- The three role entries that rendezvous before using the shared TMEM allocation. -/
def allocationEntrySites : List Nat := [1910, 3103, 7747]

private def beforeAllocationPc (pc : Nat) : Prop :=
  pc ≤ 1910 ∨ 2768 ≤ pc ∧ pc ≤ 3103 ∨ 7742 ≤ pc ∧ pc ≤ 7747 ∨ pc = 9205

private instance beforeAllocationPcDec (pc : Nat) : Decidable (beforeAllocationPc pc) :=
  inferInstanceAs (Decidable
    (pc ≤ 1910 ∨ 2768 ≤ pc ∧ pc ≤ 3103 ∨ 7742 ≤ pc ∧ pc ≤ 7747 ∨ pc = 9205))

private def beforeControl (ins : Instr) (pc : Nat) : Bool :=
  !decide (beforeAllocationPc pc) ||
    ((ins.guard.isNone || decide (beforeAllocationPc (pc+1))) &&
      (!ins.op.isLocal || match ins.op with
        | .brx .. => false
        | _ => decide (beforeAllocationPc (nextPc ins.op pc))))

private theorem beforeControlCode :
    kernel.code.zipIdx.all (fun (i, pc) => beforeControl i pc) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem segmentOutsideBefore :
    Assumptions.swExp2Sites.all (fun pc => !decide (beforeAllocationPc pc)) = true := by
  decide +kernel

private theorem returningEvents :
    kernel.code.all (fun i => i.op.isLocal || Epilogue.ordinaryEvent i.op) = true := by
  decide +kernel

private theorem beforeLocal {l : Launch} {g : Nat} {s u : TState}
    (hs : beforeAllocationPc s.pc) (ht : Tau kernel Assumptions.all l g s u) :
    beforeAllocationPc u.pc := by
  obtain ⟨i, hc, _, hStep⟩ := Softmax.tauScoreSource ht
  have hCode := List.all_eq_true.mp beforeControlCode _
    (List.mk_mem_zipIdx_iff_getElem?.mpr hc)
  simp only [beforeControl, hs, decide_true, Bool.not_true, Bool.false_or,
    Bool.and_eq_true] at hCode
  rcases hStep with ⟨rfl, hGuard⟩ | ⟨_, hLocal, hExec⟩
  · have h := hCode.1
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · have hNone := Option.isNone_iff_eq_none.mp h
      rw [hNone] at hGuard
      cases hGuard
    · exact of_decide_eq_true h
  · rcases Softmax.scoreExecLocal hExec with hFrame | ⟨_, hSite, _, _⟩
    · have hOp := hCode.2
      simp only [hLocal, Bool.not_true, Bool.false_or] at hOp
      have hPc := hFrame.pc
      cases ho : i.op <;> simp only [ho, BrxTarget, or_false] at hOp hPc
      all_goals first
        | cases hOp
        | exact hPc.symm ▸ (of_decide_eq_true hOp)
    · have hImpossible := List.all_eq_true.mp segmentOutsideBefore _ hSite
      simp [hs] at hImpossible

private theorem beforeLocals {l : Launch} {g : Nat} {s u : TState}
    (hs : beforeAllocationPc s.pc)
    (ht : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u) :
    beforeAllocationPc u.pc := by
  induction ht with
  | refl => exact hs
  | tail _ h ih => exact beforeLocal ih h

private theorem allocationEntryCode {pc : Nat} (hp : pc ∈ allocationEntrySites) :
    kernel.code[pc]? = some ⟨none, .barSyncN (.imm 2) (.imm 416) true⟩ := by
  simp only [allocationEntrySites, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact Flow.code_1910
  · exact Flow.code_3103
  · exact Flow.code_7747

/-- The startup allocation rendezvous uses the same named resource in all three roles. -/
theorem allocationEntryTemplate {l : Launch} {g : Nat} {s : TState}
    (hb : l.block = 512) (hs : s.pc ∈ allocationEntrySites) (hf : s.fault = none) :
    out kernel Assumptions.all l g s = .ev (.bar 2 (next s) (some 416) .sync) := by
  rw [out_event hf (allocationEntryCode hs) rfl rfl]
  change Out.ev (barTmpl l g s (.imm 2) (some (.imm 416)) .sync) = _
  simp [barTmpl, readBits, pure, Except.pure, hb,
    show (truncBits 32 2#64).toNat = 2 by decide,
    show (truncBits 32 416#64).toNat = 416 by decide]

private theorem beforeEvent {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hs : beforeAllocationPc s.pc) (he : EStep kernel Assumptions.all l g s e (some u))
    (hEntry : s.pc ∉ allocationEntrySites) : beforeAllocationPc u.pc := by
  obtain ⟨i, hc, hLocal, hFire⟩ := estep_event_source he
  have hEnd : s.pc ≠ 9205 := by
    intro h
    rw [h, Flow.code_9205] at hc
    obtain rfl := Option.some.inj hc.symm
    cases hFire.2
  have hOp := List.all_eq_true.mp returningEvents _ (List.mem_of_getElem? hc)
  have hFrame := Epilogue.ordinaryEventFrame (A := Assumptions.all) (l := l) (g := g) (s := s)
    (by simpa only [hLocal, Bool.false_or] using hOp)
  rcases callbackFrame_fires hFrame hFire with h | h
  · exact h.symm ▸ hs
  · have hNext : beforeAllocationPc (s.pc+1) := by
      simp only [allocationEntrySites, List.mem_cons, List.not_mem_nil, or_false] at hEntry
      unfold beforeAllocationPc at hs ⊢
      omega
    exact h.symm ▸ hNext

private theorem entryEvent {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hb : l.block = 512) (hPc : s.pc ∈ allocationEntrySites)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    e = ⟨s.pc, .bar 2 (some 416) .sync⟩ ∧ u = next s := by
  obtain ⟨f, hOut, hFire⟩ := he
  have hFault : s.fault = none := by
    cases hf : s.fault with
    | none => rfl
    | some bad =>
      have hF : out kernel Assumptions.all l g s = .ev (.ub bad) := by simp [out, hf]
      obtain rfl := Out.ev.inj (hOut.symm.trans hF)
      cases hFire.2
  obtain rfl := Out.ev.inj (hOut.symm.trans (allocationEntryTemplate hb hPc hFault))
  exact ⟨hFire.1, Option.some.inj hFire.2⟩

private theorem beforeRun {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {o : Option TState} (hb : l.block = 512) (hr : Run kernel Assumptions.all l g s es o)
    (hs : beforeAllocationPc s.pc) :
    ∀ (j : Nat) (e : Event), es[j]? = some e → beforeAllocationPc e.pc ∨
      ∃ i < j, ∃ pc ∈ allocationEntrySites, es[i]? = some ⟨pc, .bar 2 (some 416) .sync⟩ := by
  induction hr with
  | nil => simp
  | @step _ source _ _ _ _ hLocal he _ ih =>
    have hS := beforeLocals hs hLocal
    intro j e hGet
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hGet
      subst e
      exact .inl ((estep_source_pc he) ▸ hS)
    | succ j =>
      by_cases hPc : source.pc ∈ allocationEntrySites
      · obtain ⟨hEvent, _⟩ := entryEvent hb hPc he
        exact .inr ⟨0, by omega, _, hPc, congrArg some hEvent⟩
      · rcases ih (beforeEvent hS he hPc) j e hGet with h | ⟨i, hLt, pc, hp, hOld⟩
        · exact .inl h
        · exact .inr ⟨i+1, by omega, pc, hp, hOld⟩
  | last hLocal he =>
    intro j e hGet
    have hj := (List.getElem?_eq_some_iff.mp hGet).1
    simp only [List.length_cons, List.length_nil] at hj
    have hZero : j = 0 := by omega
    subst j
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hGet
    subst e
    exact .inl ((estep_source_pc he) ▸ beforeLocals hs hLocal)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- At one of the three role entries, an actual barrier-2 event is the startup wait. -/
theorem actualAllocationEntry {i : EvId} {pc : Nat} {cnt : Option Nat} {mode : BarMode}
    (hSite : pc ∈ allocationEntrySites) (he : X.get i = some ⟨pc, .bar 2 cnt mode⟩) :
    X.IsBarrier i 2 (some 416) pc := by
  obtain ⟨_, hCount, hMode, _⟩ := actualNamedBarrier hp hX he
  have hc : namedBarrierCount pc = some 416 ∧ namedBarrierMode pc = .sync := by
    simp only [allocationEntrySites, List.mem_cons, List.not_mem_nil, or_false] at hSite
    rcases hSite with rfl | rfl | rfl <;> decide
  change X.get i = some ⟨pc, .bar 2 (some 416) .sync⟩
  rwa [hCount, hc.1, hMode, hc.2] at he

omit hp hX in
private theorem roleAllocationEntry (warp pc : Nat) (h : roleBodyPc warp pc)
    (hPc : pc ∈ allocationEntrySites) :
    pc = 1910 ∧ warp = 12 ∨ pc = 3103 ∧ warp < 8 ∨ pc = 7747 ∧ 8 ≤ warp ∧ warp < 12 := by
  simp only [allocationEntrySites, List.mem_cons, List.not_mem_nil, or_false] at hPc
  rcases h with h | h
  · omega
  · split_ifs at h <;> omega

/-- A genuine allocation barrier arrival is associated with exactly its decoded warp role. -/
theorem allocationEntryRole {g j pc : Nat} (hPc : pc ∈ allocationEntrySites)
    (he : X.IsBarrier (g, j) 2 (some 416) pc) :
    pc = 1910 ∧ warpIndex l g = 12 ∨ pc = 3103 ∧ warpIndex l g < 8 ∨
      pc = 7747 ∧ 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
  have hSites : 173 < pc ∧ pc ∉ registerHintSites := by
    simp only [allocationEntrySites, List.mem_cons, List.not_mem_nil, or_false] at hPc
    rcases hPc with rfl | rfl | rfl <;> decide
  have hRole := roleBodyPcOfEvent hp hX he hSites.1 hSites.2
  exact roleAllocationEntry _ _ hRole hPc

/-- Every actual MMA or Tensor Memory data instruction follows the same entry rendezvous. -/
theorem tensorEventAfterAllocationEntry {g j : Nat} {e : Event} (he : X.get (g, j) = some e)
    (hTensor : isTcData e = true ∨ ∃ dst spec acc mask, e.kind = .tc (.mma dst spec acc mask)) :
    ∃ i < j, ∃ site ∈ allocationEntrySites, X.IsBarrier (g, i) 2 (some 416) site := by
  have hCode : kernel.code.zipIdx.all (fun (ins, site) =>
      !(tcDataOp ins.op || tcMmaOp ins.op) || !decide (beforeAllocationPc site)) = true := by
    decide +kernel
  have hNotBefore : ¬ beforeAllocationPc e.pc := by
    rcases get_source hX he with ⟨fault, hBad⟩ | ⟨s, ins, _, _, hc, hf⟩
    · rcases hTensor with hData | ⟨_, _, _, _, hMma⟩
      · simp [hBad, isTcData] at hData
      · rw [hBad] at hMma
        cases hMma
    have hMem := List.mk_mem_zipIdx_iff_getElem?.mpr hc
    have hAudit := List.all_eq_true.mp hCode _ hMem
    have hOp : tcDataOp ins.op || tcMmaOp ins.op := by
      rcases hTensor with hData | ⟨_, _, _, _, hMma⟩
      · simp [fires_tcData_op hf hData]
      · simp [fires_tcMma_op hf hMma]
    simpa only [hOp, Bool.not_true, Bool.false_or, Bool.not_eq_true',
      decide_eq_false_iff_not] using hAudit
  have hg := Step.CtaBar.thread_lt_of_get hX he
  obtain ⟨_, hr⟩ := hX.thr g hg
  rcases beforeRun hp.block hr (by decide) j e he with h | h
  · exact (hNotBefore h).elim
  · exact h

/-- A named rendezvous beyond startup and the allocation entry requires the
issuing lane's earlier allocation rendezvous. -/
theorem allocationEntryBeforeNamedBarrier {g j pc id : Nat} {count : Option Nat} {mode : BarMode}
    (he : X.get (g, j) = some ⟨pc, .bar id count mode⟩) (hCommon : pc ≠ 173)
    (hLate : pc ∉ allocationEntrySites) :
    ∃ i < j, ∃ pc ∈ allocationEntrySites, X.IsBarrier (g, i) 2 (some 416) pc := by
  obtain ⟨hSite, _, _, _, _, _, _⟩ := actualNamedBarrier hp hX he
  have hNotBefore : ¬ beforeAllocationPc pc := by
    simp only [namedBarrierSites, List.mem_cons, List.not_mem_nil, or_false] at hSite
    simp only [allocationEntrySites, List.mem_cons, List.not_mem_nil, or_false] at hLate
    unfold beforeAllocationPc
    omega
  have hg := Step.CtaBar.thread_lt_of_get hX he
  obtain ⟨_, hr⟩ := hX.thr g hg
  rcases beforeRun hp.block hr (by decide) j _ he with h | h
  · exact (hNotBefore h).elim
  · exact h

/-- Every later named barrier with identifier 2 has already returned through its role's
allocation barrier. The audited initial control flow also excludes all dynamic count sites. -/
theorem allocationEntryBeforeBarrier {g j pc : Nat} {count : Option Nat} {mode : BarMode}
    (he : X.get (g, j) = some ⟨pc, .bar 2 count mode⟩) (hLate : pc ∉ allocationEntrySites) :
    ∃ i < j, ∃ pc ∈ allocationEntrySites, X.IsBarrier (g, i) 2 (some 416) pc := by
  have hZero := (actualNamedBarrier hp hX he).2.2.2.2.2.1
  exact allocationEntryBeforeNamedBarrier hp hX he
    (fun h => (by decide : (2 : Nat) ≠ 0) (hZero h)) hLate

end PTX.Kernels.TmlFa4Fwd.Mma
