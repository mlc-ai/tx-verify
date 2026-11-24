-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLseWriters
public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalLayout
public import Kernels.TmlFa4Fwd.Proof.CorrectionPrefixAccumulator
public import Kernels.TmlFa4Fwd.Proof.CorrectionSource
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Proof.CorrectionPollPrefix
import Kernels.TmlFa4Fwd.Proof.CorrectionMbarAddress
import Lemmas.Order.OrderWaits

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Correction Softmax

noncomputable section

def PartialLoad (s : TState) : Prop :=
  s.sub = 0 ∨ ∃ ds addr shape,
    kernel.code[s.pc]? = some ⟨none, .tcLd ds addr shape none⟩ ∧
      Assumptions.all.any (·.tcLdWait s.pc) = true

def stagingEvent : Op → Bool
  | .barSyncN .. | .mbarArrive .. | .mbarWait .. | .tcSt .. | .tcWaitLd | .tcWaitSt => true
  | .tcLd _ _ _ red => red.isNone
  | .warp w => Mma.linearWarpOp w
  | .mem a => a.kind == .load && !a.nc && a.ext == .same && a.regs.length ≤ 1
  | _ => false

private theorem stagingReturns {op : Op} (h : stagingEvent op = true) :
    correctionReturningOp op = true := by
  cases op <;> simp_all [stagingEvent, correctionReturningOp, scoreEventOp]
  case mem a => exact .inl (h.2.trans (by decide))

private def scalarEvent : Op → Prop
  | .mem a => a.kind = .load → a.regs.length ≤ 1
  | _ => True

private theorem stagingScalar {op : Op} (h : stagingEvent op = true) : scalarEvent op := by
  cases op <;> try trivial
  case mem => exact fun _ => of_decide_eq_true (Bool.and_eq_true_iff.mp h).2

theorem partialLoadTail {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {i : Instr} (hc : kernel.code[s.pc]? = some i) (hLo : 7955 ≤ s.pc)
    (hStage : stagingEvent i.op = true) (hPart : PartialLoad s)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s i.op) e (some u)) :
    PartialLoad u := by
  have hZero : (∀ ds addr shape, i.op ≠ .tcLd ds addr shape none) → s.sub = 0 := by
    intro h
    rcases hPart with hz | ⟨ds, addr, shape, hCode, _⟩
    · exact hz
    · exact (h ds addr shape (congrArg Instr.op (Option.some.inj (hc.symm.trans hCode)))).elim
  have hNext (he : u = next s) (hz : s.sub = 0) : PartialLoad u :=
    .inl (he.symm ▸ hz)
  cases ho : i.op <;> simp only [ho, stagingEvent] at hStage <;> try contradiction
  case tcLd ds addr shape red =>
    obtain rfl := Option.isNone_iff_eq_none.mp hStage
    by_cases hHook : Assumptions.all.any (·.tcLdWait s.pc) = true
    · by_cases hs : s.sub = 0
      · have hShape : u.pc = s.pc ∧ u.sub = 1 := by
          apply callbackFrame_fires (P := fun t => t.pc = s.pc ∧ t.sub = 1) _ hf
          rw [ho, eventTmpl, tcLdTmpl, hHook, hs]
          simp only [ite_true]
          have lift {r : Exec Tmpl} (h : AllOk (fun m =>
              CallbackFrame (fun t => t.pc = s.pc ∧ t.sub = 1) (m.thenWaitLd s.pc)) r) :
              CallbackFrame (fun t => t.pc = s.pc ∧ t.sub = 1)
                ((ofExec r).thenWaitLd s.pc) := by cases r <;> exact h
          cases shape <;> simp only [tcTmpl, ldResult] <;> apply lift
          all_goals repeat' first | trivial | (apply allOk_bind; intro v) | split
          all_goals intro vals; exact ⟨rfl, rfl⟩
        have hGuard : i.guard = none := by
          have hTable : Assumptions.tcLdDataflowSites.all (fun pc =>
              match kernel.code[pc]? with | some ins => ins.guard.isNone | none => false) =
              true := by decide +kernel
          rw [Assumptions.all_tcLdWait] at hHook
          have hm : s.pc ∈ Assumptions.tcLdDataflowSites :=
            List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp hHook).1
          have h := List.all_eq_true.mp hTable s.pc hm
          rw [hc] at h
          exact Option.isNone_iff_eq_none.mp h
        exact .inr ⟨ds, addr, shape, by rw [hShape.1, hc, ← ho, ← hGuard],
          hShape.1.symm ▸ hHook⟩
      · obtain ⟨_, rfl⟩ := fires_tcLd_wait hHook hs (ho ▸ hf)
        exact .inl rfl
    · have hs : s.sub = 0 := hPart.elim id (fun ⟨_, _, _, _, ht⟩ => (hHook ht).elim)
      apply Or.inl
      apply callbackFrame_fires (P := fun t => t.sub = 0) _ hf
      rw [ho, eventTmpl, tcLdTmpl, show Assumptions.all.any (·.tcLdWait s.pc) = false by simpa
        using hHook]
      simp only [Bool.false_eq_true, ite_false]
      cases shape <;> simp only [tcTmpl, ldResult] <;> apply ofExec_frame
      all_goals repeat' first | trivial | (apply allOk_bind; intro v) | split
      all_goals intro vals; exact ((setRegs_skel (next s) _ _).2.1).trans hs
  case tcSt addr vals shape =>
    have hz := hZero (by intros; rw [ho]; simp)
    have hHook : Assumptions.all.any (·.tcStWaitLd s.pc) = false := by
      rw [Assumptions.all_tcStWaitLd]
      cases h : Assumptions.delayedTmemSites.contains s.pc
      · rfl
      · have hm := List.contains_iff_mem.mp h
        simp only [Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false] at hm
        omega
    apply Or.inl
    apply callbackFrame_fires (P := fun t => t.sub = 0) _ hf
    rw [ho, eventTmpl, tcStTmpl, hHook]
    simp only [Bool.false_eq_true, ite_false]
    cases shape <;> simp only [tcTmpl] <;> apply ofExec_frame
    all_goals repeat' first | exact hz | trivial | (apply allOk_bind; intro v) | split
  case mem a =>
    have hz := hZero (by intros; rw [ho]; simp)
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hStage
    obtain ⟨_, bs, _, rfl⟩ :=
      fires_load hStage.1.1.1 (by simpa using hStage.1.1.2) (ho ▸ hf) hStage.1.2
    apply Or.inl
    cases hb : rebuild 3 bs with
    | error f => simpa only [afterLoad, hb] using hz
    | ok v =>
      rw [afterLoad_last hb (by have := hStage.2; omega)]
  case warp w =>
    exact .inl ((Mma.linearWarpAdvances hStage (ho ▸ hf)).2.trans
      (hZero (by intros; rw [ho]; simp)))
  case barSyncN id n aligned =>
    apply Or.inl
    apply callbackFrame_fires (P := fun t => t.sub = 0) _ hf
    simp only [ho, eventTmpl, barTmpl]
    repeat' split
    all_goals first | exact hZero (by intros; rw [ho]; simp) | trivial
  case mbarArrive b o tx n c rel sc d =>
    rw [ho] at hf
    obtain ⟨rfl, _⟩ := fires_arrive_state hf
    exact .inl (by cases d <;> exact hZero (by intros; rw [ho]; simp))
  case mbarWait d b o p a sc =>
    rw [ho] at hf
    obtain ⟨_, _, _, _, _, rfl⟩ := fires_wait hf
    exact .inl (hZero (by intros; rw [ho]; simp))
  case tcWaitLd =>
    rw [ho, eventTmpl, tcTmpl] at hf
    split at hf
    · exact hNext (Option.some.inj hf.2) (hZero (by intros; rw [ho]; simp))
    · cases hf.2
  case tcWaitSt =>
    apply Or.inl
    apply callbackFrame_fires (P := fun t => t.sub = 0) _ hf
    simp only [ho, eventTmpl, tcTmpl]
    apply ofExec_frame
    repeat' first | exact hZero (by intros; rw [ho]; simp) | trivial | split

private inductive Interval where
  | rescale | beforeReady | firstStore

private def Interval.start : Interval → Nat
  | .rescale => 7955
  | .beforeReady => 8464
  | .firstStore => 8476

private def Interval.stop : Interval → Nat
  | .rescale => 8448
  | .beforeReady => 8472
  | .firstStore => 8492

private def Interval.regs : Interval → List Nat
  | .rescale => [1632, 1612, 1630, 1631]
  | .beforeReady | .firstStore => [6511]

private def checkedCode (b : Interval) (i : Instr) : Bool :=
  (i.op.isLocal || stagingEvent i.op) &&
    b.regs.all (fun r => !(writesRegs i.op).contains r && !(scoreEventWrites i.op).contains r) &&
    match i.op with
    | .bra pc _ => b.start ≤ pc && pc ≤ b.stop
    | .brx .. => false
    | _ => true

private theorem stageCode (b : Interval) {pc : Nat} {i : Instr}
    (hLo : b.start ≤ pc) (hHi : pc < b.stop) (hc : kernel.code[pc]? = some i) :
    checkedCode b i = true := by
  have hAll : ((kernel.code.drop b.start).take (b.stop - b.start)).all (checkedCode b) =
      true := by cases b <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll i
  apply List.mem_of_getElem? (i := pc - b.start)
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo, hc]

private theorem stageStep (b : Interval) {l : Launch} {g : Nat} {s u : TState}
    {F : List (Nat × Value)} {e : Option Event}
    (hF : ∀ rv ∈ F, rv.1 ∈ b.regs) (hLo : b.start ≤ s.pc) (hHi : s.pc < b.stop)
    (hs : s.sub ≤ 3) (hAcc : s.acc = []) (hPart : PartialLoad s) (hFrame : Holds s.regs F)
    (he : WStep kernel Assumptions.all l g s e u) :
    (b.start ≤ u.pc ∧ u.pc ≤ b.stop) ∧ u.sub ≤ 3 ∧ u.acc = [] ∧
      PartialLoad u ∧ Holds u.regs F := by
  have hFloor : 7955 ≤ s.pc := (show 7955 ≤ b.start from by cases b <;> decide).trans hLo
  rcases he with ⟨_, ht⟩ | ⟨e, _, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, _, hLocal⟩ := correctionTauFrame hOff ht
    have hCode := stageCode b hLo hHi hc
    simp only [checkedCode, Bool.and_eq_true] at hCode
    rcases hLocal with ⟨rfl, _⟩ | ⟨_, hLoc, hLocal⟩
    · exact ⟨⟨by change b.start ≤ s.pc + 1; omega, by change s.pc + 1 ≤ b.stop; omega⟩,
        Nat.zero_le _, rfl, .inl rfl, hFrame⟩
    have hz : s.sub = 0 := by
      rcases hPart with h | ⟨ds, addr, shape, hAt, _⟩
      · exact h
      · rw [hc] at hAt
        obtain rfl := Option.some.inj hAt
        cases hLoc
    refine ⟨?_, hLocal.sub ▸ hs, hLocal.acc.trans hAcc, .inl (hLocal.sub.trans hz), ?_⟩
    · have hp := hLocal.pc
      cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hp
      case bra dst uni =>
        have hDst : b.start ≤ dst ∧ dst ≤ b.stop := by simpa [ho] using hCode.2
        exact hp.symm ▸ hDst
      case brx => simp [ho] at hCode
      all_goals exact ⟨by omega, by omega⟩
    · exact holdsSchedulerFrame hFrame (fun r hm => hLocal.regs r (by
        simpa using (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hCode.1.2 r hm)).1)) hF
  · obtain ⟨i, hc, hNonlocal, hf⟩ := estep_event_source he
    have hCode := stageCode b hLo hHi hc
    simp only [checkedCode, Bool.and_eq_true, hNonlocal, Bool.false_or] at hCode
    have hOp := stagingReturns hCode.1.1
    have hProg (r : Nat) (hm : r ∈ b.regs) : ScoreEventProgress s u ∧ u.regs r = s.regs r :=
      correctionEventProgress hc hOp hs (by
        simpa using (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hCode.1.2 r hm)).2) he
    have hHead : ∃ r, r ∈ b.regs := by
      cases b <;> first | exact ⟨1632, by decide⟩ | exact ⟨6511, by decide⟩
    obtain ⟨r, hr⟩ := hHead
    have hP := (hProg r hr).1
    refine ⟨?_, hP.sub, correctionEventAccumulator hc hOp (stagingScalar hCode.1.1) hAcc he,
      partialLoadTail hc hFloor hCode.1.1 hPart hf,
      holdsSchedulerFrame hFrame (fun r hr => (hProg r hr).2) hF⟩
    rcases hP.pc with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

private theorem stageStopZero (b : Interval) {u : TState} (hp : u.pc = b.stop)
    (hs : PartialLoad u) : u.sub = 0 := by
  rcases hs with hz | ⟨ds, addr, shape, hc, _⟩
  · exact hz
  · cases b
    · rw [show u.pc = 8448 from hp, Flow.code_8448] at hc
      cases hc
    · rw [show u.pc = 8472 from hp, Flow.code_8472] at hc
      cases hc
    · rw [show u.pc = 8492 from hp, Flow.code_8492] at hc
      cases hc

private theorem hasLiveStep {l : Launch} {g : Nat} {t : TState} {es : List Event}
    {vs : List Visit} {target : Event}
    (hw : Walk kernel Assumptions.all l g t es vs) (hm : target ∈ es)
    (hAfter : t.pc < target.pc) : t.fault = none := by
  cases hw with
  | stop => simp at hm
  | tau h _ =>
    cases hh : t.fault
    · rfl
    · simp [Tau, out, hh] at h
  | ev he _ =>
    obtain ⟨m, ho, hf⟩ := he
    cases hh : t.fault
    · rfl
    · have h : m = .ub _ := Out.ev.inj (by simpa only [out, hh] using ho.symm)
      rw [h] at hf
      cases hf.2
  | last he =>
    have h := estep_source_pc he
    rw [← List.mem_singleton.mp hm] at h
    omega

private theorem cutStaging (b : Interval) {l : Launch} {g : Nat} {s : TState}
    {F : List (Nat × Value)} {es : List Event} {vs : List Visit} {target : Event}
    (hF : ∀ rv ∈ F, rv.1 ∈ b.regs) (hLo : b.start ≤ s.pc) (hHi : s.pc ≤ b.stop)
    (hSub : s.sub ≤ 3) (hAcc : s.acc = []) (hPart : PartialLoad s) (hFrame : Holds s.regs F)
    (hTarget : b.stop < target.pc) (hw : Walk kernel Assumptions.all l g s es vs)
    (hMem : target ∈ es) :
    ∃ u rest trail, At u b.stop F ∧ Walk kernel Assumptions.all l g u rest trail ∧
      target ∈ rest ∧ rest <:+ es := by
  induction hw with
  | stop => simp at hMem
  | @tau s u es vs ht hw ih =>
    by_cases hp : s.pc = b.stop
    · have hf := hasLiveStep (.tau ht hw) hMem (by omega)
      exact ⟨s, es, _, ⟨hp, stageStopZero b hp hPart, hAcc, hf, hFrame⟩,
        .tau ht hw, hMem, List.suffix_rfl⟩
    · obtain ⟨hBounds, hS, hA, hP, hR⟩ :=
        stageStep b hF hLo (by omega) hSub hAcc hPart hFrame (.inl ⟨rfl, ht⟩)
      exact ih hBounds.1 hBounds.2 hS hA hP hR hMem
  | @ev s u e es vs he hw ih =>
    by_cases hp : s.pc = b.stop
    · have hf := hasLiveStep (.ev he hw) hMem (by omega)
      exact ⟨s, e :: es, _, ⟨hp, stageStopZero b hp hPart, hAcc, hf, hFrame⟩,
        .ev he hw, hMem, List.suffix_rfl⟩
    · obtain ⟨hBounds, hS, hA, hP, hR⟩ :=
        stageStep b hF hLo (by omega) hSub hAcc hPart hFrame (.inr ⟨e, rfl, he⟩)
      have hMem' : target ∈ es := by
        rcases List.mem_cons.mp hMem with rfl | h
        · have h := estep_source_pc he
          omega
        · exact h
      obtain ⟨a, rest, trail, ha, hWalk, hLate, hSuf⟩ :=
        ih hBounds.1 hBounds.2 hS hA hP hR hMem'
      exact ⟨a, rest, trail, ha, hWalk, hLate, hSuf.trans (List.suffix_cons _ _)⟩
  | last he =>
    have h := estep_source_pc he
    rw [← List.mem_singleton.mp hMem] at h
    omega

private theorem walkRun {l : Launch} {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs) :
    ∃ o, Run kernel Assumptions.all l g s es o := by
  induction hw with
  | stop => exact ⟨some _, .nil _⟩
  | tau h _ ih =>
    obtain ⟨_, hr⟩ := ih
    cases hr with
    | nil => exact ⟨some _, .nil _⟩
    | step hLocal he hRest => exact ⟨_, .step (.head h hLocal) he hRest⟩
    | last hLocal he => exact ⟨none, .last (.head h hLocal) he⟩
  | ev he _ ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨r, .step .refl he hr⟩
  | last he => exact ⟨none, .last .refl he⟩

private def firstVectorBase (l : Launch) (g : Nat) : Nat :=
  (outputChunkLoc l g 0 0 (rowOf l g) 0).addr

private theorem firstVectorWrite {p : Params} {l : Launch} {m : Mem0} {g : Nat}
    (hp : Pre p l m) {s : TState} {es : List Event} {vs : List Visit} {target : Event}
    (ht : At s 8492 [(6511, b32 (firstVectorBase l g))])
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hm : target ∈ es) (hLater : 8492 < target.pc) :
    ∃ bytes, (⟨8492, .wr (outputElementAccess l g 0 0 0 (rowOf l g)) bytes⟩ : Event) ∈ es := by
  rcases ht with ⟨hPc, hSub, _, _, hRegs⟩
  cases hw with
  | stop => simp at hm
  | tau h _ =>
    have hOff : s.pc ∉ Assumptions.swExp2Sites := hPc.symm ▸ (show 8492 ∉ _ by decide)
    obtain ⟨i, hc, _, ht⟩ := correctionTauFrame hOff h
    rw [hPc, Flow.code_8492] at hc
    obtain rfl := Option.some.inj hc
    rcases ht with ⟨_, hFalse⟩ | ⟨_, hLocal, _⟩
    · cases hFalse
    · cases hLocal
  | last h =>
    have hTarget := (estep_source_pc h)
    rw [← List.mem_singleton.mp hm, hPc] at hTarget
    omega
  | @ev t u e es vs he _ =>
    obtain ⟨i, hc, _, hf⟩ := estep_event_source he
    rw [hPc, Flow.code_8492] at hc
    obtain rfl := Option.some.inj hc
    let loc := outputChunkLoc l g 0 0 (rowOf l g) 0
    have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
    have hRoom : loc.addr + 0 < 2 ^ 32 := by
      have := hp.shared.2.1
      simp only [loc, outputChunkLoc, sharedSlot, Loc.at, Nat.zero_xor]
      omega
    have hAlign : loc.addr % 16 = 0 := by
      have := hp.shared.1
      simp only [loc, outputChunkLoc, sharedSlot, Loc.at, Nat.zero_xor]
      omega
    have hEff : effAddr l g s .shared 6511 0 = .ok loc :=
      effAddr_b32_off hRegs.1 hRoom
    have hAcc : elemAcc loc 4 4 s.sub =
        .ok (outputElementAccess l g 0 0 0 (rowOf l g)) := by
      simp only [elemAcc, hSub, hAlign]
      rfl
    change Fires s.pc (storeTmpl l g s .shared 32 6511 0
      [.reg 6526, .reg 6527, .reg 6524, .reg 6525]) e (some u) at hf
    have hResolve : (effAddr l g s .shared 6511 0 >>= fun loc =>
        elemAcc loc 4 4 s.sub) = .ok (outputElementAccess l g 0 0 0 (rowOf l g)) := by
      rw [hEff]
      exact hAcc
    unfold storeTmpl at hf
    simp only [Nat.reduceDiv, List.length_cons, List.length_nil, Nat.reduceAdd] at hf
    rw [hResolve] at hf
    simp only [hSub, List.getElem?_cons_zero] at hf
    cases hRead : readValue l g s 32 (.reg 6526) >>= storeValue 32 with
    | error f =>
      rw [hRead] at hf
      cases hf.2
    | ok v =>
      rw [hRead] at hf
      have hEvent := hf.1
      change e = ⟨s.pc, .wr (outputElementAccess l g 0 0 0 (rowOf l g)) v.toBytes⟩ at hEvent
      rw [hPc] at hEvent
      exact ⟨v.toBytes, List.mem_cons.mpr (.inl hEvent.symm)⟩

/-- The acquire of the first MMA output stage in the receiving lane's CTA. -/
def FirstOutputAcquire (l : Launch) (X : Execution) (wait : EvId) : Prop :=
  ∃ e scope, X.get wait = some e ∧
    e.kind = .wait ⟨.shared, wait.1 / l.block, l.sharedBase + 144⟩ 0 true true scope

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hDone : Complete l X) {g : Nat}
    (hg : g < l.threads) (hWarpLo : 8 ≤ warpIndex l g) (hWarpHi : warpIndex l g < 12)
include hp hX hDone hg hWarpLo hWarpHi

/-- A completed correction lane assigned a live CTA tile has issued the first 4-byte element
of output staging in the first stage and subbox. The bytes are those of the actual store. -/
theorem firstStagingWriteEventAfterAcquire (hWork : g / l.block < tilePrefix p p.batch * p.heads) :
    ∃ wait pos bytes, FirstOutputAcquire l X (g, wait) ∧ po X (g, wait) (g, pos) ∧
      X.get (g, pos) = some ⟨8492, .wr (outputElementAccess l g 0 0 0 (rowOf l g)) bytes⟩ := by
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel (by
    dsimp [lane, laneOf]
    exact (Nat.mod_le ..).trans (Nat.mod_le ..))
  have hNoCancel := noCanceled hX (g := g)
  obtain ⟨pc, hExit⟩ := (hDone.1 g hg).resolve_left hNoCancel
  let j := (X.tr g).length - 1
  rw [List.getLast?_eq_getElem?] at hExit
  have he : X.get (g, j) = some ⟨pc, .exit⟩ := hExit
  have hExitPc := actualExitPc hX he
  subst pc
  let target : Event := ⟨9205, .exit⟩
  have hGet : X.get (warpLane l g lane, j) = some target := hLane.symm ▸ he
  obtain ⟨batch, hb, _, _, ends, sh, votes, active, hActive⟩ :=
    correctionActiveTileOfEvent hp hX hg hWarpLo hWarpHi hl hWork
      (show 7884 < target.pc by decide) hGet
  have hInput := (active.continuation lane hl).after_local_nonempty
    (active.localSteps lane hl) hActive.nonempty
  obtain ⟨t, hLocal, ht⟩ := correctionInputRun hp hb (active.checkpoint lane hl)
  have hRun := hInput.after_local_nonempty (run_rtg hLocal) hActive.nonempty
  rw [hLane] at hRun ht
  let F := [(1632, b32 (rowOf l g % 2)), (1612, b32 (g % l.block)),
    (1630, b32 (l.sharedBase + 128 * rowOf l g)),
    (1631, b32 (l.sharedBase + 3072 + 128 * rowOf l g))]
  have hF : ∀ rv ∈ F, rv.1 ∈ Interval.rescale.regs := by
    intro rv hm
    simpa [F, Interval.regs] using List.mem_map_of_mem (f := Prod.fst) hm
  have hAt : At t 7955 F := by
    apply ht.mono
    refine ⟨?_, ?_, ?_, ?_, trivial⟩
    all_goals apply holds_lookup ht.2.2.2.2
    all_goals try rfl
    change some (b32 (warpLane l g lane % l.block)) = _
    rw [hLane]
  have hTarget : target ∈ (X.tr g).drop (active.pos lane) := by
    apply List.mem_of_getElem? (i := j - (active.pos lane))
    rw [List.getElem?_drop, Nat.add_sub_of_le hActive.before]
    exact he
  obtain ⟨vs, hw⟩ := PTX.Kernels.TmlFa4Fwd.Mma.walkFromRun hRun
  obtain ⟨u, rest, trail, hu, hU, hTail, hSuffix⟩ := cutStaging .rescale hF hAt.1.ge
    (by rw [hAt.1]; decide) (by rw [hAt.2.1]; decide) hAt.2.2.1 (.inl hAt.2.1) hAt.2.2.2.2
    (by decide) hw hTarget
  obtain ⟨v, hLayout, hv⟩ := finalizeLayout hp (g := g) hu (by simp [F]) (by simp [F]) (by simp [F])
    (by simp [F]) (by set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨_, hr⟩ := walkRun hU
  have hNonempty : rest ≠ [] := fun h => by simp [h] at hTail
  obtain ⟨_, hV⟩ :=
    PTX.Kernels.TmlFa4Fwd.Mma.walkFromRun (hr.after_local_nonempty hLayout hNonempty)
  let G := [(6511, b32 (firstVectorBase l g))]
  have hG : ∀ rv ∈ G, rv.1 ∈ Interval.beforeReady.regs := by
    intro rv hm
    simpa [G, Interval.regs] using List.mem_map_of_mem (f := Prod.fst) hm
  have hv' : At v 8464 G := hv.mono ⟨holds_lookup hv.2.2.2.2 (by rfl), trivial⟩
  obtain ⟨ready, events, visits, hReady, hWalk, hContinues, hPrefix⟩ :=
    cutStaging .beforeReady hG hv'.1.ge (by rw [hv'.1]; decide)
      (by rw [hv'.2.1]; decide) hv'.2.2.1 (.inl hv'.2.1) hv'.2.2.2.2 (by decide) hV hTail
  let readyFacts := (6496, b32 0) :: G
  have hSetup : Seg kernel [] l g 1 8472 G 8473 readyFacts := by
    intro t ht
    simp only [G, readyFacts] at ht ⊢
    seg_fp ht using rfl
  obtain ⟨pollState, hSetup, hPollState⟩ := hSetup ready hReady
  have hSetupAll : run kernel Assumptions.all l g 1 ready = some pollState := by
    simp only [run, Option.bind_eq_some_iff, Option.some.injEq, exists_eq_right] at hSetup ⊢
    rw [Assumptions.tauStep_all_eq_nil (by rw [hReady.1]; decide)
      (by rw [show ready.pc = 8472 from hReady.1]; exact Flow.code_8472) rfl]
    exact hSetup
  obtain hEmpty | ⟨_, _, _, hPollWalk⟩ := Mma.advanceWalkLocals hSetupAll hWalk
  · rw [hEmpty] at hContinues
    cases hContinues
  obtain ⟨failed, loc, parity, scope, afterWait, remaining, walkVisits, hEvents, hAfter,
      hWalkAfter, hFurther, source, returned, hSource, hEvent⟩ := correctionPollTrace 0 hPollState
    (by simp [readyFacts, G, correctionPoll]) hPollWalk hContinues (by decide)
  have hParity : parity = 0 := by
    obtain ⟨ins, hc, _, hf⟩ := estep_event_source hEvent
    rw [show source.pc = 8473 from hSource.1, Flow.code_8473] at hc
    obtain rfl := Option.some.inj hc
    have hReg : source.regs 6496 = some (b32 0) := hSource.2.2.2.2.1
    have hBits := readBits_b32 (L := l) (g := g) hReg (by decide : 0 < 2 ^ 32)
    have hWide : (Assumptions.all.any (·.clusterScopeMbar source.pc)) = false := rfl
    change Fires source.pc (eventTmpl Assumptions.all l g source
      (.mbarWait 9888 6495 0 (.reg 6496) true .cta)) _ _ at hf
    cases hLoc : mbarLoc l g source 6495 0 with
    | error f =>
      simp [eventTmpl, tmaTmpl, hLoc, hWide, widenMbarScope, bind, Except.bind, ofExec] at hf
      cases hf.2
    | ok m =>
      simp only [eventTmpl, tmaTmpl, hLoc, hBits, hWide, widenMbarScope, bind, Except.bind,
        pure, Except.pure, ofExec, Bool.false_eq_true, ↓reduceIte] at hf
      obtain ⟨_, hF, _⟩ := hf
      exact (Kind.wait.inj (congrArg Event.kind hF)).2.1
  subst parity
  have hAfter := hAfter.mono hAfter.2.2.2.2.2
  have hG' : ∀ rv ∈ G, rv.1 ∈ Interval.firstStore.regs := hG
  obtain ⟨w, tail, _, hw, hW, hLate, hStageSuffix⟩ := cutStaging .firstStore hG' hAfter.1.ge
    (by rw [hAfter.1]; decide) (by rw [hAfter.2.1]; decide) hAfter.2.2.1
    (.inl hAfter.2.1) hAfter.2.2.2.2 (by decide) hWalkAfter hFurther
  obtain ⟨bytes, hWrote⟩ := firstVectorWrite hp hw hW hLate (by decide)
  obtain ⟨idx, hIdx⟩ := List.mem_iff_getElem?.mp (hStageSuffix.subset hWrote)
  let poll : Event := ⟨8473, .wait loc 0 true true scope⟩
  let output : Event := ⟨8492, .wr (outputElementAccess l g 0 0 0 (rowOf l g)) bytes⟩
  obtain ⟨pre, hPre⟩ := (hPrefix.trans hSuffix).trans
    (show (X.tr g).drop (active.pos lane) <:+ X.tr g from List.drop_suffix _ _)
  have hTrace : X.tr g = (pre ++ failed) ++ poll :: remaining := by
    rw [← hPre, hEvents, List.append_assoc]
    rfl
  let wait := (pre ++ failed).length
  let store := wait + 1 + idx
  have hWait : X.get (g, wait) = some poll := by
    change (X.tr g)[wait]? = some poll
    rw [hTrace, List.getElem?_append_right (by rfl)]
    simp [wait]
  have hStore : X.get (g, store) = some output := by
    change (X.tr g)[store]? = some output
    rw [hTrace, List.getElem?_append_right (by dsimp [store, wait]; omega)]
    have hSub : store - (pre ++ failed).length = idx + 1 := by dsimp [store, wait]; omega
    rwa [hSub]
  have hExact : loc = ⟨.shared, g / l.block, l.sharedBase + 144⟩ := by
    exact firstCorrectionWaitAddress hp hX hWait
  refine ⟨wait, store, bytes, ⟨poll, scope, hWait, ?_⟩, ?_, hStore⟩
  · rw [← hExact]
  · exact po_of_source_not_access rfl (by dsimp [store]; omega)
      (List.getElem?_eq_some_iff.mp hStore).1 (by rw [hWait]; rfl)

/-- The first staging write follows the actual output acquire of this lane. -/
theorem firstStagingWriteAfterAcquire (hWork : g / l.block < tilePrefix p p.batch * p.heads) :
    ∃ wait pos bytes, FirstOutputAcquire l X (g, wait) ∧ po X (g, wait) (g, pos) ∧
      X.Writes (g, pos) (outputElementAccess l g 0 0 0 (rowOf l g)) bytes := by
  obtain ⟨wait, pos, bytes, hWait, hBefore, hStore⟩ :=
    firstStagingWriteEventAfterAcquire hp hX hDone hg hWarpLo hWarpHi hWork
  exact ⟨wait, pos, bytes, hWait, hBefore, 8492, hStore⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Correction
