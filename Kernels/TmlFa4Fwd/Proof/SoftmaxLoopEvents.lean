-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaRoleFrame
public import Lemmas.Flow.EventCont

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

/-- Event destinations that matter to the scheduler and score-loop ranks. -/
def scoreEventWrites : Op → List Nat
  | .tcLd ds _ _ _ => ds
  | .mbarArrive _ _ _ _ _ _ _ s => s.toList
  | op => Mma.mmaWrites op

def scoreStoreOp (a : MemAccess) : Bool :=
  a.kind == .store && a.sem == .weak && a.srcs.length ≤ 4 &&
    a.rule == some .threadAccess && a.locSpace?.isSome &&
    match a.addr.base with | .reg .. => true | _ => false

/-- Returning event forms used by either softmax group. -/
def scoreEventOp : Op → Bool
  | .tcLd _ _ _ red => red.isNone
  | .barArrive .. | .mbarArrive .. | .fence .. | .tcWaitSt | .tcSt .. => true
  | .warp w => Mma.linearWarpOp w || match w.kind with | .barWarp => true | _ => false
  | .mem a => (a.kind == .load && !a.nc && a.ext == .same && a.regs.length ≤ 4) ||
      scoreStoreOp a
  | .barSync .. | .barSyncN .. | .setMaxReg .. | .mbarWait .. => true
  | _ => false

/-- A returning event advances to the next PC, consumes a sub-step, or records a read fault. -/
structure ScoreEventProgress (s u : TState) : Prop where
  sub : u.sub ≤ 3
  pc : u.pc = s.pc + 1 ∧ u.fault = s.fault ∨
    u.pc = s.pc ∧ (u.sub = s.sub + 1 ∨ u.fault.isSome)

/-- Ordinary instruction boundaries have no pending component of a split access. -/
def ScoreScratchClear (s : TState) : Prop := s.sub = 0 ∧ s.acc = []

/-- Only a split load can carry accumulated values. Split stores and audited TMEM waits
can carry a nonzero sub-step while retaining an empty accumulation. -/
def ScoreScratchReady (op : Op) (s : TState) : Prop :=
  match op with
  | .mem a => a.kind = .load ∨ s.acc = []
  | .tcLd .. => (Assumptions.all.any (·.tcLdWait s.pc) = true ∨ s.sub = 0) ∧ s.acc = []
  | .tcSt .. => (Assumptions.all.any (·.tcStWaitLd s.pc) = true ∨ s.sub = 0) ∧ s.acc = []
  | _ => ScoreScratchClear s

private def ScratchTransition (op : Op) (s u : TState) : Prop :=
  ScoreScratchReady op s → if u.pc = s.pc then ScoreScratchReady op u else ScoreScratchClear u

private theorem scoreMemLoad {l : Launch} {g r : Nat} {s u : TState} {a : MemAccess}
    {e : Event} (hOp : a.kind = .load ∧ a.nc = false ∧ a.ext = .same ∧ a.regs.length ≤ 4)
    (hs : s.sub ≤ 3) (hKeep : r ∉ a.regs)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.mem a)) e (some u)) :
    ScoreEventProgress s u ∧ u.regs r = s.regs r ∧ ScratchTransition (.mem a) s u := by
  obtain ⟨_, bs, _, rfl⟩ := fires_load hOp.1 hOp.2.1 hf hOp.2.2.1
  cases hb : rebuild 3 bs with
  | error f =>
    exact ⟨⟨by simpa [afterLoad, hb] using hs,
      .inr ⟨by simp [afterLoad, hb], .inr (by simp [afterLoad, hb])⟩⟩, by simp [afterLoad, hb], by
      simp [ScratchTransition, ScoreScratchReady, afterLoad, hb, hOp.1]⟩
  | ok v =>
    by_cases hv : s.sub + 1 < a.regs.length
    · simp only [afterLoad, hb, ite_eq_left hv]
      exact ⟨⟨by change s.sub + 1 ≤ 3; omega, .inr ⟨rfl, .inl rfl⟩⟩, trivial, by
        simp [ScratchTransition, ScoreScratchReady, hOp.1]⟩
    · rw [afterLoad_last hb (by omega)]
      exact ⟨⟨by change 0 ≤ 3; decide, .inl ⟨rfl, (setRegs_skel _ _ _).2.2.2⟩⟩,
        setRegs_other _ _ _ _ hKeep, by
          simp [ScratchTransition, ScoreScratchReady, ScoreScratchClear, hOp.1]⟩

private theorem scoreMemStore {l : Launch} {g r : Nat} {s u : TState}
    {a : MemAccess} {e : Event} (hOp : scoreStoreOp a = true)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.mem a)) e (some u)) :
    ScoreEventProgress s u ∧ u.regs r = s.regs r ∧ ScratchTransition (.mem a) s u := by
  simp only [scoreStoreOp, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hOp
  obtain ⟨⟨⟨⟨⟨hKind, hSem⟩, hLen⟩, hRule⟩, hSpace⟩, hAddr⟩ := hOp
  cases hLoc : a.locSpace? with
  | none => simp [hLoc] at hSpace
  | some sp =>
    cases hBase : a.addr.base <;> simp [hBase] at hAddr
    rename_i base width
    simp only [eventTmpl, memTmpl_direct_weakStore hRule hLoc hBase hKind hSem, storeTmpl] at hf
    repeat' split at hf
    all_goals simp only [Fires, reduceCtorEq, and_false] at hf
    obtain rfl := Option.some.inj hf.2
    by_cases h : s.sub + 1 < a.srcs.length
    · simp only [afterStore, ite_eq_left h]
      exact ⟨⟨by change s.sub + 1 ≤ 3; omega, .inr ⟨rfl, .inl rfl⟩⟩, trivial, by
        simp [ScratchTransition, ScoreScratchReady, hKind]⟩
    · simp only [afterStore, ite_eq_right h]
      exact ⟨⟨by change 0 ≤ 3; decide, .inl ⟨rfl, rfl⟩⟩, trivial, by
        simp [ScratchTransition, ScoreScratchReady, ScoreScratchClear, hKind]⟩

private theorem scoreTensorLoad {l : Launch} {g r ta : Nat} {s u : TState}
    {ds : List Nat} {sh : TcShape} {e : Event} (hs : s.sub ≤ 3) (hKeep : r ∉ ds)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.tcLd ds ta sh none)) e (some u)) :
    ScoreEventProgress s u ∧ u.regs r = s.regs r ∧ ScratchTransition (.tcLd ds ta sh none) s u := by
  let P := fun (v : TState) =>
    ScoreEventProgress s v ∧ v.regs r = s.regs r ∧ ScratchTransition (.tcLd ds ta sh none) s v
  have hFrame (hOff : Assumptions.all.any (·.tcLdWait s.pc) = false) :
      CallbackFrame P (tcTmpl l g s (.tcLd ds ta sh none)) := by
    cases sh <;> simp only [tcTmpl, ldResult] <;> apply ofExec_frame
    all_goals
      repeat' first
        | exact True.intro
        | (apply allOk_bind; intro v)
        | split
    all_goals
      intro vals
      exact ⟨⟨by simpa only [(setRegs_skel _ _ _).2.1] using (show (next s).sub ≤ 3 from hs),
        .inl ⟨(setRegs_skel _ _ _).1, (setRegs_skel _ _ _).2.2.2⟩⟩, setRegs_other _ _ _ _ hKeep, by
        unfold ScratchTransition ScoreScratchReady ScoreScratchClear
        simp only [(setRegs_skel _ _ _).1, (setRegs_skel _ _ _).2.1,
          (setRegs_skel _ _ _).2.2.1]
        simp [next, hOff]⟩
  by_cases hWait : Assumptions.all.any (·.tcLdWait s.pc) = true
  · by_cases hSub : s.sub = 0
    · have hWaitFrame : CallbackFrame P
          ((tcTmpl l g s (.tcLd ds ta sh none)).thenWaitLd s.pc) := by
        have lift {m : Exec Tmpl}
            (hm : AllOk (fun t => CallbackFrame P (t.thenWaitLd s.pc)) m) :
            CallbackFrame P ((ofExec m).thenWaitLd s.pc) := by
          cases m <;> exact hm
        cases sh <;> simp only [tcTmpl, ldResult] <;> apply lift
        all_goals
          repeat' first
            | exact True.intro
            | (apply allOk_bind; intro v)
            | split
        all_goals
          intro vals
          exact ⟨⟨by change 1 ≤ 3; decide, .inr ⟨rfl, .inl (by simp [hSub])⟩⟩,
            setRegs_other _ _ _ _ hKeep, by
              simp [ScratchTransition, ScoreScratchReady, (setRegs_skel _ _ _).2.2.1, hWait]
              exact id⟩
      apply callbackFrame_fires hWaitFrame
      simpa only [eventTmpl, tcLdTmpl, hWait, hSub, ite_true] using hf
    · obtain ⟨_, rfl⟩ := fires_tcLd_wait hWait hSub hf
      exact ⟨⟨by change 0 ≤ 3; decide, .inl ⟨rfl, rfl⟩⟩, rfl, by
        simp [ScratchTransition, ScoreScratchReady, ScoreScratchClear, hWait, next]⟩
  · have hOff : Assumptions.all.any (·.tcLdWait s.pc) = false := by simpa using hWait
    apply callbackFrame_fires (hFrame hOff)
    simpa only [eventTmpl, tcLdTmpl, hOff, Bool.false_eq_true, ite_false] using hf

private theorem scoreTensorStore {l : Launch} {g r ta : Nat} {s u : TState}
    {ss : List Opnd} {sh : TcShape} {e : Event} (hs : s.sub ≤ 3)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.tcSt ta ss sh)) e (some u)) :
    ScoreEventProgress s u ∧ u.regs r = s.regs r ∧ ScratchTransition (.tcSt ta ss sh) s u := by
  have frame (v : TState) : CallbackFrame (· = next v) (tcTmpl l g v (.tcSt ta ss sh)) := by
    cases sh <;> simp only [tcTmpl] <;> apply ofExec_frame
    all_goals repeat' first | rfl | trivial | (apply allOk_bind; intro v) | split
  simp only [eventTmpl, tcStTmpl] at hf
  split at hf
  · rename_i hHook
    split at hf
    · split at hf
      · obtain rfl := Option.some.inj hf.2
        exact ⟨⟨by change 1 ≤ 3; decide,
          .inr ⟨rfl, .inl (by change 1 = s.sub + 1; omega)⟩⟩, rfl, by
          simp [ScratchTransition, ScoreScratchReady, hHook]⟩
      · cases hf.2
    · obtain rfl := callbackFrame_fires (frame _) hf
      exact ⟨⟨by change 0 ≤ 3; decide, .inl ⟨rfl, rfl⟩⟩, rfl, by
        simp [ScratchTransition, ScoreScratchReady, ScoreScratchClear, next]⟩
  · rename_i hHook
    obtain rfl := callbackFrame_fires (frame _) hf
    exact ⟨⟨hs, .inl ⟨rfl, rfl⟩⟩, rfl, by
      simp [ScratchTransition, ScoreScratchReady, ScoreScratchClear, hHook, next]⟩

private theorem scoreBarArrive {l : Launch} {g : Nat} {s u : TState}
    {id n : Opnd} {aligned : Bool} {e : Event}
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.barArrive id n aligned)) e (some u)) :
    u = next s := by
  apply callbackFrame_fires (P := (· = next s)) _ hf
  simp only [eventTmpl, barTmpl]
  repeat' split
  all_goals first | rfl | trivial

variable {l : Launch} {g r : Nat} {s u : TState} {e : Event} {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) (hOp : scoreEventOp ins.op = true) (hs : s.sub ≤ 3)
    (hr : r ∉ scoreEventWrites ins.op) (he : EStep kernel Assumptions.all l g s e (some u))
include hc hOp hs hr he

private theorem scoreEventFacts :
    ScoreEventProgress s u ∧ u.regs r = s.regs r ∧ ScratchTransition ins.op s u := by
  obtain ⟨i, hi, _, hf⟩ := estep_event_source he
  rw [hc] at hi
  obtain rfl := Option.some.inj hi
  have finish {op : Op} (h : AdvancesOp op) (hReady : ScoreScratchReady op s → ScoreScratchClear s)
      (hf : Fires s.pc (eventTmpl Assumptions.all l g s op) e (some u)) :
      ScoreEventProgress s u ∧ u.regs r = s.regs r ∧ ScratchTransition op s u := by
    obtain rfl := fires_next h hf
    exact ⟨⟨hs, .inl ⟨rfl, rfl⟩⟩, rfl, by
      simpa [ScratchTransition, ScoreScratchClear, next] using hReady⟩
  generalize hop : ins.op = op at hOp hf hr ⊢
  cases op <;> try contradiction
  case tcLd ds addr shape red =>
    have hRed : red = none := Option.isNone_iff_eq_none.mp hOp
    subst red
    exact scoreTensorLoad hs hr hf
  case tcSt => exact scoreTensorStore hs hf
  case tcWaitSt =>
    have h : CallbackFrame (· = next s) (eventTmpl Assumptions.all l g s .tcWaitSt) := by
      simp only [eventTmpl, tcTmpl]
      apply ofExec_frame
      repeat' first | rfl | trivial | split
    obtain rfl := callbackFrame_fires h hf
    exact ⟨⟨hs, .inl ⟨rfl, rfl⟩⟩, rfl, by
      simp [ScratchTransition, ScoreScratchReady, ScoreScratchClear, next]⟩
  case mbarArrive b o tx n c rel sc d =>
    obtain ⟨rfl, _⟩ := fires_arrive_state hf
    cases d with
    | none =>
      exact ⟨⟨hs, .inl ⟨rfl, rfl⟩⟩, rfl, by
        simp [ScratchTransition, ScoreScratchReady, ScoreScratchClear, next, mbarStateDest]⟩
    | some d =>
      have hd : r ≠ d := by simpa [scoreEventWrites] using hr
      exact ⟨⟨hs, .inl ⟨rfl, rfl⟩⟩, Function.update_of_ne hd _ _, by
        simp [ScratchTransition, ScoreScratchReady, ScoreScratchClear, next, mbarStateDest]⟩
  case fence f => exact finish (op := .fence f) trivial id hf
  case barArrive =>
    obtain rfl := scoreBarArrive hf
    exact ⟨⟨hs, .inl ⟨rfl, rfl⟩⟩, rfl, by
      simp [ScratchTransition, ScoreScratchReady, ScoreScratchClear, next]⟩
  case mem a =>
    simp only [scoreEventOp, Bool.or_eq_true] at hOp
    rcases hOp with h | h
    · exact scoreMemLoad (by simpa [and_assoc] using h) hs hr hf
    · exact scoreMemStore h hf
  case warp w =>
    simp only [scoreEventOp, Bool.or_eq_true] at hOp
    rcases hOp with hLin | hBar
    · have hReg := Mma.mmaEventRegs (r := r) hc (hop.symm ▸ hLin) (hop.symm ▸ hr) he
      let same (v : TState) := {v with pc := s.pc + 1, sub := s.sub, acc := s.acc, fault := s.fault}
      have hShape : u = same u := by
        unfold Mma.linearWarpOp at hLin
        split at hLin
        · obtain ⟨_, _, _, _, _, _, rfl⟩ := fires_shfl (p := none) hf
          rfl
        · rename_i _ ty dst pred mask
          obtain ⟨_, _, _, _, rfl⟩ := fires_elect hf
          cases dst <;> rfl
        · simp only [eventTmpl, warpTmpl_vote] at hf
          apply callbackFrame_fires (P := fun v => v = same v) _ hf
          unfold voteTmpl
          split <;> (try split_ifs) <;> simp [CallbackFrame, same, next, setReg]
        · cases hLin
      dsimp only [same] at hShape
      have hFault := congrArg TState.fault hShape
      exact ⟨⟨(congrArg TState.sub hShape).symm ▸ hs,
        .inl ⟨congrArg TState.pc hShape, hFault⟩⟩, hReg, by
        simp [ScratchTransition, ScoreScratchReady, ScoreScratchClear,
          congrArg TState.pc hShape, congrArg TState.sub hShape, congrArg TState.acc hShape]⟩
    · apply finish _ id hf
      cases w with
      | mk k ty dsts srcs mask =>
        cases k <;> first | exact True.intro | cases hBar
  case barSync id aligned =>
    have h : CallbackFrame (· = next s) (eventTmpl Assumptions.all l g s
        (.barSync id aligned)) := by
      simp only [eventTmpl, barTmpl]
      repeat' split
      all_goals first | rfl | trivial
    obtain rfl := callbackFrame_fires h hf
    exact ⟨⟨hs, .inl ⟨rfl, rfl⟩⟩, rfl, by
      simp [ScratchTransition, ScoreScratchReady, ScoreScratchClear, next]⟩
  case barSyncN id n aligned =>
    have h : CallbackFrame (· = next s) (eventTmpl Assumptions.all l g s
        (.barSyncN id n aligned)) := by
      simp only [eventTmpl, barTmpl]
      repeat' split
      all_goals first | rfl | trivial
    obtain rfl := callbackFrame_fires h hf
    exact ⟨⟨hs, .inl ⟨rfl, rfl⟩⟩, rfl, by
      simp [ScratchTransition, ScoreScratchReady, ScoreScratchClear, next]⟩
  case setMaxReg inc n => exact finish (op := .setMaxReg inc n) trivial id hf
  case mbarWait p base off par acq sc =>
    obtain ⟨_, _, _, _, _, rfl⟩ := fires_wait hf
    have hn : r ≠ p := by simpa [scoreEventWrites, Mma.mmaWrites] using hr
    exact ⟨⟨hs, .inl ⟨rfl, rfl⟩⟩, Function.update_of_ne hn _ _, by
      simp [ScratchTransition, ScoreScratchReady, ScoreScratchClear, next, setReg]⟩

/-- All score dataflow events preserve a register outside their decoded destinations. -/
theorem scoreEventStep :
    ScoreEventProgress s u ∧ u.regs r = s.regs r :=
  let facts := scoreEventFacts hc hOp hs hr he
  ⟨facts.1, facts.2.1⟩

/-- A returning event clears its scratch data when it finishes. A same-instruction
continuation stays within that instruction's allowed scratch state. -/
theorem scoreEventScratch (hReady : ScoreScratchReady ins.op s) :
    if u.pc = s.pc then ScoreScratchReady ins.op u else ScoreScratchClear u :=
  (scoreEventFacts hc hOp hs hr he).2.2 hReady

end
end PTX.Kernels.TmlFa4Fwd.Softmax
