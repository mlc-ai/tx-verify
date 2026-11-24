-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaReadyHistory
public import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Flow.Code.Part033
import Kernels.TmlFa4Fwd.Flow.Code.Part034
import Kernels.TmlFa4Fwd.Proof.MmaMbarAddress
import Lemmas.Flow.TcTmpl
import Lemmas.Step.CtaBar
public import Lemmas.Flow.TraceReach

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open Epilogue Loader Prologue Softmax

noncomputable section

private inductive FirstOperand
  | parity | address | secondParity

private def FirstOperand.reg : FirstOperand → Nat
  | .parity => 2536
  | .address => 2537
  | .secondParity => 2563

private def FirstOperand.definition : FirstOperand → Nat
  | .parity => 2140
  | .address => 2144
  | .secondParity => 2209

private def FirstOperand.word (l : Launch) : FirstOperand → Value
  | .parity => b32 0
  | .address => b32 (l.sharedBase + 32)
  | .secondParity => b32 0

private def FirstOperand.after : FirstOperand → Nat
  | .secondParity => 2213
  | _ => 2148

private def FirstOperand.active (f : FirstOperand) (pc : Nat) : Prop :=
  f.definition < pc ∧ pc < f.after

private instance (f : FirstOperand) (pc : Nat) : Decidable (f.active pc) :=
  inferInstanceAs (Decidable (f.definition < pc ∧ pc < f.after))

private def InitialReadyFrame (l : Launch) (s : TState) : Prop :=
  RoleShape s ∧ s.regs 1062 = some (b32 12) ∧ s.regs 2535 = some (b32 l.sharedBase) ∧
    ∀ f : FirstOperand, f.active s.pc → s.regs f.reg = some (f.word l)

private def initialReadyCode (pc : Nat) (i : Instr) : Bool :=
  !(mmaWrites i.op).contains 2535 &&
  [FirstOperand.parity, FirstOperand.address, FirstOperand.secondParity].all (fun f =>
    (!decide (f.active pc) || !(mmaWrites i.op).contains f.reg) &&
    match i.op with
    | .bra target _ => !decide (f.active target) || decide (f.active pc)
    | .brx .. => false
    | _ => true)

private theorem initialReadyCodeAt {pc : Nat} {i : Instr}
    (hLo : 1907 ≤ pc) (hHi : pc < 2768) (hc : kernel.code[pc]? = some i) :
    initialReadyCode pc i = true := by
  let code := ((kernel.code.drop 1907).take (2768 - 1907)).zipIdx 1907
  have hAll : code.all (fun (ins, site) => initialReadyCode site ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (i, pc)
  apply List.mem_of_getElem? (i := pc - 1907)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem initialZeroDefined {l : Launch} {g pc reg : Nat} {s u : TState}
    (hPc : s.pc = pc) (hf : s.fault = none)
    (hc : kernel.code[pc]? = some ⟨none, .move ⟨.scalar, .int .b 32, [some reg], [.imm 0]⟩⟩)
    (ht : Tau kernel [] l g s u) : u.regs reg = some (b32 0) := by
  let v := next (setReg s reg (b32 0))
  have hx : execLocalA [] l g s (.move ⟨.scalar, .int .b 32, [some reg], [.imm 0]⟩) =
      .ok v := by
    rw [execLocalA_nil, execLocal_move rfl]
    simp [execMove, readValue, readBits, DType.width,
      Value.bytes, b32, bind, Except.bind, pure, Except.pure, v]
    rfl
  have hOut : out kernel [] l g s = .tau v := by
    simp only [out, hPc, hf, hc, guardHolds, pure, Except.pure]
    exact congrArg (fun x : Exec TState => match x with
      | .ok s => Out.tau s | .error f => Out.ev (.ub f)) hx
  obtain rfl := Out.tau.inj (ht.symm.trans hOut)
  change (Function.update s.regs reg (some (b32 0))) reg = some (b32 0)
  exact Function.update_self _ _ _

private theorem initialReadyDefined {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s u : TState} (f : FirstOperand) (hPc : s.pc = f.definition)
    (hf : s.fault = none) (hb : s.regs 2535 = some (b32 l.sharedBase))
    (ht : Tau kernel [] l g s u) : u.regs f.reg = some (f.word l) := by
  cases f with
  | address =>
    have hBound : l.sharedBase + 32 < 2 ^ 32 := by have := hp.shared.2.1; omega
    have h := evalSharedAdd (g := g) hPc hf hb hBound Flow.code_2144
    obtain rfl := Option.some.inj ((tauStep_iff.mpr ht).symm.trans h)
    change (Function.update s.regs 2537 (some (b32 (l.sharedBase + 32)))) 2537 =
      some (b32 (l.sharedBase + 32))
    exact Function.update_self _ _ _
  | parity => exact initialZeroDefined hPc hf Flow.code_2140 ht
  | secondParity => exact initialZeroDefined hPc hf Flow.code_2209 ht

private theorem initialReadyStep {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s u : TState} {event : Option Event} (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768)
    (hFrame : InitialReadyFrame l s) (hw : WStep kernel Assumptions.all l g s event u) :
    (1907 ≤ u.pc ∧ u.pc < 2768 ∨ u.pc = 3099 ∧ u.fault = none) ∧ InitialReadyFrame l u := by
  obtain ⟨hPc, hShape, hWarp⟩ := mmaCutStep hLo hHi hw ⟨hFrame.1, hFrame.2.1⟩
  have hBase : u.regs 2535 = s.regs 2535 := by
    apply mmaStepReg (by omega) hHi _ hw
    intro i hc
    have h := initialReadyCodeAt hLo hHi hc
    simp only [initialReadyCode, Bool.and_eq_true] at h
    simpa using h.1
  refine ⟨by simpa using hPc, hShape, hWarp, hBase.trans hFrame.2.2.1, ?_⟩
  intro f hActive
  have checked {i : Instr} (hc : kernel.code[s.pc]? = some i) :
      ((!decide (f.active s.pc) || !(mmaWrites i.op).contains f.reg) &&
        match i.op with
        | .bra target _ => !decide (f.active target) || decide (f.active s.pc)
        | .brx .. => false
        | _ => true) = true := by
    have h := initialReadyCodeAt hLo hHi hc
    simp only [initialReadyCode, Bool.and_eq_true] at h
    exact List.all_eq_true.mp h.2 f (by cases f <;> simp)
  have hKeep (hPrior : f.active s.pc) : u.regs f.reg = some (f.word l) := by
    refine (mmaStepReg (by omega) hHi (fun i hc => ?_) hw).trans (hFrame.2.2.2 f hPrior)
    have h := checked hc
    simp only [Bool.and_eq_true] at h
    simpa [hPrior] using h.1
  have hFall (hNext : u.pc = s.pc + 1) : s.pc = f.definition ∨ f.active s.pc := by
    unfold FirstOperand.active at hActive ⊢
    omega
  rcases hw with ⟨_, ht⟩ | ⟨ev, _, he⟩
  · have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← out_eq_core (by omega) hHi]
    obtain ⟨i, hc, hf, _⟩ := tauScoreSource ht
    by_cases hDef : s.pc = f.definition
    · exact initialReadyDefined hp f hDef hf hFrame.2.2.1 ht'
    apply hKeep
    rcases tau_core_frame hc ht' with rfl | hLocal
    · exact (hFall rfl).resolve_left hDef
    have h := hLocal.pc
    have hCode := checked hc
    simp only [Bool.and_eq_true] at hCode
    cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at h
    case bra target uni =>
      rw [h] at hActive
      simpa [ho, hActive] using hCode.2
    case brx => simp [ho] at hCode
    all_goals exact (hFall h).resolve_left hDef
  · apply hKeep
    have hNot : s.pc ≠ f.definition := by
      intro hEq
      obtain ⟨i, hc, hl, _⟩ := estep_event_source he
      cases f
      · change s.pc = 2140 at hEq
        rw [hEq, Flow.code_2140] at hc
        obtain rfl := Option.some.inj hc.symm
        cases hl
      · change s.pc = 2144 at hEq
        rw [hEq, Flow.code_2144] at hc
        obtain rfl := Option.some.inj hc.symm
        cases hl
      · change s.pc = 2209 at hEq
        rw [hEq, Flow.code_2209] at hc
        obtain rfl := Option.some.inj hc.symm
        cases hl
    have hE : EStep kernel [] l g s ev (some u) := by
      obtain ⟨tm, ho, hf⟩ := he
      exact ⟨tm, by rwa [← out_eq_core (by omega) hHi], hf⟩
    rcases (estep_return_pc hE (fun _ _ _ h => execLocal_frame h)).2 with h | h
    · exact h ▸ hActive
    · exact (hFall h).resolve_left hNot

private theorem initialReadyWalk {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} {events : List Event} {visits : List Visit}
    (hWalk : Walk kernel Assumptions.all l g s events visits)
    (hPc : 1907 ≤ s.pc ∧ s.pc < 2768) (hFrame : InitialReadyFrame l s)
    {e : Event} (hMem : e ∈ events) (hEnd : e.pc < 2768) :
    ∃ t o, t.pc = e.pc ∧ InitialReadyFrame l t ∧ EStep kernel Assumptions.all l g t e o := by
  induction hWalk with
  | stop => cases hMem
  | @tau s u events visits ht hw ih =>
    obtain ⟨hPc, hNext⟩ := initialReadyStep hp hPc.1 hPc.2 hFrame (.inl ⟨rfl, ht⟩)
    rcases hPc with h | h
    · exact ih h hNext hMem
    · have hRet := mmaEpilogueExitEvents h.1 h.2 (.inl rfl) hNext.2.1 hw _ hMem
      omega
  | @ev s u ev events visits he hw ih =>
    rcases List.mem_cons.mp hMem with rfl | hMem
    · exact ⟨_, _, (estep_source_pc he).symm, hFrame, he⟩
    · obtain ⟨hPc, hNext⟩ := initialReadyStep hp hPc.1 hPc.2 hFrame (.inr ⟨_, rfl, he⟩)
      rcases hPc with h | h
      · exact ih h hNext hMem
      · have hRet := mmaEpilogueExitEvents h.1 h.2 (.inl rfl) hNext.2.1 hw _ hMem
        omega
  | last he =>
    obtain rfl := List.mem_singleton.mp hMem
    exact ⟨_, _, (estep_source_pc he).symm, hFrame, he⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- An actual warp-12 event after the register hint has the role walk at its fixed
startup offset. This also exposes the two last prologue records for prefix analyses. -/
theorem mmaRoleWalkOfDemand {g index : Nat} {e : Event} (he : X.get (g,index) = some e)
    (hWarp : warpIndex l g = 12) (hDemand : 1907 < e.pc ∨ 3 ≤ index ∧ Execution.isShfl e = true) :
    ∃ s visits, 6 ≤ index ∧ At s 1908 [(1062,b32 12), (2535,b32 l.sharedBase)] ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop 6) visits ∧
      X.get (g,3) = some ⟨172,.fenceMbarInit⟩ ∧ X.get (g,4) = some ⟨173,.bar 0 none .sync⟩ ∧
      ∃ inst, X.get (g,5) = some ⟨1907,.setMaxReg false 80 inst⟩ := by
  have hg := Step.CtaBar.thread_lt_of_get hX he
  have hStartup : 173 < e.pc ∨ e.kind = .exit ∨
      3 ≤ index ∧ Execution.isShfl e = true := by
    rcases hDemand with h | h
    · exact .inl (by omega)
    · exact .inr (.inr h)
  obtain ⟨t,o,hIndex,ht,_,hr,hFence,hBar⟩ :=
    Prologue.nonzeroCommonPrefixOfDemand hp hX hg (by rw [hWarp]; decide)
      he hStartup
  have hLen : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hSuffix : (X.tr g).drop 5 ≠ [] := by
    intro h
    exact Nat.not_le_of_lt hLen ((List.drop_eq_nil_iff.mp h).trans hIndex)
  have hAt : At t 174 [(1062,b32 12), (2535,b32 l.sharedBase)] :=
    ht.mono ⟨hWarp ▸ ht.2.2.2.2.1,ht.2.2.2.2.2.1,trivial⟩
  obtain ⟨s,inst,hReq,hs,hRun⟩ :=
    firstRegisterHintFromCommon hp hg (⟨12,by decide⟩ : Fin 16) hAt hr hSuffix
  have hLt : 5 < index := by
    by_contra! h
    obtain rfl : index = 5 := by omega
    have hSame := Option.some.inj (hReq.symm.trans he)
    change (Event.mk 1907 (.setMaxReg false 80 inst)) = e at hSame
    subst e
    rcases hDemand with h | ⟨_,h⟩
    · exact (Nat.lt_irrefl 1907 h).elim
    · cases h
  obtain ⟨visits,hWalk⟩ := walkFromRun hRun
  exact ⟨s,visits,hLt,hs,hWalk,hFence,hBar,inst,hReq⟩

private theorem initialMmaTraceFromQuery {g index : Nat} {e : Event}
    (he : X.get (g, index) = some e) (hLo : 2141 ≤ e.pc) (hHi : e.pc < 2768) :
    ∃ pos s visits, pos < index ∧ At s 1908 [(1062, b32 12), (2535, b32 l.sharedBase)] ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop (pos + 1)) visits := by
  have hHint : e.pc ∉ registerHintSites := by simp [registerHintSites]; omega
  have hWarp : warpIndex l g = 12 := by
    rcases roleBodyPcOfEvent hp hX he (by omega) hHint with h | h
    · omega
    · split_ifs at h <;> omega
  obtain ⟨s,visits,hIndex,hs,hWalk,_,_,_⟩ := mmaRoleWalkOfDemand hp hX he hWarp (.inl (by omega))
  exact ⟨5,s,visits,hIndex,hs,hWalk⟩

/-- Recover the actual MMA role trace beginning after its register hint. -/
theorem initialMmaTrace {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hLo : 2145 ≤ e.pc) (hHi : e.pc < 2768) :
    ∃ pos s visits, pos < index ∧ At s 1908 [(1062, b32 12), (2535, b32 l.sharedBase)] ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop (pos + 1)) visits :=
  initialMmaTraceFromQuery hp hX he (by omega) hHi

private theorem initialMmaEventFrame {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hLo : 2141 ≤ e.pc) (hHi : e.pc < 2768) :
    ∃ t o, t.pc = e.pc ∧ InitialReadyFrame l t ∧ EStep kernel Assumptions.all l g t e o := by
  obtain ⟨pos, s, _, hLt, hs, hWalk⟩ :=
    initialMmaTraceFromQuery hp hX he hLo hHi
  have hFrame : InitialReadyFrame l s := by
    refine ⟨⟨hs.2.1.symm ▸ Nat.zero_le _, hs.2.2.1, fun _ => hs.2.1⟩,
      hs.2.2.2.2.1, hs.2.2.2.2.2.1, ?_⟩
    intro f hf
    rw [hs.1] at hf
    cases f <;> exact (by decide : ¬ FirstOperand.active _ 1908) hf |>.elim
  have hMem : e ∈ (X.tr g).drop (pos + 1) := by
    apply List.mem_of_getElem? (i := index - (pos + 1))
    rw [List.getElem?_drop, Nat.add_sub_of_le hLt]
    exact he
  exact initialReadyWalk hp hWalk (by rw [hs.1]; decide) hFrame hMem hHi

/-- Actual MMA role events after the first K poll retain the shared base established in startup. -/
theorem mmaSharedBaseBeforeEvent {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hLo : 2145 ≤ e.pc) (hHi : e.pc < 2768) :
    ∃ t o, t.pc = e.pc ∧ t.regs 2535 = some (b32 l.sharedBase) ∧
      EStep kernel Assumptions.all l g t e o := by
  obtain ⟨t, o, ht, hFrame, hStep⟩ := initialMmaEventFrame hp hX he (by omega) hHi
  exact ⟨t, o, ht, hFrame.2.2.1, hStep⟩

omit hp hX in
/-- The opening K continuation still carries the original zero phase operand. -/
theorem openingParityOfTrace {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s u : TState} {es : List Event}
    (hs : At s 1935 [(1062,b32 12),(2535,b32 l.sharedBase)])
    (hReach : TraceReach kernel Assumptions.all l g s es u) (hu : u.pc = 2146)
    (hUpper : ∀ {a : TState} {events : List Event},
      TraceReach kernel Assumptions.all l g a events u → a.pc < 2768) :
    u.regs 2536 = some (b32 0) := by
  have hF : InitialReadyFrame l s := by
    refine ⟨⟨hs.2.1.symm ▸ Nat.zero_le _,hs.2.2.1,fun _ => hs.2.1⟩,
      hs.2.2.2.2.1,hs.2.2.2.2.2.1,?_⟩
    intro f hActive
    rw [hs.1] at hActive
    exfalso
    cases f <;> exact (by decide : ¬ FirstOperand.active _ 1935) hActive
  have fold {a z : TState} {events : List Event}
      (h : TraceReach kernel Assumptions.all l g a events z) :
      (∀ {b : TState} {fs : List Event},
        TraceReach kernel Assumptions.all l g b fs z → b.pc < 2768) →
      1907 ≤ a.pc → InitialReadyFrame l a → InitialReadyFrame l z := by
    induction h with
    | refl => exact fun _ _ hKeep => hKeep
    | tau hStep hTail ih =>
      intro hUp hLower hKeep
      obtain ⟨hNext,hFrame⟩ := initialReadyStep hp hLower
        (hUp (.tau hStep hTail)) hKeep (.inl ⟨rfl,hStep⟩)
      exact ih hUp (by rcases hNext with h | h <;> omega) hFrame
    | event hStep hTail ih =>
      intro hUp hLower hKeep
      obtain ⟨hNext,hFrame⟩ := initialReadyStep hp hLower
        (hUp (.event hStep hTail)) hKeep (.inr ⟨_,rfl,hStep⟩)
      exact ih hUp (by rcases hNext with h | h <;> omega) hFrame
  exact (fold hReach hUpper (by rw [hs.1]; decide) hF).2.2.2 .parity (by rw [hu]; decide)

/-- The actual initial K-ready poll requests parity zero on slot zero, including retries.
It does not require the companion trip reads to have any particular values. -/
theorem initialReadyPollOperands {g index parity : Nat} {loc : Loc} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨2145, .wait loc parity ok acq scope⟩) :
    loc = initObject l (g / l.block) (readySlot 0) ∧ parity = 0 ∧ acq = true ∧ scope = .cta := by
  obtain ⟨u, _, hu, hFrame', tm, hOut, hFire⟩ := initialMmaEventFrame hp hX he
    (show 2141 ≤ 2145 by decide) (show 2145 < 2768 by decide)
  change u.pc = 2145 at hu
  rw [out_eq_core (by rw [hu]; decide) (by rw [hu]; decide)] at hOut
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · have hKind := congrArg Event.kind hFire.1
    cases hKind
  rw [hu, Flow.code_2145] at hc
  obtain rfl := Option.some.inj hc.symm
  have hBase : u.regs 2537 = some (b32 (l.sharedBase + 32)) :=
    hFrame'.2.2.2 .address (by rw [hu]; decide)
  have hPhase : u.regs 2536 = some (b32 0) :=
    hFrame'.2.2.2 .parity (by rw [hu]; decide)
  have hRead := readBits_b32 (L := l) (g := g) hPhase (by decide : 0 < 2 ^ 32)
  have hLocation := decodedMbarOffset hp (g := g) (off := 0) hBase
    (by unfold initializedMbarOffset; decide)
  change mbarLoc l g u 2537 0 =
    .ok ⟨.shared, g / l.block, l.sharedBase + (32 + 0)⟩ at hLocation
  simp only [eventTmpl, tmaTmpl, hLocation, hRead, bind, Except.bind, pure, Except.pure,
    ofExec, widenMbarScope, List.any_nil, Bool.false_eq_true, ↓reduceIte] at hFire
  obtain ⟨success, hFire, _⟩ := hFire
  have h := Kind.wait.inj (congrArg Event.kind hFire)
  refine ⟨?_, h.2.1, h.2.2.2.1, h.2.2.2.2⟩
  simpa [readySlot_address] using h.1

/-- The initial Q acquire uses the CTA's first query barrier and parity zero. -/
theorem firstQueryPollShape {g index parity : Nat} {loc : Loc} {ok acq : Bool} {scope : MbarScope}
    (he : X.get (g, index) = some ⟨2141, .wait loc parity ok acq scope⟩) :
    loc = ⟨.shared, g / l.block, l.sharedBase⟩ ∧ parity = 0 ∧ acq = true ∧ scope = .cta := by
  obtain ⟨u, _, hu, hFrame, tm, hOut, hFire⟩ := initialMmaEventFrame hp hX he
    (show 2141 ≤ 2141 by decide) (show 2141 < 2768 by decide)
  change u.pc = 2141 at hu
  rw [out_eq_core (by rw [hu]; decide) (by rw [hu]; decide)] at hOut
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · have hKind := congrArg Event.kind hFire.1
    cases hKind
  rw [hu, Flow.code_2141] at hc
  obtain rfl := Option.some.inj hc.symm
  have hBase : u.regs 2535 = some (b32 l.sharedBase) := hFrame.2.2.1
  have hPhase : u.regs 2536 = some (b32 0) :=
    hFrame.2.2.2 .parity (by rw [hu]; decide)
  have hRead := readBits_b32 (L := l) (g := g) hPhase (by decide : 0 < 2 ^ 32)
  have hLocation := decodedMbarOffset hp (g := g) (off := 0) (delta := 0)
    (by simpa using hBase) (by unfold initializedMbarOffset; decide)
  change mbarLoc l g u 2535 0 = .ok ⟨.shared, g / l.block, l.sharedBase⟩ at hLocation
  simp only [eventTmpl, tmaTmpl, hLocation, hRead, bind, Except.bind, pure, Except.pure,
    ofExec, widenMbarScope, List.any_nil, Bool.false_eq_true, ↓reduceIte] at hFire
  obtain ⟨success, hFire, _⟩ := hFire
  have h := Kind.wait.inj (congrArg Event.kind hFire)
  exact ⟨by simpa using h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- The initial Q acquire uses the CTA's first query barrier and parity zero. -/
theorem firstQueryPollOperands {g index parity : Nat} {loc : Loc} {ok : Bool}
    (he : X.get (g, index) = some ⟨2141, .wait loc parity ok true .cta⟩) :
    loc = ⟨.shared, g / l.block, l.sharedBase⟩ ∧ parity = 0 :=
  (firstQueryPollShape hp hX he).imp_right And.left

/-- The initial Q1 acquire and its retries use the second query barrier at parity zero. -/
theorem secondQueryPollShape {g index parity : Nat} {loc : Loc} {ok acq : Bool} {scope : MbarScope}
    (he : X.get (g, index) = some ⟨2210, .wait loc parity ok acq scope⟩) :
    loc = ⟨.shared, g / l.block, l.sharedBase + 8⟩ ∧ parity = 0 ∧ acq = true ∧ scope = .cta := by
  refine ⟨mmaFixedWaitAddress hp hX he (by decide), ?_⟩
  obtain ⟨u, _, hu, hFrame, tm, hOut, hFire⟩ := initialMmaEventFrame hp hX he
    (show 2141 ≤ 2210 by decide) (show 2210 < 2768 by decide)
  change u.pc = 2210 at hu
  rw [out_eq_core (by rw [hu]; decide) (by rw [hu]; decide)] at hOut
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · have hKind := congrArg Event.kind hFire.1
    cases hKind
  rw [hu, Flow.code_2210] at hc
  obtain rfl := Option.some.inj hc.symm
  have hPhase : u.regs 2563 = some (b32 0) :=
    hFrame.2.2.2 .secondParity (by rw [hu]; decide)
  have hRead := readBits_b32 (L := l) (g := g) hPhase (by decide : 0 < 2 ^ 32)
  cases hLoc : mbarLoc l g u 2562 0 with
  | error f =>
    simp only [eventTmpl, tmaTmpl, hLoc, bind, Except.bind, ofExec, widenMbarScope,
      List.any_nil, Bool.false_eq_true, ↓reduceIte] at hFire
    have hKind := congrArg Event.kind hFire.1
    cases hKind
  | ok target =>
    simp only [eventTmpl, tmaTmpl, hLoc, hRead, bind, Except.bind, pure, Except.pure,
      ofExec, widenMbarScope, List.any_nil, Bool.false_eq_true, ↓reduceIte] at hFire
    obtain ⟨success, hFire, _⟩ := hFire
    have h := Kind.wait.inj (congrArg Event.kind hFire)
    exact ⟨h.2.1,h.2.2.2.1,h.2.2.2.2⟩

/-- The initial Q1 acquire and its retries use the second query barrier at parity zero. -/
theorem secondQueryPollOperands {g index parity : Nat} {loc : Loc} {ok : Bool}
    (he : X.get (g, index) = some ⟨2210, .wait loc parity ok true .cta⟩) :
    loc = ⟨.shared, g / l.block, l.sharedBase + 8⟩ ∧ parity = 0 :=
  (secondQueryPollShape hp hX he).imp_right And.left

end
end PTX.Kernels.TmlFa4Fwd.Mma
