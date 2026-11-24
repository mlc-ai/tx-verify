-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasPolls
import Kernels.TmlFa4Fwd.Proof.LoaderMbarAddress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.AsyncCopy PTX.Kernels.TmlFa4Fwd.Thread.Loader

/-- The first Bias-empty poll site for each stage. -/
def biasPrimingPoll (stage : Fin 2) : Nat := if stage = 0 then 704 else 756

private def biasPrimingParityReg (stage : Fin 2) : Nat := if stage = 0 then 1898 else 1918

private def movePrimingParity (stage : Fin 2) : Op :=
  .move ⟨.scalar, .int .b 32, [some (biasPrimingParityReg stage)], [.imm 1]⟩

private theorem primingParityCode (stage : Fin 2) :
    kernel.code[biasPrimingPoll stage - 1]? = some ⟨none, movePrimingParity stage⟩ := by
  fin_cases stage
  · exact Flow.code_703
  · exact Flow.code_755

private def primingPhaseLive (stage : Fin 2) (pc : Nat) : Prop :=
  biasPrimingPoll stage ≤ pc ∧ pc ≤ biasPrimingPoll stage + 2

private instance (stage : Fin 2) (pc : Nat) : Decidable (primingPhaseLive stage pc) :=
  inferInstanceAs (Decidable (biasPrimingPoll stage ≤ pc ∧ pc ≤ biasPrimingPoll stage + 2))

private def primingPhaseSafety (stage : Fin 2) (pc : Nat) (op : Op) : Bool :=
  (!decide (primingPhaseLive stage pc) ||
    !(loaderRingWrites op).contains (biasPrimingParityReg stage)) && match op with
  | .bra dst _ => decide (primingPhaseLive stage dst → primingPhaseLive stage pc)
  | .brx .. => false
  | _ => true

private theorem primingPhaseSafetyAt (stage : Fin 2) {pc : Nat} {ins : Instr}
    (hLo : 174 ≤ pc) (hHi : pc < 1901) (hc : kernel.code[pc]? = some ins) :
    primingPhaseSafety stage pc ins.op = true := by
  let code := ((kernel.code.drop 174).take (1901 - 174)).zipIdx 174
  have hAll : code.all (fun (ins, pc) => primingPhaseSafety stage pc ins.op) = true := by
    fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (ins,pc)
  apply List.mem_of_getElem? (i := pc - 174)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem primingPhaseTransition (stage : Fin 2) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (hShape : RingShape s) (hStep : WStep kernel Assumptions.all l g s e u)
    (hDst : primingPhaseLive stage u.pc) :
    primingPhaseLive stage s.pc ∨ s.pc = biasPrimingPoll stage - 1 := by
  have hNext (h : u.pc = s.pc ∨ u.pc = s.pc + 1) :
      primingPhaseLive stage s.pc ∨ s.pc = biasPrimingPoll stage - 1 := by
    unfold primingPhaseLive at hDst ⊢
    omega
  rcases hStep with ⟨rfl, ht⟩ | ⟨event, rfl, he⟩
  · have hCore : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore hLo (by omega)]
    obtain ⟨ins, hc⟩ := tau_core_has_code hCore
    have hLaw := (Bool.and_eq_true_iff.mp (primingPhaseSafetyAt stage hLo hHi hc)).2
    rcases tau_core_frame hc hCore with rfl | hf
    · exact hNext (.inr rfl)
    have hPc := hf.pc
    cases hOp : ins.op <;> simp only [hOp, nextPc, BrxTarget, or_false] at hPc
    case bra dst aligned =>
      change (match ins.op with
        | .bra dst _ => decide (primingPhaseLive stage dst → primingPhaseLive stage s.pc)
        | .brx .. => false | _ => true) = true at hLaw
      rw [hOp] at hLaw
      exact .inl (of_decide_eq_true hLaw (hPc ▸ hDst))
    case brx => simp [hOp] at hLaw
    all_goals exact hNext (.inr hPc)
  · obtain ⟨_, hp | ⟨hp, _⟩⟩ := loaderEventProgress hLo (by omega) hShape.1 he
    · exact hNext (.inr hp)
    · exact hNext (.inl hp)

private theorem primingPhaseWrite (stage : Fin 2) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (hPc : s.pc = biasPrimingPoll stage - 1)
    (hStep : WStep kernel Assumptions.all l g s e u) :
    u.regs (biasPrimingParityReg stage) = some (b32 1) := by
  have hc := hPc.symm ▸ primingParityCode stage
  have hExec : execLocal l g s (movePrimingParity stage) =
      .ok (next (setReg s (biasPrimingParityReg stage) (b32 1))) := by
    unfold movePrimingParity
    rw [execLocal_move rfl]
    simp [execMove, readValue, readBits, DType.width, Value.bytes, b32,
      bind, Except.bind, pure, Except.pure]
    rfl
  have hLocal : (movePrimingParity stage).isLocal = true := rfl
  rcases hStep with ⟨rfl, ht⟩ | ⟨event, rfl, he⟩
  · have hCore : out kernel [] l g s = .tau u := by
      unfold Tau at ht
      rwa [← loaderOutCore hLo (by omega)]
    unfold out at hCore
    cases hf : s.fault
    · simp [hf, hc, guardHolds, hLocal,
        execLocalA_nil, hExec, pure, Except.pure] at hCore
      obtain rfl := hCore
      exact Function.update_self _ _ _
    · simp [hf] at hCore
  · obtain ⟨ins, hRead, hLocal, _⟩ := estep_event_source he
    obtain rfl := Option.some.inj (hc.symm.trans hRead)
    cases hLocal

private def PrimingPhaseFrame (stage : Fin 2) (s : TState) : Prop :=
  primingPhaseLive stage s.pc → s.regs (biasPrimingParityReg stage) = some (b32 1)

private theorem primingPhaseStep (stage : Fin 2) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (hShape : RingShape s) (hFrame : PrimingPhaseFrame stage s)
    (hStep : WStep kernel Assumptions.all l g s e u) : PrimingPhaseFrame stage u := by
  intro hDst
  rcases primingPhaseTransition stage hLo hHi hShape hStep hDst with hLive | hSeed
  · rw [loaderPipelineStepRegs hLo hHi (fun ins hc => by
      have hd := (Bool.and_eq_true_iff.mp (primingPhaseSafetyAt stage hLo hHi hc)).1
      simpa [hLive] using hd) hStep]
    exact hFrame hLive
  · exact primingPhaseWrite stage hLo hHi hSeed hStep

private theorem fullBiasLoaderBranches (bound : Nat) :
    ((kernel.code.drop 174).take (1901 - 174)).all
      (fun ins => loaderPipelineCutOp 174 1901 bound [2535, 1062] ins.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem loaderReplayEvent {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (warp : Fin 2)
    (hWalk : Walk kernel Assumptions.all l g s es vs)
    (hPc : 174 ≤ s.pc ∧ s.pc ≤ 1901) (hShape : RingShape s)
    (hRoots : Holds s.regs [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
    {pre : List Event} {P : List Event → TState → Prop} (hInv : P pre s)
    (step : ∀ {a b : TState} {ev : Option Event} {past : List Event},
      174 ≤ a.pc → a.pc < 1901 → RingShape a →
      Holds a.regs [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] →
      P past a → WStep kernel Assumptions.all l g a ev b → P (past ++ ev.toList) b)
    {j : Nat} {mark : Event} (he : es[j]? = some mark) (hLimit : mark.pc < 1901) :
    ∃ t o, t.pc = mark.pc ∧ P (pre ++ es.take j) t ∧
      EStep kernel Assumptions.all l g t mark o := by
  let frame := [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))]
  have leave {s : TState} {es : List Event} {vs : List Visit}
      (hw : Walk kernel Assumptions.all l g s es vs) (hExit : s.pc = 1901)
      (hs : RingShape s) (hf : Holds s.regs frame) (hm : mark ∈ es) : False := by
    have hh := (Epilogue.loaderWalkEventRange (lower := 1901) warp (by decide)
      (by rw [hExit]; decide) hs hf (by intro bound; rfl) hw _ hm).1
    omega
  have advance {s u : TState} {e : Option Event} (hRange : 174 ≤ s.pc ∧ s.pc < 1901)
      (hShape : RingShape s) (hRoots : Holds s.regs frame)
      (hw : WStep kernel Assumptions.all l g s e u) :
      (174 ≤ u.pc ∧ u.pc ≤ 1901) ∧ RingShape u ∧ Holds u.regs frame := by
    obtain ⟨hU, hHi, hr, hregs⟩ := pipelineCutStep (F := frame) (branch := u.pc)
      (by decide) (by decide) hRange (fullBiasLoaderBranches u.pc) hw hShape hRoots
    exact ⟨⟨hU, hHi.resolve_right (Nat.lt_irrefl _)⟩, hr, hregs⟩
  induction hWalk generalizing j pre with
  | stop => simp at he
  | @tau s u es vs ht hw ih =>
    by_cases hExit : s.pc = 1901
    · exact (leave (.tau ht hw) hExit hShape hRoots (List.mem_of_getElem? he)).elim
    have hRange : 174 ≤ s.pc ∧ s.pc < 1901 := ⟨hPc.1, by omega⟩
    let hLocal : WStep kernel Assumptions.all l g s none u := .inl ⟨rfl, ht⟩
    obtain ⟨hu, hs, hr⟩ := advance hRange hShape hRoots hLocal
    exact ih hu hs hr (by simpa using step hRange.1 hRange.2 hShape hRoots hInv hLocal) he
  | @ev s u actual es vs ht hw ih =>
    by_cases hExit : s.pc = 1901
    · exact (leave (.ev ht hw) hExit hShape hRoots (List.mem_of_getElem? he)).elim
    cases j with
    | zero =>
      obtain rfl := Option.some.inj he
      exact ⟨s, some u, (estep_source_pc ht).symm, by simpa using hInv, ht⟩
    | succ j =>
      have hRange : 174 ≤ s.pc ∧ s.pc < 1901 := ⟨hPc.1, by omega⟩
      let hLocal : WStep kernel Assumptions.all l g s (some actual) u := .inr ⟨_, rfl, ht⟩
      obtain ⟨hu, hs, hr⟩ := advance hRange hShape hRoots hLocal
      have hNext := step hRange.1 hRange.2 hShape hRoots hInv hLocal
      obtain ⟨t, o, hAt, hi, hE⟩ := ih hu hs hr hNext he
      exact ⟨t, o, hAt, by simpa [List.take_succ_cons, List.append_assoc] using hi, hE⟩
  | last ht =>
    have hj : j = 0 := by
      have hi := (List.getElem?_eq_some_iff.mp he).1
      simpa using hi
    subst j
    obtain rfl := Option.some.inj he
    exact ⟨_, none, (estep_source_pc ht).symm, by simpa using hInv, ht⟩

private theorem actualLoaderReplay {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {mark : Event} (he : X.get (g,j) = some mark)
    (hLo : 173 < mark.pc) (hHi : mark.pc < 1901) (hWarp : 14 ≤ Prologue.warpIndex l g)
    {P : List Event → TState → Prop}
    (start : ∀ (w : Fin 2) t, At t 174 [(2535, b32 l.sharedBase), (1062, b32 (14 + w.val))] →
      P [] t)
    (step : ∀ (w : Fin 2) {a b : TState} {ev : Option Event} {past : List Event},
      174 ≤ a.pc → a.pc < 1901 → RingShape a →
      Holds a.regs [(2535, b32 l.sharedBase), (1062, b32 (14 + w.val))] →
      P past a → WStep kernel Assumptions.all l g a ev b → P (past ++ ev.toList) b) :
    ∃ t o, t.pc = mark.pc ∧ P (((X.tr g).drop 5).take (j - 5)) t ∧
      EStep kernel Assumptions.all l g t mark o := by
  let warp : Fin 2 := ⟨Prologue.warpIndex l g - 14, by have := Prologue.warpIndex_lt hp g; omega⟩
  have hEq : 14 + warp.val = Prologue.warpIndex l g := Nat.add_sub_of_le hWarp
  obtain ⟨s, _, hs, hAt, hr⟩ := Prologue.nonzeroCommonPrefixOfLateEvent hp hX
    (g := g) (index := j) (event_thread_lt hX he) (by omega) he hLo
  have hAtR : At s 174 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] :=
    hAt.mono ⟨hAt.2.2.2.2.2.1, hEq.symm ▸ hAt.2.2.2.2.1, trivial⟩
  obtain ⟨vs, hw⟩ := Mma.walkFromRun hr
  have hGet : ((X.tr g).drop 5)[j-5]? = some mark := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hs]
    exact he
  obtain ⟨t, o, hPc, hI, hE⟩ := loaderReplayEvent warp hw (by rw [hAt.1]; decide)
    (ringShapeOfAt hAt) hAtR.2.2.2.2 (start warp s hAtR) (step warp) hGet hHi
  exact ⟨t, o, hPc, by simpa using hI, hE⟩

private theorem primingPollCode (stage : Fin 2) :
    ∃ dst base, kernel.code[biasPrimingPoll stage]? =
      some ⟨none, .mbarWait dst base 0 (.reg (biasPrimingParityReg stage)) true .cta⟩ := by
  fin_cases stage
  · exact ⟨_, _, Flow.code_704⟩
  · exact ⟨_, _, Flow.code_756⟩

/-- Every actual priming acquire uses parity one, including every failed attempt. -/
theorem biasPrimingPollParity {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j q : Nat} {target : Loc} {went acquire : Bool} {scope : MbarScope} (stage : Fin 2)
    (hWarp : 14 ≤ Prologue.warpIndex l g)
    (he : X.get (g,j) = some ⟨biasPrimingPoll stage, .wait target q went acquire scope⟩) :
    q = 1 := by
  have hBounds : 173 < biasPrimingPoll stage ∧ biasPrimingPoll stage < 1901 := by
    fin_cases stage <;> decide
  obtain ⟨s, o, hs, hPhase, hStep⟩ := actualLoaderReplay hp hX he hBounds.1 hBounds.2 hWarp
    (P := fun _ => PrimingPhaseFrame stage)
    (fun _ t hAt => by
      intro hActive
      rw [hAt.1] at hActive
      exact ((show ¬ primingPhaseLive stage 174 from by fin_cases stage <;> decide) hActive).elim)
    (by
      intro warp t u ev past hlo hhi hShape _ hFrame hStep
      exact primingPhaseStep stage hlo hhi hShape hFrame hStep)
  change s.pc = biasPrimingPoll stage at hs
  have hReg := hPhase ⟨hs.symm.le, by omega⟩
  obtain ⟨dst, base, hc⟩ := primingPollCode stage
  obtain ⟨tmpl, hOut, hf⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hCode, rfl⟩
  · cases congrArg Event.kind hf.1
  rw [hs, hc] at hCode
  obtain rfl := Option.some.inj hCode
  have hBits := readBits_b32 (L := l) (g := g) hReg (by decide)
  have hWide : (Assumptions.all.any (·.clusterScopeMbar s.pc)) = false := rfl
  simp only [eventTmpl, tmaTmpl, hWide, widenMbarScope, Bool.false_eq_true, ↓reduceIte,
    bind, Except.bind, pure, Except.pure, hBits] at hf
  cases hAddr : mbarLoc l g s base 0 with
  | error f => simp [hAddr, ofExec, Fires] at hf
  | ok loc =>
    simp only [hAddr, ofExec, Fires] at hf
    obtain ⟨_, hFire, _⟩ := hf
    exact (Kind.wait.inj (congrArg Event.kind hFire)).2.1

private inductive BiasParityMode where
  | done
  | initial (expected : Bool)
  | live (pending : Bool)
  | tested (pred : Nat) (priming : Bool)
  deriving DecidableEq

private def primingWait (stage : Fin 2) : DrainWaitSite :=
  if stage = 0 then ⟨704, 9608, 1897, 1898⟩ else ⟨756, 9610, 1917, 1918⟩

private def recurringWait (stage : Fin 2) : DrainWaitSite :=
  if stage = 0 then ⟨1146, 9613, 2039, 7177⟩ else ⟨1175, 9614, 2052, 7178⟩

private def tailWait : DrainWaitSite := ⟨1361, 9616, 2121, 7177⟩

private def paritySeed (stage : Fin 2) : Nat := if stage = 0 then 773 else 916

private def parityToggle (stage : Fin 2) : Nat := if stage = 0 then 1202 else 1201

private def parityEnd (stage : Fin 2) : Nat := if stage = 0 then 1363 else 1352

private def parityMode (stage : Fin 2) (pc : Nat) : BiasParityMode :=
  let priming := primingWait stage
  let recurring := recurringWait stage
  if pc = priming.pc + 1 then .tested priming.result true
  else if pc ≤ priming.pc + 2 then .initial true
  else if pc ≤ paritySeed stage then .initial false
  else if parityEnd stage < pc then .done
  else if pc = recurring.pc + 1 then .tested recurring.result false
  else if stage = 0 ∧ pc = tailWait.pc + 1 then .tested tailWait.result false
  else .live (decide (recurring.pc + 3 ≤ pc ∧ pc ≤ parityToggle stage))

private def biasParitySites (stage : Fin 2) : List DrainWaitSite :=
  primingWait stage :: recurringWait stage :: (if stage = 0 then [tailWait] else [])

private def parityEvent (stage : Fin 2) (e : Event) : Bool :=
  match e.kind with
  | .wait _ _ true _ _ => (biasParitySites stage).any (fun site => site.pc == e.pc)
  | _ => false

private def parityMove (stage : Fin 2) : Op :=
  .move ⟨.scalar, .int .b 32, [some (recurringWait stage).phase],
    [if stage = 0 then .imm 0 else .reg 7177]⟩

private def parityFlip (stage : Fin 2) : Op :=
  .int ⟨.xor, .int .b 32, false, [some (recurringWait stage).phase],
    [.reg (recurringWait stage).phase, .imm 1]⟩

private def parityTracked (stage : Fin 2) : List Nat :=
  (recurringWait stage).phase :: (biasParitySites stage).map (·.result)

private def parityEdge (stage : Fin 2) (src dst : Nat) : Bool :=
  decide (parityMode stage src = parityMode stage dst ∨ parityMode stage dst = .done)

private def parityRegular (stage : Fin 2) (pc : Nat) (ins : Instr) : Bool :=
  if pc = 676 || pc = paritySeed stage || pc = parityToggle stage ||
      (biasParitySites stage).any (fun site => pc = site.pc || pc = site.pc + 1) then true
  else
    (match parityMode stage pc with
      | .done | .initial _ => true
      | _ => (parityTracked stage).all (fun reg => !(loaderRingWrites ins.op).contains reg)) &&
      match ins.op with
      | .bra dst _ => parityEdge stage pc dst &&
          (ins.guard.isNone || parityEdge stage pc (pc + 1))
      | .brx .. => false
      | _ => parityEdge stage pc (pc + 1)

private theorem parityRegularAt (stage : Fin 2) {pc : Nat} {ins : Instr}
    (hLo : 174 ≤ pc) (hHi : pc < 1901) (hc : kernel.code[pc]? = some ins) :
    parityRegular stage pc ins = true := by
  let code := ((kernel.code.drop 174).take (1901 - 174)).zipIdx 174
  have hAll : code.all (fun (ins, pc) => parityRegular stage pc ins) = true := by
    fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (ins,pc)
  apply List.mem_of_getElem? (i := pc - 174)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private def CursorHolds (stage : Fin 2) (s : TState) (q : Bool) : BiasParityMode → Prop
  | .done => True
  | .initial expected => q = expected
  | .live pending => s.regs (recurringWait stage).phase = some (b32 (xor q pending).toNat)
  | .tested pred priming => ∃ ok : Bool, s.regs pred = some (.pred ok) ∧
      if priming then q = !ok
      else s.regs (recurringWait stage).phase = some (b32 (xor q ok).toNat)

private def BiasParityFrame (stage : Fin 2) (past : List Event) (s : TState) : Prop :=
  CursorHolds stage s ((past.countP (parityEvent stage) + 1) % 2 == 1)
    (parityMode stage s.pc)


private def CursorRegular (stage : Fin 2) (pc : Nat) : Prop :=
  pc ≠ 676 ∧ pc ≠ paritySeed stage ∧ pc ≠ parityToggle stage ∧
    ∀ site ∈ biasParitySites stage, pc ≠ site.pc ∧ pc ≠ site.pc + 1

private def cursorCheckWrites (stage : Fin 2) (pc : Nat) (op : Op) : Bool :=
  match parityMode stage pc with
  | .done | .initial _ => true
  | _ => (parityTracked stage).all (fun reg => !(loaderRingWrites op).contains reg)

private theorem cursorCheckCode (stage : Fin 2) {pc : Nat} {ins : Instr}
    (hLo : 174 ≤ pc) (hHi : pc < 1901) (hCode : kernel.code[pc]? = some ins)
    (hRegular : CursorRegular stage pc) :
    cursorCheckWrites stage pc ins.op = true ∧
      (match ins.op with
        | .bra dst _ => parityEdge stage pc dst && (ins.guard.isNone ||
            parityEdge stage pc (pc + 1))
        | .brx .. => false
        | _ => parityEdge stage pc (pc + 1)) = true := by
  obtain ⟨hGate, hSeed, hToggle, hSites⟩ := hRegular
  have hAny : ((biasParitySites stage).any (fun s => pc = s.pc || pc = s.pc + 1)) = false := by
    rw [List.any_eq_false]
    intro site hs
    obtain ⟨hNe, hNe'⟩ := hSites site hs
    simp [hNe, hNe']
  have hChecked := parityRegularAt stage hLo hHi hCode
  unfold parityRegular at hChecked
  simp only [hGate, hSeed, hToggle, decide_false, Bool.false_or, hAny,
    Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hChecked
  exact hChecked

private theorem cursorRegularNext {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (stage : Fin 2) (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901) (hShape : RingShape s)
    (hRegular : CursorRegular stage s.pc) (hStep : WStep kernel Assumptions.all l g s ev u) :
    parityEdge stage s.pc u.pc = true := by
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · have hCore : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore hLo (by omega)]
    obtain ⟨ins, hc⟩ := tau_core_has_code hCore
    have hCheck := (cursorCheckCode stage hLo hHi hc hRegular).2
    rcases tau_core_frame hc hCore with rfl | hf
    · have hFall : parityEdge stage s.pc (s.pc + 1) = true := by
        cases ho : ins.op <;> simp only [ho, Bool.and_eq_true] at hCheck
        case bra dst aligned =>
          obtain ⟨hBranch, hOr⟩ := hCheck
          cases hg : ins.guard
          · unfold Tau out at hCore
            cases hFault : s.fault
            · simp [hFault, hc, hg, ho, guardHolds, Op.isLocal,
                execLocalA, execLocalRule, execLocal, Op.rule, execBranch, pure,
                Except.pure, skip] at hCore
              have hDst : dst = s.pc + 1 := hCore.1
              exact hDst ▸ hBranch
            · simp [hFault] at hCore
          · simpa [hg] using hOr
        case brx => cases hCheck
        all_goals exact hCheck
      exact hFall
    · have hAt := hf.pc
      cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hAt
      all_goals simp only [ho, Bool.and_eq_true] at hCheck
      case bra dst aligned => exact hAt ▸ hCheck.1
      case brx => cases hCheck
      all_goals exact hAt ▸ hCheck
  · obtain ⟨ins, hc, hn, _⟩ := estep_event_source he
    have hCheck := (cursorCheckCode stage hLo hHi hc hRegular).2
    obtain ⟨_, hPc | ⟨hPc, _⟩⟩ := loaderEventProgress hLo (by omega) hShape.1 he
    · rw [hPc]
      cases ho : ins.op <;> simp only [ho, Op.isLocal] at hn
      case bra => cases hn
      case brx => cases hn
      all_goals simpa only [ho] using hCheck
    · rw [hPc]
      simp [parityEdge]

private theorem cursorRegularRegs {l : Launch} {g r : Nat} {s u : TState} {ev : Option Event}
    (stage : Fin 2) (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (hRegular : CursorRegular stage s.pc) (hStep : WStep kernel Assumptions.all l g s ev u)
    (hMode : ∀ b, parityMode stage s.pc ≠ .initial b) (hDone : parityMode stage s.pc ≠ .done)
    (hr : r ∈ parityTracked stage) : u.regs r = s.regs r := by
  apply loaderPipelineStepRegs hLo hHi ?_ hStep
  intro ins hc
  have h := (cursorCheckCode stage hLo hHi hc hRegular).1
  unfold cursorCheckWrites at h
  cases ho : parityMode stage s.pc
  · exact (hDone ho).elim
  · exact (hMode _ ho).elim
  all_goals
    rw [ho] at h
    simpa using List.all_eq_true.mp h r hr

section
variable {l : Launch}

private theorem cursorRegularCount {g : Nat} {s u : TState} {ev : Option Event} (stage : Fin 2)
    (hRegular : CursorRegular stage s.pc) (hStep : WStep kernel Assumptions.all l g s ev u) :
    ev.toList.countP (parityEvent stage) = 0 := by
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · rfl
  · have hNoSite : ((biasParitySites stage).any (fun site => site.pc == e.pc)) = false := by
      rw [List.any_eq_false]
      intro site hs
      simp [estep_source_pc he, Ne.symm ((hRegular.2.2.2 site hs).1)]
    cases ho : e.kind <;> simp [parityEvent, ho, hNoSite]
    rename_i addr phase ok acq scope
    cases ok <;> simp_all

private theorem biasLocalOutcome {g : Nat} {s u v : TState} {ev : Option Event} {ins : Instr}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901) (hc : kernel.code[s.pc]? = some ins)
    (hLocal : ins.op.isLocal = true) (hNext : ∀ _f : s.fault = none, out kernel [] l g s = .tau v)
    (hStep : WStep kernel Assumptions.all l g s ev u) : ev = none ∧ u = v := by
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · have hCore : out kernel [] l g s = .tau u := by
      unfold Tau at ht
      rwa [← loaderOutCore hLo (by omega)]
    cases hf : s.fault
    · exact ⟨rfl, Out.tau.inj (hCore.symm.trans (hNext hf))⟩
    · simp [out, hf] at hCore
  · obtain ⟨other, hCode, hOp, _⟩ := estep_event_source he
    obtain rfl := Option.some.inj (hc.symm.trans hCode)
    simp [hLocal] at hOp

private theorem biasLocalWrite {g : Nat} {s u v : TState} {ev : Option Event} {op : Op}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901) (hc : kernel.code[s.pc]? = some ⟨none, op⟩)
    (hLocal : op.isLocal = true) (hExec : execLocal l g s op = .ok v)
    (hStep : WStep kernel Assumptions.all l g s ev u) : ev = none ∧ u = v :=
  biasLocalOutcome hLo hHi hc hLocal (fun hf => by
    simp [out, hf, hc, guardHolds, hLocal, execLocalA_nil, hExec, pure, Except.pure]) hStep

private theorem biasBranchOutcome {g : Nat} {s u : TState} {ev : Option Event} {result dest : Nat}
    {uni ok : Bool} (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (hc : kernel.code[s.pc]? = some ⟨some (result, false), .bra dest uni⟩)
    (hr : s.regs result = some (.pred ok)) (hStep : WStep kernel Assumptions.all l g s ev u) :
    ev = none ∧ u = (if ok then {s with pc := dest} else skip s) := by
  apply biasLocalOutcome hLo hHi hc (by rfl) ?_ hStep
  intro hf
  cases ok <;> simp [out, hf, hc, guardHolds, readReg, hr, Op.isLocal, execLocalA, execLocalRule,
    execLocal, Op.rule, execBranch, bind, Except.bind, pure, Except.pure]

private theorem paritySeedShape (stage : Fin 2) :
    parityMode stage (paritySeed stage) = .initial false ∧
    parityMode stage (paritySeed stage + 1) = .live false ∧
    kernel.code[paritySeed stage]? = some ⟨none, parityMove stage⟩ := by
  fin_cases stage
  · exact ⟨rfl, rfl, Flow.code_773⟩
  · exact ⟨rfl, rfl, Flow.code_916⟩

private theorem parityToggleShape (stage : Fin 2) :
    parityMode stage (parityToggle stage) = .live true ∧
    parityMode stage (parityToggle stage + 1) = .live false ∧
    kernel.code[parityToggle stage]? = some ⟨none, parityFlip stage⟩ := by
  fin_cases stage
  · exact ⟨rfl, rfl, Flow.code_1202⟩
  · exact ⟨rfl, rfl, Flow.code_1201⟩

private theorem biasCursorCode (stage : Fin 2) {site : DrainWaitSite}
    (hs : site ∈ biasParitySites stage) :
    let prime := site.pc == (primingWait stage).pc
    LoaderWaitCode site ∧
    parityMode stage site.pc = (if prime then .initial true else .live false) ∧
    parityMode stage (site.pc + 1) = .tested site.result prime ∧
    parityMode stage (site.pc + 2) = (if prime then .initial true else .live false) ∧
    parityMode stage (site.pc + 3) =
      (if prime then .initial false else if site.pc = tailWait.pc then .done else .live true) ∧
    (if prime then True else site.phase = (recurringWait stage).phase) ∧
    site.result ≠ (recurringWait stage).phase := by
  fin_cases stage
  · change site ∈ [⟨704, 9608, 1897, 1898⟩, ⟨1146, 9613, 2039, 7177⟩, tailWait] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨⟨Flow.code_704, Flow.code_705, Flow.code_706⟩, rfl, rfl, rfl, rfl, trivial, by decide⟩
    · exact ⟨⟨Flow.code_1146, Flow.code_1147, Flow.code_1148⟩, rfl, rfl, rfl, rfl, rfl, by decide⟩
    · exact ⟨⟨Flow.code_1361, Flow.code_1362, Flow.code_1363⟩, rfl, rfl, rfl, rfl, rfl, by decide⟩
  · change site ∈ [⟨756, 9610, 1917, 1918⟩, ⟨1175, 9614, 2052, 7178⟩] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨⟨Flow.code_756, Flow.code_757, Flow.code_758⟩, rfl, rfl, rfl, rfl, trivial, by decide⟩
    · exact ⟨⟨Flow.code_1175, Flow.code_1176, Flow.code_1177⟩, rfl, rfl, rfl, rfl, rfl, by decide⟩

private theorem cursorParityAdd (stage : Fin 2) (past extra : List Event) :
    (((past ++ extra).countP (parityEvent stage) + 1) % 2 == 1) =
      xor (((past.countP (parityEvent stage) + 1) % 2) == 1)
        (extra.countP (parityEvent stage) % 2 == 1) := by
  simp only [List.countP_append]
  generalize past.countP (parityEvent stage) = n
  generalize extra.countP (parityEvent stage) = k
  apply Bool.eq_iff_iff.mpr
  have hn : (n + 1) % 2 = 0 ∨ (n + 1) % 2 = 1 := by omega
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hn with hn | hn <;> rcases hk with hk | hk
  all_goals simp_all
  all_goals omega

private theorem cursorCountWait (stage : Fin 2) {site : DrainWaitSite}
    (hs : site ∈ biasParitySites stage) {target : Loc} {phase : Nat} {ok acq : Bool}
    {scope : MbarScope} :
    [(⟨site.pc, .wait target phase ok acq scope⟩ : Event)].countP (parityEvent stage) =
      ok.toNat := by
  have hm : ((biasParitySites stage).any (fun s => s.pc == site.pc)) = true :=
    List.any_eq_true.mpr ⟨site, hs, by simp⟩
  cases ok <;> simp [parityEvent, hm]

private theorem cursorPollStep {g : Nat} {s u : TState} {ev : Option Event} {past : List Event}
    (stage : Fin 2) {site : DrainWaitSite} (hs : site ∈ biasParitySites stage)
    (hPc : s.pc = site.pc) (hFrame : BiasParityFrame stage past s)
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    BiasParityFrame stage (past ++ ev.toList) u := by
  let prime := site.pc == (primingWait stage).pc
  obtain ⟨hc, hMode, hNext, _, _, _, hNe⟩ := biasCursorCode stage hs
  change parityMode stage site.pc = (if prime then .initial true else .live false) at hMode
  change parityMode stage (site.pc + 1) = .tested site.result prime at hNext
  obtain ⟨addr, p, ok, sc, rfl, rfl⟩ := wstep_poll hStep (hPc.symm ▸ hc.1)
  have hPC' : (next (setReg s site.result (.pred ok))).pc = site.pc + 1 := by
    simp [next, setReg, hPc]
  let q := ((past.countP (parityEvent stage) + 1) % 2 == 1)
  unfold BiasParityFrame at hFrame ⊢
  rw [hPc, hMode] at hFrame
  rw [hPC', hNext, cursorParityAdd]
  simp only [Option.toList_some, hPc, cursorCountWait stage hs]
  have hCount : (ok.toNat % 2 == 1) = ok := by cases ok <;> rfl
  rw [hCount]
  change CursorHolds stage _ (xor q ok) (.tested site.result prime)
  refine ⟨ok, Function.update_self _ _ _, ?_⟩
  cases hPrime : prime
  · simp only [hPrime, Bool.false_eq_true, ↓reduceIte] at hFrame ⊢
    change s.regs (recurringWait stage).phase = some (b32 (xor q false).toNat) at hFrame
    have hKeep : (next (setReg s site.result (.pred ok))).regs (recurringWait stage).phase =
        s.regs (recurringWait stage).phase := Function.update_of_ne hNe.symm _ _
    rw [hKeep, hFrame]
    cases q <;> cases ok <;> rfl
  · simp only [hPrime, ↓reduceIte] at hFrame ⊢
    change q = true at hFrame
    rw [hFrame]
    cases ok <;> rfl

private theorem cursorPollBranch {g : Nat} {s u : TState} {ev : Option Event} {past : List Event}
    (stage : Fin 2) {site : DrainWaitSite} (hs : site ∈ biasParitySites stage)
    (hPc : s.pc = site.pc + 1) (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (hFrame : BiasParityFrame stage past s) (hStep : WStep kernel Assumptions.all l g s ev u) :
    BiasParityFrame stage (past ++ ev.toList) u := by
  let prime := site.pc == (primingWait stage).pc
  obtain ⟨hc, _, hMode, hBad, hOK, _, _⟩ := biasCursorCode stage hs
  change parityMode stage (site.pc + 1) = .tested site.result prime at hMode
  change parityMode stage (site.pc + 2) = (if prime then .initial true else .live false) at hBad
  change parityMode stage (site.pc + 3) = (if prime then .initial false
    else if site.pc = tailWait.pc then .done else .live true) at hOK
  unfold BiasParityFrame at hFrame ⊢
  rw [hPc, hMode] at hFrame
  obtain ⟨ok, hReg, hFacts⟩ := hFrame
  obtain ⟨rfl, rfl⟩ := biasBranchOutcome hLo hHi (hPc.symm ▸ hc.2.1) hReg hStep
  simp only [Option.toList_none, List.append_nil]
  cases ok
  · have hNext : (skip s).pc = site.pc + 2 := by simp [skip, hPc]
    change CursorHolds stage (skip s) _ (parityMode stage (skip s).pc)
    rw [hNext, hBad]
    cases hPrime : prime <;> simpa [hPrime, CursorHolds, skip] using hFacts
  · change CursorHolds stage {s with pc := site.pc + 3} _ (parityMode stage (site.pc + 3))
    rw [hOK]
    cases hPrime : prime
    · by_cases hTail : site.pc = tailWait.pc
      · simp [hTail, CursorHolds]
      · simpa [hPrime, hTail, CursorHolds] using hFacts
    · simpa [hPrime, CursorHolds] using hFacts

private theorem cursorRegularStep {g : Nat} {s u : TState} {ev : Option Event} {past : List Event}
    (stage : Fin 2) (hRegular : CursorRegular stage s.pc) (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (hShape : RingShape s) (hFrame : BiasParityFrame stage past s)
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    BiasParityFrame stage (past ++ ev.toList) u := by
  have hEdge := of_decide_eq_true (cursorRegularNext stage hLo hHi hShape hRegular hStep)
  change parityMode stage s.pc = parityMode stage u.pc ∨ parityMode stage u.pc = .done at hEdge
  unfold BiasParityFrame at hFrame ⊢
  rw [List.countP_append, cursorRegularCount stage hRegular hStep, Nat.add_zero]
  rcases hEdge with hMode | hDone
  · rw [← hMode]
    cases hSrc : parityMode stage s.pc <;> rw [hSrc] at hFrame
    · trivial
    · exact hFrame
    · unfold CursorHolds at hFrame ⊢
      rw [cursorRegularRegs stage hLo hHi hRegular hStep (by simp [hSrc]) (by simp [hSrc])]
      · exact hFrame
      · simp [parityTracked]
    · unfold CursorHolds at hFrame ⊢
      obtain ⟨ok, hR, hFacts⟩ := hFrame
      rename_i pred prime
      exfalso
      have hPriming := (hRegular.2.2.2 (primingWait stage)
        (by simp [biasParitySites])).2
      have hRecurring := (hRegular.2.2.2 (recurringWait stage)
        (by simp [biasParitySites])).2
      have hTail : ¬ (stage = 0 ∧ s.pc = tailWait.pc + 1) := by
        intro h
        exact (hRegular.2.2.2 tailWait (by simp [biasParitySites, h.1])).2 h.2
      simp only [parityMode, hPriming, hRecurring, hTail, ↓reduceIte] at hSrc
      split at hSrc
      · cases hSrc
      · split at hSrc
        · cases hSrc
        · split at hSrc <;> cases hSrc
  · rw [hDone]
    trivial
end

private def cursorPrepBounds (which : Fin 2) : Nat × Nat :=
  if which = 0 then (539, 676) else (774, 916)

private def cursorPrepReg (which : Fin 2) : Nat := if which = 0 then 123 else 7177

private def cursorPrepLive (which : Fin 2) (pc : Nat) : Prop :=
  (cursorPrepBounds which).1 ≤ pc ∧ pc ≤ (cursorPrepBounds which).2

private instance (which : Fin 2) (pc : Nat) : Decidable (cursorPrepLive which pc) :=
  inferInstanceAs (Decidable (_ ≤ pc ∧ pc ≤ _))

private def cursorPrepCheck (which : Fin 2) (pc : Nat) (op : Op) : Bool :=
  (!decide (cursorPrepLive which pc) || !(loaderRingWrites op).contains (cursorPrepReg which)) &&
    match op with
    | .bra dst _ => decide (cursorPrepLive which dst → cursorPrepLive which pc ∨ pc = 676)
    | .brx .. => false
    | _ => true

private theorem cursorPrepCheckAt (which : Fin 2) {pc : Nat} {ins : Instr}
    (hLo : 174 ≤ pc) (hHi : pc < 1901) (hc : kernel.code[pc]? = some ins) :
    cursorPrepCheck which pc ins.op = true := by
  let code := ((kernel.code.drop 174).take (1901 - 174)).zipIdx 174
  have hAll : code.all (fun (ins, pc) => cursorPrepCheck which pc ins.op) = true := by
    fin_cases which <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (ins,pc)
  apply List.mem_of_getElem? (i := pc - 174)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private def CursorPrep (which : Fin 2) (s : TState) : Prop :=
  cursorPrepLive which s.pc →
    s.regs (cursorPrepReg which) = some (if which = 0 then .pred false else b32 0)

section
variable {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}

private theorem cursorPrepStepNoGate (which : Fin 2) (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (hShape : RingShape s) (hWarp : s.regs 1062 = some (b32 14)) (hNoGate : s.pc ≠ 676)
    (hFrame : CursorPrep which s) (hStep : WStep kernel Assumptions.all l g s ev u)
    : CursorPrep which u := by
  intro hDst
  have hFrom (hu : u.pc = s.pc ∨ u.pc = s.pc + 1) :
      cursorPrepLive which s.pc ∨ s.pc = (cursorPrepBounds which).1 - 1 := by
    unfold cursorPrepLive at hDst ⊢
    omega
  have hSource : cursorPrepLive which s.pc ∨ s.pc = (cursorPrepBounds which).1 - 1 := by
    rcases hStep with ⟨rfl, ht⟩ | ⟨event, rfl, he⟩
    · have hCore : Tau kernel [] l g s u := by
        unfold Tau at ht ⊢
        rwa [← loaderOutCore hLo (by omega)]
      obtain ⟨ins, hc⟩ := tau_core_has_code hCore
      have hLaw := (Bool.and_eq_true_iff.mp (cursorPrepCheckAt which hLo hHi hc)).2
      rcases tau_core_frame hc hCore with rfl | hf
      · exact hFrom (.inr rfl)
      have hPc := hf.pc
      cases hOp : ins.op <;> simp only [hOp, nextPc, BrxTarget, or_false] at hPc
      case bra dst aligned =>
        change (match ins.op with
          | .bra dst _ => decide (cursorPrepLive which dst →
              cursorPrepLive which s.pc ∨ s.pc = 676)
          | .brx .. => false | _ => true) = true at hLaw
        rw [hOp] at hLaw
        exact .inl ((of_decide_eq_true hLaw (hPc ▸ hDst)).resolve_right hNoGate)
      case brx => simp [hOp] at hLaw
      all_goals exact hFrom (.inr hPc)
    · obtain ⟨_, hp | ⟨hp, _⟩⟩ := loaderEventProgress hLo (by omega) hShape.1 he
      · exact hFrom (.inr hp)
      · exact hFrom (.inl hp)
  rcases hSource with hLive | hWrite
  · rw [loaderPipelineStepRegs hLo hHi (fun ins hc => by
      have hd := (Bool.and_eq_true_iff.mp (cursorPrepCheckAt which hLo hHi hc)).1
      simpa [hLive] using hd) hStep]
    exact hFrame hLive
  · fin_cases which
    · change s.pc = 538 at hWrite
      change u.regs 123 = some (.pred false)
      let ins : IntInstr :=
        ⟨.setp .ne none, .int .b 32, false, [some 123], [.reg 1062, .imm 14]⟩
      have hExec : execLocal l g s (.int ins) = .ok (next (setReg s 123 (.pred false))) := by
        rw [execLocal_int (i := ins) rfl]
        simp [ins, execInt, compare, DType.width, readBits, readReg, hWarp, b32,
          bind, Except.bind, pure, Except.pure]
        rfl
      obtain ⟨rfl, rfl⟩ := biasLocalWrite hLo hHi (hWrite.symm ▸ Flow.code_538) rfl hExec hStep
      simp [next, setReg]
    · change s.pc = 773 at hWrite
      change u.regs 7177 = some (b32 0)
      let op := parityMove 0
      have hExec : execLocal l g s op = .ok (next (setReg s 7177 (b32 0))) := by
        change execLocal l g s (parityMove 0) = _
        rw [show parityMove 0 = .move ⟨.scalar, .int .b 32, [some 7177], [.imm 0]⟩ from rfl]
        rw [execLocal_move rfl]
        simp [execMove, readValue, readBits, DType.width, Value.bytes, b32,
          bind, Except.bind, pure, Except.pure]
        rfl
      obtain ⟨rfl, rfl⟩ := biasLocalWrite hLo hHi (hWrite.symm ▸ Flow.code_773) rfl hExec hStep
      simp [next, setReg]

private theorem actualBiasGateFall (hPc : s.pc = 676) (hPrep : CursorPrep 0 s)
    (hStep : WStep kernel Assumptions.all l g s ev u) : ev = none ∧ u = skip s := by
  have hRole := hPrep (show cursorPrepLive 0 s.pc by rw [hPc]; decide)
  exact biasBranchOutcome (by omega) (by omega) (hPc.symm ▸ Flow.code_676) hRole hStep

private theorem cursorPrepStep (which : Fin 2) (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (hShape : RingShape s) (hWarp : s.regs 1062 = some (b32 14)) (hGate : CursorPrep 0 s)
    (hFrame : CursorPrep which s) (hStep : WStep kernel Assumptions.all l g s ev u)
    : CursorPrep which u := by
  by_cases hPc : s.pc = 676
  · obtain ⟨_, rfl⟩ := actualBiasGateFall hPc hGate hStep
    intro hLive
    have hNext : (skip s).pc = 677 := by simp [skip, hPc]
    rw [hNext] at hLive
    fin_cases which <;> exact (by decide : ¬ cursorPrepLive _ 677) hLive |>.elim
  · exact cursorPrepStepNoGate which hLo hHi hShape hWarp hPc hFrame hStep

private theorem cursorSeedStep {past : List Event} (stage : Fin 2) (hPc : s.pc = paritySeed stage)
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901) (hPrep : CursorPrep 1 s)
    (hFrame : BiasParityFrame stage past s) (hStep : WStep kernel Assumptions.all l g s ev u) :
    BiasParityFrame stage (past ++ ev.toList) u := by
  obtain ⟨hMode, hNext, hc⟩ := paritySeedShape stage
  have hExec : execLocal l g s (parityMove stage) =
      .ok (next (setReg s (recurringWait stage).phase (b32 0))) := by
    fin_cases stage
    · change execLocal l g s (parityMove 0) = _
      rw [show parityMove 0 = .move ⟨.scalar, .int .b 32, [some 7177], [.imm 0]⟩ from rfl]
      rw [execLocal_move rfl]
      simp [execMove, readValue, readBits, DType.width, Value.bytes, b32,
        bind, Except.bind, pure, Except.pure]
      rfl
    · have hPrev : s.regs 7177 = some (b32 0) := hPrep (by rw [hPc]; decide)
      change execLocal l g s (parityMove 1) = _
      rw [show parityMove 1 = .move ⟨.scalar, .int .b 32, [some 7178], [.reg 7177]⟩ from rfl]
      rw [execLocal_move rfl]
      simp [execMove, readValue, readReg, hPrev, DType.width, Value.bytes, b32,
        bind, Except.bind, pure, Except.pure]
      rfl
  have hLocal : (parityMove stage).isLocal = true := by fin_cases stage <;> rfl
  obtain ⟨rfl, rfl⟩ := biasLocalWrite hLo hHi (hPc.symm ▸ hc) hLocal hExec hStep
  unfold BiasParityFrame at *
  rw [hPc, hMode] at hFrame
  have hp : (next (setReg s (recurringWait stage).phase (b32 0))).pc =
      paritySeed stage + 1 := by simp [next, setReg, hPc]
  rw [hp, hNext]
  simp only [Option.toList_none, List.append_nil]
  change ((past.countP (parityEvent stage) + 1) % 2 == 1) = false at hFrame
  rw [hFrame]
  exact Function.update_self _ _ _

private theorem cursorToggleStep {past : List Event} (stage : Fin 2)
    (hPc : s.pc = parityToggle stage) (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (hFrame : BiasParityFrame stage past s) (hStep : WStep kernel Assumptions.all l g s ev u) :
    BiasParityFrame stage (past ++ ev.toList) u := by
  obtain ⟨hMode, hNext, hc⟩ := parityToggleShape stage
  let q := ((past.countP (parityEvent stage) + 1) % 2 == 1)
  unfold BiasParityFrame at hFrame
  rw [hPc, hMode] at hFrame
  change s.regs (recurringWait stage).phase = some (b32 (xor q true).toNat) at hFrame
  have hExec : execLocal l g s (parityFlip stage) =
      .ok (next (setReg s (recurringWait stage).phase (b32 q.toNat))) := by
    let ins : IntInstr := ⟨.xor, .int .b 32, false, [some (recurringWait stage).phase],
      [.reg (recurringWait stage).phase, .imm 1]⟩
    change execLocal l g s (.int ins) = _
    rw [execLocal_int (i := ins) rfl]
    cases hq : q
    all_goals
      rw [hq] at hFrame
      simp [ins, execInt, DType.width, readBits, readReg, hFrame, b32, bind,
        Except.bind, pure, Except.pure]
      try rfl
  have hLocal : (parityFlip stage).isLocal = true := rfl
  obtain ⟨rfl, rfl⟩ := biasLocalWrite hLo hHi (hPc.symm ▸ hc) hLocal hExec hStep
  unfold BiasParityFrame
  have hp : (next (setReg s (recurringWait stage).phase (b32 q.toNat))).pc =
      parityToggle stage + 1 := by simp [next, setReg, hPc]
  rw [hp, hNext]
  simp only [Option.toList_none, List.append_nil]
  change _ = some (b32 (xor q false).toNat)
  rw [Bool.xor_false]
  exact Function.update_self _ _ _

private theorem cursorStep {past : List Event} (stage : Fin 2) (hLo : 174 ≤ s.pc)
    (hHi : s.pc < 1901) (hShape : RingShape s) (hPrep : CursorPrep 0 s ∧ CursorPrep 1 s)
    (hFrame : BiasParityFrame stage past s) (hStep : WStep kernel Assumptions.all l g s ev u) :
    BiasParityFrame stage (past ++ ev.toList) u := by
  by_cases hGate : s.pc = 676
  · obtain ⟨rfl, rfl⟩ := actualBiasGateFall hGate hPrep.1 hStep
    have hNext : (skip s).pc = 677 := by simp [skip, hGate]
    unfold BiasParityFrame at hFrame ⊢
    rw [hGate] at hFrame
    rw [hNext]
    simp only [Option.toList_none, List.append_nil]
    fin_cases stage <;> exact hFrame
  by_cases hSeed : s.pc = paritySeed stage
  · exact cursorSeedStep stage hSeed hLo hHi hPrep.2 hFrame hStep
  by_cases hFlip : s.pc = parityToggle stage
  · exact cursorToggleStep stage hFlip hLo hHi hFrame hStep
  by_cases hHit : ∃ site ∈ biasParitySites stage, s.pc = site.pc ∨ s.pc = site.pc + 1
  · obtain ⟨site, hs, hPc | hPc⟩ := hHit
    · exact cursorPollStep stage hs hPc hFrame hStep
    · exact cursorPollBranch stage hs hPc hLo hHi hFrame hStep
  · have hRegular : CursorRegular stage s.pc :=
      ⟨hGate, hSeed, hFlip, fun site hm =>
        ⟨fun h => hHit ⟨site, hm, .inl h⟩, fun h => hHit ⟨site, hm, .inr h⟩⟩⟩
    exact cursorRegularStep stage hRegular hLo hHi hShape hFrame hStep
end

private theorem paritySitesMap (stage : Fin 2) :
    (biasParitySites stage).map (·.pc) = biasEmptyWaitSites stage := by
  fin_cases stage <;> rfl

private theorem biasSitesBounds (stage : Fin 2) {pc : Nat} (h : pc ∈ biasEmptyWaitSites stage) :
    173 < pc ∧ pc < 1901 ∧ pc ∈ [517, 679, 704, 730, 756, 782, 1146, 1175, 1361, 1893] ∧
      fixedLoaderWaitOffset pc = 336 + 8 * stage.val := by
  fin_cases stage
  · change pc ∈ [704, 1146, 1361] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> decide
  · change pc ∈ [756, 1175] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> decide

private theorem biasCountExact {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g j : Nat} (hWarp : 14 ≤ Prologue.warpIndex l g) :
    (((X.tr g).drop 5).take (j - 5)).countP (parityEvent stage) =
      okPolls (biasEmptyObject l (g / l.block) stage) ((X.tr g).take j) := by
  let obj := biasEmptyObject l (g / l.block) stage
  have hSite (pc : Nat) :
      ((biasParitySites stage).any fun site => site.pc == pc) = true ↔
        pc ∈ biasEmptyWaitSites stage := by
    rw [← paritySitesMap]
    simp only [List.any_eq_true, beq_iff_eq, List.mem_map]
  have hEq {k : Nat} {e : Event} (he : X.get (g,k) = some e) :
      parityEvent stage e ↔ okPoll obj e := by
    obtain ⟨pc, kind⟩ := e
    cases kind <;> try rfl
    rename_i loc phase ok acq scope
    cases ok
    · rfl
    change ((biasParitySites stage).any fun site => site.pc == pc) = true ↔
      sourceWaitSuccess obj ⟨pc, .wait loc phase true acq scope⟩ = true
    rw [hSite]
    change (pc ∈ biasEmptyWaitSites stage) ↔ (loc == obj) = true
    rw [beq_iff_eq]
    constructor
    · intro hs
      obtain ⟨_, _, hOffset, hAddress⟩ := biasSitesBounds stage hs
      rw [loaderFixedWaitOffset hp hX he hOffset, hAddress]
      rfl
    · intro hLoc
      subst loc
      exact biasEmptyLoaderPollSite hp hX stage hWarp he
  rw [List.take_drop]
  have hEqCount (es : List Event) (hMem : ∀ e ∈ es, e ∈ X.tr g) :
      es.countP (parityEvent stage) = es.countP (okPoll obj) := by
    apply List.countP_congr
    intro e h
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (hMem e h)
    exact hEq hk
  have hPrefix : ∀ k, ((X.tr g).take k).countP (okPoll obj) =
      (((X.tr g).take k).drop 5).countP (okPoll obj) := by
    intro k
    conv_lhs =>
      rw [← List.take_append_drop 5 ((X.tr g).take k)]
    rw [List.countP_append]
    have hZero : (((X.tr g).take k).take 5).countP (okPoll obj) = 0 := by
      apply List.countP_eq_zero.mpr
      intro e hm h
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
      have hLe := (List.getElem?_eq_some_iff.mp hi).1
      simp only [List.length_take] at hLe
      have hBound : i < 5 := by omega
      have he : X.get (g,i) = some e := by
        rw [List.getElem?_take_of_lt hBound, List.getElem?_take_of_lt (by omega)] at hi
        exact hi
      have ht := (hEq he).mpr h
      obtain ⟨pc, kind⟩ := e
      cases kind <;> try cases ht
      rename_i loc phase ok acq scope
      cases ok
      · cases ht
      have hb := biasSitesBounds stage ((hSite pc).mp ht)
      obtain ⟨_, _, hN, _, _⟩ := Prologue.nonzeroCommonPrefixOfLateEvent hp hX
        (g := g) (index := i) (event_thread_lt hX he) (by omega) he hb.1
      omega
    rw [hZero, Nat.zero_add]
  have hSize (k : Nat) : (((X.tr g).take k).drop 5).countP (parityEvent stage) =
      (((X.tr g).take k).drop 5).countP (okPoll obj) :=
    hEqCount _ (fun e hm => List.mem_of_mem_take (List.mem_of_mem_drop hm))
  rcases Nat.le_total 5 j with hj | hj
  · rw [Nat.add_sub_of_le hj, hSize]
    exact (hPrefix j).symm
  · rw [Nat.sub_eq_zero_of_le hj, Nat.add_zero, hSize, ← hPrefix]
    change ((X.tr g).take 5).countP (okPoll obj) = ((X.tr g).take j).countP (okPoll obj)
    rw [hPrefix 5, hPrefix j]
    simp [List.drop_take, Nat.sub_eq_zero_of_le hj]

private theorem pollUsesBiasParity {l : Launch} {g pc : Nat} {t : TState}
    {o : Option TState} (site : DrainWaitSite) (hCode : LoaderWaitCode site)
    {target : Loc} {q : Nat} {went acq : Bool} {scope : MbarScope}
    (hb : Bool) (hPc : pc = site.pc) (ht : t.pc = pc)
    (hReg : t.regs site.phase = some (b32 hb.toNat))
    (he : EStep kernel Assumptions.all l g t ⟨pc, .wait target q went acq scope⟩ o) :
    q = hb.toNat := by
  obtain ⟨tmpl, hOut, hf⟩ := he
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases congrArg Event.kind hf.1
  rw [ht, hPc, hCode.1] at hc
  obtain rfl := Option.some.inj hc
  have hWide : (Assumptions.all.any (·.clusterScopeMbar t.pc)) = false := rfl
  have hBits := readBits_b32 (L := l) (g := g) hReg (by cases hb <;> decide)
  simp only [eventTmpl, tmaTmpl, hWide, widenMbarScope, Bool.false_eq_true, ↓reduceIte,
    bind, Except.bind, pure, Except.pure, hBits] at hf
  cases hAddr : mbarLoc l g t site.base 0 with
  | error f => simp [hAddr, ofExec, Fires] at hf
  | ok loc =>
    simp only [hAddr, ofExec, Fires] at hf
    obtain ⟨_, hFire, _⟩ := hf
    have hEq := (Kind.wait.inj (congrArg Event.kind hFire)).2.1
    cases hb <;> exact hEq

/-- The physical loader's selected Bias-empty acquire alternates independently per buffer.
Failed attempts leave its stage's successful-acquire ordinal unchanged. -/
theorem biasEmptyPollParity {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g j q : Nat} {went acquire : Bool} {scope : MbarScope}
    (hWarp : Prologue.warpIndex l g = 14)
    {e : Event} (he : X.get (g,j) = some e)
    (hEvent : e.kind = .wait (biasEmptyObject l (g / l.block) stage) q went acquire scope) :
    q = (okPolls (biasEmptyObject l (g / l.block) stage) ((X.tr g).take j) + 1) % 2 := by
  obtain ⟨pc, kind⟩ := e
  change kind = _ at hEvent
  subst kind
  have hs := biasEmptyLoaderPollSite hp hX stage hWarp.ge he
  obtain ⟨hLo, hHi, _, _⟩ := biasSitesBounds stage hs
  obtain ⟨site, hSite, hPc⟩ := List.mem_map.mp (paritySitesMap stage ▸ hs)
  have hFirst (w : Fin 2) (t : TState)
      (hAt : At t 174 [(2535, b32 l.sharedBase), (1062, b32 (14 + w.val))]) :
      w = 0 → CursorPrep 0 t ∧ CursorPrep 1 t ∧ BiasParityFrame stage [] t := by
    intro _
    refine ⟨?_, ?_, ?_⟩
    · intro h; rw [hAt.1] at h; exact (by decide : ¬ cursorPrepLive 0 174) h |>.elim
    · intro h; rw [hAt.1] at h; exact (by decide : ¬ cursorPrepLive 1 174) h |>.elim
    · unfold BiasParityFrame
      rw [hAt.1]
      fin_cases stage <;> rfl
  -- Specialize the replay to the physical Bias warp to rule out the paired warp's bypass.
  obtain ⟨s, _, hj, hAt, hr⟩ := Prologue.nonzeroCommonPrefixOfLateEvent hp hX
    (g := g) (index := j) (event_thread_lt hX he) (by omega) he hLo
  have hAtR : At s 174 [(2535, b32 l.sharedBase), (1062, b32 (14 + (0 : Fin 2).val))] :=
    hAt.mono ⟨hAt.2.2.2.2.2.1, hWarp ▸ hAt.2.2.2.2.1, trivial⟩
  obtain ⟨vs, hw⟩ := Mma.walkFromRun hr
  have hGet : ((X.tr g).drop 5)[j-5]? = some
      ⟨pc, .wait (biasEmptyObject l (g / l.block) stage) q went acquire scope⟩ := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hj]
    exact he
  obtain ⟨t, o, ht, hi, hE⟩ := loaderReplayEvent 0 hw (pre := [])
    (P := fun past s => CursorPrep 0 s ∧ CursorPrep 1 s ∧ BiasParityFrame stage past s)
    (by rw [hAt.1]; decide) (ringShapeOfAt hAt) hAtR.2.2.2.2 (hFirst 0 s hAtR rfl) (by
      intro a b ev past hlo hhi hShape hRoots hInv hStep
      exact ⟨cursorPrepStep 0 hlo hhi hShape hRoots.2.1 hInv.1 hInv.1 hStep,
        cursorPrepStep 1 hlo hhi hShape hRoots.2.1 hInv.1 hInv.2.1 hStep,
        cursorStep stage hlo hhi hShape ⟨hInv.1, hInv.2.1⟩ hInv.2.2 hStep⟩) hGet hHi
  have hFrame := hi.2.2
  simp only [List.nil_append] at hFrame
  unfold BiasParityFrame at hFrame
  rw [biasCountExact hp hX stage hWarp.ge] at hFrame
  let n := okPolls (biasEmptyObject l (g / l.block) stage) ((X.tr g).take j)
  let b := (n + 1) % 2 == 1
  have hB : b.toNat = (n + 1) % 2 := by
    have h : (n + 1) % 2 = 0 ∨ (n + 1) % 2 = 1 := by omega
    rcases h with h | h <;> simp [b, h]
  rw [← hB]
  have hAtPc : t.pc = pc := ht
  obtain ⟨hCode, hMode, _, _, _, hPhase, _⟩ := biasCursorCode stage hSite
  rw [hAtPc, ← hPc, hMode] at hFrame
  cases hPrime : (site.pc == (primingWait stage).pc)
  · simp only [hPrime, Bool.false_eq_true, ↓reduceIte] at hFrame hPhase
    change t.regs (recurringWait stage).phase = some (b32 (xor b false).toNat) at hFrame
    rw [Bool.xor_false] at hFrame
    exact pollUsesBiasParity site hCode b hPc.symm hAtPc (hPhase.symm ▸ hFrame) hE
  · simp only [hPrime, ↓reduceIte] at hFrame
    change b = true at hFrame
    rw [hFrame]
    have hPrime' : pc = biasPrimingPoll stage := by
      rw [beq_iff_eq] at hPrime
      rw [← hPc, hPrime]
      fin_cases stage <;> rfl
    exact biasPrimingPollParity hp hX stage hWarp.ge (hPrime' ▸ he)
end PTX.Kernels.TmlFa4Fwd.Loader
