-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderDrainPoll
public import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
public import Kernels.TmlFa4Fwd.Proof.PollSafety
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasCredits
import Lemmas.Flow.WarpUniform
import Lemmas.Flow.EventCont
import Lemmas.Flow.ElectActor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

private structure BiasGateSite where
  wait : DrainWaitSite
  expect : Nat
  stage : Fin 2

private def biasGateSite : Fin 5 → BiasGateSite
  | 0 => ⟨⟨704, 9608, 1897, 1898⟩, 711, 0⟩
  | 1 => ⟨⟨756, 9610, 1917, 1918⟩, 763, 1⟩
  | 2 => ⟨⟨1146, 9613, 2039, 7177⟩, 1153, 0⟩
  | 3 => ⟨⟨1175, 9614, 2052, 7178⟩, 1182, 1⟩
  | 4 => ⟨⟨1361, 9616, 2121, 7177⟩, 1368, 0⟩

private theorem biasGateWaitCode (i : Fin 5) : LoaderWaitCode (biasGateSite i).wait := by
  fin_cases i
  · exact ⟨Flow.code_704, Flow.code_705, Flow.code_706⟩
  · exact ⟨Flow.code_756, Flow.code_757, Flow.code_758⟩
  · exact ⟨Flow.code_1146, Flow.code_1147, Flow.code_1148⟩
  · exact ⟨Flow.code_1175, Flow.code_1176, Flow.code_1177⟩
  · exact ⟨Flow.code_1361, Flow.code_1362, Flow.code_1363⟩

private theorem biasGateBounds (i : Fin 5) :
    let s := biasGateSite i
    174 ≤ s.wait.pc ∧ s.expect = s.wait.pc + 7 ∧ s.expect < 1901 := by
  fin_cases i <;> decide

private def BiasGateSite.interior (s : BiasGateSite) (pc : Nat) : Bool :=
  s.wait.pc < pc && pc ≤ s.expect

private def biasGateLandingCode (s : BiasGateSite) (pc : Nat) (op : Op) : Bool :=
  match op with
  | .bra dst _ => !s.interior dst || (pc == s.wait.pc + 1 && dst == s.wait.pc + 3)
  | .brx .. => false
  | _ => true

private theorem biasGateLandingAt (i : Fin 5) {pc : Nat} {ins : Instr}
    (hLo : 174 ≤ pc) (hHi : pc < 1901)
    (hc : kernel.code[pc]? = some ins) :
    biasGateLandingCode (biasGateSite i) pc ins.op = true := by
  let code := ((kernel.code.drop 174).take (1901 - 174)).zipIdx 174
  have hAll : code.all (fun (ins, pc) => biasGateLandingCode (biasGateSite i) pc ins.op) =
      true := by
    fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (ins, pc)
  apply List.mem_of_getElem? (i := pc - 174)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem biasGateOfCredit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g j pc : Nat}
    (he : X.get (g,j) = some ⟨pc, .arrive (Thread.Loader.biasReadyObject l (g / l.block) stage)
      32768 1 true .cta⟩) :
    ∃ i : Fin 5, (biasGateSite i).expect = pc ∧ (biasGateSite i).stage = stage := by
  have hm := actualBiasCreditSite hp hX stage he rfl
  fin_cases stage
  · change pc ∈ [711, 1153, 1368] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact ⟨0, rfl, rfl⟩
    · exact ⟨2, rfl, rfl⟩
    · exact ⟨4, rfl, rfl⟩
  · change pc ∈ [763, 1182] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨1, rfl, rfl⟩
    · exact ⟨3, rfl, rfl⟩

private def GuardPoll (site : BiasGateSite) (e : Event) : Prop :=
  e.pc = site.wait.pc ∧ ∃ target par scope, e.kind = .wait target par true true scope

private def BeforeGuard (site : BiasGateSite) (s : TState) : Prop :=
  (s.pc = site.wait.pc + 1 → s.regs site.wait.result = some (.pred false)) ∧
    ¬ (site.wait.pc + 3 ≤ s.pc ∧ s.pc ≤ site.expect)

private theorem beforeGuardStep (i : Fin 5) {l : Launch} {g : Nat} {s u : TState}
    {ev : Option Event} (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (hShape : RingShape s) (hBefore : BeforeGuard (biasGateSite i) s)
    (hStep : WStep kernel Assumptions.all l g s ev u)
    (hNoGuard : ∀ e ∈ ev.toList, ¬ GuardPoll (biasGateSite i) e) :
    BeforeGuard (biasGateSite i) u := by
  let site := biasGateSite i
  have hCode := biasGateWaitCode i
  have hWindow : site.expect = site.wait.pc + 7 := (biasGateBounds i).2.1
  change BeforeGuard site s at hBefore
  change BeforeGuard site u
  by_cases hStart : s.pc = site.wait.pc
  · have hc := hCode.1
    rw [← hStart] at hc
    obtain ⟨target, par, ok, scope, hEv, rfl⟩ := wstep_poll hStep hc
    have hFalse : ok = false := by
      cases ok
      · rfl
      · exact (hNoGuard ⟨s.pc, .wait target par true true scope⟩ (by simp [hEv])
          ⟨hStart, target, par, scope, rfl⟩).elim
    subst ok
    refine ⟨fun _ => Function.update_self _ _ _, ?_⟩
    simp [next, setReg, hStart]
  have hNext (hu : u.pc = s.pc ∨ u.pc = s.pc + 1)
      (h1 : s.pc ≠ site.wait.pc + 1) (h2 : s.pc ≠ site.wait.pc + 2) :
      BeforeGuard site u := by
    obtain ⟨_, hb⟩ := hBefore
    constructor
    · intro h
      omega
    · intro h
      omega
  by_cases hOne : s.pc = site.wait.pc + 1
  · have hc := hCode.2.1
    rw [← hOne] at hc
    have hReg := hBefore.1 hOne
    rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
    · have hCore : Tau kernel [] l g s u := by
        unfold Tau at ht ⊢
        rwa [← loaderOutCore hLo (by omega)]
      unfold Tau out at hCore
      cases hFault : s.fault
      · change s.regs (biasGateSite i).wait.result = some (.pred false) at hReg
        simp [hFault, hc, guardHolds, readReg, hReg, bind, Except.bind, pure,
          Except.pure] at hCore
        obtain rfl := hCore
        simp [BeforeGuard, skip, hOne]
      · simp [hFault] at hCore
    · obtain ⟨ins, hc', hLocal, _⟩ := estep_event_source he
      obtain rfl := Option.some.inj (hc.symm.trans hc')
      cases hLocal
  by_cases hTwo : s.pc = site.wait.pc + 2
  · have hc := hCode.2.2
    rw [← hTwo] at hc
    rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
    · have hCore : Tau kernel [] l g s u := by
        unfold Tau at ht ⊢
        rwa [← loaderOutCore hLo (by omega)]
      unfold Tau out at hCore
      cases hFault : s.fault
      · simp [hFault, hc, guardHolds, execLocalA, execLocalRule, execLocal, Op.isLocal, Op.rule,
          execBranch, pure, Except.pure] at hCore
        obtain rfl := hCore
        simp [BeforeGuard, site]
      · simp [hFault] at hCore
    · obtain ⟨ins, hc', hLocal, _⟩ := estep_event_source he
      obtain rfl := Option.some.inj (hc.symm.trans hc')
      cases hLocal
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · have hCore : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore hLo (by omega)]
    obtain ⟨ins, hc⟩ := tau_core_has_code hCore
    have hb := biasGateLandingAt i hLo hHi hc
    rcases tau_core_frame hc hCore with rfl | hFrame
    · exact hNext (.inr rfl) hOne hTwo
    have hPc := hFrame.pc
    cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
    case bra dst aligned =>
      have hOut : site.interior dst = false := by
        change biasGateLandingCode site s.pc ins.op = true at hb
        rw [ho] at hb
        simpa [biasGateLandingCode, hOne] using hb
      have hNot : ¬ (site.wait.pc < u.pc ∧ u.pc ≤ site.expect) := by
        rw [hPc]
        simpa [BiasGateSite.interior] using hOut
      constructor <;> intro h
      · exfalso
        apply hNot
        omega
      · exact hNot ⟨by omega, h.2⟩
    case brx => simp [biasGateLandingCode, ho] at hb
    all_goals exact hNext (.inr hPc) hOne hTwo
  · obtain ⟨_, hPc | ⟨hPc, _⟩⟩ := loaderEventProgress hLo (by omega) hShape.1 he
    · exact hNext (.inr hPc) hOne hTwo
    · exact hNext (.inl hPc) hOne hTwo

private theorem loaderGateWholeCode (bound : Nat) :
    ((kernel.code.drop 174).take (1901 - 174)).all
      (fun ins => loaderPipelineCutOp 174 1901 bound [2535, 1062] ins.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem loaderGateTail {l : Launch} {g : Nat}
  {s : TState} {es : List Event} {vs : List Visit} (warp : Fin 2) {mark : Event}
  (hLimit : mark.pc < 1901)
    (hw : Walk kernel Assumptions.all l g s es vs) (ht : s.pc = 1901)
    (hs : RingShape s)
    (hf : Holds s.regs [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
    (hm : mark ∈ es) : False := by
  have hSp := Epilogue.loaderWalkEventRange (lower := 1901) warp (by decide)
    (by rw [ht]; decide) hs hf (by intro bound; rfl) hw mark hm
  omega

private theorem loaderGateStep {l : Launch} {g : Nat}
  {s u : TState} {ev : Option Event} (warp : Fin 2)
    (hs : 174 ≤ s.pc ∧ s.pc < 1901) (hS : RingShape s)
    (hf : Holds s.regs [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
    (hw : WStep kernel Assumptions.all l g s ev u) :
    (174 ≤ u.pc ∧ u.pc ≤ 1901) ∧ RingShape u ∧
      Holds u.regs [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] := by
  obtain ⟨hLo, hHi, hs, hf⟩ := pipelineCutStep
    (F := [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
    (branch := u.pc) (by decide) (by decide) hs (loaderGateWholeCode u.pc) hw hS hf
  exact ⟨⟨hLo, hHi.resolve_right (Nat.lt_irrefl _)⟩, hs, hf⟩

/-- A certified loader invariant finds a required earlier event in the actual role walk. -/
theorem loaderEventPrecededBy {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (warp : Fin 2)
    (hWalk : Walk kernel Assumptions.all l g s es vs)
    (hPc : 174 ≤ s.pc ∧ s.pc ≤ 1901) (hShape : RingShape s)
    (hFrame : Holds s.regs [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
    {Q : TState → Prop} {prior : Event → Prop} (hBefore : Q s) {j : Nat} {mark : Event}
    (he : es[j]? = some mark) (hLimit : mark.pc < 1901)
    (hExclude : ∀ {t}, Q t → t.pc ≠ mark.pc)
    (hStep : ∀ {t u : TState} {e : Option Event}, 174 ≤ t.pc → t.pc < 1901 → RingShape t →
      Holds t.regs [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] →
      Q t → WStep kernel Assumptions.all l g t e u → (∀ e' ∈ e.toList, ¬ prior e') → Q u) :
    ∃ k < j, ∃ e, es[k]? = some e ∧ prior e := by
  classical
  induction hWalk generalizing j with
  | stop => simp at he
  | @tau s u es vs ht hw ih =>
    by_cases hEnd : s.pc = 1901
    · exact (loaderGateTail warp hLimit (.tau ht hw) hEnd hShape hFrame
        (List.mem_of_getElem? he)).elim
    have hRange : 174 ≤ s.pc ∧ s.pc < 1901 := ⟨hPc.1, by omega⟩
    let hLocal : WStep kernel Assumptions.all l g s none u := .inl ⟨rfl, ht⟩
    obtain ⟨hu, hs, hf⟩ := loaderGateStep warp hRange hShape hFrame hLocal
    have hb := hStep hRange.1 hRange.2 hShape hFrame hBefore hLocal (by simp)
    exact ih hu hs hf hb he
  | @ev s u actual es vs ht hw ih =>
    by_cases hEnd : s.pc = 1901
    · exact (loaderGateTail warp hLimit (.ev ht hw) hEnd hShape hFrame
        (List.mem_of_getElem? he)).elim
    have hRange : 174 ≤ s.pc ∧ s.pc < 1901 := ⟨hPc.1, by omega⟩
    cases j with
    | zero =>
      obtain rfl := Option.some.inj he
      exact (hExclude hBefore (estep_source_pc ht).symm).elim
    | succ j =>
      by_cases hGuard : prior actual
      · exact ⟨0, Nat.zero_lt_succ _, actual, rfl, hGuard⟩
      · let hLocal : WStep kernel Assumptions.all l g s (some actual) u := .inr ⟨_, rfl, ht⟩
        obtain ⟨hu, hs, hf⟩ := loaderGateStep warp hRange hShape hFrame hLocal
        have hb := hStep hRange.1 hRange.2 hShape hFrame hBefore hLocal (by simpa using hGuard)
        obtain ⟨k, hk, pred, hp, hg⟩ := ih hu hs hf hb he
        exact ⟨k + 1, Nat.succ_lt_succ hk, pred, hp, hg⟩
  | last ht =>
    have hJ : j = 0 := by
      have hl := (List.getElem?_eq_some_iff.mp he).1
      simpa using hl
    subst j
    obtain rfl := Option.some.inj he
    exact (hExclude hBefore (estep_source_pc ht).symm).elim

private theorem guardedEventInLoaderWalk (i : Fin 5) {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (warp : Fin 2)
    (hWalk : Walk kernel Assumptions.all l g s es vs)
    (hPc : 174 ≤ s.pc ∧ s.pc ≤ 1901) (hShape : RingShape s)
    (hFrame : Holds s.regs [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
    (hBefore : BeforeGuard (biasGateSite i) s) {j : Nat} {mark : Event}
    (he : es[j]? = some mark) (hMark : mark.pc = (biasGateSite i).expect) :
    ∃ k < j, ∃ e, es[k]? = some e ∧ GuardPoll (biasGateSite i) e := by
  have hBounds := biasGateBounds i
  have hLimit : mark.pc < 1901 := hMark ▸ hBounds.2.2
  refine loaderEventPrecededBy warp hWalk hPc hShape hFrame hBefore he hLimit ?_ ?_
  · intro t hBlocked hEq
    have hAt := hEq.trans hMark
    exact hBlocked.2 ⟨hAt.symm ▸ (show (biasGateSite i).wait.pc + 3 ≤
      (biasGateSite i).expect from by rw [hBounds.2.1]; omega), hAt.le⟩
  · intro _ _ _ hlo hhi hs _
    exact beforeGuardStep i hlo hhi hs

private def biasElectPc (i : Fin 5) : Nat := (biasGateSite i).wait.pc + 3

private def biasElectRegs : Fin 5 → Nat × Nat
  | 0 => (1899, 146)
  | 1 => (1919, 158)
  | 2 => (2040, 186)
  | 3 => (2053, 192)
  | 4 => (2122, 203)

private theorem biasElectCode (i : Fin 5) :
    let (dst, pred) := biasElectRegs i
    let election := biasElectPc i
    kernel.code[election]? = some ⟨none, .warp
      ⟨.elect, none, [some dst, some pred], [], some (.imm (-1))⟩⟩ ∧
    kernel.code[election + 1]? = some ⟨none,
      .int ⟨.not, .pred, false, [some (pred + 1)], [.reg pred]⟩⟩ ∧
    kernel.code[election + 2]? = some
      ⟨some (pred + 1, false), .bra ((biasGateSite i).expect + 1) false⟩ := by
  fin_cases i
  · exact ⟨Flow.code_707, Flow.code_708, Flow.code_709⟩
  · exact ⟨Flow.code_759, Flow.code_760, Flow.code_761⟩
  · exact ⟨Flow.code_1149, Flow.code_1150, Flow.code_1151⟩
  · exact ⟨Flow.code_1178, Flow.code_1179, Flow.code_1180⟩
  · exact ⟨Flow.code_1364, Flow.code_1365, Flow.code_1366⟩

private def biasElectInterior (i : Fin 5) (pc : Nat) : Prop :=
  biasElectPc i < pc ∧ pc ≤ (biasGateSite i).expect

private def BeforeBiasSelection (i : Fin 5) (l : Launch) (g : Nat) (s : TState) : Prop :=
  biasElectInterior i s.pc →
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      u.pc = (biasGateSite i).expect + 1

private def BiasSelectedBy (i : Fin 5) (l : Launch) (g : Nat) (e : Event) : Prop :=
  ∃ inst, e = ⟨biasElectPc i, .elect (2 ^ 32 - 1) inst (laneOf l g)⟩

private theorem biasNotElectedSkips (i : Fin 5) {l : Launch} {g : Nat} {s : TState}
    (hPc : s.pc = biasElectPc i + 1) (hShape : RingShape s) (hClean : s.fault = none)
    (hPred : s.regs (biasElectRegs i).2 = some (.pred false)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      u.pc = (biasGateSite i).expect + 1 := by
  let pred := (biasElectRegs i).2
  let e := biasElectPc i
  let predFrame : List (Nat × Value) := [(pred, .pred false)]
  have hBounds := biasGateBounds i
  have hWindow : 174 ≤ e ∧ e + 3 < 1906 := by dsimp [e, biasElectPc]; omega
  have hNeg : Seg kernel [] l g 1 (e+1) predFrame (e+2) [(pred+1, .pred true)] := by
    fin_cases i <;> dsimp [e, predFrame, pred, biasElectPc, biasGateSite, biasElectRegs] <;>
      intro t ht <;> seg_fp ht using rfl
  have hAt : At s (e+1) predFrame := pipelineAtCut hPc hShape ⟨hPred, trivial⟩ hClean
    ⟨_, (biasElectCode i).2.1, rfl⟩
  obtain ⟨v, hr, hv⟩ := hNeg.apply hAt
  obtain ⟨hRun, _⟩ := loaderLinear (regs := []) (n := 1)
    (by omega) (by omega) hAt.1 (by simp) rfl hr
  have hBranch : Tau kernel Assumptions.all l g v {v with pc := (biasGateSite i).expect + 1} := by
    unfold Tau
    rw [loaderOutCore (by have := hv.1; omega) (by have := hv.1; omega)]
    have hPred : v.regs (pred + 1) = some (.pred true) := hv.2.2.2.2.1
    have hCode := (biasElectCode i).2.2
    have hvPc : v.pc = e + 2 := hv.1
    rw [← hvPc] at hCode
    change kernel.code[v.pc]? = some
      ⟨some (pred+1, false), .bra ((biasGateSite i).expect+1) false⟩ at hCode
    simp [out, hv.2.2.2.1, hCode, guardHolds, readReg, hPred, bind, Except.bind,
      pure, Except.pure, execLocalA_nil, execLocal, execBranch, Op.isLocal, Op.rule]
  exact ⟨_, (run_rtg hRun).tail hBranch, rfl⟩

private theorem entersBiasElection (i : Fin 5) {l : Launch} {g : Nat} {s u : TState}
    {ev : Option Event} (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901) (hShape : RingShape s)
    (hIn : biasElectInterior i u.pc) (hOut : ¬ biasElectInterior i s.pc)
    (hStep : WStep kernel Assumptions.all l g s ev u) : s.pc = biasElectPc i := by
  have consume (hNext : u.pc = s.pc ∨ u.pc = s.pc + 1) : s.pc = biasElectPc i := by
    unfold biasElectInterior at hIn hOut
    omega
  rcases hStep with ⟨rfl, ht⟩ | ⟨actual, rfl, he⟩
  · have hCore : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore hLo (by omega)]
    obtain ⟨ins, hc⟩ := tau_core_has_code hCore
    have hLanding := biasGateLandingAt i hLo hHi hc
    rcases tau_core_frame hc hCore with rfl | hFrame
    · exact consume (.inr rfl)
    have hPc := hFrame.pc
    cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
    case bra dst aligned =>
      have hIn2 := hIn
      rw [hPc] at hIn2
      unfold biasElectInterior biasElectPc at hIn2
      have hInside : (biasGateSite i).interior dst = true := by
        simp only [BiasGateSite.interior, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by omega, hIn2.2⟩
      rw [ho] at hLanding
      simp [biasGateLandingCode, hInside] at hLanding
      omega
    case brx => simp [biasGateLandingCode, ho] at hLanding
    all_goals exact consume (.inr hPc)
  · obtain ⟨_, hp | ⟨hp, _⟩⟩ := loaderEventProgress hLo (by omega) hShape.1 he
    · exact consume (.inr hp)
    · exact consume (.inl hp)

private theorem beforeBiasSelectionStep (i : Fin 5) {l : Launch} {g : Nat} {s u : TState}
    {ev : Option Event} (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (hShape : RingShape s) (hBefore : BeforeBiasSelection i l g s)
    (hStep : WStep kernel Assumptions.all l g s ev u)
    (hNo : ∀ e ∈ ev.toList, ¬ BiasSelectedBy i l g e) : BeforeBiasSelection i l g u := by
  intro hIn
  by_cases hFrom : biasElectInterior i s.pc
  · obtain ⟨exit, hPath, hExit⟩ := hBefore hFrom
    rcases Relation.ReflTransGen.cases_head hPath with rfl | ⟨first, hTau, rest⟩
    · have := hFrom.2
      omega
    · rcases hStep with ⟨rfl, hNext⟩ | ⟨e, rfl, he⟩
      · obtain rfl := tau_det hTau hNext
        exact ⟨exit, rest, hExit⟩
      · exact (not_tau_of_stops (stops_of_estep he) hTau).elim
  have hSrc := entersBiasElection i hLo hHi hShape hIn hFrom hStep
  have hc := (biasElectCode i).1
  rw [← hSrc] at hc
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · have hCore : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore hLo (by omega)]
    exact (tau_core_not_event hc rfl hCore).elim
  · obtain ⟨ins, hRead, _, hFire⟩ := estep_event_source he
    obtain rfl := Option.some.inj (hc.symm.trans hRead)
    have hAll := fires_elect_mask (bits := BitVec.ofNat 64 (2 ^ 32 - 1)) rfl hFire
    obtain ⟨_, inst, leader, hEvent, hU⟩ := fires_elect hFire
    have hFull : e = ⟨biasElectPc i, .elect (2 ^ 32 - 1) inst leader⟩ := by
      rcases hAll with ⟨inst', leader', hEq⟩ | ⟨f, hEq⟩
      · obtain ⟨_, rfl, rfl⟩ := Kind.elect.inj (congrArg Event.kind (hEvent.symm.trans hEq))
        rwa [hSrc] at hEq
      · cases congrArg Event.kind (hEvent.symm.trans hEq)
    have hNot : laneOf l g ≠ leader := by
      intro h
      exact hNo e (by simp) ⟨inst, h ▸ hFull⟩
    have hUShape := loaderPipelineStepShape hLo (by omega) hShape (.inr ⟨_, rfl, he⟩)
    have hClean : s.fault = none := by
      cases hf : s.fault
      · rfl
      · obtain ⟨tmp, hout, hFire⟩ := he
        simp only [out, hf, Out.ev.injEq] at hout
        subst tmp
        cases hFire.2
    apply biasNotElectedSkips i (hShape := hUShape)
    · rw [hU]
      change s.pc + 1 = biasElectPc i + 1
      rw [hSrc]
    · simpa [hU, next, setReg] using hClean
    · change u = next (setReg (setReg s (biasElectRegs i).1
        (.bits 32 (BitVec.ofNat 64 leader))) (biasElectRegs i).2
        (.pred (laneOf l g == leader))) at hU
      have hFalse : (laneOf l g == leader) = false := by simp [hNot]
      simp only [hU, next, setReg, Function.update_self, hFalse]

private def biasRoleBranch (i : Fin 3) : Nat :=
  ![676, 1143, 1358] i

private def biasRoleJoin (i : Fin 3) : Nat :=
  ![780, 1203, 1384] i

private def biasRolePred (i : Fin 3) : Nat :=
  ![123, 123, 202] i

private def inBiasRole (i : Fin 3) (pc : Nat) : Prop :=
  biasRoleBranch i < pc ∧ pc < biasRoleJoin i

private instance (i : Fin 3) (pc : Nat) : Decidable (inBiasRole i pc) :=
  inferInstanceAs (Decidable (biasRoleBranch i < pc ∧ pc < biasRoleJoin i))

private def roleBiasLanding (pc : Nat) (op : Op) : Bool :=
  match op with
  | .bra dst _ => decide ((538 < dst ∧ dst < 1849 → 538 < pc ∧ pc < 1849) ∧
      ¬ (1356 ≤ dst ∧ dst ≤ 1358)) &&
      (List.ofFn fun i : Fin 3 => decide (inBiasRole i dst → inBiasRole i pc)).all id
  | .brx .. => false
  | _ => true

private theorem roleBiasLandingAt {pc : Nat} {ins : Instr}
    (hLo : 174 ≤ pc) (hHi : pc < 1901) (hc : kernel.code[pc]? = some ins) :
    roleBiasLanding pc ins.op = true := by
  let code := ((kernel.code.drop 174).take (1901 - 174)).zipIdx 174
  have hTable : code.all (fun (ins, pc) => roleBiasLanding pc ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hTable (ins,pc)
  apply List.mem_of_getElem? (i := pc - 174)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private def RoleBiasBranchSource (pc dst : Nat) : Prop :=
  (538 < dst ∧ dst < 1849 → 538 < pc ∧ pc < 1849) ∧ ¬ (1356 ≤ dst ∧ dst ≤ 1358) ∧
    ∀ i : Fin 3, inBiasRole i dst → inBiasRole i pc

private theorem loaderBiasLanding {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901) (hShape : RingShape s)
    (hStep : WStep kernel Assumptions.all l g s e u) :
    (u.pc = s.pc ∨ u.pc = s.pc + 1) ∨ RoleBiasBranchSource s.pc u.pc := by
  rcases hStep with ⟨rfl, ht⟩ | ⟨event, rfl, he⟩
  · have hCore : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore hLo (by omega)]
    obtain ⟨ins, hc⟩ := tau_core_has_code hCore
    have hOk := roleBiasLandingAt hLo hHi hc
    rcases tau_core_frame hc hCore with rfl | hFrame
    · exact .inl (.inr rfl)
    have hPc := hFrame.pc
    cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
    case bra dst aligned =>
      rw [ho] at hOk
      simp only [roleBiasLanding, Bool.and_eq_true_iff, decide_eq_true_eq] at hOk
      rw [hPc]
      exact .inr ⟨hOk.1.1, hOk.1.2, fun i =>
        of_decide_eq_true (List.all_eq_true.mp hOk.2 _ (List.mem_ofFn.mpr ⟨i, rfl⟩))⟩
    case brx => simp [roleBiasLanding, ho] at hOk
    all_goals exact .inl (.inr hPc)
  · obtain ⟨_, hPc | ⟨hPc, _⟩⟩ := loaderEventProgress hLo (by omega) hShape.1 he
    · exact .inl (.inr hPc)
    · exact .inl (.inl hPc)

private theorem biasWarpTest (j : Fin 2) :
    let pc := if j = 0 then 538 else 1355
    let reg := if j = 0 then 123 else 200
    kernel.code[pc]? = some ⟨none, .int
      ⟨.setp .ne none, .int .b 32, false, [some reg], [.reg 1062, .imm 14]⟩⟩ := by
  fin_cases j
  · exact Flow.code_538
  · exact Flow.code_1355

private theorem warpTestFires {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (which : Fin 2)
    (hPc : s.pc = if which = 0 then 538 else 1355)
    (hWarp : s.regs 1062 = some (b32 15))
    (hStep : WStep kernel Assumptions.all l g s e u) :
    u.regs (if which = 0 then 123 else 200) = some (.pred true) := by
  let dest := if which = 0 then 123 else 200
  let ins : IntInstr :=
    ⟨.setp .ne none, .int .b 32, false, [some dest], [.reg 1062, .imm 14]⟩
  have hLo : 174 ≤ s.pc := by rw [hPc]; fin_cases which <;> decide
  have hHi : s.pc < 1906 := by rw [hPc]; fin_cases which <;> decide
  have hc : kernel.code[s.pc]? = some ⟨none, .int ins⟩ := hPc.symm ▸ biasWarpTest which
  have hExec : execLocal l g s (.int ins) = .ok (next (setReg s dest (.pred true))) := by
    rw [execLocal_int (i := ins) rfl]
    simp [ins, execInt, compare, DType.width, readBits, readReg, hWarp, b32,
      bind, Except.bind, pure, Except.pure]
    rfl
  have hVar : (Op.int ins).varyingSregs = [] := rfl
  rcases hStep with ⟨rfl, ht⟩ | ⟨actual, rfl, he⟩
  · have hCore : out kernel [] l g s = .tau u := by
      unfold Tau at ht
      rwa [← loaderOutCore hLo hHi]
    unfold out at hCore
    cases hf : s.fault
    · simp [hf, hc, guardHolds, Op.isLocal, execLocalA_nil, hExec, hVar, pure, Except.pure] at hCore
      obtain rfl := hCore
      exact Function.update_self _ _ _
    · simp [hf] at hCore
  · obtain ⟨ins, hi, hLocal, _⟩ := estep_event_source he
    obtain rfl := Option.some.inj (hc.symm.trans hi)
    cases hLocal

private theorem warpTestTailCombine {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hPc : s.pc = 1357) (hPred : s.regs 200 = some (.pred true))
    (hStep : WStep kernel Assumptions.all l g s e u) :
    u.regs 202 = some (.pred true) := by
  let ins : IntInstr := ⟨.or, .pred, false, [some 202], [.reg 200, .reg 201]⟩
  have hc : kernel.code[s.pc]? = some ⟨none, .int ins⟩ := hPc.symm ▸ Flow.code_1357
  rcases hStep with ⟨rfl, ht⟩ | ⟨actual, rfl, he⟩
  · have hCore : out kernel [] l g s = .tau u := by
      unfold Tau at ht
      rwa [← loaderOutCore (by omega) (by omega)]
    unfold out at hCore
    cases hf : s.fault
    · have hVar : (Op.int ins).varyingSregs = [] := rfl
      have hRead : readPred l g s (.reg 200) = .ok true := by
        simp [readPred_reg, readReg, hPred, bind, Except.bind, pure, Except.pure]
      have hExec : execLocal l g s (.int ins) =
          (do let last ← readPred l g s (.reg 201)
              pure (next (setReg s 202 (.pred (true || last))))) := by
        rw [execLocal_int (i := ins) rfl]
        simp [ins, execInt, DType.width, hRead, bind, Except.bind, pure, Except.pure]
      simp only [hf, hc, guardHolds, hVar, List.isEmpty_nil, Op.isLocal,
        ↓reduceIte, execLocalA_nil, hExec, pure, Except.pure] at hCore
      cases hVal : readPred l g s (.reg 201) with
      | error fault => simp [hVal, bind, Except.bind] at hCore
      | ok b =>
        simp [hVal, bind, Except.bind] at hCore
        obtain rfl := hCore
        simp [next, setReg]
    · simp [hf] at hCore
  · obtain ⟨ins, hi, hLocal, _⟩ := estep_event_source he
    obtain rfl := Option.some.inj (hc.symm.trans hi)
    cases hLocal

private theorem biasRoleBranchCode (i : Fin 3) :
    kernel.code[biasRoleBranch i]? =
      some ⟨some (biasRolePred i, false), .bra (biasRoleJoin i) false⟩ := by
  fin_cases i
  · exact Flow.code_676
  · exact Flow.code_1143
  · exact Flow.code_1358

private theorem biasRoleSkips {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (i : Fin 3) (hPc : s.pc = biasRoleBranch i)
    (hReg : s.regs (biasRolePred i) = some (.pred true))
    (hStep : WStep kernel Assumptions.all l g s e u) : u.pc = biasRoleJoin i := by
  have hc := hPc.symm ▸ biasRoleBranchCode i
  have hLo : 174 ≤ s.pc := by rw [hPc]; fin_cases i <;> decide
  have hHi : s.pc < 1906 := by rw [hPc]; fin_cases i <;> decide
  rcases hStep with ⟨rfl, ht⟩ | ⟨actual, rfl, he⟩
  · have hCore : out kernel [] l g s = .tau u := by
      unfold Tau at ht
      rwa [← loaderOutCore hLo hHi]
    unfold out at hCore
    cases hf : s.fault
    · simp [hf, hc, guardHolds, readReg, hReg, bind, Except.bind, pure, Except.pure,
        execLocalA_nil, execLocal, execBranch, Op.isLocal, Op.rule] at hCore
      obtain rfl := hCore
      rfl
    · simp [hf] at hCore
  · obtain ⟨ins, hi, hLocal, _⟩ := estep_event_source he
    obtain rfl := Option.some.inj (hc.symm.trans hi)
    cases hLocal

private structure BeforeBiasWarp15 (s : TState) : Prop where
  prefixPred : 538 < s.pc → s.pc < 1849 → s.regs 123 = some (.pred true)
  tailPred : 1356 ≤ s.pc → s.pc ≤ 1357 → s.regs 200 = some (.pred true)
  tailGate : s.pc = 1358 → s.regs 202 = some (.pred true)
  excluded : ∀ i : Fin 3, ¬ inBiasRole i s.pc

private theorem roleBiasRegisterWrites {lo hi r pc : Nat}
    (hCode : ((kernel.code.drop lo).take (hi - lo)).all
      (fun ins => !(loaderRingWrites ins.op).contains r) = true)
    (hLo : lo ≤ pc) (hHi : pc < hi) {ins : Instr} (hc : kernel.code[pc]? = some ins) :
    r ∉ loaderRingWrites ins.op := by
  have hAt : ((kernel.code.drop lo).take (hi - lo))[pc-lo]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
    exact hc
  simpa using List.all_eq_true.mp hCode ins (List.mem_of_getElem? hAt)

private theorem beforeBiasWarp15Step {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901) (hShape : RingShape s)
    (hWarp : s.regs 1062 = some (b32 15))
    (hBefore : BeforeBiasWarp15 s) (hStep : WStep kernel Assumptions.all l g s e u) :
    BeforeBiasWarp15 u := by
  have hLanding := loaderBiasLanding hLo hHi hShape hStep
  constructor
  · intro hlo hhi
    have hSource : s.pc = 538 ∨ 538 < s.pc ∧ s.pc < 1849 := by
      rcases hLanding with (h | h) | h
      · omega
      · omega
      · exact .inr (h.1 ⟨hlo, hhi⟩)
    rcases hSource with h | ⟨ha, hb⟩
    · exact warpTestFires 0 h hWarp hStep
    · have hCode : ((kernel.code.drop 539).take (1849 - 539)).all
          (fun ins => !(loaderRingWrites ins.op).contains 123) = true := by
        set_option maxRecDepth 100000 in kernel_rfl
      rw [loaderPipelineStepRegs hLo hHi (fun _ hc =>
        roleBiasRegisterWrites hCode ha hb hc) hStep]
      exact hBefore.prefixPred ha hb
  · intro hlo hhi
    have hSource : s.pc = 1355 ∨ 1356 ≤ s.pc ∧ s.pc ≤ 1357 := by
      rcases hLanding with (h | h) | h
      · omega
      · omega
      · exact (h.2.1 ⟨hlo, by omega⟩).elim
    rcases hSource with h | ⟨ha, hb⟩
    · exact warpTestFires 1 h hWarp hStep
    · have hCode : ((kernel.code.drop 1356).take (1358 - 1356)).all
          (fun ins => !(loaderRingWrites ins.op).contains 200) = true := by
        set_option maxRecDepth 100000 in kernel_rfl
      rw [loaderPipelineStepRegs hLo hHi (fun _ hc =>
        roleBiasRegisterWrites hCode ha (by omega) hc) hStep]
      exact hBefore.tailPred ha hb
  · intro hup
    rcases hLanding with (h | h) | h
    · rw [loaderPipelineStepRegs hLo hHi (fun ins hc => by
          rw [show s.pc = 1358 by omega, Flow.code_1358] at hc
          obtain rfl := Option.some.inj hc
          decide) hStep]
      exact hBefore.tailGate (by omega)
    · exact warpTestTailCombine (by omega) (hBefore.tailPred (by omega) (by omega)) hStep
    · exact (h.2.1 ⟨by omega, hup.le⟩).elim
  · intro i hIn
    have hSrc : s.pc = biasRoleBranch i := by
      rcases hLanding with (h | h) | h
      · exact (hBefore.excluded i (h ▸ hIn)).elim
      · have hOut := hBefore.excluded i
        unfold inBiasRole at hIn hOut
        omega
      · exact (hBefore.excluded i (h.2.2 i hIn)).elim
    have hPred : s.regs (biasRolePred i) = some (.pred true) := by
      fin_cases i
      · exact hBefore.prefixPred (hSrc ▸ (by decide)) (hSrc ▸ (by decide))
      · exact hBefore.prefixPred (hSrc ▸ (by decide)) (hSrc ▸ (by decide))
      · exact hBefore.tailGate hSrc
    have hNext := biasRoleSkips i hSrc hPred hStep
    exact (Nat.lt_irrefl _ (hNext ▸ hIn.2)).elim

private theorem biasCreditAdvance {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {target : Loc} (hKind : e.kind = .arrive target 32768 1 true .cta)
    (he : EStep kernel Assumptions.all l g s e (some u)) : u.pc = e.pc + 1 := by
  obtain ⟨ins, _, _, hFire⟩ := estep_event_source he
  obtain ⟨_, _, _, _, _, _, state, hOp, _⟩ := fires_arrive_flags hFire hKind
  rw [hOp] at hFire
  obtain ⟨rfl, _⟩ := fires_arrive_state hFire
  cases state <;> exact congrArg (· + 1) (estep_source_pc he).symm

private theorem afterBiasCreditOutside (i j : Fin 5) :
    let (prior, site) := (biasGateSite i, biasGateSite j)
    prior.expect + 1 ≠ site.wait.pc + 1 ∧
      ¬ (site.wait.pc + 3 ≤ prior.expect + 1 ∧ prior.expect + 1 ≤ site.expect) := by
  fin_cases i <;> fin_cases j <;> decide

private theorem guardedEventAfterCredit (i beforeSite : Fin 5) {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (warp : Fin 2)
    (hWalk : Walk kernel Assumptions.all l g s es vs)
    (hPc : 174 ≤ s.pc ∧ s.pc ≤ 1901) (hShape : RingShape s)
    (hFrame : Holds s.regs [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
    {start finish : Nat} {earlier mark : Event} {target : Loc}
    (hOrder : start < finish)
    (hStart : es[start]? = some earlier) (hEarlier : earlier.pc = (biasGateSite beforeSite).expect)
    (hKind : earlier.kind = .arrive target 32768 1 true .cta)
    (hEnd : es[finish]? = some mark) (hMark : mark.pc = (biasGateSite i).expect) :
    ∃ k, start < k ∧ k < finish ∧ ∃ e, es[k]? = some e ∧ GuardPoll (biasGateSite i) e := by
  have hEarlierLimit : earlier.pc < 1901 := hEarlier ▸ (biasGateBounds beforeSite).2.2
  induction hWalk generalizing start finish with
  | stop => simp at hStart
  | @tau s u es vs ht hw ih =>
    by_cases hExit : s.pc = 1901
    · exact (loaderGateTail warp hEarlierLimit (.tau ht hw) hExit hShape hFrame
        (List.mem_of_getElem? hStart)).elim
    have hRange : 174 ≤ s.pc ∧ s.pc < 1901 := ⟨hPc.1, by omega⟩
    obtain ⟨hu, hs, hf⟩ := loaderGateStep warp hRange hShape hFrame (.inl ⟨rfl, ht⟩)
    exact ih hu hs hf hOrder hStart hEnd
  | @ev s u actual es vs ht hw ih =>
    by_cases hExit : s.pc = 1901
    · exact (loaderGateTail warp hEarlierLimit (.ev ht hw) hExit hShape hFrame
        (List.mem_of_getElem? hStart)).elim
    have hRange : 174 ≤ s.pc ∧ s.pc < 1901 := ⟨hPc.1, by omega⟩
    obtain ⟨hu, hs, hf⟩ := loaderGateStep warp hRange hShape hFrame (.inr ⟨_, rfl, ht⟩)
    cases finish with
    | zero => omega
    | succ finish =>
      cases start with
      | zero =>
        obtain rfl := Option.some.inj hStart
        have hAt := (biasCreditAdvance hKind ht).trans (congrArg (· + 1) hEarlier)
        have hBefore : BeforeGuard (biasGateSite i) u := by
          refine ⟨fun h => ((afterBiasCreditOutside beforeSite i).1 (hAt.symm.trans h)).elim, ?_⟩
          rw [hAt]
          exact (afterBiasCreditOutside beforeSite i).2
        obtain ⟨k, hk, e, he, hGuard⟩ :=
          guardedEventInLoaderWalk i warp hw hu hs hf hBefore hEnd hMark
        exact ⟨k + 1, Nat.zero_lt_succ _, Nat.succ_lt_succ hk, e, he, hGuard⟩
      | succ start =>
        obtain ⟨k, hs, hf, e, he, hGuard⟩ :=
          ih hu hs hf (Nat.lt_of_succ_lt_succ hOrder) hStart hEnd
        exact ⟨k + 1, Nat.succ_lt_succ hs, Nat.succ_lt_succ hf, e, he, hGuard⟩
  | last ht =>
    have hLen := (List.getElem?_eq_some_iff.mp hEnd).1
    simp only [List.length_singleton] at hLen
    omega

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem biasExpectationWalk {g j pc : Nat} (stage : Fin 2)
    (he : X.get (g,j) = some ⟨pc, .arrive (Thread.Loader.biasReadyObject l (g / l.block) stage)
      32768 1 true .cta⟩) :
    ∃ (i : Fin 5) (warp : Fin 2) (s : TState) (vs : List Visit),
      (biasGateSite i).stage = stage ∧ 14 + warp.val = Prologue.warpIndex l g ∧ 5 ≤ j ∧
      At s 174 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop 5) vs ∧
      ((X.tr g).drop 5)[j - 5]? = some ⟨(biasGateSite i).expect,
        .arrive (Thread.Loader.biasReadyObject l (g / l.block) stage) 32768 1 true .cta⟩ := by
  obtain ⟨i, hPc, hStage⟩ := biasGateOfCredit hp hX stage he
  subst pc
  let site := biasGateSite i
  let e : Event := ⟨site.expect,
    .arrive (Thread.Loader.biasReadyObject l (g / l.block) stage) 32768 1 true .cta⟩
  have hBounds : 174 ≤ site.wait.pc ∧ site.expect = site.wait.pc + 7 ∧ site.expect < 1901 :=
    biasGateBounds i
  have hLate : 173 < e.pc := by change 173 < site.expect; omega
  have hHint : e.pc ∉ registerHintSites := by
    change site.expect ∉ registerHintSites
    fin_cases i <;> decide
  have he' : X.get (g,j) = some e := he
  have hRole : roleBodyPc (Prologue.warpIndex l g) site.expect :=
    roleBodyPcOfEvent hp hX he' hLate hHint
  have hWarp : 14 ≤ Prologue.warpIndex l g := by
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  let warp : Fin 2 := ⟨Prologue.warpIndex l g - 14, by have := Prologue.warpIndex_lt hp g; omega⟩
  have hWarpEq : 14 + warp.val = Prologue.warpIndex l g := Nat.add_sub_of_le hWarp
  obtain ⟨start, result, hIndex, hAt, hr⟩ := Prologue.nonzeroCommonPrefixOfLateEvent hp hX
    (g := g) (index := j) (event_thread_lt hX he') (by omega) he' hLate
  obtain ⟨vs, hWalk⟩ := Mma.walkFromRun hr
  have hGet : ((X.tr g).drop 5)[j-5]? = some e := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hIndex]
    exact he'
  have hStart : At start 174 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] :=
    hAt.mono ⟨hAt.2.2.2.2.2.1, hWarpEq.symm ▸ hAt.2.2.2.2.1, trivial⟩
  exact ⟨i, warp, start, vs, hStage, hWarpEq, hIndex, hStart, hWalk, hGet⟩

private theorem biasExpectationGuardedSince {cta g j : Nat} (stage : Fin 2) (lower : Option Nat)
    (hIssue : X.Arrive (g,j) (Thread.Loader.biasReadyObject l cta stage) 32768 1 true .cta)
    (hPrior : ∀ a, lower = some a → a < j ∧ ∃ stage' : Fin 2,
      X.Arrive (g,a) (Thread.Loader.biasReadyObject l cta stage') 32768 1 true .cta) :
    ∃ (k : Nat) (e : Event) (phase : Nat) (scope : MbarScope),
      X.get (g,k) = some e ∧
      e.kind = .wait (Thread.Loader.biasEmptyObject l cta stage) phase true true scope ∧
      Resumes kernel X (g,k) (g,j) ∧ ∀ a, lower = some a → a < k := by
  obtain ⟨pc, he⟩ := hIssue
  obtain ⟨_, _, hLoc⟩ := actualArriveOffsetIn hp hX he
  have hOwner : cta = g / l.block := congrArg Loc.cta hLoc
  subst cta
  obtain ⟨i, warp, start, vs, hStage, _, hIndex, hAt, hWalk, hGet⟩ :=
    biasExpectationWalk hp hX stage he
  let site := biasGateSite i
  have hBounds : 174 ≤ site.wait.pc ∧ site.expect = site.wait.pc + 7 ∧ site.expect < 1901 :=
    biasGateBounds i
  have hBefore : BeforeGuard site start := by
    have hStart := hAt.1
    constructor <;> intro h <;> omega
  have hPC : 174 ≤ start.pc ∧ start.pc ≤ 1901 := by rw [hAt.1]; decide
  have hFrame := hAt.2.2.2.2
  obtain ⟨k, hk, poll, hPoll, hShape, hLower⟩ : ∃ k < j - 5, ∃ poll,
      ((X.tr g).drop 5)[k]? = some poll ∧ GuardPoll site poll ∧
      ∀ a, lower = some a → a < 5 + k := by
    cases lower with
    | none =>
      obtain ⟨k, hk, f, hf, hGuard⟩ := guardedEventInLoaderWalk i warp hWalk
        hPC (ringShapeOfAt hAt) hFrame hBefore hGet rfl
      exact ⟨k, hk, f, hf, hGuard, by simp⟩
    | some a =>
      obtain ⟨hOrder, stage', predSite, hEarlier⟩ := hPrior a rfl
      obtain ⟨before, hPrev, _⟩ := biasGateOfCredit hp hX stage' hEarlier
      let prior : Event := ⟨predSite,
        .arrive (Thread.Loader.biasReadyObject l (g / l.block) stage') 32768 1 true .cta⟩
      obtain ⟨_, _, _, _, _, _, ha, _, _, _⟩ := biasExpectationWalk hp hX stage' hEarlier
      have hGetPrior : ((X.tr g).drop 5)[a - 5]? = some prior := by
        rw [List.getElem?_drop, Nat.add_sub_of_le ha]
        exact hEarlier
      obtain ⟨k, hak, hkj, f, hf, hGuard⟩ := guardedEventAfterCredit i before warp hWalk
        hPC (ringShapeOfAt hAt) hFrame (by omega) hGetPrior hPrev.symm rfl hGet rfl
      exact ⟨k, hkj, f, hf, hGuard, by intro q h; obtain rfl := Option.some.inj h; omega⟩
  have hTrue : X.get (g,5+k) = some poll := by
    change (X.tr g)[5 + k]? = some poll
    simpa only [List.getElem?_drop] using hPoll
  obtain ⟨pollSite, pollKind⟩ := poll
  obtain ⟨hPollSite, target, phase, scope, hPollKind⟩ := hShape
  change pollSite = site.wait.pc at hPollSite
  change pollKind = _ at hPollKind
  subst pollSite pollKind
  have hWaitPc : site.wait.pc ∈ [517, 679, 704, 730, 756, 782, 1146, 1175, 1361, 1893] := by
    fin_cases i <;> decide
  have hOff : fixedLoaderWaitOffset site.wait.pc = 336 + 8 * stage.val := by
    rw [← hStage]
    fin_cases i <;> decide
  have hTarget := loaderFixedWaitOffset hp hX hTrue hWaitPc
  rw [hOff] at hTarget
  obtain ⟨exit, hSpin⟩ := actualCanonicalPoll hX hTrue
  have hTrace : TraceBefore X (g,5+k) (g,j) :=
    ⟨rfl, show 5 + k < j by omega, (List.getElem?_eq_some_iff.mp he).1⟩
  refine ⟨5+k, _, phase, scope, hTrue, ?_, ⟨hTrace, ?_⟩, hLower⟩
  · exact congrArg (fun loc => Kind.wait loc phase true true scope) hTarget
  · simp only [hTrue, Option.map_some, Kind.resume]
    exact ⟨_, exit, _, _, _, _, hTrue, hSpin, hTrace⟩

/-- Every actual Bias expectation passes a successful acquire of its own stage's
return object on the same loader lane, even in a prefix ending at the expectation. -/
theorem biasExpectationGuarded {cta : Nat} (stage : Fin 2) {issue : EvId}
    (hIssue : X.Arrive issue (Thread.Loader.biasReadyObject l cta stage) 32768 1 true .cta) :
    ∃ (guard : EvId) (e : Event) (phase : Nat) (scope : MbarScope),
      X.get guard = some e ∧
      e.kind = .wait (Thread.Loader.biasEmptyObject l cta stage) phase true true scope ∧
      Resumes kernel X guard issue := by
  obtain ⟨g, j⟩ := issue
  obtain ⟨k, e, phase, scope, hk, hWait, hResume, _⟩ :=
    biasExpectationGuardedSince hp hX stage none hIssue (by simp)
  exact ⟨(g,k), e, phase, scope, hk, hWait, hResume⟩

/-- Two Bias expectations on the same loader lane have a fresh matching stage acquire
between them. The earlier expectation can belong to either stage. -/
theorem biasExpectationGuardedAfterCredit {cta g a j : Nat} {before stage : Fin 2}
    (hPrior : X.Arrive (g,a) (Thread.Loader.biasReadyObject l cta before) 32768 1 true .cta)
    (hIssue : X.Arrive (g,j) (Thread.Loader.biasReadyObject l cta stage) 32768 1 true .cta)
    (hOrder : a < j) :
    ∃ (k : Nat) (e : Event) (phase : Nat) (scope : MbarScope), a < k ∧
      X.get (g,k) = some e ∧
      e.kind = .wait (Thread.Loader.biasEmptyObject l cta stage) phase true true scope ∧
      Resumes kernel X (g,k) (g,j) := by
  have hPrev : ∀ x, some a = some x → x < j ∧ ∃ s : Fin 2,
      X.Arrive (g,x) (Thread.Loader.biasReadyObject l cta s) 32768 1 true .cta := by
    intro x hx
    obtain rfl := Option.some.inj hx
    exact ⟨hOrder, before, hPrior⟩
  obtain ⟨k, e, phase, scope, hk, hWait, hResume, hFresh⟩ :=
    biasExpectationGuardedSince hp hX stage (some a) hIssue hPrev
  exact ⟨k, e, phase, scope, hFresh a rfl, hk, hWait, hResume⟩

/-- The actual loader lane issuing an expectation was selected by its full-mask election. -/
theorem biasExpectationSelectedIssuerWithStageFloor {g j cta : Nat} (stage : Fin 2)
    (hIssue : X.Arrive (g,j) (Thread.Loader.biasReadyObject l cta stage) 32768 1 true .cta) :
    ∃ k site inst, k < j ∧ 707 + 52 * stage.val ≤ site ∧
      X.Elect (g,k) site (2^32-1) inst (laneOf l g) := by
  obtain ⟨pc, he⟩ := hIssue
  obtain ⟨_, _, hLoc⟩ := actualArriveOffsetIn hp hX he
  have hOwner : cta = g / l.block := congrArg Loc.cta hLoc
  subst cta
  obtain ⟨i, warp, start, _, hStage, _, hIndex, hAt, hWalk, hGet⟩ :=
    biasExpectationWalk hp hX stage he
  have hBounds := biasGateBounds i
  have hRange : 174 ≤ start.pc ∧ start.pc ≤ 1901 := by rw [hAt.1]; decide
  have hBefore : BeforeBiasSelection i l g start := by
    intro hAct
    have hLo := hAct.1
    rw [hAt.1] at hLo
    dsimp [biasElectPc] at hLo
    dsimp only at hBounds
    omega
  obtain ⟨a, ha, elected, he, inst, hElect⟩ := loaderEventPrecededBy
    warp hWalk hRange (ringShapeOfAt hAt) hAt.2.2.2.2 hBefore hGet hBounds.2.2 (by
      intro t hBlocked hEq
      change t.pc = (biasGateSite i).expect at hEq
      have hAct : biasElectInterior i t.pc := by
        rw [hEq]
        dsimp [biasElectInterior, biasElectPc]
        dsimp only at hBounds
        omega
      obtain ⟨exit, steps, hExit⟩ := hBlocked hAct
      -- At the marked instruction a local transition cannot skip its unpredicated arrival.
      have hCode : ∃ ins, kernel.code[(biasGateSite i).expect]? = some ins ∧
          ins.guard = none ∧ ins.op.isLocal = false := by
        fin_cases i
        · exact ⟨_, Flow.code_711, rfl, rfl⟩
        · exact ⟨_, Flow.code_763, rfl, rfl⟩
        · exact ⟨_, Flow.code_1153, rfl, rfl⟩
        · exact ⟨_, Flow.code_1182, rfl, rfl⟩
        · exact ⟨_, Flow.code_1368, rfl, rfl⟩
      obtain ⟨ins, hc, hg, hl⟩ := hCode
      rcases Relation.ReflTransGen.cases_head steps with rfl | ⟨nextState, hTau, _⟩
      · omega
      · have hCore : Tau kernel [] l g t nextState := by
          unfold Tau at hTau ⊢
          rw [← loaderOutCore (by dsimp only at hBounds; omega) (by omega)]
          exact hTau
        have hC : kernel.code[t.pc]? = some ⟨none, ins.op⟩ := by
          rw [hEq]
          cases ins
          simp_all
        exact tau_core_not_event hC hl hCore)
      (fun hlo hhi hs _ => beforeBiasSelectionStep i hlo hhi hs)
  have he' : (X.tr g)[5+a]? = some elected := by simpa only [List.getElem?_drop] using he
  have hFloor : 707 + 52 * stage.val ≤ biasElectPc i := by
    rw [← hStage]
    fin_cases i <;> decide
  exact ⟨5+a, biasElectPc i, inst, by omega, hFloor, by rw [hElect] at he'; exact he'⟩

/-- Every Bias transaction expectation has an earlier full-warp election. -/
theorem biasExpectationSelectedIssuerWithFloor {g j cta : Nat} (stage : Fin 2)
    (hIssue : X.Arrive (g,j) (Thread.Loader.biasReadyObject l cta stage) 32768 1 true .cta) :
    ∃ k site inst, k < j ∧ 707 ≤ site ∧ X.Elect (g,k) site (2^32-1) inst (laneOf l g) := by
  obtain ⟨k,site,inst,hBefore,hFloor,hElect⟩ :=
    biasExpectationSelectedIssuerWithStageFloor hp hX stage hIssue
  exact ⟨k,site,inst,hBefore,by omega,hElect⟩

/-- The actual loader lane issuing an expectation was selected by its full-mask election. -/
theorem biasExpectationSelectedIssuer {g j cta : Nat} (stage : Fin 2)
    (hIssue : X.Arrive (g,j) (Thread.Loader.biasReadyObject l cta stage) 32768 1 true .cta) :
    ∃ k site inst, k < j ∧ X.Elect (g,k) site (2^32-1) inst (laneOf l g) := by
  obtain ⟨k,site,inst,hBefore,_,he⟩ := biasExpectationSelectedIssuerWithFloor hp hX stage hIssue
  exact ⟨k,site,inst,hBefore,he⟩

omit hp hX in
private theorem biasExpectationInRole (i : Fin 5) :
    ∃ gate : Fin 3, inBiasRole gate (biasGateSite i).expect := by
  fin_cases i
  · exact ⟨0, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨2, by decide⟩

/-- The second loader warp bypasses every Bias expectation site, including recurring sites. -/
theorem biasExpectationIssuerWarp {g j cta : Nat} (stage : Fin 2)
    (hIssue : X.Arrive (g,j) (Thread.Loader.biasReadyObject l cta stage) 32768 1 true .cta) :
    Prologue.warpIndex l g = 14 := by
  obtain ⟨pc, he⟩ := hIssue
  obtain ⟨_, _, hLoc⟩ := actualArriveOffsetIn hp hX he
  have hOwner : cta = g / l.block := congrArg Loc.cta hLoc
  subst cta
  obtain ⟨i, warp, start, _, _, hWarp, _, hAt, hWalk, hGet⟩ :=
    biasExpectationWalk hp hX stage he
  by_contra hWrong
  have hE : warp = 1 := Fin.ext (by have := warp.isLt; omega)
  subst warp
  have hRange : 174 ≤ start.pc ∧ start.pc ≤ 1901 := by rw [hAt.1]; decide
  have hBefore : BeforeBiasWarp15 start := by
    have hPc := hAt.1
    constructor
    · intro h _; omega
    · intro h _; omega
    · intro h; omega
    · intro gate
      rw [hPc]
      fin_cases gate <;> decide
  obtain ⟨gate, hIn⟩ := biasExpectationInRole i
  obtain ⟨_, _, _, _, hFalse⟩ := loaderEventPrecededBy 1 hWalk hRange
    (ringShapeOfAt hAt) hAt.2.2.2.2 (prior := fun _ => False) hBefore hGet (biasGateBounds i).2.2
    (fun hBlocked hEq => hBlocked.excluded gate (hEq.symm ▸ hIn))
    (fun hlo hhi hs hf hg hStep _ => beforeBiasWarp15Step hlo hhi hs hf.2.1 hg hStep)
  exact hFalse

/-- Regardless of stage or iteration, actual Bias expectations in one CTA select one loader lane. -/
theorem biasExpectationSameIssuer {g h i j cta : Nat} {sa sb : Fin 2}
    (ha : X.Arrive (g,i) (Thread.Loader.biasReadyObject l cta sa) 32768 1 true .cta)
    (hb : X.Arrive (h,j) (Thread.Loader.biasReadyObject l cta sb) 32768 1 true .cta) : g = h := by
  obtain ⟨_, _, _, _, hA⟩ := biasExpectationSelectedIssuer hp hX sa ha
  obtain ⟨_, _, _, _, hB⟩ := biasExpectationSelectedIssuer hp hX sb hb
  have hWA := biasExpectationIssuerWarp hp hX sa ha
  have hWB := biasExpectationIssuerWarp hp hX sb hb
  obtain ⟨_, hea⟩ := ha
  obtain ⟨_, heb⟩ := hb
  obtain ⟨_, _, hLoc⟩ := actualArriveOffsetIn hp hX hea
  obtain ⟨_, _, hLoc'⟩ := actualArriveOffsetIn hp hX heb
  have hCta : g / l.block = h / l.block :=
    (congrArg Loc.cta hLoc).symm.trans (congrArg Loc.cta hLoc')
  have hWarp : SameWarp l g h :=
    ⟨⟨event_thread_lt hX hea, event_thread_lt hX heb, hCta⟩,
      hWA.trans hWB.symm⟩
  exact selected_elect_thread_unique hX.elect hA hB hWarp rfl rfl


/-- A reached marked Bias instruction has the actual indexed loader-role walk. -/
theorem biasInstructionWalk {g j : Nat} {e : Event} (he : X.get (g,j) = some e)
    (hRange : 677 ≤ e.pc ∧ e.pc ≤ 1383) :
    ∃ (warp : Fin 2) (s : TState) (vs : List Visit),
      14 + warp.val = Prologue.warpIndex l g ∧ 5 ≤ j ∧
      At s 174 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop 5) vs ∧
      ((X.tr g).drop 5)[j - 5]? = some e := by
  have hHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hRole := roleBodyPcOfEvent hp hX he (by omega) hHint
  have hWarp : 14 ≤ Prologue.warpIndex l g := by
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  let warp : Fin 2 := ⟨Prologue.warpIndex l g - 14, by have := Prologue.warpIndex_lt hp g; omega⟩
  have hEq : 14 + warp.val = Prologue.warpIndex l g := Nat.add_sub_of_le hWarp
  obtain ⟨s, rest, hLength, hAt, hRun⟩ := Prologue.nonzeroCommonPrefixOfLateEvent hp hX
    (g := g) (index := j) (event_thread_lt hX he) (by omega) he (by omega)
  obtain ⟨vs, hWalk⟩ := Mma.walkFromRun hRun
  have hStart : At s 174 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] :=
    hAt.mono ⟨hAt.2.2.2.2.2.1, hEq.symm ▸ hAt.2.2.2.2.1, trivial⟩
  refine ⟨warp, s, vs, hEq, hLength, hStart, hWalk, ?_⟩
  rw [List.getElem?_drop, Nat.add_sub_of_le hLength]
  exact he

/-- The paired loader warp bypasses the actual instructions of every Bias transfer corridor. -/
theorem biasInstructionWarp {g j : Nat} {e : Event} (he : X.get (g,j) = some e)
    (hPc : 677 ≤ e.pc ∧ e.pc < 780 ∨ 1144 ≤ e.pc ∧ e.pc < 1203 ∨ 1359 ≤ e.pc ∧ e.pc < 1384)
    : Prologue.warpIndex l g = 14 := by
  have hRange : 677 ≤ e.pc ∧ e.pc ≤ 1383 := by rcases hPc with h | h | h <;> omega
  obtain ⟨warp, s, vs, hWarp, _, hAt, hWalk, hGet⟩ := biasInstructionWalk hp hX he hRange
  by_contra hBad
  have hE : warp = 1 := Fin.ext (by have := warp.isLt; omega)
  subst warp
  have hIn : ∃ k : Fin 3, inBiasRole k e.pc := by
    rcases hPc with h | h | h
    · exact ⟨0, by change 676 < e.pc ∧ e.pc < 780; omega⟩
    · exact ⟨1, by change 1143 < e.pc ∧ e.pc < 1203; omega⟩
    · exact ⟨2, by change 1358 < e.pc ∧ e.pc < 1384; omega⟩
  obtain ⟨gate, hGate⟩ := hIn
  have hBefore : BeforeBiasWarp15 s := by
    have hPc := hAt.1
    constructor
    · intro h _; omega
    · intro h _; omega
    · intro h; omega
    · intro gate
      rw [hPc]
      fin_cases gate <;> decide
  obtain ⟨_, _, _, _, impossible⟩ :=
    loaderEventPrecededBy 1 hWalk (by rw [hAt.1]; decide)
      (ringShapeOfAt hAt) hAt.2.2.2.2 (prior := fun _ => False) hBefore hGet (by omega)
      (fun hb h => hb.excluded gate (h.symm ▸ hGate))
      (fun hlo hhi hs hf hg hStep _ => beforeBiasWarp15Step hlo hhi hs hf.2.1 hg hStep)
  exact impossible
end

/-- A loader invariant initialized after an earlier actual event locates a required
intervening event in the same role walk. -/
theorem loaderEventBetween {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (warp : Fin 2)
    (hWalk : Walk kernel Assumptions.all l g s es vs)
    (hPc : 174 ≤ s.pc ∧ s.pc ≤ 1901) (hShape : RingShape s)
    (hFrame : Holds s.regs [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
    {start finish : Nat} {earlier mark : Event}
    (hStart : es[start]? = some earlier) (hEnd : es[finish]? = some mark)
    (hOrder : start < finish) (hEarlier : earlier.pc < 1901) (hLimit : mark.pc < 1901)
    {Q : TState → Prop} {prior : Event → Prop}
    (hInit : ∀ {t u}, EStep kernel Assumptions.all l g t earlier (some u) → Q u)
    (hExclude : ∀ {t}, Q t → t.pc ≠ mark.pc)
    (hStep : ∀ {t u : TState} {e : Option Event}, 174 ≤ t.pc → t.pc < 1901 → RingShape t →
      Holds t.regs [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] →
      Q t → WStep kernel Assumptions.all l g t e u → (∀ e' ∈ e.toList, ¬ prior e') → Q u) :
    ∃ k, start < k ∧ k < finish ∧ ∃ e, es[k]? = some e ∧ prior e := by
  induction hWalk generalizing start finish with
  | stop => simp at hStart
  | @tau s u es vs ht hw ih =>
    by_cases hExit : s.pc = 1901
    · exact (loaderGateTail warp hEarlier (.tau ht hw) hExit hShape hFrame
        (List.mem_of_getElem? hStart)).elim
    have hRange : 174 ≤ s.pc ∧ s.pc < 1901 := ⟨hPc.1, by omega⟩
    obtain ⟨hu, hs, hf⟩ := loaderGateStep warp hRange hShape hFrame (.inl ⟨rfl, ht⟩)
    exact ih hu hs hf hStart hEnd hOrder
  | @ev s u actual es vs ht hw ih =>
    by_cases hExit : s.pc = 1901
    · exact (loaderGateTail warp hEarlier (.ev ht hw) hExit hShape hFrame
        (List.mem_of_getElem? hStart)).elim
    have hRange : 174 ≤ s.pc ∧ s.pc < 1901 := ⟨hPc.1, by omega⟩
    obtain ⟨hu, hs, hf⟩ := loaderGateStep warp hRange hShape hFrame (.inr ⟨_, rfl, ht⟩)
    cases finish with
    | zero => omega
    | succ finish =>
      cases start with
      | zero =>
        obtain rfl := Option.some.inj hStart
        obtain ⟨k, hk, e, he, hPrior⟩ :=
          loaderEventPrecededBy warp hw hu hs hf (hInit ht) hEnd hLimit hExclude hStep
        exact ⟨k + 1, Nat.zero_lt_succ _, Nat.succ_lt_succ hk, e, he, hPrior⟩
      | succ start =>
        obtain ⟨k, hs, hf, e, he, hPrior⟩ :=
          ih hu hs hf hStart hEnd (Nat.lt_of_succ_lt_succ hOrder)
        exact ⟨k + 1, Nat.succ_lt_succ hs, Nat.succ_lt_succ hf, e, he, hPrior⟩
  | last ht =>
    have hLen := (List.getElem?_eq_some_iff.mp hEnd).1
    simp only [List.length_singleton] at hLen
    omega
end PTX.Kernels.TmlFa4Fwd.Loader
