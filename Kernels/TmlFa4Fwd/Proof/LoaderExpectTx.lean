-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderInputDescriptors
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
public import Lemmas.Flow.OpPcsFast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption

noncomputable section

private structure CreditSite where
  pc : Nat
  txReg : Nat
  base : Nat
  offset : Nat
  state : Nat

private def creditSite : Fin 8 → CreditSite
  | 0 => ⟨686, 1892, 2535, 0, 7579⟩
  | 1 => ⟨711, 1900, 1114, 0, 7584⟩
  | 2 => ⟨737, 1910, 2535, 8, 7589⟩
  | 3 => ⟨763, 1920, 2535, 328, 7594⟩
  | 4 => ⟨1153, 2041, 1140, 0, 7698⟩
  | 5 => ⟨1182, 2054, 2535, 328, 7703⟩
  | 6 => ⟨1368, 2123, 1142, 0, 7753⟩
  | 7 => ⟨1900, 2307, 2535, 8, 7861⟩

private def creditMove (site : CreditSite) : Op :=
  .move ⟨.scalar, .int .b 32, [some site.txReg], [.imm 32768]⟩

private def expectTx (site : CreditSite) : Op :=
  .mbarArrive site.base site.offset (.reg site.txReg) (.imm 1) false true .cta (some site.state)

private theorem creditInstructions :
    (List.ofFn fun j : Fin 8 => (kernel.code[(creditSite j).pc - 1]?,
      kernel.code[(creditSite j).pc]?)) =
    (List.ofFn fun j : Fin 8 => (some ⟨none, creditMove (creditSite j)⟩,
      some ⟨none, expectTx (creditSite j)⟩)) := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem creditMoveCode (j : Fin 8) :
    kernel.code[(creditSite j).pc - 1]? = some ⟨none, creditMove (creditSite j)⟩ := by
  have h := congrArg (fun xs : List (Option Instr × Option Instr) => xs[j.val]?.map Prod.fst)
    creditInstructions
  simpa only [List.getElem?_ofFn, j.isLt, ↓reduceDIte, Option.map_some, Option.some.injEq] using h

private theorem expectTxCode (j : Fin 8) :
    kernel.code[(creditSite j).pc]? = some ⟨none, expectTx (creditSite j)⟩ := by
  have h := congrArg (fun xs : List (Option Instr × Option Instr) => xs[j.val]?.map Prod.snd)
    creditInstructions
  simpa only [List.getElem?_ofFn, j.isLt, ↓reduceDIte, Option.map_some, Option.some.injEq] using h

private theorem noTarget (j : Fin 8) : kernel.branchTarget (creditSite j).pc = false := by
  fin_cases j <;> decide +kernel

private theorem loaderPc (j : Fin 8) : 0 < (creditSite j).pc ∧ (creditSite j).pc < 1904 := by
  fin_cases j <;> decide

private theorem segmentAfterLoader :
    Assumptions.swExp2Sites.all (fun pc => match cuteExp2.matchAt kernel pc with
      | none => false | some x => decide (1904 ≤ x.stop)) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private def CreditAt (j : Fin 8) (t : TState) : Prop :=
  t.pc = (creditSite j).pc → t.regs (creditSite j).txReg = some (b32 32768)

private theorem creditAfterTau {l : Launch} {g : Nat} {s u : TState} (j : Fin 8)
    (ht : Tau kernel Assumptions.all l g s u) : CreditAt j u := by
  intro hu
  obtain ⟨ins, hc, _, hStep⟩ := Softmax.tauScoreSource ht
  rcases hStep with ⟨rfl, hSkipped⟩ | ⟨_, _, hExec⟩
  · have hp : s.pc = (creditSite j).pc - 1 := by change s.pc + 1 = _ at hu; omega
    rw [hp, creditMoveCode j] at hc
    obtain rfl := Option.some.inj hc.symm
    cases hSkipped
  · rcases Softmax.scoreExecLocal hExec with hFrame | ⟨segment, hSite, hMatch, hRun⟩
    · have hu' := PTX.LocalFrame.pc_succ hc hFrame (hu.symm ▸ noTarget j)
      have hp : s.pc = (creditSite j).pc - 1 := by omega
      rw [hp, creditMoveCode j] at hc
      obtain rfl := Option.some.inj hc.symm
      have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hp]; fin_cases j <;> decide
      rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff rfl,
        execLocalA_nil] at hExec
      have hU : u = next (setReg s (creditSite j).txReg (b32 32768)) := by
        unfold creditMove at hExec
        rw [execLocal_move rfl] at hExec
        have hMove : execMove l g s (Op.move
            ⟨.scalar, .int .b 32, [some (creditSite j).txReg], [.imm 32768]⟩) =
            .ok (next (setReg s (creditSite j).txReg (b32 32768))) := by
          simp [execMove, readValue, readBits, DType.width,
            Value.bytes, truncBits, b32, bind, Except.bind, pure, Except.pure]
        exact (Except.ok.inj (hMove.symm.trans hExec)).symm
      rw [hU]
      exact Function.update_self _ _ _
    · have hAway := List.all_eq_true.mp segmentAfterLoader _ hSite
      rw [hMatch] at hAway
      have hStop : 1904 ≤ segment.stop := of_decide_eq_true hAway
      have hAt := (Softmax.scoreSegmentFrame hRun).1
      have hPc := (loaderPc j).2
      omega

private theorem eventCoverage :
    kernel.code.all (fun ins => ins.op.isLocal || Epilogue.ordinaryEvent ins.op) = true := by
  decide +kernel

private theorem otherEventCannotEnter {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (j : Fin 8) (he : EStep kernel Assumptions.all l g s e (some u))
    (hu : u.pc = (creditSite j).pc) : False := by
  obtain ⟨ins, hc, hLocal, hf⟩ := estep_event_source he
  have hOp := List.all_eq_true.mp eventCoverage _ (List.mem_of_getElem? hc)
  have hFrame := Epilogue.ordinaryEventFrame (by simpa only [hLocal, Bool.false_or] using hOp)
    (A := Assumptions.all) (l := l) (g := g) (s := s)
  rcases callbackFrame_fires hFrame hf with hSame | hNext
  · have hp := hSame.symm.trans hu
    rw [hp, expectTxCode j] at hc
    obtain rfl := Option.some.inj hc.symm
    unfold expectTx at hf
    have hReturn := (fires_arrive_state hf).1
    have hu' : u.pc = s.pc + 1 := congrArg TState.pc hReturn
    omega
  · have hp : s.pc = (creditSite j).pc - 1 := by omega
    rw [hp, creditMoveCode j] at hc
    obtain rfl := Option.some.inj hc.symm
    have : (creditMove (creditSite j)).isLocal = true := rfl
    rw [this] at hLocal
    cases hLocal

private theorem creditAtTauChain {l : Launch} {g : Nat} {s u : TState}
    (j : Fin 8) (h : CreditAt j s)
    (hSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u) : CreditAt j u := by
  induction hSteps with
  | refl => exact h
  | tail _ ht _ => exact creditAfterTau j ht

private theorem firesExactCredit {l : Launch} {g pc : Nat} {t : TState}
    {site : CreditSite} {o : Option TState} {loc : Loc} {tx count : Nat} {release : Bool}
    {scope : MbarScope} (hReg : t.regs site.txReg = some (b32 32768))
    (hf : Fires pc (eventTmpl Assumptions.all l g t (expectTx site))
      ⟨pc, .arrive loc tx count release scope⟩ o) :
    tx = 32768 ∧ count = 1 ∧ release = true ∧ scope = .cta := by
  have hTx := readBits_b32 (L := l) (g := g) hReg (by decide : 32768 < 2^32)
  have hN : readBits l g t 32 (.imm 1) = .ok 1#64 := rfl
  have hScope : (Assumptions.all.any (·.clusterScopeMbar t.pc)) = false := rfl
  simp only [expectTx, eventTmpl, tmaTmpl, Bool.false_eq_true, ↓reduceIte, hTx, hN,
    widenMbarScope, hScope, bind, Except.bind, pure, Except.pure] at hf
  cases hLoc : mbarLoc l g t site.base site.offset with
  | error f => simp [hLoc, ofExec, Fires] at hf
  | ok dst =>
    simp only [hLoc, ofExec, Fires, Event.mk.injEq, Kind.arrive.injEq] at hf
    exact hf.1.2.2

private theorem creditInRun {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {o : Option TState} (j : Fin 8) (hs : CreditAt j s)
    (hr : Run kernel Assumptions.all l g s es o) :
    ∀ loc tx count release scope, (⟨(creditSite j).pc, .arrive loc tx count release scope⟩ : Event)
      ∈ es → tx = 32768 ∧ count = 1 ∧ release = true ∧ scope = .cta := by
  have issue {t : TState} {loc : Loc} {tx count : Nat} {release : Bool} {scope : MbarScope}
      {next : Option TState} (h : CreditAt j t)
      (he : EStep kernel Assumptions.all l g t
        ⟨(creditSite j).pc, .arrive loc tx count release scope⟩ next) :
      tx = 32768 ∧ count = 1 ∧ release = true ∧ scope = .cta := by
    have ht : t.pc = (creditSite j).pc := (estep_source_pc he).symm
    obtain ⟨tmpl, hOut, hf⟩ := he
    rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
    · exact Kind.noConfusion (congrArg Event.kind hf.1)
    rw [ht, expectTxCode j] at hc
    obtain rfl := Option.some.inj hc.symm
    exact firesExactCredit (h ht) (ht ▸ hf)
  induction hr with
  | nil => simp
  | step hl he _ ih =>
    intro loc tx count rel scope hm
    rcases List.mem_cons.mp hm with heq | hMem
    · rw [← heq] at he
      exact issue (creditAtTauChain j hs hl) he
    · exact ih (fun hu => (otherEventCannotEnter j he hu).elim) loc tx count rel scope hMem
  | last hl he =>
    intro loc tx count rel scope hm
    rw [← List.mem_singleton.mp hm] at he
    exact issue (creditAtTauChain j hs hl) he

/-- A loader expect-tx issues one release and credits two 16 KiB subboxes. -/
theorem actualLoaderCredit {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {pc tx count : Nat} {loc : Loc} {release : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨pc, .arrive loc tx count release scope⟩)
    (hPc : pc ∈ [686, 711, 737, 763, 1153, 1182, 1368, 1900]) :
    tx = 32768 ∧ count = 1 ∧ release = true ∧ scope = .cta := by
  have hs : pc ∈ List.ofFn (fun j : Fin 8 => (creditSite j).pc) := hPc
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
  have hg := event_thread_lt hX he
  obtain ⟨_, hr⟩ := hX.thr i.1 hg
  have hInit : CreditAt j ({} : TState) := by
    intro h
    have hp := (loaderPc j).1
    change 0 = _ at h
    omega
  exact creditInRun j hInit hr _ _ _ _ _ (List.mem_of_getElem? he)

end
end PTX.Kernels.TmlFa4Fwd.Loader
