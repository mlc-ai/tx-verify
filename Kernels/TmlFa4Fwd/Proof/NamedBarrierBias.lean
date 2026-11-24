-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.NamedBarrierSites
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

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Assumption PTX.Proof PTX.Flow PTX.EventFrame

private def biasBarPc (repeated : Bool) : Nat := if repeated then 5271 else 3583

private def biasBarDest (repeated : Bool) : Nat := if repeated then 4235 else 3075

private def biasBarPred (repeated : Bool) : Nat := if repeated then 631 else 481

private def biasBarSelect (repeated : Bool) : Op :=
  .int ⟨.selp, .int .b 32, false, [some (biasBarDest repeated)],
    [.imm 12, .imm 11, .reg (biasBarPred repeated)]⟩

private def biasBarOp (repeated : Bool) : Op :=
  .barSyncN (.reg (biasBarDest repeated)) (.imm 128) true

private theorem biasBarSelectCode (repeated : Bool) :
    kernel.code[biasBarPc repeated-1]? = some ⟨none, biasBarSelect repeated⟩ := by
  cases repeated
  · exact Flow.code_3582
  · exact Flow.code_5270

private theorem biasBarCode (repeated : Bool) :
    kernel.code[biasBarPc repeated]? = some ⟨none, biasBarOp repeated⟩ := by
  cases repeated
  · exact Flow.code_3583
  · exact Flow.code_5271

private theorem biasBarNoTarget (repeated : Bool) :
    kernel.branchTarget (biasBarPc repeated) = false := by
  cases repeated <;> decide +kernel

private theorem biasBarNoSegment (repeated : Bool) :
    Assumptions.swExp2Sites.all (fun pc => match cuteExp2.matchAt kernel pc with
      | none => false | some x => x.stop != biasBarPc repeated) = true := by
  cases repeated <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem ordinaryKernelEvents :
    kernel.code.all (fun ins => ins.op.isLocal || Epilogue.ordinaryEvent ins.op) = true := by
  decide +kernel

private theorem biasSelectRegs {l : Launch} {g : Nat} {s u : TState} (repeated : Bool)
    (hs : s.pc = biasBarPc repeated-1)
    (he : execLocalA Assumptions.all l g s (biasBarSelect repeated) = .ok u) :
    u.regs (biasBarDest repeated) = some (b32 11) ∨
      u.regs (biasBarDest repeated) = some (b32 12) := by
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hs]; cases repeated <;> decide
  rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff rfl,
    execLocalA_nil] at he
  simp only [biasBarSelect, execLocal, Op.rule, IntInstr.rule] at he
  cases h : s.regs (biasBarPred repeated) with
  | none => simp [execMove, readReg, h, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at he
  | some value =>
    cases value <;> simp [execMove, readReg, h, bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw] at he
    rename_i b
    cases b <;> simp [readValue, readBits, DType.width, pure, Except.pure, bind,
      Except.bind, Value.bytes, truncBits] at he <;>
      subst u <;> simp [next, setReg, b32]

private theorem biasBarReturning {l : Launch} {g : Nat} {s u : TState} {event : Event}
    (repeated : Bool)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (biasBarOp repeated)) event (some u)) :
    u.pc = s.pc+1 := by
  change Fires s.pc (barTmpl l g s (.reg (biasBarDest repeated)) (some (.imm 128)) .sync)
    event (some u) at hf
  unfold barTmpl at hf
  repeat' split at hf
  all_goals
    simp only [Fires] at hf
    first
    | exact (congrArg TState.pc (Option.some.inj hf.2)).trans rfl
    | exact False.elim (by cases hf.2)

private theorem biasBarLocal {l : Launch} {g : Nat} {s u : TState} (repeated : Bool)
    (hu : u.pc = biasBarPc repeated) (ht : Tau kernel Assumptions.all l g s u) :
    u.regs (biasBarDest repeated) = some (b32 11) ∨
      u.regs (biasBarDest repeated) = some (b32 12) := by
  obtain ⟨ins, hc, _, hSource⟩ := Softmax.tauScoreSource ht
  rcases hSource with ⟨rfl, hGuard⟩ | ⟨_, _, he⟩
  · have hS : s.pc = biasBarPc repeated-1 := by change s.pc+1 = _ at hu; omega
    rw [hS, biasBarSelectCode repeated] at hc
    obtain rfl := Option.some.inj hc.symm
    cases hGuard
  · rcases Softmax.scoreExecLocal he with hCore | ⟨m, hSite, hm, hM⟩
    · have hIncoming : u.pc = s.pc+1 :=
        LocalFrame.pc_succ hc hCore (hu.symm ▸ biasBarNoTarget repeated)
      have hS : s.pc = biasBarPc repeated-1 := by omega
      rw [hS, biasBarSelectCode repeated] at hc
      obtain rfl := Option.some.inj hc.symm
      exact biasSelectRegs repeated hS he
    · have hNo := List.all_eq_true.mp (biasBarNoSegment repeated) _ hSite
      rw [hm] at hNo
      have hP := (Softmax.scoreSegmentFrame hM).1
      simp [hP.symm.trans hu] at hNo

private theorem biasBarAfterEvent {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (repeated : Bool) (hu : u.pc = biasBarPc repeated)
    (he : EStep kernel Assumptions.all l g s e (some u)) : False := by
  obtain ⟨i, hc, hLocal, hF⟩ := estep_event_source he
  have hOp := List.all_eq_true.mp ordinaryKernelEvents _ (List.mem_of_getElem? hc)
  have hFrame := Epilogue.ordinaryEventFrame (by simpa only [hLocal, Bool.false_or] using hOp)
      (A := Assumptions.all) (l := l) (g := g) (s := s)
  rcases callbackFrame_fires hFrame hF with hh | hh
  · have hP : s.pc = biasBarPc repeated := hh.symm.trans hu
    rw [hP, biasBarCode repeated] at hc
    obtain rfl := Option.some.inj hc.symm
    have := biasBarReturning repeated hF
    omega
  · have hP : s.pc = biasBarPc repeated-1 := by omega
    rw [hP, biasBarSelectCode repeated] at hc
    obtain rfl := Option.some.inj hc.symm
    cases repeated <;> contradiction

private def BiasBarValue (repeated : Bool) (s : TState) : Prop :=
  s.pc = biasBarPc repeated →
    s.regs (biasBarDest repeated) = some (b32 11) ∨
      s.regs (biasBarDest repeated) = some (b32 12)

private theorem biasBarLocalChain {l : Launch} {g : Nat} {s u : TState} (repeated : Bool)
    (hs : BiasBarValue repeated s)
    (hSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u) :
    BiasBarValue repeated u := by
  induction hSteps with
  | refl => exact hs
  | tail _ ht _ => exact fun hu => biasBarLocal repeated hu ht

private theorem biasBarEvent {l : Launch} {g id : Nat} {s : TState}
    {count : Option Nat} {mode : BarMode} {o : Option TState} (repeated : Bool)
    (hb : l.block = 512) (hs : BiasBarValue repeated s)
    (he : EStep kernel Assumptions.all l g s ⟨biasBarPc repeated, .bar id count mode⟩ o) :
    id = 11 ∨ id = 12 := by
  have hPc : s.pc = biasBarPc repeated := (estep_source_pc he).symm
  have hCode := hPc.symm ▸ biasBarCode repeated
  obtain ⟨m, hOut, hFire⟩ := he
  cases hFault : s.fault with
  | some f =>
    simp only [out, hFault] at hOut
    obtain rfl := Out.ev.inj hOut
    exact Kind.noConfusion (congrArg Event.kind hFire.1)
  | none =>
    have hTmpl : m = barTmpl l g s (.reg (biasBarDest repeated)) (some (.imm 128)) .sync := by
      rw [out_event hFault hCode rfl rfl] at hOut
      exact (Out.ev.inj hOut).symm
    subst m
    have hAt (n : Nat) (hn : n < 16)
        (hReg : s.regs (biasBarDest repeated) = some (b32 n)) : id = n := by
      have hRead : readBits l g s 32 (.reg (biasBarDest repeated)) =
          .ok (BitVec.ofNat 64 n) := by
        simp [readBits, readReg, hReg, b32, pure, Except.pure, bind, Except.bind,
          truncBits_ofNat (show n < 2^32 by omega) (by decide)]
      have hn' : (BitVec.ofNat 64 n).toNat = n := toNat_ofNat_lt (by omega)
      have hImm : readBits l g s 32 (.imm 128) = .ok 128#64 := rfl
      have hT : barTmpl l g s (.reg (biasBarDest repeated)) (some (.imm 128)) .sync =
          Tmpl.bar n (next s) (some 128) .sync := by
        simp [barTmpl, hRead, hImm, hn', Nat.not_le_of_gt hn, hb]
      rw [hT] at hFire
      exact (Kind.bar.inj (congrArg Event.kind hFire.1)).1
    exact (hs hPc).imp (hAt 11 (by decide)) (hAt 12 (by decide))

private theorem biasBarRun {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {o : Option TState} (repeated : Bool) (hb : l.block = 512)
    (hs : BiasBarValue repeated s)
    (hr : Run kernel Assumptions.all l g s es o) :
    ∀ id count mode, (⟨biasBarPc repeated, .bar id count mode⟩ : Event) ∈ es →
      id = 11 ∨ id = 12 := by
  induction hr with
  | nil => simp
  | step hl he _ ih =>
    intro id count mode h
    rcases List.mem_cons.mp h with heq | hm
    · rw [← heq] at he
      exact biasBarEvent repeated hb (biasBarLocalChain repeated hs hl) he
    · exact ih (fun hPc => (biasBarAfterEvent repeated hPc he).elim) id count mode hm
  | last hl he =>
    intro id count mode h
    rw [← List.mem_singleton.mp h] at he
    exact biasBarEvent repeated hb (biasBarLocalChain repeated hs hl) he

/-- Both actual Bias rendezvous sites use barrier 11 or 12, including in finite traces. -/
theorem actualBiasBarrierId {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (repeated : Bool) {g j id : Nat} {count : Option Nat} {mode : BarMode}
    (hg : g < l.threads)
    (he : X.get (g, j) =
      some ⟨if repeated then 5271 else 3583, .bar id count mode⟩) :
    id = 11 ∨ id = 12 := by
  obtain ⟨o, hr⟩ := hX.thr g hg
  have hStart : BiasBarValue repeated {} := by
    intro hPc
    cases repeated <;> contradiction
  exact biasBarRun repeated hp.block hStart hr _ _ _ (List.mem_of_getElem? he)

end PTX.Kernels.TmlFa4Fwd
