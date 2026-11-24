-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.Base
public import Lemmas.Flow.Fire
public import Lemmas.Flow.Resource

@[expose] public section

/-!
# The kind of a thread's next event

The progress layer classifies a released pending thread by the kind of its next event. The kind is
read off the instruction at the machine state's site (`TSt.pc`) and its sub-step (`TSt.sub`):
`opKind` is a function of the instruction alone, not a table of the sites, so the classification
needs no per-role enumeration. The audit `kernel_kinds` (by `decide +kernel`) shows that every
instruction of the decoded program that is not local has a kind other than `.other`.

`KindTmpl` names the templates of each kind. The template at a concrete state of a machine state is
undefined behaviour or of the state's kind (`tmpl_kind`): this is `Flow.eventTmpl_opTmpl` plus the
`tcgen05.st` and `tcgen05.wait::st` templates, and the allocation, whose first sub-step requests
the allocation (`.tmem`) and whose second stores the address (`.allocStore`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

/-- The kind of a thread's next event. -/
inductive NextKind where
  /-- An mbarrier poll. -/
  | wait
  /-- A warp collective: a shuffle, an election, the warp barrier, a vote. -/
  | warp
  /-- A named barrier `bar.sync` or `bar.arrive`. -/
  | bar
  /-- A register request. -/
  | reg
  /-- A paired Tensor Memory operation (allocation request, relinquishment, deallocation). -/
  | tmem
  /-- An mbarrier initialization. -/
  | init
  /-- An mbarrier arrival. -/
  | arrive
  /-- A TMA load. -/
  | tensorLoad
  /-- An MMA. -/
  | mma
  /-- A Tensor Core commit. -/
  | commit
  /-- A Tensor Memory load or its wait (`tcgen05.ld`, `tcgen05.wait::ld`). -/
  | tcLoad
  /-- A Tensor Memory store or its wait (`tcgen05.st`, `tcgen05.wait::st`). -/
  | tcStore
  /-- A read without acquire-release semantics beyond acquire (a load). -/
  | read
  /-- A fence or a bulk commit. -/
  | quiet
  /-- A store without release semantics. -/
  | store
  /-- The allocation's store of its address. -/
  | allocStore
  /-- The thread's exit. -/
  | exit
  /-- An instruction the classification does not cover. -/
  | other
  deriving DecidableEq

/-- The kind of the event of an instruction. -/
def opKind : Op → NextKind
  | .mbarWait .. => .wait
  | .warp ⟨.shfl _, _, _, _, _⟩ | .warp ⟨.elect, _, _, _, _⟩ | .warp ⟨.barWarp, _, _, _, _⟩
  | .warp ⟨.vote .ballot _, _, _, _, _⟩ => .warp
  | .barSync .. | .barSyncN .. | .barArrive .. => .bar
  | .setMaxReg .. => .reg
  | .tcAlloc .. | .tcDealloc .. | .tcRelinquish .. => .tmem
  | .mbarInit .. => .init
  | .mbarArrive .. => .arrive
  | .cpTensor .. => .tensorLoad
  | .tcMma .. => .mma
  | .tcCommit .. => .commit
  | .tcLd .. | .tcWaitLd => .tcLoad
  | .tcSt .. | .tcWaitSt => .tcStore
  | .mem a =>
    if a.kind == .load && a.space != some .param && !a.nc && (a.sem == .weak || a.sem == .acquire)
    then .read
    else if a.kind == .store && a.sem == .weak then .store else .other
  | .fence (.proxy (.async (some (.shared .cta))) none none) | .fenceMbarInit | .bulkCommit =>
    .quiet
  | .ret | .exit => .exit
  | _ => .other

/-- The kind of the event of an instruction at sub-step `n`: the allocation's second sub-step
stores its address. -/
def opKindSub (op : Op) (n : Nat) : NextKind :=
  match op with
  | .tcAlloc .. => if n = 0 then .tmem else .allocStore
  | _ => opKind op

/-- The sub-step of a machine state. -/
def TSt.sub : TSt → Nat
  | .d s => DComp.sub s
  | .w s => WComp.sub s

/-- The kind of the next event of a thread in machine state `s`. -/
def nextKind (s : TSt) : NextKind :=
  match kernel.code[TSt.pc s]? with
  | some ins => opKindSub ins.op (TSt.sub s)
  | none => .other

/-- The templates of an event of each kind, apart from undefined behaviour. -/
def KindTmpl : NextKind → Tmpl → Prop
  | .wait, m => ∃ l p k a s, m = .wait l p k a s
  | .warp, m => (∃ md a b c k, m = .shfl md a b c k) ∨ (∃ mask k, m = .elect mask k) ∨
    (∃ mask t, m = .warpBar mask t) ∨ ∃ mask a k, m = .vote mask a k
  | .bar, m => ∃ id t c md, m = .bar id t c md
  | .reg, m => ∃ inc n t, m = .setMaxReg inc n t
  | .tmem, m => ∃ grp dst act t, m = .tc (.resource grp dst act) t
  | .init, m => ∃ l c t, m = .mbInit l c t
  | .arrive, m => ∃ l tx t c r s, m = .arrive l tx t c r s
  | .tensorLoad, m => ∃ a s t, m = .tensorIssue a s t
  | .mma, m => ∃ d s acc ms t, m = .tc (.mma d s acc ms) t
  | .commit, m => ∃ s t, m = .tc (.commit s) t
  | .tcLoad, m => (∃ a n sh k, m = .tcLd a n sh k) ∨ ∃ t, m = .tc .waitLd t
  | .tcStore, m => (∃ a vs sh t, m = .tc (.st a vs sh) t) ∨ ∃ t, m = .tc .waitSt t
  | .read, m => ∃ a k, m = .read a k
  | .quiet, m => (∃ t, m = .fenceProxy (.async (some (.shared .cta))) none t) ∨
    (∃ t, m = .fenceMbarInit t) ∨ ∃ t, m = .bulkCommit t
  | .store, m => ∃ a bs t, m = .write a bs t ∧ a.release = false
  | .allocStore, m => ∃ dst t, m = .tcAllocStore dst t
  | .exit, m => m = .exit
  | .other, _ => False

/-- **Every instruction of the program that is not local has a kind.** -/
theorem kernel_kinds :
    kernel.code.all (fun ins => ins.op.isLocal || decide (opKind ins.op ≠ .other)) = true := by
  decide +kernel

/-- The `tcgen05.st` template at a site no assumption precedes by a load wait: undefined
behaviour or the store. -/
theorem eventTmpl_tcSt {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {ta : Nat}
    {ss : List Opnd} {sh : TcShape} (hw : A.any (·.tcStWaitLd t.pc) = false) :
    (∃ f, eventTmpl A L g t (.tcSt ta ss sh) = .ub f) ∨
      ∃ a vs u, eventTmpl A L g t (.tcSt ta ss sh) = .tc (.st a vs sh) u := by
  rw [eventTmpl_tcSt_noWait hw]
  simp only [tcTmpl, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw]
  repeat' (first | split | simp [ofExec] | simp_all)

/-- The `tcgen05.wait::st` template: undefined behaviour or the wait. -/
theorem eventTmpl_tcWaitSt {A : List Assumption} {L : Launch} {g : Nat} {t : TState} :
    (∃ f, eventTmpl A L g t .tcWaitSt = .ub f) ∨
      ∃ u, eventTmpl A L g t .tcWaitSt = .tc .waitSt u := by
  simp only [eventTmpl, tcTmpl, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw]
  repeat' (first | split | simp [ofExec])

end

end PTX.Kernels.InklingRelDecode.Proof.Progress
