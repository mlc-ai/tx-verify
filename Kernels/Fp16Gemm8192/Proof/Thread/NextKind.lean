-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Machine
public import Lemmas.Flow.Fire

@[expose] public section

/-! # The kind of a thread's next event

The kind of a thread's next event is fixed by the site of its machine state (`nextKind`): one of
the mbarrier waits, a cluster barrier operation, a named barrier arrival, a register request, a
paired Tensor Memory operation, a warp-synchronous collective, an mbarrier arrival or
initialization, a copy, MMA, commit or cancellation issue, a Tensor Memory load, a read, a plain
event, or the exit. The instruction at a site of kind `k` is one `kindOp k` accepts, and the
template it fires is undefined behaviour or one of kind `k` (`KindTmpl`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX

/-- The kind of a thread's next event, by the site of its machine state. -/
inductive NextKind where
  /-- A loader's empty poll of a slot. -/
  | emptyWait
  /-- An MMA thread's full poll of a slot. -/
  | fullWait
  /-- An MMA thread's accumulator-empty poll. -/
  | mmaAccWait
  /-- A consumer's accumulator-full poll. -/
  | consAccWait
  /-- A role's CLC response poll. -/
  | clcWait
  /-- The scheduler's acknowledgement poll. -/
  | ackWait
  /-- A cluster barrier arrival or wait. -/
  | cluster
  /-- A consumer's named barrier arrival. -/
  | bar
  /-- A register request. -/
  | reg
  /-- A paired Tensor Memory operation (allocation, relinquishment, deallocation). -/
  | tmem
  /-- A warp-synchronous collective: the shuffle, an election, the warp barrier. -/
  | warp
  /-- A loader's final empty poll of a slot, after its last task. -/
  | drainWait
  /-- An mbarrier arrival (a slot's full arrival, an acknowledgement, the response arrival,
  the accumulator arrival). -/
  | arrive
  /-- An mbarrier initialization. -/
  | init
  /-- A TMA load. -/
  | tensorLoad
  /-- A TMA store. -/
  | tensorStore
  /-- An MMA. -/
  | mma
  /-- A Tensor Core commit. -/
  | commit
  /-- A cancellation request. -/
  | clcIssue
  /-- A bulk async-group wait. -/
  | bulkWait
  /-- A Tensor Memory load or its wait (`tcgen05.ld`, `tcgen05.wait::ld`). -/
  | tcLoad
  /-- A read of shared memory (the CLC response, the Tensor Memory base). -/
  | read
  /-- A fence, a CLC response query, a store to shared memory, a bulk commit, the allocation's
  write of its column. -/
  | plain
  /-- The thread's exit. -/
  | exit
  deriving DecidableEq

/-- The kind of a prologue site's event. -/
def prologueKind : Prologue.Site → NextKind
  | .shfl | .elect | .warpBar | .roleElect => .warp
  | .init _ => .init
  | .alloc => .tmem
  | .allocWrite | .fence | .fenceInit => .plain
  | .arrive | .wait => .cluster
  | .setMaxReg => .reg

/-- The kind of a loader site's event. -/
def loaderKind : Loader.Site → NextKind
  | .wait _ => .emptyWait
  | .load _ _ => .tensorLoad
  | .arrive _ | .ack => .arrive
  | .clcWait => .clcWait
  | .clcLoad => .read
  | .clcStatus | .clcFirst | .clcFence => .plain
  | .drain _ => .drainWait
  | .exitArrive | .exitWait => .cluster
  | .exit => .exit

/-- The kind of an MMA site's event. -/
def mmaKind : Mma.Site → NextKind
  | .elect => .warp
  | .clcWait => .clcWait
  | .clcLoad => .read
  | .clcStatus | .clcFirst | .clcFence => .plain
  | .ack => .arrive
  | .accWait => .mmaAccWait
  | .full _ => .fullWait
  | .mma _ _ => .mma
  | .commit _ | .accCommit => .commit
  | .exitArrive | .exitWait => .cluster
  | .exit => .exit

/-- The kind of a scheduler site's event. -/
def schedKind : Scheduler.Site → NextKind
  | .elect => .warp
  | .ackWait => .ackWait
  | .tryCancel => .clcIssue
  | .arriveTx | .ack => .arrive
  | .clcWait => .clcWait
  | .clcLoad => .read
  | .clcStatus | .clcFirst | .clcFence => .plain
  | .exitArrive | .exitWait => .cluster
  | .exit => .exit

/-- The kind of a consumer site's event. -/
def consKind : Consumer.Site → NextKind
  | .setMaxReg => .reg
  | .clcWait => .clcWait
  | .clcLoad | .ldBase => .read
  | .clcStatus | .clcFirst | .clcFence | .store _ _ _ | .fence _ | .commit _ => .plain
  | .clcBar | .barA _ | .barB _ => .bar
  | .ack | .accArrive => .arrive
  | .accWait => .consAccWait
  | .load _ | .loadWait _ => .tcLoad
  | .drain _ | .finalDrain => .bulkWait
  | .tma _ => .tensorStore
  | .exitArrive | .exitWait => .cluster
  | .relinquish | .dealloc => .tmem
  | .exit => .exit

/-- The kind of the next event of a thread in state `d`. -/
def nextKind : ThreadD → NextKind
  | .inl p => prologueKind p.site
  | .inr (.loader l) => loaderKind l.site
  | .inr (.mma m) => mmaKind m.site
  | .inr (.sched s) => schedKind s.site
  | .inr (.cons c) => consKind c.site

/-- The instructions at a site of each kind. -/
def kindOp : NextKind → Op → Bool
  | .emptyWait, .mbarWait .. | .fullWait, .mbarWait .. | .mmaAccWait, .mbarWait ..
  | .consAccWait, .mbarWait .. | .clcWait, .mbarWait .. | .ackWait, .mbarWait ..
  | .drainWait, .mbarWait .. => true
  | .cluster, .cluster _ => true
  | .bar, .barSyncN .. => true
  | .reg, .setMaxReg .. => true
  | .tmem, .tcAlloc .. | .tmem, .tcDealloc .. | .tmem, .tcRelinquish .. => true
  | .warp, .warp { kind := .shfl _, .. } | .warp, .warp { kind := .elect, .. }
  | .warp, .warp { kind := .barWarp, .. } => true
  | .arrive, .mbarArrive .. => true
  | .init, .mbarInit .. => true
  | .tensorLoad, .cpTensor .. => true
  | .tensorStore, .cpTensorStore .. => true
  | .mma, .tcMma .. => true
  | .commit, .tcCommit .. => true
  | .clcIssue, .clcTryCancel .. => true
  | .bulkWait, .bulkWait .. => true
  | .tcLoad, .tcLd .. | .tcLoad, .tcWaitLd => true
  | .read, .mem { kind := .load, sem := .acquire, nc := false, .. }
  | .read, .mem { kind := .load, sem := .weak, nc := false, .. } => true
  | .plain, .fence (.proxy ..) | .plain, .fenceMbarInit | .plain, .clcQuery ..
  | .plain, .mem { kind := .store, sem := .weak, .. } | .plain, .bulkCommit
  | .plain, .tcAlloc .. => true
  | .exit, .ret => true
  | _, _ => false

/-- The templates of an event of each kind of thread `g`, apart from undefined behaviour. -/
def KindTmpl (L : Launch) (g : Nat) : NextKind → Tmpl → Prop
  | .emptyWait, m | .fullWait, m | .mmaAccWait, m | .consAccWait, m | .clcWait, m
  | .ackWait, m | .drainWait, m => ∃ l p k a s, m = .wait l p k a s
  | .cluster, m => ∃ op t, m = .cluster op t
  | .bar, m => ∃ id t c, m = .bar id t c
  | .reg, m => ∃ inc n t, m = .setMaxReg inc n t
  | .tmem, m => ∃ grp dst act t, m = .tc (.resource grp dst act) t
  | .warp, m => (∃ md a b c k, m = .shfl md a b c k) ∨ (∃ mask k, m = .elect mask k) ∨
    ∃ mask t, m = .warpBar mask t
  | .arrive, m => ∃ l tx t c r s, m = .arrive l tx t c r s
  | .init, m => ∃ l c t, m = .mbInit l c t
  | .tensorLoad, m => ∃ a s t, m = .tensorIssue a s t
  | .tensorStore, m => ∃ a s t, m = .tensorStore a s t
  | .mma, m => ∃ d s acc ms t, m = .tc (.mma d s acc ms) t
  | .commit, m => ∃ s t, m = .tc (.commit s) t
  | .clcIssue, m => ∃ s ts t, m = .clcIssue s ts t ∧ Flow.CancelSpec L g s ts
  | .bulkWait, m => ∃ md n t, m = .bulkWait md n t
  | .tcLoad, m => (∃ a n sh k, m = .tcLd a n sh k) ∨ ∃ t, m = .tc .waitLd t
  | .read, m => ∃ a k, m = .read a k
  | .plain, m => (∃ k o t, m = .fenceProxy k o t) ∨ (∃ t, m = .fenceMbarInit t) ∨
    (∃ q r t, m = .clcQuery q r t) ∨ (∃ a bs t, m = .write a bs t ∧ a.release = false) ∨
    (∃ dst t, m = .tcAllocStore dst t) ∨ ∃ t, m = .bulkCommit t
  | .exit, m => m = .exit

/-- An event of an instruction a kind accepts is of that kind; the allocation is of the kind
whose templates it fires (the request, or the store of its address). -/
theorem kindTmpl_of {L : Launch} {g : Nat} {k : NextKind} {op : Op} {m : Tmpl}
    (hk : kindOp k op = true) (h : Flow.OpEv L g op m)
    (halloc : ∀ grp b o nc, op = .tcAlloc grp b o nc →
      (k = .plain → Flow.NotResource m) ∧ (k = .tmem → ∀ dst t, m ≠ .tcAllocStore dst t)) :
    KindTmpl L g k m := by
  cases k <;> cases op <;> (try simp only [kindOp, Bool.false_eq_true] at hk)
  case read.mem a =>
    obtain ⟨kd, _, sem, _, _, _, _, nc, _, _, _, _, _⟩ := a
    cases kd <;> cases sem <;> cases nc <;> simp only [Bool.false_eq_true] at hk
    · obtain ⟨a, k, rfl, -⟩ := h
      exact ⟨a, k, rfl⟩
    · exact h
  case plain.mem a =>
    obtain ⟨kd, _, sem, _, _, _, _, _, _, _, _, _, _⟩ := a
    cases kd <;> cases sem <;> simp only [Bool.false_eq_true] at hk
    exact .inr (.inr (.inr (.inl h)))
  case warp.warp w =>
    obtain ⟨kd, _, _, _, _⟩ := w
    cases kd <;> simp only [Bool.false_eq_true] at hk
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  case plain.fence f =>
    cases f <;> simp only [Bool.false_eq_true] at hk
    obtain ⟨t, rfl⟩ := h
    exact .inl ⟨_, _, t, rfl⟩
  case tmem.tcAlloc grp b o nc =>
    rcases h with ⟨grp', dst, n, t, rfl⟩ | ⟨dst, t, rfl⟩
    · exact ⟨grp', some dst, .alloc n, t, rfl⟩
    · exact absurd rfl ((halloc grp b o nc rfl).2 rfl dst t)
  case plain.tcAlloc grp b o nc =>
    rcases h with ⟨grp', dst, n, t, rfl⟩ | h
    · exact ((halloc grp b o nc rfl).1 rfl : False).elim
    · exact .inr (.inr (.inr (.inr (.inl h))))
  case tmem.tcDealloc =>
    obtain ⟨grp, act, t, rfl, -⟩ := h
    exact ⟨grp, none, act, t, rfl⟩
  case tmem.tcRelinquish =>
    obtain ⟨grp, act, t, rfl, -⟩ := h
    exact ⟨grp, none, act, t, rfl⟩
  all_goals simp only [KindTmpl]
  all_goals first
    | exact h
    | exact .inr h
    | exact .inr (.inl h)
    | exact .inr (.inr (.inl h))
    | exact .inr (.inr (.inr (.inr (.inr h))))
    | exact ⟨_, h⟩

end PTX.Kernels.Fp16Gemm8192.Proof
