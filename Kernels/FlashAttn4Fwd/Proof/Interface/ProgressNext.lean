-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tmem
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStatic
public import Lemmas.Order.Order
public import Lemmas.Tcgen05.TcMmaSource

@[expose] public section

/-! # What the progress layer needs of a thread's next event

The kind of a thread's next event is fixed by the site of its machine state (`nextKind`, a
table per role): an mbarrier poll, a warp collective (shuffle, election, warp barrier, vote), a
cluster barrier operation, a named barrier (`bar.sync`, `bar.arrive`), a register request, a
paired Tensor Memory operation, an mbarrier initialization or arrival, a tensor copy or store
issue, an MMA, a commit, a bulk-group wait, a Tensor Memory load or its wait, a Tensor Memory
store or its wait, a read of shared memory, a fence or bulk commit, a store to shared memory, the
allocation's store of its address, or the exit. `KindTmpl` names the templates of each kind.

`NextFacts` holds what the progress classes of the released threads use, for one execution,
beside the exports of `ProgressAsync.lean` (polls spin, writes do not release):

* `fire`: a thread at its trace's end reaches, by local steps, a concrete state of its machine
  state whose template is undefined behaviour or of its site's kind;
* `alloc_next`: a thread whose last event is an allocation request is at the allocation's
  address store, or is not lane 0 of its warp (the other lanes continue at a named barrier);
* `reg_entry`: a thread at a register request has made none, and its last event is the
  prologue's cluster wait.

The facts of the execution as a whole that the same classes use (the order of the conflicts at
the bytes that are read, the 4-byte words of Tensor Memory, the column of the allocation) are not
thread facts: `Progress.NextSafe` states them, and the root proves them from the safety goal. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The kind of a thread's next event, by the site of its machine state. -/
inductive NextKind where
  /-- An mbarrier poll. -/
  | wait
  /-- A warp collective: a shuffle, an election, the warp barrier, a vote. -/
  | warp
  /-- A cluster barrier arrival or wait. -/
  | cluster
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
  /-- A TMA store. -/
  | tensorStore
  /-- An MMA. -/
  | mma
  /-- A Tensor Core commit. -/
  | commit
  /-- A bulk async-group wait. -/
  | bulkWait
  /-- A Tensor Memory load or its wait (`tcgen05.ld`, its implicit `tcgen05.wait::ld`). -/
  | tcLoad
  /-- A Tensor Memory store or its wait (`tcgen05.st`, `tcgen05.wait::st`). -/
  | tcStore
  /-- A read of shared memory without acquire semantics. -/
  | read
  /-- A fence or a bulk commit. -/
  | quiet
  /-- A store to shared memory without release semantics. -/
  | store
  /-- The allocation's store of its address. -/
  | allocStore
  /-- The thread's exit. -/
  | exit
  deriving DecidableEq

/-- The kind of a prologue site's event. -/
def prologueKind : Prologue.Site → NextKind
  | .shfl0 | .shfl1 | .shfl2 | .shfl3 | .elect12 | .elect _ => .warp
  | .init320 | .init _ => .init
  | .fence0 | .fence1 => .quiet
  | .clArrive | .clWait => .cluster

/-- The kind of an idle warp site's event. -/
def idleKind : Idle.Site → NextKind
  | .setMaxReg => .reg
  | .exit => .exit

/-- The kind of a loader site's event. -/
def loaderKind : Loader.Site → NextKind
  | .setMaxReg => .reg
  | .head | .elA _ | .elC _ _ | .elTail => .warp
  | .wait _ | .drain _ | .drainQ => .wait
  | .arrive _ | .arriveTail => .arrive
  | .copy _ _ => .tensorLoad
  | .exit => .exit

/-- The kind of an MMA warp site's event. -/
def mmaKind : Mma.Site → NextKind
  | .setMaxReg => .reg
  | .alloc | .relinquish | .dealloc => .tmem
  | .allocWrite => .allocStore
  | .bar0 | .bar1 => .bar
  | .ldBase => .read
  | .shflQ | .shfl _ | .elM _ | .elC _ => .warp
  | .qWait _ | .kvWait _ | .pWait _ | .p2Wait _ _ | .waitDealloc => .wait
  | .mma _ _ => .mma
  | .commit _ => .commit
  | .arrivePeer => .arrive
  | .exit => .exit

/-- The kind of a store warp site's event. -/
def storeKind : Store.Site → NextKind
  | .setMaxReg => .reg
  | .wait _ => .wait
  | .tma _ _ => .tensorStore
  | .commit _ => .quiet
  | .drain _ => .bulkWait
  | .free _ => .arrive
  | .exit => .exit

/-- The kind of a softmax site's event. -/
def softmaxKind : Softmax.Site → NextKind
  | .setMaxReg => .reg
  | .bar0 | .gen _ | .barEnd => .bar
  | .statsW _ | .sW _ => .wait
  | .ld _ _ | .ldW _ _ => .tcLoad
  | .alphaSt | .lSt => .store
  | .pst _ _ | .pwait _ _ => .tcStore
  | .pArr _ | .p2Arr _ => .arrive
  | .warpBar _ | .el _ => .warp
  | .exit => .exit

/-- The kind of a correction site's event. -/
def corrKind : Correction.Site → NextKind
  | .setMaxReg => .reg
  | .bar0 | .sync _ _ | .barEnd => .bar
  | .free _ | .credit _ | .oFree _ _ | .staged _ => .arrive
  | .ldA _ | .ldL _ => .read
  | .vote _ => .warp
  | .rld _ _ | .rldW _ _ | .fld _ _ | .fldW _ _ => .tcLoad
  | .rst _ _ | .rwait _ => .tcStore
  | .oWait _ | .fWait _ | .tailWait => .wait
  | .fst _ _ _ _ => .store
  | .fence _ => .quiet
  | .exit => .exit

/-- The kind of the next event of a thread in state `d`. -/
def nextKind : ThreadD → NextKind
  | .inl p => prologueKind p.site
  | .inr (.idle s) => idleKind s.site
  | .inr (.loader d) => loaderKind d.site
  | .inr (.mma d) => mmaKind d.site
  | .inr (.store d) => storeKind d.site
  | .inr (.softmax d) => softmaxKind d.site
  | .inr (.corr d) => corrKind d.site

/-- The templates of an event of each kind, apart from undefined behaviour. -/
def KindTmpl : NextKind → Tmpl → Prop
  | .wait, m => ∃ l p k a s, m = .wait l p k a s
  | .warp, m => (∃ md a b c k, m = .shfl md a b c k) ∨ (∃ mask k, m = .elect mask k) ∨
    (∃ mask t, m = .warpBar mask t) ∨ ∃ mask a k, m = .vote mask a k
  | .cluster, m => ∃ op t, m = .cluster op t
  | .bar, m => ∃ id t c md, m = .bar id t c md
  | .reg, m => ∃ inc n t, m = .setMaxReg inc n t
  | .tmem, m => ∃ grp dst act t, m = .tc (.resource grp dst act) t
  | .init, m => ∃ l c t, m = .mbInit l c t
  | .arrive, m => ∃ l tx t c r s, m = .arrive l tx t c r s
  | .tensorLoad, m => ∃ a s t, m = .tensorIssue a s t
  | .tensorStore, m => ∃ a s t, m = .tensorStore a s t
  | .mma, m => ∃ d s acc ms t, m = .tc (.mma d s acc ms) t
  | .commit, m => ∃ s t, m = .tc (.commit s) t
  | .bulkWait, m => ∃ md n t, m = .bulkWait md n t
  | .tcLoad, m => (∃ a n sh k, m = .tcLd a n sh k) ∨ ∃ t, m = .tc .waitLd t
  | .tcStore, m => (∃ a vs sh t, m = .tc (.st a vs sh) t) ∨ ∃ t, m = .tc .waitSt t
  | .read, m => ∃ a k, m = .read a k
  | .quiet, m => (∃ t, m = .fenceProxy (.async (some (.shared .cta))) none t) ∨
    (∃ t, m = .fenceMbarInit t) ∨ ∃ t, m = .bulkCommit t
  | .store, m => ∃ a bs t, m = .write a bs t ∧ a.release = false
  | .allocStore, m => ∃ dst t, m = .tcAllocStore dst t
  | .exit, m => m = .exit

/-- The thread facts the progress classes of the released threads use, for one execution. -/
structure NextFacts (L : Launch) (X : Execution) : Prop where
  /-- A thread at its trace's end fires the event of its site's kind: by local steps it reaches
  a concrete state of its machine state, whose template is undefined behaviour or of the kind. -/
  fire : ∀ {g : Nat} {d : ThreadD} {t : TState}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some d) →
    Run kernel asms L g {} (X.tr g) (some t) → ∃ t1 m,
      Relation.ReflTransGen (Tau kernel asms L g) t t1 ∧ (code L g).AtD d t1 ∧
      out kernel asms L g t1 = .ev m ∧ ((∃ f, m = .ub f) ∨ KindTmpl (nextKind d) m)
  /-- A thread whose last event is an allocation request is at the allocation's address store,
  or is not lane 0 of its warp: only lane 0 stores the address, and the other lanes continue at
  the named barrier after it. -/
  alloc_next : ∀ {g pc : Nat} {grp : CtaGroup} {dst : Option Loc} {n : Nat} {d : ThreadD},
    g < L.threads →
    X.get (g, (X.tr g).length - 1) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ →
    Frame.stateAt (code L) X g (X.tr g).length = some (some d) →
      nextKind d = .allocStore ∨ laneOf L g ≠ 0
  /-- The allocating warp's lane 0 stores its local base word as the second event of the
  allocation instruction, if the trace includes that event. -/
  alloc_result_event : ¬ HasUb X →
    ∀ {g j site : Nat} {grp : CtaGroup} {dst : Option Loc} {n : Nat} {e : Event},
      X.get (g, j) = some ⟨site, .tc (.resource grp dst (.alloc n))⟩ →
      X.get (g, j + 1) = some e → laneOf L g = 0 →
      ∃ bytes, X.get (g, j + 1) =
        some ⟨site, .wr { loc := baseLoc L (ctaOf L g), size := 4 } bytes⟩
  /-- A thread at a register request has made none, and its last event is a cluster-barrier
  operation: every role starts with its request, right after the prologue's cluster wait. -/
  reg_entry : ∀ {g : Nat} {d : ThreadD}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some d) → nextKind d = .reg →
    (∃ pc op, X.get (g, (X.tr g).length - 1) = some ⟨pc, .cluster op⟩) ∧
      ∀ j pc inc n inst, X.get (g, j) ≠ some ⟨pc, .setMaxReg inc n inst⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof
