-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Elect
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOutDefs
public import Kernels.Fp16Gemm8192.Proof.Thread.ClusterDefs
public import Kernels.Fp16Gemm8192.Proof.Thread.RegDefs
public import Kernels.Fp16Gemm8192.Proof.Thread.TmemDefs
public import Kernels.Fp16Gemm8192.Proof.Thread.TcCollDefs
public import Kernels.Fp16Gemm8192.Proof.Thread.WarpSites
public import Kernels.Fp16Gemm8192.Proof.Thread.NextKind
public import Kernels.Fp16Gemm8192.Proof.Thread.Fire
public import Lemmas.Flow.Resource
public import Lemmas.Kernel.Goals
public import Lemmas.Kernel.Frame
public import Kernels.Fp16Gemm8192.Proof.Thread.RankDefs
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcSites
public import Kernels.Fp16Gemm8192.Proof.Thread.ExitDefs
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderIssues
public import Kernels.Fp16Gemm8192.Proof.Rings
public import Lemmas.Flow.RunInv
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Slot
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Stage
public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Slot
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Slot
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
public import Lemmas.Step.StoreDone
public import Kernels.Fp16Gemm8192.Data.TensorMaps
public import Lemmas.Flow.Polls
public import Lemmas.Flow.NotCommit
public import Lemmas.Flow.NotTcData
public import Lemmas.Flow.NotTensor
public import Lemmas.Flow.NotObject
public import Lemmas.Tcgen05.TcMmaSource
public import Lemmas.Protocol.RegionOrder
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerTileDefs
public import Kernels.Fp16Gemm8192.Proof.Support.Geometry
public import Lemmas.Protocol.ObjectSource

@[expose] public section

/-! # The interfaces between the proof's layers

The protocol layer sees the threads only through `ThreadFacts`: what each thread does along
its own events, stated with the abstract state its machine (`code`) is in at an event
(`Frame.stateAt (code L)`, from `Lemmas/Kernel/Frame`, which also derives the generic facts of
sound machines from `ThreadFacts.sound` and `ThreadFacts.tracked`). The thread layer proves
`ThreadFacts` (`Thread/Facts.lean`); the instruction at each site is one its kind accepts
(`site_kindOp`, `Thread/Fire.lean`, a fact of the code). The layers above the protocols see the
input ring through `InputFacts` and the accumulator ring through `TmemFacts`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The warp a role runs on. -/
def roleWarp (w : Nat) : Prologue.Role → Prop
  | .loader _ => w = 11
  | .mma m => m.w = w ∧ (w = 8 ∨ w = 9)
  | .sched _ => w = 10
  | .cons _ => w < 8

/-- Which thread polls barrier `b`: a loader its CTA's input empty barriers, an MMA thread its
CTA's input full barriers and its accumulator's empty barrier, a consumer thread its CTA's full
barrier of its accumulator, every role its CTA's CLC response barrier, and the scheduler its
CTA's acknowledgement barrier. -/
def Bar.pollBy (L : Launch) (g : Nat) (d : ThreadD) : Bar → Prop
  | ⟨.input, _, false⟩ => ∃ l, d = .inr (.loader l)
  | ⟨.input, _, true⟩ => ∃ mm, d = .inr (.mma mm)
  | ⟨.acc, j, false⟩ => ∃ mm, d = .inr (.mma mm) ∧ j = mm.w % 2
  | ⟨.acc, j, true⟩ => (∃ cs, d = .inr (.cons cs)) ∧ j = g % L.block / 32 / 4
  | ⟨.clc, _, true⟩ => ∃ r, d = .inr r
  | ⟨.clc, _, false⟩ => ∃ sd, d = .inr (.sched sd)

/-- Which thread arrives on barrier `b`: the loader of a leader CTA on the input full
barriers, a consumer thread on its accumulator's empty barrier, the scheduler on its CTA's CLC
response barrier, and the loader, the leader CTA's MMA threads, the scheduler and the first
consumer threads on the acknowledgement barrier. -/
def Bar.arriveBy (L : Launch) (g : Nat) (d : ThreadD) : Bar → Prop
  | ⟨.input, _, true⟩ => (∃ l, d = .inr (.loader l)) ∧ g / L.block % 2 = 0
  | ⟨.acc, j, false⟩ => (∃ cs, d = .inr (.cons cs)) ∧ j = g % L.block / 32 / 4
  | ⟨.clc, _, true⟩ => ∃ sd, d = .inr (.sched sd)
  | ⟨.clc, _, false⟩ => (∃ l, d = .inr (.loader l)) ∨
      ((∃ mm, d = .inr (.mma mm)) ∧ g / L.block % 2 = 0) ∨ (∃ sd, d = .inr (.sched sd)) ∨
        ((∃ cs, d = .inr (.cons cs)) ∧ Consumer.first L g = true)
  | _ => False

/-- Which thread's commits notify barrier `b`: an MMA thread's, on the input empty barriers and
on its accumulator's full barrier. -/
def Bar.commitBy (d : ThreadD) : Bar → Prop
  | ⟨.input, _, false⟩ => ∃ mm, d = .inr (.mma mm)
  | ⟨.acc, j, true⟩ => ∃ mm, d = .inr (.mma mm) ∧ j = mm.w % 2
  | _ => False

/-- Which thread's copies complete on barrier `b`: a loader's, on the input full barriers. -/
def Bar.copyBy (d : ThreadD) : Bar → Prop
  | ⟨.input, _, true⟩ => ∃ l, d = .inr (.loader l)
  | _ => False

/-- Which thread's cancellation requests complete on barrier `b`: the leader CTA's
scheduler's, on the CLC response barriers of its cluster. -/
def Bar.clcBy (L : Launch) (g : Nat) (d : ThreadD) : Bar → Prop
  | ⟨.clc, _, true⟩ => (∃ sd, d = .inr (.sched sd)) ∧ g / L.block % 2 = 0
  | _ => False

/-- The CTA an arrival of thread `g` on barrier `b` lands in. -/
def Bar.arriveCta (L : Launch) (g : Nat) (b : Bar) : Nat :=
  if b.arriveLeader then 2 * (g / L.block / 2) else g / L.block

/-- The barriers that live only in a cluster's leader CTA: the input full barriers, the accumulator
empty barriers and the CLC acknowledgement barrier (the other barriers of the rings are in both
CTAs). -/
def Bar.leaderOnly : Bar → Bool
  | ⟨.input, _, true⟩ => true
  | ⟨.acc, _, false⟩ => true
  | ⟨.clc, _, false⟩ => true
  | _ => false

/-- The mbarriers an event kind arrives on, polls or commits to. -/
def NamesMbar (k : Kind) (m : Loc) : Prop :=
  (∃ tx c rel sc, k = .arrive m tx c rel sc) ∨ (∃ p ok acq sc, k = .wait m p ok acq sc) ∨
    ∃ sp rank, k = .tc (.commit sp) ∧ TcCommit.target sp rank = some m

/-- The index among CTA thread 0's events of the prologue's initialization of the mbarrier at
offset `off` of the shared window: the initializations are events 2 to 19, at offsets 8 to 128 in
steps of eight, then 160 and 168. -/
def initIndexOf (off : Nat) : Nat := if off ≤ 128 then off / 8 + 1 else off / 8 - 2

/-- How event `e`, the `k`-th of thread `g` in state `d`, may use the ring barriers. A poll is
on a barrier of the thread's CTA that the thread polls (`Bar.pollBy`). An arrival is on a
barrier that the thread arrives on (`Bar.arriveBy`), in the CTA the barrier's table names
(`Bar.arriveCta`), once, with the barrier's bytes. A copy completes on a barrier of the leader
CTA that the thread copies to (`Bar.copyBy`), with the barrier's bytes. A commit is by a thread
of a leader CTA that notifies the barrier (`Bar.commitBy`), on its own CTA's barrier, and
notifies that barrier in the CTAs of its cluster by rank. A cancellation request is by the
leader CTA's scheduler (`Bar.clcBy`), on its own CTA's barrier, and completes in the CTAs of
its cluster. Only CTA thread 0 initializes a barrier, as its initialization with the barrier's
index and count. No bulk copy uses them and no thread invalidates one. -/
structure RingEvent (L : Launch) (g k : Nat) (d : ThreadD) (e : Event) : Prop where
  wait : ∀ (b : Bar) cta p ok acq sc, e.kind = .wait (b.loc L cta) p ok acq sc → b.Valid →
    b.pollBy L g d ∧ cta = g / L.block
  arrive : ∀ (b : Bar) cta tx c rel sc, e.kind = .arrive (b.loc L cta) tx c rel sc → b.Valid →
    b.arriveBy L g d ∧ cta = b.arriveCta L g ∧ tx = b.arriveTx ∧ c = 1
  tensor : ∀ a sp (b : Bar) cta, e.kind = .tensorIssue a sp → sp.mbar = b.loc L cta → b.Valid →
    b.copyBy d ∧ cta = 2 * (g / L.block / 2) ∧
      TensorTransfer.bytes sp.descriptor = b.completeBytes
  commit : ∀ sp rank (b : Bar) cta, e.kind = .tc (.commit sp) →
    TcCommit.target sp rank = some (b.loc L cta) → b.Valid → b.commitBy d ∧ g / L.block % 2 = 0 ∧
      rank.val < 2 ∧
      cta = g / L.block + rank.val ∧ sp.mbar = b.loc L (g / L.block)
  init : ∀ (b : Bar) cta c, e.kind = .mbInit (b.loc L cta) c → b.Valid →
    g % L.block = 0 ∧ cta = g / L.block ∧ k = b.initIndex ∧ c = b.count
  clc : ∀ sp targets, e.kind = .clcIssue sp targets → ∃ b : Bar, b.Valid ∧ b.clcBy L g d ∧
    sp.mbar = b.loc L (g / L.block) ∧
    sp.response = ⟨.shared, g / L.block, L.sharedBase + b.responseOff⟩ ∧
    ∀ c ∈ targets, c / 2 = g / L.block / 2
  /-- No event is a linear copy (`cp.async`, `cp.async.bulk`). -/
  copy : ∀ s, e.kind ≠ .copy s
  inval : ∀ m, e.kind ≠ .mbInval m
  /-- An mbarrier an event arrives on, polls or commits to is a ring barrier of some CTA. -/
  loc : ∀ m, NamesMbar e.kind m → ∃ (b : Bar) (cta : Nat), b.Valid ∧ m = b.loc L cta
  /-- A poll of a barrier that lives only in a leader CTA is in an even CTA. -/
  wait_leader : ∀ (b : Bar) cta p ok acq sc, e.kind = .wait (b.loc L cta) p ok acq sc → b.Valid →
    b.leaderOnly = true → cta % 2 = 0
  /-- An initialization is by CTA thread 0, of a barrier of its CTA's shared window, at the event
  whose index the barrier's offset gives, with a valid arrival count; the barrier's eight bytes are
  those of the rings' barriers (offsets 8 to 136) or the unused barriers beyond (offsets 160 and
  168). -/
  init_site : ∀ m c, e.kind = .mbInit m c →
    g % L.block = 0 ∧ m.cta = g / L.block ∧ k = initIndexOf (m.addr - L.sharedBase) ∧ 0 < c ∧
      c ≤ 256 ∧ m.space = .shared ∧ L.sharedBase + 8 ≤ m.addr ∧
      (m.addr + 8 ≤ L.sharedBase + 144 ∨ L.sharedBase + 160 ≤ m.addr ∧ m.addr + 8 ≤ L.sharedBase +
        176)

/-- The consumer's accumulator-full wait, for the progress layer. A consumer `g` at its accumulator
wait, stopped at a failed poll of its accumulator-full barrier whose phase has the poll's parity,
has an open commit that is not notified, or a pending MMA lane of its leader CTA's warp of its
buffer whose time is within its block `blockAt T + 4160` (`T` its successful polls), or a lane whose
machine stopped without its exit. -/
def ConsAccBlockedX (L : Launch) (X : Execution) : Prop :=
  ∀ (g : Nat) (c : Consumer.D) (pc : Nat) (sc : MbarScope) (before : MBarrier.State),
    g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c))) → c.site = .accWait →
    (X.tr g).getLast? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 / 4, true⟩)
      c.ap false true sc⟩ →
    MBarrier.stateBefore (X.objects (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 / 4, true⟩))
      (X.objects (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 / 4, true⟩)).length =
        some before →
    before.phase % 2 = c.ap % 2 →
    (∃ i s r m, X.Commit i s ∧ TcCommit.target s r = some m ∧ r ∉ X.tcNotified i) ∨
    (∃ h, h < L.threads ∧ h / L.block = g / L.block / 2 * 2 ∧
      h % L.block / 32 = 8 + g % L.block / 32 / 4 ∧ X.tr h ≠ [] ∧
      (∀ pc', (X.tr h).getLast? ≠ some ⟨pc', .exit⟩) ∧
      ∃ d, Frame.stateAt (code L) X h (X.tr h).length = some (some d) ∧ d.exitOff = none ∧
        d.vtime L h (X.tr h) ≤ blockAt (consCount L g (X.tr g)) + 4160) ∨
    (∃ h, h < L.threads ∧ h / L.block = g / L.block / 2 * 2 ∧
      h % L.block / 32 = 8 + g % L.block / 32 / 4 ∧ X.tr h ≠ [] ∧
      Frame.stateAt (code L) X h (X.tr h).length = none ∧ ∀ pc', (X.tr h).getLast? ≠
        some ⟨pc', .exit⟩)

/-- Per-thread facts of an execution. -/
structure ThreadFacts (L : Launch) (X : Execution) : Prop where
  /-- Every launched thread is simulated by its machine. -/
  sound : ∀ g < L.threads, (code L g).Sound
  /-- Every thread is followed by its machine at each of its events. -/
  tracked : Frame.Tracked (code L) X
  /-- Every successful mbarrier wait of a thread is the poll of a canonical spin of the code. -/
  wait_spins : ∀ {g k pc : Nat} {m : Loc} {p : Nat} {acq : Bool} {sc : MbarScope},
    g < L.threads → X.get (g, k) = some ⟨pc, .wait m p true acq sc⟩ →
    ∃ exit, kernel.CanonicalSpin pc exit
  /-- No write event of a thread has release semantics. -/
  no_release : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → a.release = false
  /-- A poll of a ring barrier uses the parity of the thread's own successful polls on it,
  after them on an empty barrier. -/
  poll_parity : ∀ {g k : Nat} {e : Event} {d : ThreadD} {b : Bar} {cta p : Nat} {ok acq : Bool}
    {sc : MbarScope}, g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k =
      some (some d) →
    e.kind = .wait (b.loc L cta) p ok acq sc → b.Valid →
    p % 2 = (okPolls (b.loc L cta) ((X.tr g).take k) + b.pollOffset) % 2
  /-- An arrival on a ring barrier is preceded by more successful polls of its partner in the
  thread's CTA than earlier arrivals on it. -/
  arrival_budget : ∀ {g k : Nat} {e : Event} {d : ThreadD} {b : Bar} {cta tx c : Nat}
    {rel : Bool} {sc : MbarScope}, g < L.threads → X.get (g, k) = some e →
    Frame.stateAt (code L) X g k = some (some d) → e.kind = .arrive (b.loc L cta) tx c rel sc →
      b.Valid →
    arrivals (b.loc L cta) ((X.tr g).take k) + b.gateSlack ≤
      okPolls (b.gate.loc L (g / L.block)) ((X.tr g).take k)
  /-- A commit to a ring barrier is preceded by more successful polls of its partner than
  earlier commits to it. -/
  commit_budget : ∀ {g k : Nat} {e : Event} {d : ThreadD} {sp : TcCommit.Spec} {rank : Fin 16}
    {b : Bar} {cta : Nat}, g < L.threads → X.get (g, k) = some e →
    Frame.stateAt (code L) X g k = some (some d) → e.kind = .tc (.commit sp) →
    TcCommit.target sp rank = some (b.loc L cta) → b.Valid →
    ((X.tr g).take k).countP (commitsTo sp.mbar) + 1 ≤
      okPolls (b.partner.loc L (g / L.block)) ((X.tr g).take k)
  /-- A copy completing on a ring barrier is preceded by fewer earlier such copies than the
  barrier's copies per successful poll of its partner. -/
  issue_budget : ∀ {g k : Nat} {e : Event} {d : ThreadD} {b : Bar} {cta : Nat}, g < L.threads →
    X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) →
      issuesTo (b.loc L cta) e = true →
    b.Valid → ((X.tr g).take k).countP (issuesTo (b.loc L cta)) + 1 ≤
      b.issues * okPolls (b.partner.loc L (g / L.block)) ((X.tr g).take k)
  /-- A cancellation request completing on a ring barrier is preceded by fewer earlier such
  requests than the barrier's requests per successful poll of its partner. -/
  clc_budget : ∀ {g k : Nat} {e : Event} {d : ThreadD} {sp : Clc.Spec} {tg : List Nat}
    {b : Bar}, g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k =
      some (some d) →
    e.kind = .clcIssue sp tg → sp.mbar = b.loc L (g / L.block) → b.Valid →
    ((X.tr g).take k).countP (clcIssuesTo sp.mbar) + 1 ≤
      b.issues * okPolls (b.partner.loc L (g / L.block)) ((X.tr g).take k)
  /-- An mbarrier event of an elected role follows the full-mask election of its lane at the
  role's election site. -/
  elected : ∀ {g k : Nat} {e : Event} {r : Prologue.Role} {pc : Nat}, g < L.threads →
    X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some (.inr r)) → r.electPc =
      some pc →
    ObjectKind e.kind →
    ∃ j inst leader, j < k ∧ X.get (g, j) = some ⟨pc, .elect 4294967295 inst leader⟩ ∧
      laneOf L g = leader
  /-- A thread's polls are cluster-scope acquire polls and its arrivals cluster-scope release
  arrivals. -/
  sync_flags : ∀ {g k : Nat} {e : Event} {d : ThreadD}, g < L.threads → X.get (g, k) = some e →
    Frame.stateAt (code L) X g k = some (some d) →
    (∀ m p ok acq sc, e.kind = .wait m p ok acq sc → acq = true ∧ sc = .cluster) ∧
    (∀ m tx c rel sc, e.kind = .arrive m tx c rel sc → rel = true ∧ sc = .cluster)
  /-- A role's acknowledgement of a CLC response follows a proxy fence after its latest
  successful poll of its CTA's response barrier. -/
  ack_fenced : ∀ {g k : Nat} {e : Event} {r : Prologue.Role} {tx n : Nat} {rel : Bool}
    {sc : MbarScope}, g < L.threads → X.get (g, k) = some e →
    Frame.stateAt (code L) X g k = some (some (.inr r)) →
    e.kind = .arrive (Bar.loc L (2 * (g / L.block / 2)) ⟨.clc, 0, false⟩) tx n rel sc →
    ∃ j f, j < k ∧ X.get (g, j) = some f ∧
      f.kind = .fenceProxy (.async (some (.shared .cta))) none ∧
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k)
  /-- A role's query of a CLC response reports the response the thread read from its CTA's
  response buffer right after its latest successful poll of the response barrier. -/
  clc_query : ∀ {g k : Nat} {e : Event} {r : Prologue.Role} {q : ClcQuery} {rr : ClcResponse},
    g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some (.inr r)) →
    e.kind = .clcQuery q rr →
    ∃ j pc p acq sc pcr, ∃ src : Acc, ∃ bs, k ≤ j + 3 ∧ j + 2 ≤ k ∧
      X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
      X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ ∧
      src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ ∧
      Flow.responseOf bs = some rr
  /-- At a request the scheduler has requested at most once per response it observed, and each
  of its earlier successful response polls was followed by a read of a response that claims a
  CTA: after a response claiming none, it requests no more. -/
  sched_issue : ∀ {g k : Nat} {e : Event} {sd : Scheduler.D} {sp : Clc.Spec} {tg : List Nat},
    g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k =
      some (some (.inr (.sched sd))) →
    e.kind = .clcIssue sp tg →
    ((X.tr g).take k).countP (clcIssuesTo (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)) ≤
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) ∧
    ∀ j pc p acq sc, j < k →
      X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      ∃ pcr, ∃ src : Acc, ∃ bs rr, X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ ∧
        src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ ∧
        Flow.responseOf bs = some rr ∧ Loader.claims rr
  /-- A consumer thread exits only after a successful poll of its CTA's response barrier and the
  read, right after it, of a response that claims no CTA. -/
  consumer_exit : ∀ {g k : Nat} {e : Event} {d : ThreadD}, g < L.threads →
    X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) → e.kind = .exit →
    g % L.block / 32 < 8 →
    ∃ j pc p acq sc pcr, ∃ src : Acc, ∃ bs rr, j + 1 < k ∧
      X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
      X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ ∧
      src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ ∧
      Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr
  /-- A consumer's output events: its output barrier arrivals and bulk commits by site
  (`Consumer.OutRel`), its writes (staging stores of its slice's parity), its TMA stores (reading
  only the 8 KB staging buffer of the slice's parity, right after its proxy fence), its bulk waits
  (its drains) and its named barriers (its group's CLC barrier, or its output barrier with the
  group's 128 threads). -/
  cons_out : ∀ {g k : Nat} {e : Event} {c : Consumer.D}, g < L.threads →
    X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some (.inr (.cons c))) →
    Consumer.OutRel L g c ((X.tr g).take k) ∧
    (∀ a bs, e.kind = .wr a bs → ∃ s i el, c.site = .store s i el ∧
      a.loc = ⟨.shared, g / L.block,
        L.sharedBase + Consumer.stagingOff (Consumer.tidOf L g) (s.val % 2) i el⟩ ∧ a.size = 4) ∧
    (∀ a sp, e.kind = .tensorStore a sp → ∃ s, c.site = .tma s ∧
      (∀ x y b l, TensorStore.readLoc sp x y b = some l → l.space = .shared ∧
        l.cta = g / L.block ∧
        L.sharedBase + Consumer.stagingBase (Consumer.tidOf L g) (s.val % 2) ≤ l.addr ∧
        l.addr < L.sharedBase + Consumer.stagingBase (Consumer.tidOf L g) (s.val % 2) + 8192) ∧
      ∃ pc, 0 < k ∧ X.get (g, k - 1) = some ⟨pc, .fenceProxy (.async (some (.shared .cta))) none⟩) ∧
    (∀ m r, e.kind = .bulkWait m r → (∃ s, c.site = .drain s ∧ m = .read ∧ r = 1) ∨
      (c.site = .finalDrain ∧ m = .full ∧ r = 0)) ∧
    (∀ id cnt, e.kind = .bar id cnt →
      (c.site = .clcBar ∧ id = Consumer.tidOf L g / 32 / 4 + 1 ∧ cnt = some 128) ∨
      ((∃ s, c.site = .barA s ∨ c.site = .barB s) ∧ id = Consumer.outId L g ∧ cnt = some 128)) ∧
    (∀ s, c.site = .barA s → ∃ pc, 0 < k ∧ X.get (g, k - 1) = some ⟨pc, .bulkWait .read 1⟩)
  /-- A thread's memory accesses, by the state it fires from: it reads its CTA's response buffer or
  the Tensor Memory base word at the start of its CTA's shared window; it writes the base word, or
  is a consumer; it issues tensor stores as a consumer. -/
  access_region : ∀ {g k : Nat} {e : Event} {d : ThreadD}, g < L.threads →
    X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) →
    (∀ a bs, e.kind = .rd a bs →
      (a.loc = ⟨.shared, g / L.block, L.sharedBase + 144⟩ ∧ a.size = 16) ∨
        (a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ ∧ a.size = 4)) ∧
    (∀ a bs, e.kind = .wr a bs → (∃ c, d = .inr (.cons c)) ∨
      (a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ ∧ a.size = 4)) ∧
    (∀ a sp, e.kind = .tensorStore a sp → ∃ c, d = .inr (.cons c))
  /-- A consumer at its slice's second output barrier, on a trace without undefined behaviour, has
  just made the slice's sixteen staging stores: element `m` of the slice, at index `k - 16 + m`, is
  the write of four bytes of its chunk `m / 4` and element `m % 4` in the staging buffer of the
  slice's parity. -/
  cons_slice_stores : ∀ {g k : Nat} {c : Consumer.D} {s : Fin 8}, g < L.threads →
    (∀ j pc f, X.get (g, j) ≠ some ⟨pc, .ub f⟩) → k < (X.tr g).length →
    Frame.stateAt (code L) X g k = some (some (.inr (.cons c))) → c.site = .barB s →
    16 ≤ k ∧ ∀ m, m < 16 → ∃ pc a bs, X.get (g, k - 16 + m) = some ⟨pc, .wr a bs⟩ ∧
      a.loc = ⟨.shared, g / L.block, L.sharedBase +
        Consumer.stagingOff (Consumer.tidOf L g) (s.val % 2) (m / 4) (m % 4)⟩ ∧
      a.size = 4 ∧ bs.length = 4
  /-- A consumer at its TMA store has made, as its two latest events, its output barrier arrival and
  its proxy fence. -/
  cons_tma_prev : ∀ {g k : Nat} {c : Consumer.D} {s : Fin 8}, g < L.threads → k < (X.tr g).length →
    Frame.stateAt (code L) X g k = some (some (.inr (.cons c))) → c.site = .tma s →
    2 ≤ k ∧ (∃ pc, X.get (g, k - 2) = some ⟨pc, .bar (Consumer.outId L g) (some 128)⟩) ∧
      ∃ pc, X.get (g, k - 1) = some ⟨pc, .fenceProxy (.async (some (.shared .cta))) none⟩
  /-- A tensor store is a consumer's slice's: valid, through the output tensor map, from the staging
  buffer of the slice's parity. -/
  cons_tma : ∀ {g k pc a : Nat} {sp : TensorStore.Spec} {d : ThreadD}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tensorStore a sp⟩ → Frame.stateAt (code L) X g k = some (some d) →
    ∃ (c : Consumer.D) (s : Fin 8), d = .inr (.cons c) ∧ c.site = .tma s ∧
      TensorStore.Valid (g / L.block) sp ∧
      ∃ b cls origin, sp = ⟨⟨1, Fp16Gemm8192.mapD b cls, origin,
        ⟨.shared, g / L.block, L.sharedBase + Consumer.stagingBase (Consumer.tidOf L g)
          (s.val % 2)⟩,
        none⟩, none⟩
  /-- A consumer's write has as many bytes as its footprint. -/
  cons_write_len : ∀ {g k pc : Nat} {a : Acc} {bs : List Byte} {c : Consumer.D}, g < L.threads →
    X.get (g, k) = some ⟨pc, .wr a bs⟩ → Frame.stateAt (code L) X g k =
      some (some (.inr (.cons c))) →
    bs.length = a.size
  /-- A consumer's successful polls of its CTA's CLC response barrier are its arrivals on its
  group's CLC barrier, plus the response it holds (`Consumer.D.clcHold`). -/
  cons_clc : ∀ {g k : Nat} {e : Event} {c : Consumer.D}, g < L.threads →
    X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some (.inr (.cons c))) →
    okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) =
      ((X.tr g).take k).countP (Execution.isBarId (Consumer.tidOf L g / 32 / 4 + 1)) + c.clcHold
  /-- A consumer's proxy fence follows its latest successful CLC response poll before its group
  CLC barrier arrival. -/
  cons_clc_fence : ∀ {g k : Nat} {e : Event} {c : Consumer.D}, g < L.threads →
    X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some (.inr (.cons c))) → c.site =
      .clcBar →
    ∃ j f, j < k ∧ X.get (g, j) = some f ∧
      f.kind = .fenceProxy (.async (some (.shared .cta))) none ∧
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k)
  /-- An MMA thread of a non-leader CTA polls no CLC response: the MMA warps of the leader CTA are
  the only MMA readers of a response ring. -/
  mma_odd_quiet : ∀ {g k : Nat} {e : Event} {d : ThreadD}, g < L.threads →
    X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) →
      (∃ m, d = .inr (.mma m)) →
    g / L.block % 2 = 1 → ∀ p ok acq sc, e.kind ≠ .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)
      p ok acq sc
  /-- A consumer's acknowledgement arrival on the CLC acknowledgement barrier happens at a state
  holding no CLC response (its `clcHold` is 0). -/
  ack_hold : ∀ {g k : Nat} {e : Event} {c : Consumer.D} {tx n : Nat} {rel : Bool} {sc : MbarScope},
    g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k =
      some (some (.inr (.cons c))) →
    e.kind = .arrive (Bar.loc L (2 * (g / L.block / 2)) ⟨.clc, 0, false⟩) tx n rel sc →
    c.clcHold = 0
  /-- An acknowledging thread of a cluster, one of the ten selectors of its acknowledgement ring,
  has acknowledged each response it polled but the one it holds (`ThreadD.clcHeld`): its successful
  response polls are its arrivals on the leader CTA's acknowledgement barrier plus that held
  response. -/
  ack_exact : ∀ {g k : Nat} {d : ThreadD}, g < L.threads →
    (∃ b : Fin 10, ClcRing.consumerSel L (g / L.block / 2) b g = true) →
    k ≤ (X.tr g).length → Frame.stateAt (code L) X g k = some (some d) →
    okPolls (clcResp L g) ((X.tr g).take k) =
      arrivals (clcAck L g) ((X.tr g).take k) + d.clcHeld
  /-- Only consumers arrive on named barriers. -/
  bar_role : ∀ {g k : Nat} {e : Event} {d : ThreadD} {id : Nat} {cnt : Option Nat},
    g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) →
    e.kind = .bar id cnt → ∃ c, d = .inr (.cons c)
  /-- A bulk-group wait is a consumer's. -/
  bulk_role : ∀ {g k : Nat} {e : Event} {d : ThreadD} {m : BulkGroup.WaitMode} {r : Nat},
    g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) →
    e.kind = .bulkWait m r → ∃ c, d = .inr (.cons c)
  /-- A thread's cluster barrier events: its arrivals so far count its state's phase; an
  arrival releases and is its first or second; an exit follows its exit wait, after its second
  arrival. -/
  cluster : ∀ {g k : Nat} {e : Event} {d : ThreadD}, g < L.threads → X.get (g, k) = some e →
    Frame.stateAt (code L) X g k = some (some d) →
    clArrives ((X.tr g).take k) = d.clPhase ∧
    (∀ rel al, e.kind = .cluster (.arrive rel al) → rel = true ∧ d.clPhase ≤ 1) ∧
    (e.kind = .exit → d.clPhase = 2 ∧ ExitWaited ((X.tr g).take k))
  /-- A loader whose trace ends with a failed poll while at a slot's empty wait can next poll the
  slot's empty barrier, with its parity, successfully. -/
  loader_retry : ∀ {g : Nat} {l : Loader.D} {b : Fin 8} {pc : Nat} {m : Loc} {p : Nat}
    {acq : Bool} {sc : MbarScope}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) → l.site = .wait b →
    (X.tr g).getLast? = some ⟨pc, .wait m p false acq sc⟩ →
    ∃ t t1 u sc', Run kernel Prod L g {} (X.tr g) (some t) ∧
      Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨(Loader.Site.wait b).pc,
        .wait (InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b)) (InputRing.producerParity b)
          true true sc'⟩ (some u)
  /-- A loader whose trace ends with a failed poll while at a slot's empty wait polled that slot's
  empty barrier, with the parity after its own successful polls on it. -/
  loader_wait : ∀ {g : Nat} {l : Loader.D} {b : Fin 8} {pc : Nat} {m : Loc} {p : Nat}
    {acq : Bool} {sc : MbarScope}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) → l.site = .wait b →
    (X.tr g).getLast? = some ⟨pc, .wait m p false acq sc⟩ →
    m = InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b) ∧
      InputRing.producerParity b % 2 =
        (okPolls (InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b)) (X.tr g) + 1) % 2
  /-- A leader scheduler's response arrival follows one more of its cancellation requests on that
  response barrier than its earlier response arrivals: the request it expects is issued first. -/
  lead_arrive_after_issue : ∀ {g k : Nat} {e : Event} {sd : Scheduler.D} {tx n : Nat} {rel : Bool}
    {sc : MbarScope}, g < L.threads → X.get (g, k) = some e →
    Frame.stateAt (code L) X g k = some (some (.inr (.sched sd))) → Loader.leader L g = true →
    e.kind = .arrive (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) tx n rel sc →
    arrivals (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) + 1 ≤
      ((X.tr g).take k).countP (clcIssuesTo (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩))
  /-- A query of a CLC response fires from a role's state. -/
  query_role : ∀ {g k pc : Nat} {q : ClcQuery} {rr : ClcResponse}, g < L.threads →
    X.get (g, k) = some ⟨pc, .clcQuery q rr⟩ → ∃ r, Frame.stateAt (code L) X g k =
      some (some (.inr r))
  /-- The prologue performs no mbarrier wait. -/
  prologue_no_wait : ∀ {g k : Nat} {e : Event} {p : Prologue.D}, g < L.threads →
    X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some (.inl p)) →
    ∀ m par ok acq sc, e.kind ≠ .wait m par ok acq sc
  /-- A thread in a role state runs on that role's warp. -/
  role_warp : ∀ {g k : Nat} {r : Prologue.Role}, g < L.threads → k ≤ (X.tr g).length →
    Frame.stateAt (code L) X g k = some (some (.inr r)) → roleWarp (g % L.block / 32) r
  /-- A thread's events use the ring objects only as `RingEvent` says. -/
  ring_event : ∀ {g k : Nat} {e : Event} {d : ThreadD}, g < L.threads → X.get (g, k) = some e →
    Frame.stateAt (code L) X g k = some (some d) → RingEvent L g k d e
  /-- A poll is on an mbarrier of the polling thread's own CTA. -/
  wait_local : ∀ {g k : Nat} {e : Event} {d : ThreadD} {m : Loc} {p : Nat} {ok acq : Bool}
    {sc : MbarScope}, g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k =
      some (some d) →
    e.kind = .wait m p ok acq sc → m.space = .shared ∧ m.cta = g / L.block
  /-- Before a role's event, CTA thread 0 of every CTA of the thread's cluster has initialized
  each ring barrier, and the initialization happens before the event. -/
  ring_initialized : ∀ {g j : Nat} {ev : Event} {r : Prologue.Role} {b : Bar} {cta : Nat},
    g < L.threads → X.get (g, j) = some ev → Frame.stateAt (code L) X g j = some (some (.inr r)) →
      b.Valid →
    cta < L.grid → L.clusterOfCta cta = L.clusterOfCta (g / L.block) →
    ∃ pc, X.get (cta * L.block, b.initIndex) = some ⟨pc, .mbInit (b.loc L cta) b.count⟩ ∧
      baseCausality L X (cta * L.block, b.initIndex) (g, j)
  /-- A loader's successful empty polls go round the four slots, and at a slot's empty wait
  their number is the k-block of the wait. -/
  loader_rank : ∀ {g : Nat} {l : Loader.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) →
    (∀ s : Fin 4, okPolls (inputEmpty L (g / L.block) s) (X.tr g) =
      (loaderCount L g (X.tr g) + 3 - s) / 4) ∧
    ∀ b : Fin 8, l.site = .wait b →
      loaderCount L g (X.tr g) % 128 = l.q + b.val ∧ l.q % 8 = 0
  /-- An MMA thread's commits go round the four slots, and their number is the k-block of its
  site. -/
  mma_rank : ∀ {g : Nat} {m : Mma.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m))) →
    (∀ s : Fin 4, (X.tr g).countP (commitsTo (inputEmpty L (g / L.block) s)) =
      (mmaCount L g (X.tr g) + 3 - s) / 4) ∧
    (match m.site with
     | .full s | .mma s _ | .commit s => mmaCount L g (X.tr g) % 128 = m.q + s.val ∧ m.q % 4 = 0
     | .clcWait | .clcLoad | .clcStatus | .clcFirst | .clcFence | .ack | .accWait =>
       mmaCount L g (X.tr g) % 128 = 0
     | .accCommit => 128 ≤ mmaCount L g (X.tr g) ∧ mmaCount L g (X.tr g) % 128 = 0
     | _ => True)
  /-- A loader at a slot's empty wait can poll that barrier, succeeding or failing; after a failed
  poll it is still there. -/
  loader_poll : ∀ {g : Nat} {l : Loader.D} {b : Fin 8} {t : TState}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) → l.site = .wait b →
    Run kernel Prod L g {} (X.tr g) (some t) → ∀ ok : Bool, ∃ t1 u sc,
      Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨(Loader.Site.wait b).pc, .wait (InputRing.emptyLoc L (g / L.block)
        (InputRing.slotOf b)) (InputRing.producerParity b) ok true sc⟩ (some u) ∧
      (ok = false → (code L g).toMachine.after (some (code L g).init) (X.tr g ++
        [⟨(Loader.Site.wait b).pc, .wait (InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b))
          (InputRing.producerParity b) false true sc⟩]) = some (some (.inr (.loader l))))
  /-- A loader at its tail drain of slot `i` can poll that slot's empty barrier in its CTA with
  parity 1, succeeding or failing; after a failed poll it is still at that drain. -/
  loader_drain_poll : ∀ {g : Nat} {l : Loader.D} {i : Fin 4} {t : TState}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) → l.site =
      .drain i →
    Run kernel Prod L g {} (X.tr g) (some t) → ∀ ok : Bool, ∃ t1 u sc,
      Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨(Loader.Site.drain i).pc,
        .wait (InputRing.emptyLoc L (g / L.block) i) 1 ok true sc⟩ (some u) ∧
      (ok = false → (code L g).toMachine.after (some (code L g).init) (X.tr g ++
        [⟨(Loader.Site.drain i).pc, .wait (InputRing.emptyLoc L
          (g / L.block) i) 1 false true sc⟩]) =
          some (some (.inr (.loader l))))
  /-- An MMA thread at a slot's full wait can poll that slot's full barrier in its own CTA, with its
  full parity, succeeding or failing; after a failed poll it is still at that wait. -/
  mma_poll : ∀ {g : Nat} {m : Mma.D} {s : Fin 4} {t : TState}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m))) → m.site = .full s →
    Run kernel Prod L g {} (X.tr g) (some t) → ∀ ok : Bool, ∃ t1 u sc,
      Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨m.site.pc,
        .wait ⟨.shared, g / L.block, L.sharedBase + 8 + 8 * s.val⟩ (m.fp % 2) ok true sc⟩ (some u) ∧
      (ok = false → (code L g).toMachine.after (some (code L g).init) (X.tr g ++
        [⟨m.site.pc, .wait ⟨.shared, g / L.block, L.sharedBase + 8 + 8 * s.val⟩ (m.fp % 2) false
          true sc⟩]) = some (some (.inr (.mma m))))
  /-- An MMA thread at its accumulator-empty wait can poll its buffer's empty barrier, succeeding
  or failing, with its accumulator parity; after a failed poll it is still at that wait. -/
  mma_acc_poll : ∀ {g : Nat} {m : Mma.D} {t : TState}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m))) → m.site = .accWait →
    Run kernel Prod L g {} (X.tr g) (some t) → ∀ ok : Bool, ∃ t1 u sc,
      Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨m.site.pc,
        .wait ⟨.shared, g / L.block, L.sharedBase + 8 * (m.w % 2) + 88⟩ m.ap ok true sc⟩ (some u) ∧
      (ok = false → (code L g).toMachine.after (some (code L g).init) (X.tr g ++
        [⟨m.site.pc, .wait ⟨.shared, g / L.block, L.sharedBase + 8 * (m.w % 2) + 88⟩ m.ap false true
          sc⟩]) = some (some (.inr (.mma m))))
  /-- A consumer thread at its accumulator-full wait can poll its CTA's full barrier of its
  accumulator, succeeding or failing, with its phase; after a failed poll it is still at that wait.
  -/
  cons_acc_poll : ∀ {g : Nat} {c : Consumer.D} {t : TState}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c))) → c.site = .accWait →
    Run kernel Prod L g {} (X.tr g) (some t) → ∀ ok : Bool, ∃ t1 u sc,
      Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨Consumer.Site.accWait.pc,
        .wait (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 / 4, true⟩) c.ap ok true sc⟩
        (some u) ∧
      (ok = false → (code L g).toMachine.after (some (code L g).init) (X.tr g ++
        [⟨Consumer.Site.accWait.pc,
          .wait (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 / 4, true⟩) c.ap false true sc⟩]) =
          some (some (.inr (.cons c))))
  /-- A thread at its CLC poll site can poll its CTA's response barrier, succeeding or failing, with
  the exact phase of its state; after a failed poll it is still at that site. -/
  clc_poll : ∀ {g : Nat} {d : ThreadD} {t : TState}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some d) → d.AtClcWait →
    Run kernel Prod L g {} (X.tr g) (some t) → ∀ ok : Bool, ∃ t1 u sc,
      Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨(code L g).pc d, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)
        d.cpOf ok true sc⟩ (some u) ∧
      (ok = false → (code L g).toMachine.after (some (code L g).init) (X.tr g ++
        [⟨(code L g).pc d, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) d.cpOf false true sc⟩]) =
          some (some d))
  /-- The leader scheduler at its acknowledgement poll can poll its CTA's acknowledgement barrier,
  succeeding or failing, with its exact phase; after a failed poll it is still at that poll. -/
  sched_ack_poll : ∀ {g : Nat} {sd : Scheduler.D} {t : TState}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.sched sd))) → sd.site =
      .ackWait →
    Run kernel Prod L g {} (X.tr g) (some t) → ∀ ok : Bool, ∃ t1 u sc,
      Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨sd.site.pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) sd.ap
        ok true sc⟩ (some u) ∧
      (ok = false → (code L g).toMachine.after (some (code L g).init) (X.tr g ++
        [⟨sd.site.pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) sd.ap false true sc⟩]) =
          some (some (.inr (.sched sd))))
  /-- A scheduler at its response wait has arrived on its CTA's response barrier once more than it
  has polled that barrier successfully: each arrival expecting a response precedes the wait for it.
  -/
  sched_arrive_clc : ∀ {g : Nat} {sd : Scheduler.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.sched sd))) → sd.site =
      .clcWait →
    arrivals (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) + 1
  /-- A scheduler in its exit stage that has polled successfully holds, after its last successful
  response poll, the read of a response that claims no CTA. -/
  sched_exit : ∀ {g : Nat} {sd : Scheduler.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.sched sd))) →
    (sd.site = .exitArrive ∨ sd.site = .exitWait ∨ sd.site = .exit) →
    0 < okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) →
    ∃ j pc p acq sc pcr, ∃ src : Acc, ∃ bs rr,
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) ∧
      (X.tr g)[j]? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
      (X.tr g)[j + 1]? = some ⟨pcr, .rd src bs⟩ ∧
      src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ ∧
      Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr
  /-- A scheduler at its response wait has read no non-claiming response after a successful response
  poll: each read after a successful poll of its CTA's response barrier names a response that claims
  a CTA. -/
  sched_fail_wait : ∀ {g : Nat} {sd : Scheduler.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.sched sd))) → sd.site =
      .clcWait →
    ∀ j pc p acq sc pcr src bs rr,
      X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ →
      src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ →
      Flow.responseOf bs = some rr → Loader.claims rr
  /-- A warp-10 thread with no election event is before its scheduler election: a prologue state, or
  the scheduler's first state (its election), with time at most 58 and no exit. -/
  sched_unelected : ∀ {g : Nat}, g < L.threads → g % L.block / 32 = 10 →
    (∀ j pc mask inst leader, ¬ X.Elect (g, j) pc mask inst leader) →
    ∃ d, Frame.stateAt (code L) X g (X.tr g).length = some (some d) ∧
      ((∃ p, d = .inl p) ∨ d = .inr (.sched Prologue.schedStart)) ∧ d.exitOff = none ∧
      d.vtime L g (X.tr g) ≤ 58
  /-- A scheduler's arrivals on its CTA's response barrier are its successful response polls, plus
  one at its response wait, at every state of its run. -/
  sched_arrivals : ∀ {g : Nat} {sd : Scheduler.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.sched sd))) →
    arrivals (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) +
        (if sd.site = .clcWait then 1 else 0)
  /-- A scheduler outside its exit stage whose arrivals on its CTA's response barrier are at most
  `n` ranks at most `blockAt n + 4`: its time is one block per successful response poll, and its
  arrivals are those polls plus one at its response wait. -/
  sched_time : ∀ {g : Nat} {sd : Scheduler.D} {n : Nat}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.sched sd))) →
      Scheduler.exitOff sd = none →
    arrivals (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) ≤ n →
    Scheduler.vtime (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)) sd ≤ blockAt n + 4
  /-- Every cancellation request names every CTA of its issuer's cluster below the grid: the
  kernel's request is a multicast one, so each such CTA is among its targets. -/
  clc_multicast : ∀ (h ki pc : Nat) (sp : Clc.Spec) (tg : List Nat),
    X.get (h, ki) = some ⟨pc, .clcIssue sp tg⟩ →
    ∀ c', c' < L.grid → c' / 2 = h / L.block / 2 → c' ∈ tg
  /-- An MMA thread at its response wait has read no non-claiming response after a successful
  response poll: each read after a successful poll of its CTA's response barrier names a response
  that claims a CTA (after a non-claiming read it takes the exit and polls the response barrier no
  more). -/
  mma_fail_wait : ∀ {g : Nat} {m : Mma.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m))) → m.site = .clcWait →
    ∀ j pc p acq sc pcr src bs rr,
      X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ →
      src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ →
      Flow.responseOf bs = some rr → Loader.claims rr
  /-- A consumer thread at its response wait has read no non-claiming response after a successful
  response poll: each read after a successful poll of its CTA's response barrier names a response
  that claims a CTA (after a non-claiming read it drains and exits, and polls the response barrier
  no more). -/
  cons_fail_wait : ∀ {g : Nat} {c : Consumer.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c))) → c.site = .clcWait →
    ∀ j pc p acq sc pcr src bs rr,
      X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ →
      src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ →
      Flow.responseOf bs = some rr → Loader.claims rr
  /-- A successful poll of a thread's response barrier that is not the thread's last event is
  followed by a read of its CTA's response buffer: the read of the response at the next index, with
  the buffer's footprint, in every role. -/
  poll_read : ∀ {g j pc p : Nat} {acq : Bool} {sc : MbarScope}, g < L.threads →
    X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
    j + 1 < (X.tr g).length →
    ∃ pcr src bs, X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ ∧
      src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩
  /-- A loader at its response wait has read no non-claiming response after a successful response
  poll: each read after a successful poll of its CTA's response barrier names a response that claims
  a CTA (after a non-claiming read it drains and exits, and polls the response barrier no more). -/
  loader_fail_wait : ∀ {g : Nat} {l : Loader.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) → l.site =
      .clcWait →
    ∀ j pc p acq sc pcr src bs rr,
      X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ →
      src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ →
      Flow.responseOf bs = some rr → Loader.claims rr
  /-- A thread has at most one election event: a warp's election at the thread's election site is
  executed once (the prologue's and the roles' elections are straight-line). -/
  elect_once : ∀ {g j j' pc pc' mask mask' inst inst' leader leader' : Nat}, g < L.threads →
    X.Elect (g, j) pc mask inst leader → X.Elect (g, j') pc' mask' inst' leader' → j = j'
  /-- A warp-10 thread elected by its warp, in its scheduler's exit stage, has polled its response
  barrier successfully. -/
  sched_elected_exit : ∀ {g : Nat} {sd : Scheduler.D}, g < L.threads →
    (∃ j pc mask inst, X.Elect (g, j) pc mask inst (laneOf L g)) →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.sched sd))) →
      Scheduler.exitOff sd ≠ none →
    0 < okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)
  /-- A loader at its CLC poll has one task more than its successful response polls: its successful
  empty polls are 128 per task. -/
  loader_clc_count : ∀ {g : Nat} {l : Loader.D}, g < L.threads →
    (∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) → l.site =
      .clcWait →
    loaderCount L g (X.tr g) / 128 = okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) + 1
  /-- An MMA thread at its CLC poll has made 128 commits per successful response poll. -/
  mma_clc_count : ∀ {g : Nat} {m : Mma.D}, g < L.threads →
    (∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m))) → m.site = .clcWait →
    mmaCount L g (X.tr g) = 128 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)
  /-- An MMA thread's successful response polls are its completed tasks, plus one when its task has
  started: the states from the response poll on, up to the accumulator commit, count one more task
  than their commits show; the states before the response poll, after the accumulator commit and in
  the exit stage count exactly their completed tasks. -/
  mma_task_count : ∀ {g : Nat} {m : Mma.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m))) →
    okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) =
      mmaCount L g (X.tr g) / 128 + (if m.site = .elect ∨ m.site = .clcWait ∨
        m.site = .accCommit ∨ m.site = .exitArrive ∨ m.site = .exitWait ∨ m.site = .exit then 0
        else 1)
  /-- A leader scheduler at its acknowledgement poll has polled its acknowledgement barrier as often
  as its response barrier. -/
  sched_ack_count : ∀ {g : Nat} {sd : Scheduler.D}, g < L.threads →
    (∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.sched sd))) → sd.site =
      .ackWait →
    okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) (X.tr g) =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)
  /-- A consumer at its trace's end has as many successful accumulator-full polls as its successful
  response polls, less its open task, plus the accumulator it holds (`Consumer.tileOpen`,
  `Consumer.holds`). -/
  cons_tiles : ∀ {g : Nat} {c : Consumer.D}, g < L.threads →
    (∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c))) →
    consCount L g (X.tr g) + Consumer.tileOpen c =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) + Consumer.holds c
  /-- The state before a consumer warp's accumulator-full poll is a consumer state. -/
  cons_acc_state : ∀ {g k : Nat} {e : Event} {p : Nat} {ok acq : Bool} {sc : MbarScope},
    g < L.threads → g % L.block / 32 < 8 → X.get (g, k) = some e →
    e.kind = .wait (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 / 4, true⟩) p ok acq sc →
    ∃ c : Consumer.D, Frame.stateAt (code L) X g k = some (some (.inr (.cons c)))
  /-- A consumer at its accumulator-full wait (before its poll) has its accumulator-full barrier
  initialized by CTA thread 0 of its CTA: the consumer state before its last event is a consumer
  state, after the ring initialization. -/
  cons_acc_init : ∀ {g : Nat} {c : Consumer.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c))) → c.site = .accWait →
    ∃ ipc, X.get (g / L.block * L.block, Bar.initIndex ⟨.acc, g % L.block / 32 / 4, true⟩) =
      some ⟨ipc, .mbInit (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 / 4, true⟩)
        (Bar.count ⟨.acc, g % L.block / 32 / 4, true⟩)⟩
  /-- An elected MMA lane of a leader CTA's warp 8 or 9 ends its trace in an MMA state or stopped
  (its election is event 6, and the MMA states go on after it). -/
  mma_elect_state : ∀ {g j pc mask inst : Nat}, g < L.threads → g / L.block % 2 = 0 →
    (g % L.block / 32 = 8 ∨ g % L.block / 32 = 9) → X.Elect (g, j) pc mask inst (laneOf L g) →
    Frame.stateAt (code L) X g (X.tr g).length = none ∨
      ∃ m, Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m)))
  /-- An exited MMA warp thread (warp 8 or 9) has one accumulator commit to its own buffer per task:
  its commits to the buffer's full barrier are its input commits over 128, as its exit is its last
  event. -/
  mma_exit_acc : ∀ {g pc : Nat}, g < L.threads → (g % L.block / 32 = 8 ∨ g % L.block / 32 = 9) →
    (X.tr g).getLast? = some ⟨pc, .exit⟩ →
    (X.tr g).countP (commitsTo (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩)) =
      mmaCount L g (X.tr g) / 128
  /-- An accumulator commit of an MMA thread of a leader CTA notifies buffer `j`'s accumulator-full
  barrier in both CTAs of its cluster: rank `r < 2` targets the barrier of CTA `g / L.block + r`. -/
  acc_commit_ranks : ∀ {g k : Nat} {e : Event} {d : ThreadD} {sp : TcCommit.Spec} {j : Fin 2}
    (rank : Fin 16), g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k =
      some (some d) →
    e.kind = .tc (.commit sp) → sp.mbar = Bar.loc L (g / L.block) ⟨.acc, j.val, true⟩ →
    rank.val < 2 → TcCommit.target sp rank = some
      (Bar.loc L (g / L.block + rank.val) ⟨.acc, j.val, true⟩)
  /-- A loader at an empty wait is in the task numbered by its successful response polls, each of
  which was followed by a read of a response that claims a CTA. -/
  loader_tasks : ∀ {g : Nat} {l : Loader.D} {b : Fin 8}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) → l.site = .wait b →
    loaderCount L g (X.tr g) / 128 = okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) ∧
    ∀ j pc p acq sc,
      X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      ∃ pcr, ∃ src : Acc, ∃ bs rr, X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ ∧
        src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ ∧
        Flow.responseOf bs = some rr ∧ Loader.claims rr
  /-- A loader's successful response polls that are not its latest are followed by a read of a
  response that claims a CTA. -/
  loader_claims_before : ∀ {g : Nat} {l : Loader.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) →
    ∀ j pc p acq sc,
      X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 <
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) →
      ∃ pcr, ∃ src : Acc, ∃ bs rr, X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ ∧
        src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ ∧
        Flow.responseOf bs = some rr ∧ Loader.claims rr
  /-- An MMA thread of a leader CTA that won its warp's election is working (between its first
  response poll and its accumulator commit), or has finished: one task of 128 commits per
  successful response poll, the last followed by a read of a response that claims nothing. -/
  mma_leader : ∀ {g j pc mask inst : Nat}, g < L.threads → g / L.block % 2 = 0 →
    (g % L.block / 32 = 8 ∨ g % L.block / 32 = 9) →
    X.Elect (g, j) pc mask inst (laneOf L g) →
    (∃ m, Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m))) ∧ Mma.exitOff m =
      none ∧
      m.site ≠ .elect) ∨
    ((∀ s : Fin 4, (X.tr g).countP (commitsTo (inputEmpty L (g / L.block) s)) =
        32 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)) ∧
      ∃ j pc p acq sc pcr, ∃ src : Acc, ∃ bs rr,
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 =
          okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) ∧
        X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
        X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ ∧
        src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ ∧
        Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr) ∨
    (Frame.stateAt (code L) X g (X.tr g).length = none ∧ ∀ pc, (X.tr g).getLast? ≠ some ⟨pc, .exit⟩)
  /-- An MMA-warp thread of a leader CTA without an election event is before its election. -/
  mma_unelected : ∀ {g : Nat}, g < L.threads → g / L.block % 2 = 0 →
    (g % L.block / 32 = 8 ∨ g % L.block / 32 = 9) →
    (∀ j pc mask inst leader, ¬ X.Elect (g, j) pc mask inst leader) →
    ∃ d, Frame.stateAt (code L) X g (X.tr g).length = some (some d) ∧ d.exitOff = none ∧
      d.vtime L g (X.tr g) ≤ 58
  /-- A thread that exited is no longer followed by its machine. -/
  exited_state : ∀ {g pc : Nat}, g < L.threads →
    (X.tr g).getLast? = some ⟨pc, .exit⟩ → Frame.stateAt (code L) X g (X.tr g).length = none
  /-- After a role's event, every thread of the cluster has started. -/
  cluster_started : ∀ {g j h : Nat} {ev : Event} {r : Prologue.Role}, g < L.threads →
    X.get (g, j) = some ev → Frame.stateAt (code L) X g j = some (some (.inr r)) → h < L.threads →
    L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block) → X.tr h ≠ []
  /-- A thread of warps 8 to 11 in a role state has passed the prologue: CTA thread 0 of every
  CTA of its cluster has initialized each ring barrier. -/
  ring_init_exists : ∀ {g k : Nat} {r : Prologue.Role} {b : Bar} {cta : Nat}, g < L.threads →
    8 ≤ g % L.block / 32 → k ≤ (X.tr g).length → Frame.stateAt (code L) X g k =
      some (some (.inr r)) → b.Valid → cta < L.grid →
    L.clusterOfCta cta = L.clusterOfCta (g / L.block) →
    ∃ pc, X.get (cta * L.block, b.initIndex) = some ⟨pc, .mbInit (b.loc L cta) b.count⟩
  /-- A loader's site fixes its successful empty polls modulo the task's 128 blocks. -/
  loader_site_count : ∀ {g : Nat} {l : Loader.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) →
    match l.site with
    | .wait b => loaderCount L g (X.tr g) % 128 = l.q + b.val ∧ l.q % 8 = 0
    | .load b _ | .arrive b => 0 < loaderCount L g (X.tr g) ∧
        (loaderCount L g (X.tr g) - 1) % 128 = l.q + b.val
    | .clcWait | .clcLoad | .clcStatus | .clcFirst | .clcFence | .ack =>
        128 ≤ loaderCount L g (X.tr g) ∧ loaderCount L g (X.tr g) % 128 = 0
    | .drain i => 128 ≤ loaderCount L g (X.tr g) ∧ loaderCount L g (X.tr g) % 128 = i.val
    | _ => True
  /-- An MMA thread outside the common exit is on its cluster's leader CTA. -/
  mma_lead : ∀ {g : Nat} {m : Mma.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m))) → Mma.Lead L g m
  /-- No event of a followed thread is a Tensor Core copy. -/
  no_tc_cp : ∀ {g k : Nat} {e : Event} {d : ThreadD} {s : TcCopy.Spec}, g < L.threads →
    X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) →
    e.kind ≠ .tc (.cp s)
  /-- No event of a followed thread is a Tensor Memory store. -/
  no_tc_st : ∀ {g k : Nat} {e : Event} {d : ThreadD} {a : Nat} {vals : List Value}
    {sh : TcShape},
    g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) →
    e.kind ≠ .tc (.st a vals sh)
  /-- No event is a non-coherent read: the kernel's assumptions allow none. -/
  no_nc : ∀ {g k : Nat} {e : Event} {d : ThreadD} {a : Acc} {bs : List (Option Byte)},
    g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) → e.kind ≠
      .nc a bs
  /-- No event of a followed thread is a tensor prefetch. -/
  no_tensor_prefetch : ∀ {g k : Nat} {e : Event} {d : ThreadD} {a : Nat} {s : TensorPrefetch.Spec},
    g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) →
    e.kind ≠ .tensorPrefetch a s
  /-- A write other than a consumer's is CTA thread 0's address store, its event 21, and it
  happens before every role event of its cluster. -/
  base_write : ∀ {g k : Nat} {e : Event} {d : ThreadD} {a : Acc} {bs : List Byte}, g < L.threads →
    X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) → e.kind = .wr a bs →
    (∀ c, d ≠ .inr (.cons c)) → g % L.block = 0 ∧ k = 21 ∧ ∀ h j ev r, X.get (h, j) = some ev →
      Frame.stateAt (code L) X h j = some (some (.inr r)) → SameCluster L g h → baseCausality L X
          (g, k) (h, j)
  /-- A read is a role event. -/
  read_role : ∀ {g k : Nat} {e : Event} {d : ThreadD} {a : Acc} {bs : List (Option Byte)},
    g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) → e.kind =
      .rd a bs →
    ∃ r, d = .inr r
  /-- A read follows a successful poll of its CTA's response barrier, unless it reads the Tensor
  Memory base word. -/
  read_poll : ∀ {g k : Nat} {e : Event} {d : ThreadD} {a : Acc} {bs : List (Option Byte)},
    g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) → e.kind =
      .rd a bs →
    a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ ∨
      (0 < k ∧ ∃ pc p acq sc, X.get (g, k - 1) =
        some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩)
  /-- A tensor store is the TMA store of a slice `s` by its warp group's first thread, at the tile
  `(m, n)` of its task (`Consumer.TileAt`): a box from column `256 n + 32 s` and row
  `512 m + 128 q + 256 r`, for the thread's warp group `q` and its CTA's rank `r`. -/
  store_tile : ∀ {g k pc a : Nat} {sp : TensorStore.Spec} {c : Consumer.D}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tensorStore a sp⟩ →
    Frame.stateAt (code L) X g k = some (some (.inr (.cons c))) →
    ∃ s : Fin 8, c.site = .tma s ∧ Consumer.first L g = true ∧ c.m < 16 ∧ c.n < 32 ∧
      sp.rows = none ∧ sp.reduce = none ∧ (∀ i : Fin (sp.outer + 1), sp.origin i =
        if i.val = 0 then ((256 * c.n + 32 * s.val : Nat) : Int)
        else if i.val = 1 then
          ((512 * c.m + 128 * (Consumer.tidOf L g / 32 / 4) + 256 * (g / L.block % 2) : Nat) : Int)
        else 0) ∧
      Consumer.TileAt L g ((X.tr g).take k) (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)
        ((X.tr g).take k) - 1) c.m c.n
  /-- An mbarrier arrival comes before the thread's exit arrival on the cluster barrier. -/
  arrive_phase : ∀ {g k : Nat} {e : Event} {d : ThreadD} {m : Loc} {tx c : Nat} {rel : Bool}
    {sc : MbarScope}, g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k =
      some (some d) →
    e.kind = .arrive m tx c rel sc → d.clPhase ≤ 1
  /-- A commit to an input empty barrier notifies that barrier in both CTAs of the cluster. -/
  commit_ranks : ∀ {g k : Nat} {e : Event} {d : ThreadD} {sp : TcCommit.Spec} (s : Fin 4)
    (rank : Fin 16), g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k =
      some (some d) →
    e.kind = .tc (.commit sp) → sp.mbar = inputEmpty L (g / L.block) s → rank.val < 2 →
    TcCommit.target sp rank = some (inputEmpty L (g / L.block + rank.val) s)
  /-- The elected loader's counts are exact on a trace without undefined behaviour, outside the exit
  stage. On each slot, its tensor issues plus the loads it still has to issue there are three times
  its successful empty polls, less the drain's polls on the slot; the leader CTA's loader's arrivals
  plus its pending batch are its successful polls, less the drain's. -/
  loader_exact : ∀ {g : Nat} {l : Loader.D}, g < L.threads →
    (∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) → l.site.done =
      false →
    (∀ s : Fin 4, (X.tr g).countP (issuesTo (Loader.fullOf L g s)) + Loader.remaining l s +
      3 * Loader.drained l s = 3 * okPolls (Loader.emptyOf L g s) (X.tr g)) ∧
    (Loader.leader L g = true → ∀ s : Fin 4, arrivals (Loader.fullOf L g s) (X.tr g) +
      (if Loader.pending l s then 1 else 0) + Loader.drained l s =
        okPolls (Loader.emptyOf L g s) (X.tr g))
  /-- An elected loader at its exit stage, once it has polled the response (`0 < loaderCount`), on a
  trace without undefined behaviour: its tensor issues on each slot plus three are three times its
  successful empty polls, and the leader's arrivals plus one are its successful polls. -/
  loader_exit_exact : ∀ {g : Nat} {l : Loader.D}, g < L.threads →
    (∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) → l.site.done =
      true →
    0 < loaderCount L g (X.tr g) →
    (∀ s : Fin 4, (X.tr g).countP (issuesTo (Loader.fullOf L g s)) + 3 =
      3 * okPolls (Loader.emptyOf L g s) (X.tr g)) ∧
    (Loader.leader L g = true → ∀ s : Fin 4, arrivals (Loader.fullOf L g s) (X.tr g) + 1 =
      okPolls (Loader.emptyOf L g s) (X.tr g))
  /-- An elected loader at its exit stage, once it has made an empty poll (`0 < loaderCount`): its
  empty polls are 128 per response poll, plus the drain's four polls. -/
  loader_exit_tasks : ∀ {g : Nat} {l : Loader.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) → l.site.done =
      true →
    0 < loaderCount L g (X.tr g) →
    loaderCount L g (X.tr g) = 128 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) + 4
  /-- An elected loader that has left its task loop after a response, with `0 < loaderCount`: its
  latest successful response poll is followed by a read of a response that names no first CTA. -/
  loader_exit_claim : ∀ {g : Nat} {l : Loader.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) →
    ((∃ i : Fin 4, l.site = .drain i) ∨ l.site = .exitArrive ∨ l.site = .exitWait ∨ l.site =
      .exit) →
    0 < okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) →
    ∃ j pc p acq sc pcr a bs rr, (X.tr g)[j]? = some
      ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
      (X.tr g)[j + 1]? = some ⟨pcr, .rd a bs⟩ ∧ a.loc = ⟨.shared, g / L.block, L.sharedBase + 144⟩ ∧
      a.size = 16 ∧ Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr ∧
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)
  /-- A loader state's trip starts at a block that is a multiple of eight: its block register `q` is
  a multiple of eight. -/
  loader_q8 : ∀ {g : Nat} {l : Loader.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) → l.q % 8 = 0
  /-- An elected warp-11 loader in its exit stage has polled its empty barriers and the response:
  its empty polls and its response polls are positive. Its election is its seventh event, and the
  run from its loader start reaches an exit stage only through the drain's last poll. -/
  loader_elected_exit : ∀ {g : Nat} {l : Loader.D}, g < L.threads → g % L.block / 32 = 11 →
    (∃ j pc mask inst, X.Elect (g, j) pc mask inst (laneOf L g)) →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) → l.site.done =
      true →
    0 < loaderCount L g (X.tr g) ∧
      0 < okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)
  /-- An MMA thread's successful response poll that is not its latest is followed by a read of a
  response that claims a CTA. -/
  mma_claims_before : ∀ {g : Nat} {m : Mma.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m))) →
    ∀ (j pc p : Nat) (acq : Bool) (sc : MbarScope),
      (X.tr g)[j]? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 <
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) →
      ∃ pcr a bs rr, (X.tr g)[j + 1]? = some ⟨pcr, .rd a bs⟩ ∧
        a.loc = ⟨.shared, g / L.block, L.sharedBase + 144⟩ ∧ a.size = 16 ∧
        Flow.responseOf bs = some rr ∧ Loader.claims rr
  /-- A warp-11 thread without an election event is in a prologue state before its role election
  (time at most 56, no exit). -/
  loader_unelected : ∀ {g : Nat}, g < L.threads → g % L.block / 32 = 11 →
    (∀ j pc mask inst leader, ¬ X.Elect (g, j) pc mask inst leader) →
    ∃ d, Frame.stateAt (code L) X g (X.tr g).length = some (some d) ∧ (∃ p, d = .inl p) ∧
      d.exitOff = none ∧
      d.vtime L g (X.tr g) ≤ 56
  /-- A loader at a load, at any position of its run: its successful empty polls on each slot are at
  most 32 per task up to the current one, and each response poll before is followed by a read of a
  response that claims a CTA. -/
  loader_load_tasks : ∀ {g k : Nat} {l : Loader.D} {b : Fin 8} {j : Fin 3}, g < L.threads →
    Frame.stateAt (code L) X g k = some (some (.inr (.loader l))) → l.site = .load b j →
    (∀ s : Fin 4, okPolls (Loader.emptyOf L g s) ((X.tr g).take k) ≤
      32 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) + 32) ∧
    ∀ j' pc p acq sc, j' < k →
      X.get (g, j') =
        some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      ∃ pcr, ∃ src : Acc, ∃ bs rr, X.get (g, j' + 1) = some ⟨pcr, .rd src bs⟩ ∧
        src.SameFootprint
          ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0, false⟩ ∧
        Flow.responseOf bs = some rr ∧ Loader.claims rr
  /-- An MMA thread at its exit arrival, at any position of its run: its successful polls of each
  slot's full barrier are 32 per successful response poll; after a response poll, its latest one
  is followed by a read of a response that claims no CTA; without one, it is not on a leader CTA or
  lost its warp's election; its commits to each slot's empty barrier are its full polls. -/
  mma_exit_tasks : ∀ {g k : Nat} {m : Mma.D}, g < L.threads →
    Frame.stateAt (code L) X g k = some (some (.inr (.mma m))) → m.site = .exitArrive →
    (∀ s : Fin 4,
      okPolls ⟨.shared, g / L.block, L.sharedBase + 8 + 8 * s.val⟩ ((X.tr g).take k) =
      32 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k)) ∧
    (0 < okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) →
      ∃ j pc p acq sc pcr, ∃ a : Acc, ∃ bs rr, j + 1 < k ∧
        X.get (g, j) =
          some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
        X.get (g, j + 1) = some ⟨pcr, .rd a bs⟩ ∧
        a.SameFootprint
          ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0, false⟩ ∧
        Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr ∧
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 =
          okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k)) ∧
    (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) = 0 →
      Loader.leader L g = false ∨
        ∃ j pc mask inst lane, j < k ∧ X.Elect (g, j) pc mask inst lane ∧
          lane ≠ laneOf L g) ∧
    (∀ s : Fin 4, ((X.tr g).take k).countP
        (commitsTo ⟨.shared, g / L.block, L.sharedBase + 40 + 8 * s.val⟩) =
      okPolls ⟨.shared, g / L.block, L.sharedBase + 8 + 8 * s.val⟩ ((X.tr g).take k))
  /-- An MMA thread at its exit arrival, at any position of its run: its accumulator commits are its
  successful response polls, and a successful response poll that is not its latest is followed by a
  read of a response that claims a CTA. -/
  mma_exit_reads : ∀ {g k : Nat} {m : Mma.D}, g < L.threads → k ≤ (X.tr g).length →
    Frame.stateAt (code L) X g k = some (some (.inr (.mma m))) → m.site = .exitArrive →
    ((X.tr g).take k).countP
        (commitsTo (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩)) =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) ∧
    ∀ j pc p acq sc, X.get (g, j) =
        some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 <
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) →
      ∃ pcr, ∃ a : Acc, ∃ bs rr, X.get (g, j + 1) = some ⟨pcr, .rd a bs⟩ ∧
        a.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ ∧
        Flow.responseOf bs = some rr ∧ Loader.claims rr
  /-- An elected loader whose trace ends with its exit has drained: it polled the response, its
  successful empty polls on each slot are 32 per successful response poll plus one, and its latest
  successful response poll is followed by a read of a response that claims no CTA. -/
  loader_exit_drain : ∀ {g pc : Nat}, g < L.threads → g % L.block / 32 = 11 →
    (∃ j pce mask inst, X.Elect (g, j) pce mask inst (laneOf L g)) →
    (X.tr g).getLast? = some ⟨pc, .exit⟩ →
    0 < okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) ∧
    (∀ s : Fin 4, okPolls (InputRing.emptyLoc L (g / L.block) s) (X.tr g) =
      32 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) + 1) ∧
    ∃ j pcw p acq sc pcr, ∃ a : Acc, ∃ bs rr,
      X.get (g, j) = some ⟨pcw, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
      X.get (g, j + 1) = some ⟨pcr, .rd a bs⟩ ∧
      a.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ ∧
      Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr ∧
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)
  /-- A consumer whose trace ends with its exit: its successful polls of its accumulator's full
  barrier are its successful response polls, and its latest successful response poll is followed by
  a read of a response that claims no CTA. -/
  cons_exit_tiles : ∀ {g pc : Nat}, g < L.threads → g % L.block / 32 < 8 →
    (X.tr g).getLast? = some ⟨pc, .exit⟩ →
    okPolls (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 / 4, true⟩) (X.tr g) =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) ∧
    ∃ j pcw p acq sc pcr, ∃ a : Acc, ∃ bs rr,
      X.get (g, j) = some ⟨pcw, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
      X.get (g, j + 1) = some ⟨pcr, .rd a bs⟩ ∧
      a.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ ∧
      Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr ∧
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)
  /-- A consumer's TMA stores along its run: only its group's first thread reaches a slice's fence
  and TMA store, and without undefined behaviour the first thread has issued one TMA store per
  commit plus the one of the slice it is committing (`Consumer.TmaRel`). -/
  cons_tmas : ∀ {g k : Nat} {c : Consumer.D}, g < L.threads →
    Frame.stateAt (code L) X g k = some (some (.inr (.cons c))) →
      Consumer.TmaRel L g c ((X.tr g).take k)
  /-- A group's first consumer thread whose trace ends with its exit, without undefined behaviour,
  issued eight TMA stores per successful response poll. -/
  cons_exit_tmas : ∀ {g pc : Nat}, g < L.threads → g % L.block / 32 < 8 →
    Consumer.first L g = true → (∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) →
    (X.tr g).getLast? = some ⟨pc, .exit⟩ →
    storeIssues (X.tr g) = 8 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)
  /-- At an MMA thread's full wait on slot `s`, its successful polls of the slot's full barrier are
  its round-robin share of its commits to the input empty barriers. -/
  mma_full_count : ∀ {g : Nat} {m : Mma.D} {s : Fin 4}, g < L.threads →
    (∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m))) → m.site = .full s →
    okPolls ⟨.shared, g / L.block, L.sharedBase + 8 + 8 * s.val⟩ (X.tr g) =
      (mmaCount L g (X.tr g) + 3 - s.val) / 4
  /-- An MMA thread's accumulator commits, with the one it is making, are its commits to the input
  empty barriers over 128. Its successful polls of its accumulator-empty barrier, with the
  accumulator commit it is making, are that count plus one when it holds an accumulator. -/
  mma_acc_count : ∀ {g : Nat} {m : Mma.D}, g < L.threads →
    (∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m))) →
    (X.tr g).countP (commitsTo (Bar.loc L (g / L.block) ⟨.acc, m.w % 2, true⟩)) +
      (if m.site = .accCommit then 1 else 0) = mmaCount L g (X.tr g) / 128 ∧
    okPolls (Bar.loc L (g / L.block) ⟨.acc, m.w % 2, false⟩) (X.tr g) +
      (if m.site = .accCommit then 1 else 0) = mmaCount L g (X.tr g) / 128 +
        (match m.site with | .full _ | .mma _ _ | .commit _ | .accCommit => 1 | _ => 0)
  /-- A thread's cluster barrier arrivals at its trace's end are its state's cluster phase. -/
  cl_phase : ∀ {g : Nat} {d : ThreadD}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some d) → clArrives (X.tr g) = d.clPhase
  /-- A thread's cluster barrier operations: those so far count its state's (`ThreadD.clOps`); an
  operation is every thread's operation of that count (`clEvent`), at a cluster site; an exit
  follows all four. -/
  cl_ops : ∀ {g k : Nat} {d : ThreadD}, g < L.threads → Frame.stateAt (code L) X g k =
    some (some d) →
    clOps ((X.tr g).take k) = d.clOps ∧ ∀ e, X.get (g, k) = some e →
      (isCluster e = true → e = clEvent d.clOps ∧ d.AtCluster) ∧ (e.kind = .exit → d.clOps = 4)
  /-- A consumer at a named barrier site can arrive there, with its group's 128 threads. -/
  bar_fire : ∀ {g : Nat} {c : Consumer.D} {t : TState}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c))) →
    (c.site = .clcBar ∨ (∃ k, c.site = .barA k) ∨ ∃ k, c.site = .barB k) →
    Run kernel Prod L g {} (X.tr g) (some t) → ∃ t1 u id,
      Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨t1.pc, .bar id (some 128)⟩ (some u)
  /-- A consumer at a slice's drain or at its final drain can perform its bulk-group wait. -/
  bulk_fire : ∀ {g : Nat} {c : Consumer.D} {t : TState}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c))) →
    ((∃ k, c.site = .drain k) ∨ c.site = .finalDrain) →
    Run kernel Prod L g {} (X.tr g) (some t) → ∃ t1 u mode n,
      Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨t1.pc, .bulkWait mode n⟩ (some u)
  /-- A thread at a cluster site can perform its cluster operation. -/
  cluster_fire : ∀ {g : Nat} {d : ThreadD} {t : TState}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some d) → d.AtCluster →
    Run kernel Prod L g {} (X.tr g) (some t) → ∃ t1 u,
      Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 (clEvent d.clOps) (some u)
  /-- A thread at its trace's end fires the event of its site's kind: by local steps it reaches a
  concrete state of its machine state, whose template is undefined behaviour or of the kind
  (`KindTmpl`). -/
  fire : ∀ {g : Nat} {d : ThreadD} {t : TState}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some d) →
    Run kernel Prod L g {} (X.tr g) (some t) → ∃ t1 m,
      Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧ (code L g).AtD d t1 ∧
      out kernel Prod L g t1 = .ev m ∧ ((∃ f, m = .ub f) ∨ KindTmpl L g (nextKind d) m)
  /-- A consumer at its trace's end has as many successful accumulator-full polls as its arrivals
  on its accumulator's empty barrier in the leader CTA, plus the accumulator it holds. -/
  cons_acc_count : ∀ {g : Nat} {c : Consumer.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c))) →
    consCount L g (X.tr g) = arrivals (Bar.loc L (2 * (g / L.block / 2))
      ⟨.acc, Consumer.tidOf L g / 32 / 4, false⟩) (X.tr g) + Consumer.holds c
  /-- A consumer in its exit stage has read, after a successful poll of its CTA's response barrier,
  a response that claims no CTA. -/
  cons_exit_read : ∀ {g : Nat} {c : Consumer.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c))) → Consumer.exitOff c ≠
      none →
    ∃ j pc p acq sc pcr, ∃ src : Acc, ∃ bs rr,
      (X.tr g)[j]? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
      (X.tr g)[j + 1]? = some ⟨pcr, .rd src bs⟩ ∧
      src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ ∧
      Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr
  /-- A scheduler's exit-stage facts at every state of its run (`Scheduler.ExitQ`): its exit stage
  follows a no-claim query or an election that left it unelected, and its fence or acknowledgement
  of a no-CTA value follows a no-claim query. -/
  sched_exit_query : ∀ {g k : Nat} {sd : Scheduler.D}, g < L.threads →
    Frame.stateAt (code L) X g k = some (some (.inr (.sched sd))) →
      Scheduler.ExitQ L g sd ((X.tr g).take k)
  /-- A loader's exit-stage facts at every state of its run (`Loader.ExitQ`). -/
  loader_exit_query : ∀ {g k : Nat} {l : Loader.D}, g < L.threads →
    Frame.stateAt (code L) X g k = some (some (.inr (.loader l))) →
      Loader.ExitQ L g l ((X.tr g).take k)
  /-- A scheduler's wait on its CTA's acknowledgement barrier is its acknowledgement poll. -/
  sched_ack_wait_site : ∀ {g k : Nat} {e : Event} {sd : Scheduler.D} {p : Nat} {ok acq : Bool}
    {sc : MbarScope}, g < L.threads → X.get (g, k) = some e →
    Frame.stateAt (code L) X g k = some (some (.inr (.sched sd))) →
    e.kind = .wait (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) p ok acq sc → sd.site = .ackWait
  /-- A scheduler at its acknowledgement wait has read, after each of its earlier successful
  response polls, a response that claims a CTA. -/
  sched_ack_claims : ∀ {g : Nat} {sd : Scheduler.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.sched sd))) → sd.site =
      .ackWait →
    ∀ j pc p acq sc, j + 1 < (X.tr g).length →
      (X.tr g)[j]? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      ∃ pcr, ∃ src : Acc, ∃ bs rr, (X.tr g)[j + 1]? = some ⟨pcr, .rd src bs⟩ ∧
        src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ ∧
        Flow.responseOf bs = some rr ∧ Loader.claims rr
  /-- An exit event is fired from an exit stage of its thread. -/
  exit_event_state : ∀ {g k : Nat} {pc : Nat}, g < L.threads → X.get (g, k) = some ⟨pc, .exit⟩ →
    ∃ d : ThreadD, Frame.stateAt (code L) X g k = some (some d) ∧ d.exitOff ≠ none
  /-- A loader's counts at its trace's end, by its site: its response polls and its empty polls are
  the tasks of 128 (`LoaderTasks.CountOK`), as its site fixes them. -/
  loader_count_ok : ∀ {g : Nat} {l : Loader.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) →
    (∀ b, l.site = .wait b → okPolls (clcResp L g) (X.tr g) = loaderCount L g (X.tr g) / 128) ∧
    (∀ b j, l.site = .load b j →
      okPolls (clcResp L g) (X.tr g) = (loaderCount L g (X.tr g) - 1) / 128) ∧
    (∀ b, l.site = .arrive b →
      okPolls (clcResp L g) (X.tr g) = (loaderCount L g (X.tr g) - 1) / 128) ∧
    (l.site = .clcWait → okPolls (clcResp L g) (X.tr g) + 1 = loaderCount L g (X.tr g) / 128) ∧
    ((l.site = .clcLoad ∨ l.site = .clcStatus ∨ l.site = .clcFirst ∨ l.site = .clcFence ∨
        l.site = .ack) → okPolls (clcResp L g) (X.tr g) = loaderCount L g (X.tr g) / 128) ∧
    (∀ i, l.site = .drain i → okPolls (clcResp L g) (X.tr g) = loaderCount L g (X.tr g) / 128)
  /-- A thread's register requests at a prefix of its trace count its state's: none before its
  request's site, one after it. -/
  reg_ops : ∀ {g k : Nat} {d : ThreadD}, g < L.threads → Frame.stateAt (code L) X g k =
    some (some d) →
    regOps ((X.tr g).take k) = d.regOps
  /-- A register request is its warp's (its program position, direction and count), and is its
  thread's first; the thread's state after it exists. -/
  reg_event : ∀ {g k pc : Nat} {inc : Bool} {n inst : Nat}, g < L.threads →
    X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩ →
    (pc, inc, n) = regRequest (g % L.block / 32) ∧ regOps ((X.tr g).take k) = 0 ∧
      ∃ d, Frame.stateAt (code L) X g (k + 1) = some (some d)
  /-- A thread at its trace's end has its next event early in the rank table before its register
  request (outside the exit stage, at most `regEarly` of its warp), and late after it (in the exit
  stage, or at least `regLate` of its warp). -/
  reg_stage : ∀ {g : Nat} {d : ThreadD}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some d) →
    (regOps (X.tr g) = 0 → d.exitOff = none ∧
      d.vtime L g (X.tr g) ≤ regEarly (g % L.block / 32)) ∧
    (regOps (X.tr g) ≠ 0 → d.exitOff.isSome ∨
      regLate (g % L.block / 32) ≤ d.vtime L g (X.tr g))
  /-- A thread at its register request site can issue the request. -/
  reg_fire : ∀ {g : Nat} {d : ThreadD} {t : TState}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some d) → d.AtSetMaxReg →
    Run kernel Prod L g {} (X.tr g) (some t) → ∃ t1 u,
      Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧ ∀ inst,
        EStep kernel Prod L g t1
          ⟨d.regRequest.1, .setMaxReg d.regRequest.2.1 d.regRequest.2.2 inst⟩ (some u)
  /-- A thread at its register request site has just made its cluster wait. -/
  reg_prev : ∀ {g : Nat} {d : ThreadD}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some d) → d.AtSetMaxReg →
    ∃ pc, X.get (g, (X.tr g).length - 1) = some ⟨pc, .cluster (.wait true)⟩
  /-- A consumer at its trace's end: its arrivals on its group's CLC barrier, with the response and
  the accumulator it holds, are its accumulator polls plus its open task; its arrivals on its output
  barrier, with the sixteen of its epilogue in progress and the accumulator it holds, are sixteen
  per accumulator poll plus its slice's position; and a state that has started an epilogue, with the
  accumulator it holds, is within its accumulator polls. -/
  cons_bars : ∀ {g : Nat} {c : Consumer.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c))) →
    (X.tr g).countP (Execution.isBarId (Consumer.tidOf L g / 32 / 4 + 1)) + c.clcHold +
        Consumer.holds c = consCount L g (X.tr g) + Consumer.tileOpen c ∧
      Consumer.outBars L g (X.tr g) + 16 * (Consumer.holds c + c.inEpi) =
        16 * consCount L g (X.tr g) + c.outPhase ∧
      c.started + Consumer.holds c ≤ consCount L g (X.tr g)
  /-- A consumer at an event of its trace read, before it, at each successful response poll that is
  not its latest there, a response that claims a CTA. -/
  cons_claims : ∀ {g k : Nat} {c : Consumer.D}, g < L.threads →
    Frame.stateAt (code L) X g k = some (some (.inr (.cons c))) →
    ∀ j pc p acq sc pcr src bs rr,
      ((X.tr g).take k)[j]? =
        some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      ((X.tr g).take k)[j + 1]? = some ⟨pcr, .rd src bs⟩ →
      src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ →
      Flow.responseOf bs = some rr →
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (((X.tr g).take k).take j) + 1 <
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) → Loader.claims rr
  /-- A consumer's state after a named barrier arrival is in its task loop, not in its exit stage
  and past its start. -/
  cons_after_bar : ∀ {g k : Nat} {e : Event} {id : Nat} {cnt : Option Nat} {c0 c : Consumer.D},
    g < L.threads → X.get (g, k) = some e → e.kind = .bar id cnt →
    Frame.stateAt (code L) X g k = some (some (.inr (.cons c0))) →
    Frame.stateAt (code L) X g (k + 1) = some (some (.inr (.cons c))) →
    Consumer.exitOff c = none ∧ c.site ≠ .setMaxReg
  /-- A consumer at its trace's end: its warp-collective `tcgen05` events, with thirty-two for the
  accumulator it holds, are its paired Tensor Memory operations, thirty-two per accumulator-full
  poll and its position in the tile it is loading (`Consumer.D.tcPos`). -/
  cons_tc : ∀ {g : Nat} {c : Consumer.D}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c))) →
    (X.tr g).countP isTcColl + 32 * Consumer.holds c =
      tmemOps (X.tr g) + 32 * consCount L g (X.tr g) + c.tcPos
  /-- A consumer's state after a Tensor Memory load or wait (a thread's, whatever its state before)
  is in its task loop, not in its exit stage and past its start. -/
  cons_after_tc : ∀ {g k : Nat} {e : Event} {d0 : ThreadD} {c : Consumer.D},
    g < L.threads → X.get (g, k) = some e → isTcData e = true →
    Frame.stateAt (code L) X g k = some (some d0) →
    Frame.stateAt (code L) X g (k + 1) = some (some (.inr (.cons c))) →
    Consumer.exitOff c = none ∧ c.site ≠ .setMaxReg
  /-- A consumer at a load's wait, with its run, reaches the wait instruction, which fires the wait.
  -/
  cons_wait_fire : ∀ {g : Nat} {c : Consumer.D} {t : TState}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c))) →
      (∃ j, c.site = .loadWait j) →
    Run kernel Prod L g {} (X.tr g) (some t) → ∃ t1 u,
      Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
        EStep kernel Prod L g t1 ⟨t1.pc, .tc .waitLd⟩ (some u)
  /-- A data event is a consumer's, and leaves it at a consumer's state when every word its earlier
  loads returned is a single-precision float (the load's wait converts them). -/
  cons_data_next : ∀ {g k : Nat} {e : Event} {d : ThreadD}, g < L.threads →
    X.get (g, k) = some e → isTcData e = true → Frame.stateAt (code L) X g k = some (some d) →
    (∀ k' pc a vals sh, k' < k → X.get (g, k') = some ⟨pc, .tc (.ld a vals sh)⟩ →
      ∀ v ∈ vals, ∃ r, v = .float .f32 r) →
    ∃ c, Frame.stateAt (code L) X g (k + 1) = some (some (.inr (.cons c)))
  /-- An MMA is issued by MMA warp 8 or 9 of a leader CTA holding its buffer's accumulator: its
  accumulator commits before it are one fewer than its successful polls of the empty barrier. -/
  mma_acc_batch : ∀ {g k : Nat} {e : Event} {d : ThreadD} {dst : Nat} {sp : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat}, g < L.threads → X.get (g, k) = some e →
    Frame.stateAt (code L) X g k = some (some d) → e.kind = .tc (.mma dst sp acc mask) →
    (g % L.block / 32 = 8 ∨ g % L.block / 32 = 9) ∧ g / L.block % 2 = 0 ∧
      ((X.tr g).take k).countP
          (commitsTo (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩)) + 1 =
        okPolls (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, false⟩) ((X.tr g).take k)
  /-- A Tensor Memory load is issued by a consumer warp holding its accumulator: its successful
  polls of its accumulator's full barrier are one more than its arrivals on the empty barrier; its
  next event is the load's wait. -/
  cons_load : ∀ {g k pc a : Nat} {vals : List Value} {d : ThreadD}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.ld a vals .s32x32b)⟩ →
    Frame.stateAt (code L) X g k = some (some d) →
    g % L.block / 32 < 8 ∧
      okPolls (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 / 4, true⟩) ((X.tr g).take k) =
        arrivals (Bar.loc L (2 * (g / L.block / 2)) ⟨.acc, g % L.block / 32 / 4, false⟩)
          ((X.tr g).take k) + 1 ∧
      (k + 1 < (X.tr g).length → X.WaitLd (g, k + 1))
  /-- Every Tensor Memory load has the `.32x32b` shape. -/
  ld_shape : ∀ {g k pc a : Nat} {vals : List Value} {sh : TcShape}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩ → sh = .s32x32b
  /-- A Tensor Memory load returns sixteen words (the site's destination registers). -/
  ld_len : ∀ {g k pc a : Nat} {vals : List Value}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.ld a vals .s32x32b)⟩ → vals.length = 16
  /-- An accumulator commit follows an MMA of its thread. -/
  acc_commit_mma : ∀ {g k : Nat} {e : Event} {d : ThreadD} {sp : TcCommit.Spec}, g < L.threads →
    X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) → e.kind =
      .tc (.commit sp) →
    sp.mbar = Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩ →
    ∃ k' pc dst sp' acc mask, k' < k ∧ X.get (g, k') = some ⟨pc, .tc (.mma dst sp' acc mask)⟩
  /-- A thread's paired Tensor Memory operations at a prefix of its trace, when the trace has no
  undefined behaviour, count its state's (by whether the thread is in warp 0). -/
  tmem_ops : ∀ {g k : Nat} {d : ThreadD}, g < L.threads →
    (∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) → Frame.stateAt (code L) X g k = some (some d) →
    tmemOps ((X.tr g).take k) = d.tmemOps (decide (g % L.block / 32 = 0))
  /-- A paired Tensor Memory operation is made by warp 0, in group two; it is its thread's `n`-th,
  at the `n`-th operation's site and of its shape, and the state after it is that operation's
  successor. -/
  tmem_event : ∀ {g k pc : Nat} {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request},
    g < L.threads → (∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) →
    X.get (g, k) = some ⟨pc, .tc (.resource grp dst act)⟩ →
    g % L.block / 32 = 0 ∧ grp = .two ∧ pc = tmemPc (tmemOps ((X.tr g).take k)) ∧
      TmemShape (tmemOps ((X.tr g).take k)) act ∧
      ∃ d, Frame.stateAt (code L) X g (k + 1) = some (some d) ∧
        TmemAfter (tmemOps ((X.tr g).take k)) d
  /-- A thread of warp 0 at its trace's end is in the rank table before its next operation. -/
  tmem_stage : ∀ {g : Nat} {d : ThreadD}, g < L.threads →
    (∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) → g % L.block / 32 = 0 →
    Frame.stateAt (code L) X g (X.tr g).length = some (some d) → TmemStage (tmemOps (X.tr g)) d
  /-- A thread of warp 0 exits after its three operations. -/
  tmem_exit : ∀ {g k pc : Nat}, g < L.threads → (∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) →
    g % L.block / 32 = 0 → X.get (g, k) = some ⟨pc, .exit⟩ → tmemOps ((X.tr g).take k) = 3
  /-- A thread at a paired Tensor Memory site fires the operation or undefined behaviour. -/
  tmem_fire : ∀ {g : Nat} {d : ThreadD} {t : TState}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some d) → d.AtTmem →
    Run kernel Prod L g {} (X.tr g) (some t) → ∃ t1 m,
      Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧ out kernel Prod L g t1 = .ev m ∧
      Flow.TmemTmpl .two m
  /-- A thread at a warp-synchronous collective site can perform every event of the site. -/
  coll_fire : ∀ {g : Nat} {d : ThreadD} {s : CollSite} {t : TState}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some d) → d.coll = some s →
    Run kernel Prod L g {} (X.tr g) (some t) → ∃ t1,
      Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      ∀ e, s.Fires L g e → ∃ u, EStep kernel Prod L g t1 e (some u)
  /-- A thread at a collective site has made no event of an instance of the site. -/
  coll_none : ∀ {g j : Nat} {e : Event} {d : ThreadD} {s : CollSite}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some d) → d.coll = some s → X.get (g, j) =
      some e →
    ¬ s.Matches e
  /-- A thread's events before its collective site (`CollSite.Before`). -/
  coll_before : ∀ {g : Nat} {d : ThreadD} {s : CollSite}, g < L.threads →
    (∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) →
    Frame.stateAt (code L) X g (X.tr g).length = some (some d) → d.coll = some s → s.Before X g
  /-- A lane of the warp of a thread at a collective site has made an event of an instance of the
  site, or stopped before the site without exiting, or is at the site, or at a site whose time is at
  least 2 below the thread's. -/
  coll_lane : ∀ {g h : Nat} {d : ThreadD} {s : CollSite}, g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some d) → d.coll = some s → SameWarp L g h →
    (∀ k pc f, X.get (h, k) ≠ some ⟨pc, .ub f⟩) →
    (∃ j e, X.get (h, j) = some e ∧ s.Matches e) ∨
    (Frame.stateAt (code L) X h (X.tr h).length = none ∧
      (∀ pc, (X.tr h).getLast? ≠ some ⟨pc, .exit⟩) ∧
      s ≠ .shfl) ∨
    ∃ d', Frame.stateAt (code L) X h (X.tr h).length = some (some d') ∧
      (d'.coll = some s ∨ (d'.exitOff = none ∧ d'.vtime L h (X.tr h) + 2 ≤ d.vtime L g (X.tr g)))
  /-- A tensor issue is the loader's load at block `b`, part `j`: the copy of the A or B map's
  64 x 128 box (held as the first or second parameter) into tile `j` of slot `b % 4` of the loader's
  CTA, routed from the loader's CTA, completing on the slot's full barrier, after three issues there
  per earlier successful poll of the slot's empty barrier, less the batch's loads still to issue. -/
  tensor_issue : ∀ {g k : Nat} {e : Event} {d : ThreadD} {a : Nat} {sp : TensorCopy.Spec},
    g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) →
    e.kind = .tensorIssue a sp →
    ∃ (l : Loader.D) (b : Fin 8) (j : Fin 3), d = .inr (.loader l) ∧ l.site = .load b j ∧
      sp.mbar = InputRing.fullLoc L (g / L.block / 2) (InputRing.slotOf b) ∧
      (∃ base cls origin, sp = stageCopy (Fp16Gemm8192.mapA base cls) origin (g / L.block)
        (L.sharedBase + InputRing.stageOff (InputRing.slotOf b).val j.val) sp.mbar true .two ∧
        L.tensorMaps a = some ⟨1, Fp16Gemm8192.mapA base cls⟩ ∧
        (L.paramObjects "gemm_kernel_param_0" = some (mapParam "gemm_kernel_param_0", a) ∨
          L.paramObjects "gemm_kernel_param_1" = some (mapParam "gemm_kernel_param_1", a))) ∧
      TensorCopy.RoutingOk L (g / L.block) sp ∧
      ((X.tr g).take k).countP (issuesTo (Loader.fullOf L g (InputRing.slotOf b))) + 3 =
        3 * okPolls (Loader.emptyOf L g (InputRing.slotOf b)) ((X.tr g).take k) + j.val
  /-- An MMA is the MMA thread's MMA at slot `s`, K step `j`, on its cluster's leader CTA: the MMA
  of its warp's A tile and the B tile of slot `s`, K step `j`, after one more successful poll of the
  slot's full barrier than its commits to the slot's empty barrier. -/
  mma_issue : ∀ {g k : Nat} {e : Event} {d : ThreadD} {dst : Nat} {sp : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat}, g < L.threads → X.get (g, k) = some e →
    Frame.stateAt (code L) X g k = some (some d) → e.kind = .tc (.mma dst sp acc mask) →
    ∃ (m : Mma.D) (s j : Fin 4), d = .inr (.mma m) ∧ m.site = .mma s j ∧ g / L.block % 2 = 0 ∧
      sp = InputRing.mmaSpec L (g / L.block) (g % L.block / 32) s.val j.val ∧
      ((X.tr g).take k).countP (commitsTo ⟨.shared, g / L.block, L.sharedBase + 40 + 8 * s.val⟩) +
        1 =
        okPolls ⟨.shared, g / L.block, L.sharedBase + 8 + 8 * s.val⟩ ((X.tr g).take k)
  /-- An MMA thread's commit to slot `s`'s empty barrier follows the slot's four MMAs, right before
  it: the MMA of K step `t` is `4 - t` events before the commit, with as many commits to the slot
  before it, and one more successful poll of the slot's full barrier. -/
  mma_batch : ∀ {g jc : Nat} {e : Event} {m : Mma.D} {sp : TcCommit.Spec} {s : Fin 4},
    g < L.threads → X.get (g, jc) = some e → Frame.stateAt (code L) X g jc =
      some (some (.inr (.mma m))) →
    e.kind = .tc (.commit sp) → sp.mbar = ⟨.shared, g / L.block, L.sharedBase + 40 + 8 * s.val⟩ →
    4 ≤ jc ∧ ∀ t : Fin 4, ∃ pc dst acc mask, X.get (g, jc - 4 + t.val) =
        some ⟨pc, .tc (.mma dst (InputRing.mmaSpec L (g / L.block) (g % L.block / 32) s.val t.val)
          acc mask)⟩ ∧
      ((X.tr g).take (jc - 4 + t.val)).countP
          (commitsTo ⟨.shared, g / L.block, L.sharedBase + 40 + 8 * s.val⟩) =
        ((X.tr g).take jc).countP (commitsTo ⟨.shared, g / L.block, L.sharedBase + 40 + 8 *
          s.val⟩) ∧
      ((X.tr g).take (jc - 4 + t.val)).countP
          (commitsTo ⟨.shared, g / L.block, L.sharedBase + 40 + 8 * s.val⟩) + 1 =
        okPolls ⟨.shared, g / L.block, L.sharedBase + 8 + 8 * s.val⟩
          ((X.tr g).take (jc - 4 + t.val))
  /-- A thread writes shared memory: every store of the kernel names shared memory. -/
  write_shared : ∀ {g k : Nat} {e : Event} {d : ThreadD} {a : Acc} {bs : List Byte},
    g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) →
    e.kind = .wr a bs → a.loc.space = .shared
  /-- A tensor store reads the output map, held as the third parameter. -/
  store_map : ∀ {g k : Nat} {e : Event} {d : ThreadD} {a : Nat} {sp : TensorStore.Spec},
    g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) →
    e.kind = .tensorStore a sp →
    L.paramObjects "gemm_kernel_param_2" = some (mapParam "gemm_kernel_param_2", a) ∧
      L.tensorMaps a = some ⟨sp.outer, sp.descriptor⟩
  /-- An MMA writes its warp's accumulator buffer, at Tensor Memory column `256 * (w % 2)`, with
  no output lane masked. -/
  mma_dst : ∀ {g k : Nat} {e : Event} {d : ThreadD} {dst : Nat} {sp : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat}, g < L.threads → X.get (g, k) = some e →
    Frame.stateAt (code L) X g k = some (some d) → e.kind = .tc (.mma dst sp acc mask) →
    dst = 256 * (g % L.block / 32 % 2) ∧ mask = List.replicate 8 0
  /-- An accumulating MMA follows an MMA of its thread. -/
  mma_acc_prev : ∀ {g k : Nat} {e : Event} {d : ThreadD} {dst : Nat} {sp : TcMma.OperandSpec}
    {mask : List Nat}, g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k =
      some (some d) →
    e.kind = .tc (.mma dst sp true mask) →
    ∃ k' pc' dst' sp' acc' mask', k' < k ∧
      X.get (g, k') = some ⟨pc', .tc (.mma dst' sp' acc' mask')⟩
  /-- A commit is an MMA thread's, on a leader CTA: a slot's commit to its input empty barrier or
  the accumulator commit to its buffer's full barrier, multicast to the CTA pair. -/
  commit_spec : ∀ {g k : Nat} {e : Event} {d : ThreadD} {sp : TcCommit.Spec}, g < L.threads →
    X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) → e.kind =
      .tc (.commit sp) →
    ∃ m : Mma.D, d = .inr (.mma m) ∧ g / L.block % 2 = 0 ∧
      ((∃ s : Fin 4, m.site = .commit s ∧
          sp = ⟨.two, ⟨.shared, g / L.block, L.sharedBase + 40 + 8 * s.val⟩, 3,
            g / L.block / 2 * 2, 2⟩) ∨
        (m.site = .accCommit ∧ sp = ⟨.two, ⟨.shared, g / L.block,
          L.sharedBase + 8 * (g % L.block / 32 % 2) + 72⟩, 3, g / L.block / 2 * 2, 2⟩))
  /-- A thread's undefined behaviour fires after its machine stopped, or at its deallocation right
  after its read of its CTA's base word, whose bytes rebuild to no integer. -/
  ub_site : ∀ {g k pc : Nat} {f : Fault}, g < L.threads → X.get (g, k) = some ⟨pc, .ub f⟩ →
    Frame.stateAt (code L) X g k = none ∨ (0 < k ∧ ∃ pcr a bs, X.get (g, k - 1) =
      some ⟨pcr, .rd a bs⟩ ∧
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ ∧ a.size = 4 ∧
        ∀ w x, rebuild 3 bs ≠ .ok (.bits w x))
  /-- A thread's machine stops after an event that another follows only after a read of its CTA's
  response buffer, right after a successful poll of the response barrier, whose bytes are no
  response; after a read of its CTA's base word whose bytes rebuild to no value; or after a Tensor
  Memory data event. -/
  stop_read : ∀ {g k : Nat} {e : Event} {d : ThreadD}, g < L.threads → X.get (g, k) = some e →
    k + 1 < (X.tr g).length → Frame.stateAt (code L) X g k = some (some d) →
      Frame.stateAt (code L) X g (k + 1) = none →
    (∃ a bs, e.kind = .rd a bs ∧ a.loc = ⟨.shared, g / L.block, L.sharedBase + 144⟩ ∧
        a.size = 16 ∧ Flow.responseOf bs = none ∧ 0 < k ∧ ∃ pc p acq sc, X.get (g, k - 1) =
          some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩) ∨
      (∃ a bs f, e.kind = .rd a bs ∧ a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ ∧ a.size = 4 ∧
        rebuild 3 bs = .error f) ∨
      isTcData e = true
  /-- A tensor load reads its map's box inside the map: no slot of the box is out of bounds. -/
  tensor_bounds : ∀ {g k : Nat} {e : Event} {d : ThreadD} {a : Nat} {sp : TensorCopy.Spec},
    g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) →
    e.kind = .tensorIssue a sp → ¬ TensorHasOob sp.descriptor sp.origin sp.rows
  /-- A tensor store writes its map's box inside the map: no slot of the box is out of bounds. -/
  store_bounds : ∀ {g k : Nat} {e : Event} {d : ThreadD} {a : Nat} {sp : TensorStore.Spec},
    g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) →
    e.kind = .tensorStore a sp → ¬ TensorHasOob sp.descriptor sp.origin sp.rows
  /-- A role event of a thread comes after its CTA thread 0's allocation request of the Tensor
  Memory (event 20: 512 columns, into the CTA's base word) and its store of the returned address
  (event 21, with the column the allocation returned). -/
  base_written : ∀ {g k : Nat} {ev : Event} {r : Prologue.Role}, g < L.threads →
    X.get (g, k) = some ev → Frame.stateAt (code L) X g k = some (some (.inr r)) →
    ∃ pca pcw col, X.get (g / L.block * L.block, 20) = some ⟨pca, .tc (.resource .two
        (some ⟨.shared, g / L.block, L.sharedBase⟩) (.alloc 512))⟩ ∧
      X.get (g / L.block * L.block, 21) = some ⟨pcw, .wr
        ⟨⟨.shared, g / L.block, L.sharedBase⟩, 4, false, false, .cta, 0, false⟩ (b32 col).toBytes⟩ ∧
      col < 2 ^ 16 ∧ baseCausality L X (g / L.block * L.block, 21) (g, k)
  /-- A paired Tensor Memory operation is made by warp 0, in group two; it is its thread's `n`-th,
  at the `n`-th operation's site and of its shape, and the state after it is that operation's
  successor (at every event: the events before it are not undefined behaviour). -/
  tmem_event_at : ∀ {g k pc : Nat} {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request},
    g < L.threads → X.get (g, k) = some ⟨pc, .tc (.resource grp dst act)⟩ →
    g % L.block / 32 = 0 ∧ grp = .two ∧ pc = tmemPc (tmemOps ((X.tr g).take k)) ∧
      TmemShape (tmemOps ((X.tr g).take k)) act ∧
      ∃ d, Frame.stateAt (code L) X g (k + 1) = some (some d) ∧
        TmemAfter (tmemOps ((X.tr g).take k)) d
  /-- A thread of warp 0 exits after its three paired operations. -/
  tmem_exit_at : ∀ {g k pc : Nat}, g < L.threads → g % L.block / 32 = 0 →
    X.get (g, k) = some ⟨pc, .exit⟩ → tmemOps ((X.tr g).take k) = 3
  /-- A deallocation frees the base its thread read from its CTA's base word right before it: the
  column the read's bytes hold, as a 32-bit integer. -/
  dealloc_base : ∀ {g k pc : Nat} {grp : CtaGroup} {dst : Option Loc} {a n : Nat}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩ →
    0 < k ∧ ∃ pcr ra bs, X.get (g, k - 1) = some ⟨pcr, .rd ra bs⟩ ∧
      ra.loc = ⟨.shared, g / L.block, L.sharedBase⟩ ∧ ra.size = 4 ∧
      ∀ col, bs = (b32 col).toBytes.map some → a = col % 2 ^ 32
  /-- A warp-collective `tcgen05` event is a consumer warp's, at a position of its warp's sequence
  (`tcCollPc`, `TcCollKind`) that its thread's collective events before it, with its successful
  response polls, determine (`TcCollAt`). -/
  tc_coll : ∀ {g k pc : Nat} {kd : TcKind}, g < L.threads → X.get (g, k) = some ⟨pc, .tc kd⟩ →
    isTcColl ⟨pc, .tc kd⟩ = true →
    g % L.block / 32 < 8 ∧ ∃ p, pc = tcCollPc p ∧ TcCollKind L g p kd ∧
      TcCollAt L g p ((X.tr g).take k)
  /-- A consumer exits after all of its collective events, its latest response read claiming no
  CTA (`TcExitAt`). -/
  tc_exit : ∀ {g k pc : Nat}, g < L.threads → g % L.block / 32 < 8 →
    X.get (g, k) = some ⟨pc, .exit⟩ → TcExitAt L g ((X.tr g).take k)
  /-- A consumer's barrier arrivals along its run: its arrivals on its group's CLC barrier, with the
  response it holds, are its tiles (`q`) plus its open task, and its arrivals on its output barrier,
  with the sixteen of its epilogue in progress, are sixteen per tile plus its slice's position. -/
  cons_bar_phase : ∀ {g k : Nat} {c : Consumer.D}, g < L.threads →
    Frame.stateAt (code L) X g k = some (some (.inr (.cons c))) →
    ∃ q, ((X.tr g).take k).countP (Execution.isBarId (Consumer.tidOf L g / 32 / 4 + 1)) +
        c.clcHold = q + Consumer.tileOpen c ∧
      Consumer.outBars L g ((X.tr g).take k) + 16 * c.inEpi = 16 * q + c.outPhase
  /-- A tensor load's box starts at a 16-byte aligned coordinate. -/
  tensor_aligned : ∀ {g k : Nat} {e : Event} {d : ThreadD} {a : Nat} {sp : TensorCopy.Spec},
    g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) →
    e.kind = .tensorIssue a sp → TensorDescriptor.BoxAligned sp.descriptor sp.origin
  /-- A tensor store reads the staging buffer of its issuer's CTA, and its box starts at a 16-byte
  aligned coordinate. -/
  store_box : ∀ {g k : Nat} {e : Event} {d : ThreadD} {a : Nat} {sp : TensorStore.Spec},
    g < L.threads → X.get (g, k) = some e → Frame.stateAt (code L) X g k = some (some d) →
    e.kind = .tensorStore a sp →
    sp.sharedBase.cta = g / L.block ∧ TensorDescriptor.BoxAligned sp.descriptor sp.origin
  /-- A consumer's exit follows its final drain: the bulk wait for every group, right after a bulk
  commit, before which every tensor store of the thread lies. -/
  cons_exit_drain : ∀ {g k pc : Nat} {d : ThreadD}, g < L.threads →
    X.get (g, k) = some ⟨pc, .exit⟩ → Frame.stateAt (code L) X g k = some (some d) →
      g % L.block / 32 < 8 →
    ∃ j pcw pcc, 0 < j ∧ j < k ∧ X.get (g, j) = some ⟨pcw, .bulkWait .full 0⟩ ∧
      X.get (g, j - 1) = some ⟨pcc, .bulkCommit⟩ ∧
      ∀ i, j ≤ i → i < k → ∀ pc' a s, X.get (g, i) ≠ some ⟨pc', .tensorStore a s⟩
  /-- Thread 0 of a CTA of a role event's cluster allocates Tensor Memory at its event 20, has
  events past it, and the allocation happens before the role event. -/
  alloc_before : ∀ {h j T : Nat} {ev : Event} {r : Prologue.Role}, X.get (h, j) = some ev →
    Frame.stateAt (code L) X h j = some (some (.inr r)) → T < L.grid →
    L.clusterOfCta T = L.clusterOfCta (h / L.block) →
    (∃ pc grp dst n, X.get (T * L.block, 20) =
      some ⟨pc, .tc (.resource grp dst (.alloc n))⟩) ∧
    21 < (X.tr (T * L.block)).length ∧ baseCausality L X (T * L.block, 20) (h, j)
  /-- A deallocation is made past its thread's exit wait. -/
  dealloc_waited : ∀ {g k pc : Nat} {grp : CtaGroup} {dst : Option Loc} {a n : Nat},
    g < L.threads → X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩ →
    ExitWaited ((X.tr g).take k)
  /-- A Tensor Memory data event is a consumer's in its task loop, and a load returns sixteen
  words. -/
  data_loop : ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e →
    isTcData e = true →
    ∃ c, Frame.stateAt (code L) X g k = some (some (.inr (.cons c))) ∧ Consumer.exitOff c = none ∧
      ∀ pc a vals, e = ⟨pc, .tc (.ld a vals .s32x32b)⟩ → vals.length = 16
  /-- An MMA's accumulator commits before it are fewer than its thread's successful response polls,
  and a successful response poll that is not its latest is followed by a read of a response that
  claims a CTA. -/
  mma_tile : ∀ {g k : Nat} {e : Event} {d : ThreadD} {dst : Nat} {sp : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat}, g < L.threads → X.get (g, k) = some e →
    Frame.stateAt (code L) X g k = some (some d) → e.kind = .tc (.mma dst sp acc mask) →
    ((X.tr g).take k).countP
        (commitsTo (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩)) <
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) ∧
    ∀ j pc p acq sc, X.get (g, j) =
        some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 <
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) →
      ∃ pcr, ∃ a : Acc, ∃ bs rr, X.get (g, j + 1) = some ⟨pcr, .rd a bs⟩ ∧
        a.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ ∧
        Flow.responseOf bs = some rr ∧ Loader.claims rr
  /-- A consumer in its exit stage, at any position of its run: its successful polls of its
  accumulator's full barrier are its successful response polls, and its latest successful response
  poll is followed by a read of a response that claims no CTA. -/
  cons_exit_stage : ∀ {g k : Nat} {c : Consumer.D}, g < L.threads → k ≤ (X.tr g).length →
    Frame.stateAt (code L) X g k = some (some (.inr (.cons c))) → Consumer.exitOff c ≠ none →
    okPolls (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 / 4, true⟩) ((X.tr g).take k) =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) ∧
    ∃ j pcw p acq sc pcr, ∃ a : Acc, ∃ bs rr,
      X.get (g, j) = some ⟨pcw, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
      X.get (g, j + 1) = some ⟨pcr, .rd a bs⟩ ∧
      a.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ ∧
      Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr ∧
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k)
  /-- A consumer at a slice's second output barrier, on a trace without undefined behaviour: element
  `m` of the slice's staging stores wrote the packed halves of accumulator entries
  `32 s + 8 (m / 4) + 2 (m % 4)` and the next (`Consumer.storeWord`); entry `16 ch + w` is word `w`
  of a load of chunk `ch` made one arrival on the accumulator's empty barrier before; and its output
  barrier arrivals are sixteen per accumulator arrival, less fifteen less `2 s`. -/
  cons_slice_values : ∀ {g k : Nat} {c : Consumer.D} {s : Fin 8}, g < L.threads →
    (∀ j pc f, X.get (g, j) ≠ some ⟨pc, .ub f⟩) → k < (X.tr g).length →
    Frame.stateAt (code L) X g k = some (some (.inr (.cons c))) → c.site = .barB s →
    (∀ m, m < 16 → ∃ pc a bs, X.get (g, k - 16 + m) = some ⟨pc, .wr a bs⟩ ∧
      bs = (Consumer.storeWord c.acc s (m / 4) (m % 4)).toBytes) ∧
    (∀ ch, ch < 16 → ∃ kl pc vals, kl < k ∧
      X.get (g, kl) =
        some ⟨pc, .tc (.ld (256 * (Consumer.tidOf L g / 32 / 4) + 16 * ch) vals .s32x32b)⟩ ∧
      (∀ w, w < 16 → vals[w]? = some (c.acc (16 * ch + w))) ∧
      arrivals (Bar.loc L (2 * (g / L.block / 2)) ⟨.acc, Consumer.tidOf L g / 32 / 4, false⟩)
          ((X.tr g).take kl) + 1 =
        arrivals (Bar.loc L (2 * (g / L.block / 2)) ⟨.acc, Consumer.tidOf L g / 32 / 4, false⟩)
          ((X.tr g).take k)) ∧
    Consumer.outBars L g ((X.tr g).take k) + 16 =
      16 * arrivals (Bar.loc L (2 * (g / L.block / 2)) ⟨.acc, Consumer.tidOf L g / 32 / 4, false⟩)
        ((X.tr g).take k) + (2 * s.val + 1)
  /-- A consumer at its TMA store of slice `s`: its output barrier arrivals are sixteen per
  accumulator arrival, less fourteen less `2 s`, and its successful response polls are its
  accumulator arrivals. -/
  cons_tma_epoch : ∀ {g k : Nat} {c : Consumer.D} {s : Fin 8}, g < L.threads →
    Frame.stateAt (code L) X g k = some (some (.inr (.cons c))) → c.site = .tma s →
    Consumer.outBars L g ((X.tr g).take k) + 16 =
      16 * arrivals (Bar.loc L (2 * (g / L.block / 2)) ⟨.acc, Consumer.tidOf L g / 32 / 4, false⟩)
        ((X.tr g).take k) + (2 * s.val + 2) ∧
    okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) =
      arrivals (Bar.loc L (2 * (g / L.block / 2)) ⟨.acc, Consumer.tidOf L g / 32 / 4, false⟩)
        ((X.tr g).take k)
  /-- An MMA of K step `j` at slot `s` of the trip at block `q`: its thread's commits to the input
  empty barriers are `q + s` modulo the task's 128 blocks, its round-robin share of them is on slot
  `s`, its accumulator commits are its completed tasks, and it accumulates unless it is its task's
  first MMA (`Mma.accumulates`). -/
  mma_block : ∀ {g k pc dst : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    {m : Mma.D} {s j : Fin 4}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
    Frame.stateAt (code L) X g k = some (some (.inr (.mma m))) → m.site = .mma s j →
    mmaCount L g ((X.tr g).take k) % 128 = m.q + s.val ∧ m.q % 4 = 0 ∧
    ((X.tr g).take k).countP (commitsTo (inputEmpty L (g / L.block) s.val)) =
      (mmaCount L g ((X.tr g).take k) + 3 - s.val) / 4 ∧
    ((X.tr g).take k).countP
        (commitsTo (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩)) =
      mmaCount L g ((X.tr g).take k) / 128 ∧
    acc = Mma.accumulates m.q s.val j.val
  /-- An accumulating MMA follows the MMA one earlier in its task (by `4 (commits % 128) + j`),
  with no MMA of the thread between. -/
  mma_prev : ∀ {g k : Nat} {m : Mma.D} {s j : Fin 4}, g < L.threads → k < (X.tr g).length →
    Frame.stateAt (code L) X g k = some (some (.inr (.mma m))) → m.site = .mma s j →
    Mma.accumulates m.q s.val j.val = true →
    ∃ k' m', ∃ s' j' : Fin 4, k' < k ∧ Frame.stateAt (code L) X g k' =
      some (some (.inr (.mma m'))) ∧
      m'.site = .mma s' j' ∧
      (∃ pc dst sp acc mask, X.get (g, k') = some ⟨pc, .tc (.mma dst sp acc mask)⟩) ∧
      (∀ i pc dst sp acc mask, k' < i → i < k →
        X.get (g, i) ≠ some ⟨pc, .tc (.mma dst sp acc mask)⟩) ∧
      4 * (mmaCount L g ((X.tr g).take k') % 128) + j'.val + 1 =
        4 * (mmaCount L g ((X.tr g).take k) % 128) + j.val ∧
      mmaCount L g ((X.tr g).take k') / 128 = mmaCount L g ((X.tr g).take k) / 128
  /-- An MMA thread at its accumulator commit made, two events before, its task's last MMA (K step 3
  at slot 3), with one fewer commit than 128 per accumulator commit then made. -/
  acc_commit_last : ∀ {g jc : Nat} {m : Mma.D}, g < L.threads → jc ≤ (X.tr g).length →
    Frame.stateAt (code L) X g jc = some (some (.inr (.mma m))) → m.site = .accCommit →
    2 ≤ jc ∧ (∃ m2, Frame.stateAt (code L) X g (jc - 2) = some (some (.inr (.mma m2))) ∧ m2.site =
      .mma 3 3) ∧
    (∃ pc dst sp acc mask, X.get (g, jc - 2) = some ⟨pc, .tc (.mma dst sp acc mask)⟩) ∧
    (∃ pc sp, X.get (g, jc - 1) = some ⟨pc, .tc (.commit sp)⟩) ∧
    mmaCount L g ((X.tr g).take (jc - 2)) + 1 =
      128 * (((X.tr g).take jc).countP
        (commitsTo (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩)) + 1)
  /-- A loader's load of block `b`, part `j`, of the trip at `q`: block `q + b` of the task numbered
  by its successful response polls, on that task's tile (`Consumer.TileAt`), its slot's round-robin
  share of the blocks so far, and the box at column `64 (q + b)` and the part's row of the tile. -/
  loader_block : ∀ {g k pc a : Nat} {sp : TensorCopy.Spec} {l : Loader.D} {b : Fin 8} {j : Fin 3},
    g < L.threads → X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩ →
    Frame.stateAt (code L) X g k = some (some (.inr (.loader l))) → l.site = .load b j →
    loaderCount L g ((X.tr g).take k) =
      128 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) + l.q + b.val + 1 ∧
    l.q % 8 = 0 ∧ l.q < 128 ∧
    okPolls (InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b)) ((X.tr g).take k) =
      (loaderCount L g ((X.tr g).take k) + 3 - (InputRing.slotOf b).val) / 4 ∧
    Consumer.TileAt L g ((X.tr g).take k)
      (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k)) l.m l.n ∧
    l.m < 16 ∧ l.n < 32 ∧
    (∀ i : Fin (sp.outer + 1), sp.origin i = if i.val = 0 then ((64 * (l.q + b.val) : Nat) : Int)
      else if i.val = 1 then
        ((if j.val < 2 then outputRow l.m (g / L.block % 2) j.val 0
          else 256 * l.n + 128 * (g / L.block % 2) : Nat) : Int)
      else 0) ∧
    L.paramObjects (if j.val < 2 then "gemm_kernel_param_0" else "gemm_kernel_param_1") =
      some (mapParam (if j.val < 2 then "gemm_kernel_param_0" else "gemm_kernel_param_1"), a)
  /-- An event of a thread at its response wait polls its CTA's response barrier. -/
  clc_wait_event : ∀ {g k : Nat} {e : Event} {d : ThreadD}, g < L.threads → X.get (g, k) = some e →
    Frame.stateAt (code L) X g k = some (some d) → d.AtClcWait →
    ∃ p ok acq sc, e.kind = .wait (clcResp L g) p ok acq sc

/-- The input ring's facts, for the layers above the protocols: the facts of a ring of
mbarrier slots (`MbarRing.RingSlot.Facts`), one slot per cluster and stage. -/
abbrev InputFacts (L : Launch) (X : Execution) : Prop :=
  MbarRing.RingSlot.Facts (fun i : Nat × Fin 4 => InputRing.slot L i.1 i.2) X

/-- The accumulator ring's facts, for the layers above the protocols: the facts of a ring of
mbarrier slots (`MbarRing.RingSlot.Facts`), one slot per cluster and accumulator buffer. -/
abbrev TmemFacts (L : Launch) (X : Execution) : Prop :=
  MbarRing.RingSlot.Facts (fun i : Nat × Fin 2 => TmemRing.slot L i.1 i.2) X

/-- The CLC response ring's facts, for the layers above the protocols: the facts of a ring of
mbarrier slots (`MbarRing.RingSlot.Facts`), one slot per cluster. -/
abbrev ClcFacts (L : Launch) (X : Execution) : Prop :=
  MbarRing.RingSlot.Facts (fun c : Nat => ClcRing.slot L c) X

/-- The exit protocol, for the layers above the protocols: a CTA that has exited was notified of
every request targeting it, and that notification finished before one of its threads exited. -/
def ExitNotified (L : Launch) (X : Execution) : Prop :=
  ∀ i s tg c, X.ClcIssue i s tg → c ∈ tg → CtaExited L X c →
    SharedFinished L kernel Prod X (.async i (.notify (.cta c))) c

/-- The commits' notifications, for the layers above the protocols: a CTA that has exited was
notified by every commit targeting it, and that notification finished before one of its threads
exited. -/
def CommitNotified (L : Launch) (X : Execution) : Prop :=
  ∀ i s rank m, X.Commit i s → TcCommit.target s rank = some m → CtaExited L X m.cta →
    SharedFinished L kernel Prod X (.async i (.tcNotify rank)) m.cta

/-- The Tensor Memory base word, for the layers above the protocols: a thread's read of its CTA's
base word returns bytes that rebuild to an integer. -/
def BaseWord (L : Launch) (X : Execution) : Prop :=
  ∀ g k pc a bs, X.get (g, k) = some ⟨pc, .rd a bs⟩ → a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ →
    a.size = 4 → ∃ w x, rebuild 3 bs = .ok (.bits w x)

/-- The Tensor Memory loads' words, for the layers above the protocols: every word a Tensor Memory
load returns is a single-precision float. -/
def LoadWords (X : Execution) : Prop :=
  ∀ e a vals sh, X.TLd e a vals sh → ∀ v ∈ vals, ∃ r, v = .float .f32 r

/-- The Tensor Memory base word's value, for the layers above the protocols: a thread's read of its
CTA's base word returns the bytes of the address its CTA thread 0 stored after its allocation
request (event 20) returned (event 21). -/
def BaseValue (L : Launch) (X : Execution) : Prop :=
  ∀ g k pc a bs, X.get (g, k) = some ⟨pc, .rd a bs⟩ → a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ →
    a.size = 4 → ∃ pca pcw col, X.get (g / L.block * L.block, 20) = some ⟨pca, .tc (.resource .two
      (some ⟨.shared, g / L.block, L.sharedBase⟩) (.alloc 512))⟩ ∧
      X.get (g / L.block * L.block, 21) = some ⟨pcw, .wr
        ⟨⟨.shared, g / L.block, L.sharedBase⟩, 4, false, false, .cta, 0, false⟩ (b32 col).toBytes⟩ ∧
      col < 2 ^ 16 ∧ bs = (b32 col).toBytes.map some

/-- The exit protocol's cluster barrier, for the layers above the protocols: an event of a
thread before its exit arrival on the cluster barrier, other than a cluster arrival, happens
before every exit in its cluster. -/
def ExitOrder (L : Launch) (X : Execution) : Prop :=
  ∀ (e f : EvId) (ev : Event) (d : ThreadD) (pcf : Nat), X.get e = some ev →
    Frame.stateAt (code L) X e.1 e.2 = some (some d) → d.clPhase ≤ 1 →
    (∀ rel al, ev.kind ≠ .cluster (.arrive rel al)) → X.get f = some ⟨pcf, .exit⟩ →
    SameCluster L e.1 f.1 → baseCausality L X e f

/-- The input ring's exit coverage, for the layers above the protocols: a CTA that has exited
received every write of a tensor load that targets its shared window and every notification of one
that completes on its barrier, and they finished before an exit of one of its threads. -/
def TensorExitFinished (L : Launch) (X : Execution) : Prop :=
  (∀ i address s, X.TensorIssue i address s → CtaExited L X s.sharedBase.cta →
    ∀ x y k, (TensorTransfer.slotAt s.descriptor x y k).isSome →
      SharedFinished L kernel Prod X (.async i (.write (.load x y k))) s.sharedBase.cta) ∧
  (∀ i address s, X.TensorIssue i address s → CtaExited L X s.mbar.cta →
    SharedFinished L kernel Prod X (.async i (.notify .load)) s.mbar.cta)

/-- The exit protocol's cluster barrier, for the progress layer: once a thread has exited, every
thread of its cluster has made both its cluster arrivals. -/
def ClusterExitAll (L : Launch) (X : Execution) : Prop :=
  ∀ (h pc : Nat), h < L.threads → (X.tr h).getLast? = some ⟨pc, .exit⟩ →
    ∀ g : Nat, g < L.threads → L.clusterOfCta (g / L.block) = L.clusterOfCta (h / L.block) →
      clArrives (X.tr g) = 2

/-- The accumulator-empty blocker of an MMA leader's failed poll, for the progress layer. An MMA
thread `g` of the leader CTA, stopped at a failed poll of its buffer's empty barrier whose phase is
not ready for its parity, has polled successfully once more than the barrier's phase; and a
consumer of its cluster in the buffer's warp group, which has not exited and is not in its exit
stage, has arrived on the barrier as many times as the phase. -/
def AccEmptyWitness (L : Launch) (X : Execution) : Prop :=
  ∀ (g : Nat) (mm : Mma.D) (pc : Nat) (sc : MbarScope) (before : MBarrier.State),
    g < L.threads → g / L.block % 2 = 0 →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma mm))) → mm.site = .accWait →
    (X.tr g).getLast? = some
      ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.acc, mm.w % 2, false⟩) mm.ap false true sc⟩ →
    MBarrier.stateBefore (X.objects (Bar.loc L (g / L.block) ⟨.acc, mm.w % 2, false⟩))
      (X.objects (Bar.loc L (g / L.block) ⟨.acc, mm.w % 2, false⟩)).length = some before →
    before.phase % 2 = mm.ap % 2 →
    before.phase + 1 = okPolls (Bar.loc L (g / L.block) ⟨.acc, mm.w % 2, false⟩) (X.tr g) ∧
    ∃ h, h < L.threads ∧ h / L.block / 2 = g / L.block / 2 ∧
      h % L.block / 32 / 4 = mm.w % 2 ∧
      arrivals (Bar.loc L (g / L.block) ⟨.acc, mm.w % 2, false⟩) (X.tr h) = before.phase ∧
      (∀ pc', (X.tr h).getLast? ≠ some ⟨pc', .exit⟩) ∧
      ∀ d, Frame.stateAt (code L) X h (X.tr h).length = some (some d) → d.exitOff = none

/-- **The working MMA leader's response reads.** At an accumulator-empty wait, a working MMA thread
of a leader CTA reads a claiming response after each of its successful response polls that is
followed by another successful poll, and it has polled the response `mmaCount / 128 + 1` times. The
latest poll's read may name no CTA: the last task's K loop runs whatever it names, and the thread
leaves at its accumulator commit (`Mma.next`). -/
def MmaWorkingClaims (L : Launch) (X : Execution) : Prop :=
  ∀ (g : Nat) (m : Mma.D), g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m))) → m.site = .accWait →
    (∀ j pc p acq sc, (X.tr g)[j]? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)
        p true acq sc⟩ →
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 <
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) →
      ∃ pcr, ∃ src : Acc, ∃ bs rr, (X.tr g)[j + 1]? = some ⟨pcr, .rd src bs⟩ ∧
        src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ ∧
        Flow.responseOf bs = some rr ∧ Loader.claims rr) ∧
    okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) = mmaCount L g (X.tr g) / 128 + 1

/-- The input ring, for the progress layer: a loader stopped at a failed poll of a slot's empty
barrier whose final phase has the loader's parity has produced into the slot once more than the
slot was returned, and one MMA consumer of the cluster has left on that barrier as many
notifications as its phase. -/
def InputBlocked (L : Launch) (X : Execution) : Prop :=
  ∀ (g : Nat) (l : Loader.D) (b : Fin 8) (pc : Nat) (m : Loc) (p : Nat) (acq : Bool)
    (sc : MbarScope) (before : MBarrier.State), g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) → l.site = .wait b →
    (X.tr g).getLast? = some ⟨pc, .wait m p false acq sc⟩ →
    MBarrier.stateBefore (X.objects (InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b)))
      (X.objects (InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b))).length = some before →
    before.phase % 2 = InputRing.producerParity b % 2 →
    before.phase + 1 = okPolls (InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b)) (X.tr g) ∧
    ∃ b' : Fin 2, (X.objects (InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b))).countP
      (InputRing.notification L (g / L.block / 2) ⟨g / L.block % 2, Nat.mod_lt _ (by decide)⟩ b') =
        before.phase

/-- The input ring, for the progress layer: a loader stopped at a failed poll of its tail drain of
slot `i` (parity 1) whose barrier's final phase is odd has produced into the slot once more than the
slot was returned, and one MMA consumer of the cluster has left on that barrier as many
notifications as its phase. -/
def DrainBlocked (L : Launch) (X : Execution) : Prop :=
  ∀ (g : Nat) (l : Loader.D) (i : Fin 4) (pc : Nat) (m : Loc) (p : Nat) (acq : Bool)
    (sc : MbarScope) (before : MBarrier.State), g < L.threads →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))) → l.site =
      .drain i →
    (X.tr g).getLast? = some ⟨pc, .wait m p false acq sc⟩ → m =
      InputRing.emptyLoc L (g / L.block) i →
    MBarrier.stateBefore (X.objects (InputRing.emptyLoc L (g / L.block) i))
      (X.objects (InputRing.emptyLoc L (g / L.block) i)).length = some before →
    before.phase % 2 = 1 →
    before.phase + 1 = okPolls (InputRing.emptyLoc L (g / L.block) i) (X.tr g) ∧
    ∃ b' : Fin 2, (X.objects (InputRing.emptyLoc L (g / L.block) i)).countP
      (InputRing.notification L (g / L.block / 2) ⟨g / L.block % 2, Nat.mod_lt _ (by decide)⟩ b') =
        before.phase

/-- The input ring, for the progress layer: an MMA thread of a leader CTA stopped at a failed poll
of slot `s`'s full barrier, whose phase has the poll's parity, is blocked, and its successful polls
of the barrier are its phase (as for the loaders' empty barriers). Either a tensor copy on
the full barrier is issued and not notified, or a warp-11 loader of the cluster that is elected has
issued fewer than `3 (phase + 1)` copies on it, or the leader CTA's loader that is elected has
arrived on it fewer than `phase + 1` times, or a warp-11 lane of the cluster has no election event.
An elected lane is one whose election returns its own lane; an idle lane returns another lane. -/
def InputFullBlocked (L : Launch) (X : Execution) : Prop :=
  ∀ (g : Nat) (m : Mma.D) (s : Fin 4) (pc : Nat) (sc : MbarScope) (before : MBarrier.State),
    g < L.threads → g / L.block % 2 = 0 →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m))) → m.site = .full s →
    (X.tr g).getLast? = some ⟨pc, .wait (InputRing.fullLoc L (g / L.block / 2) s) (m.fp % 2) false
      true sc⟩ →
    MBarrier.stateBefore (X.objects (InputRing.fullLoc L (g / L.block / 2) s))
      (X.objects (InputRing.fullLoc L (g / L.block / 2) s)).length = some before →
    before.phase % 2 = m.fp % 2 →
    before.phase = okPolls (InputRing.fullLoc L (g / L.block / 2) s) (X.tr g) ∧
    ((∃ i mapAddress s', X.TensorIssue i mapAddress s' ∧
        s'.mbar = InputRing.fullLoc L (g / L.block / 2) s ∧
        ¬ ∃ obs, X.tensor i = some obs ∧ obs.effects.notified = true) ∨
    (∃ h, h < L.threads ∧ h / L.block / 2 = g / L.block / 2 ∧ h % L.block / 32 = 11 ∧
        (∃ j pc' mask inst, X.Elect (h, j) pc' mask inst (laneOf L h)) ∧
        (X.tr h).countP (issuesTo (InputRing.fullLoc L (g / L.block / 2) s)) <
          3 * (before.phase + 1)) ∨
    (∃ h, h < L.threads ∧ h / L.block = g / L.block ∧ h % L.block / 32 = 11 ∧
        (∃ j pc' mask inst, X.Elect (h, j) pc' mask inst (laneOf L h)) ∧
        arrivals (InputRing.fullLoc L (g / L.block / 2) s) (X.tr h) < before.phase + 1) ∨
    (∃ h, h < L.threads ∧ h / L.block / 2 = g / L.block / 2 ∧ h % L.block / 32 = 11 ∧
        ∀ j pc' mask inst leader, ¬ X.Elect (h, j) pc' mask inst leader))

/-- The response of CLC request `i` to CTA `c`, observed (`AsyncCopy.AsyncObserved`, acquire) by the
poll `w` of a thread of CTA `c`. -/
def ClcObserved (L : Launch) (X : Execution) (i : EvId) (c : Nat) (w : EvId) : Prop :=
  c = w.1 / L.block ∧ w.1 < L.threads ∧ ∃ ws,
    AsyncCopy.AsyncObserved X i (.notify (.cta c)) w true ws

/-- The CLC ring, for the layers above the protocols: a request happens before every observer of
its notification on its own CTA's response barrier, from the observer's next event on. -/
def IssueBeforeObservers (L : Launch) (X : Execution) : Prop :=
  ∀ (i : EvId) (s : Clc.Spec) (tg : List Nat) (w : EvId), X.ClcIssue i s tg →
    ClcObserved L X i (i.1 / L.block) w → ∀ f2, w.2 < f2 → f2 < (X.tr w.1).length →
      baseCausality L X i (w.1, f2)

/-- The CLC ring, for the layers above the protocols: every request of a cluster is a request
whose response names no first CTA, or happens before it. -/
def RequestsBeforeFailure (L : Launch) (X : Execution) : Prop :=
  ∀ (i : EvId) (s : Clc.Spec) (tg : List Nat) (i' : EvId) (s' : Clc.Spec) (tg' : List Nat)
    (r' : ClcResponse), X.ClcIssue i s tg → X.ClcIssue i' s' tg' →
    (∃ c ∈ tg, ∃ c' ∈ tg', c / 2 = c' / 2) → (X.clc i').resolved = some r' →
    r'.firstCta = none → i = i' ∨ baseCausality L X i i'

/-- The CLC response ring, for the progress layer: a reader at its CLC poll (`ThreadD.AtClcWait`),
stopped at a failed poll of its CTA's response barrier whose phase is not ready for its parity, is
blocked. Either a request of the cluster is issued and not delivered to every target, or a warp-10
thread of the cluster (the leader CTA's scheduler issues the requests, each CTA's expects the
response on its own barrier) has started and is outside its exit stage with its next event ranked at
most `blockAt n + 4`, where `n` is the reader's successful response polls (it has issued or expected
no more responses than those), or has stopped without its exit. -/
def ClcBlocked (L : Launch) (X : Execution) : Prop :=
  ∀ (g pc p : Nat) (acq : Bool) (sc : MbarScope) (before : MBarrier.State) (dg : ThreadD),
    g < L.threads → Frame.stateAt (code L) X g (X.tr g).length = some (some dg) → dg.AtClcWait →
    (X.tr g).getLast? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p false acq sc⟩ →
    MBarrier.stateBefore (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩))
      (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)).length = some before →
    before.phase % 2 = p % 2 →
    (∃ i s tg, X.ClcIssue i s tg ∧ ¬ ∀ c ∈ tg, c ∈ (X.clc i).notified) ∨
      ∃ h, h < L.threads ∧ h / L.block / 2 = g / L.block / 2 ∧ h % L.block / 32 = 10 ∧
        X.tr h ≠ [] ∧
        ((∃ d, Frame.stateAt (code L) X h (X.tr h).length = some (some d) ∧ d.exitOff = none ∧
            d.vtime L h (X.tr h) ≤
              blockAt (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)) + 4) ∨
          (Frame.stateAt (code L) X h (X.tr h).length = none ∧ ∀ pc', (X.tr h).getLast? ≠
            some ⟨pc', .exit⟩))

/-- The CLC acknowledgement ring, for the progress layer: the leader scheduler (warp 10 of an even
CTA) stopped at a failed poll of its acknowledgement barrier, whose phase is not ready for its
parity, is blocked by one of the ten acknowledging threads. That thread has started and has arrived
on the barrier fewer times than the scheduler's successful polls, and it is outside the exit stage
or has stopped without its exit. -/
def AckBlocked (L : Launch) (X : Execution) : Prop :=
  ∀ (g pc p : Nat) (acq : Bool) (sc : MbarScope) (before : MBarrier.State), g < L.threads →
    g / L.block % 2 = 0 → g % L.block / 32 = 10 →
    (X.tr g).getLast? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) p false acq sc⟩ →
    MBarrier.stateBefore (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩))
      (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩)).length = some before →
    before.phase % 2 = p % 2 →
    ∃ b, b < L.threads ∧ X.tr b ≠ [] ∧
      (∃ f : Fin 10, ClcRing.consumerSel L (g / L.block / 2) f b = true) ∧
      arrivals (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) (X.tr b) <
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) (X.tr g) ∧
      ((∃ d, Frame.stateAt (code L) X b (X.tr b).length = some (some d) ∧ d.exitOff = none) ∨
        (Frame.stateAt (code L) X b (X.tr b).length = none ∧ ∀ pc', (X.tr b).getLast? ≠
          some ⟨pc', .exit⟩))

/-! ## Memory regions

The accessors of the regions of a CTA's shared window, for the protocols that order a region's
accesses: the region layer (`Region/`) proves them. -/

/-- Every write covering a byte of a CTA's CLC response buffer is a cancellation response written
there by a request targeting that CTA. -/
def ResponseWriters (L : Launch) (X : Execution) : Prop :=
  ∀ cta k, k < 16 → ∀ w (a : Acc) bs, X.MemWrites w a bs →
    a.Covers ⟨.shared, cta, L.sharedBase + 144 + k⟩ →
    ∃ i s tg, w = .async i (.write (.cta cta)) ∧ X.ClcIssue i s tg ∧ cta ∈ tg

/-- A byte of the consumers' staging buffers. -/
def IsStaging (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 197632 ≤ l.addr ∧ l.addr < L.sharedBase + 230400

/-- Every access covering a staging byte is a consumer's staging store or a consumer's TMA store
reading it. -/
def StagingAccessors (L : Launch) (X : Execution) : Prop :=
  ∀ ref a w l, X.Intent ref a w → a.Covers l → IsStaging L l →
    (∃ e pc bs c, ref = .thread e ∧ X.get e = some ⟨pc, .wr a bs⟩ ∧
      Frame.stateAt (code L) X e.1 e.2 = some (some (.inr (.cons c)))) ∨
    (∃ i x y k c, ref = .async i (.read (.store x y k)) ∧
      Frame.stateAt (code L) X i.1 i.2 = some (some (.inr (.cons c))))

/-- A byte of the input stages: the four slots' tiles, after the 1 KiB of control storage and
before the consumers' staging buffers. -/
def IsInputStage (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 1024 ≤ l.addr ∧ l.addr < L.sharedBase + 197632

/-- Every access covering an input stage byte is a tensor load writing it or an MMA operand read
of it. -/
def InputAccessors (L : Launch) (X : Execution) : Prop :=
  ∀ ref a w l, X.Intent ref a w → a.Covers l → IsInputStage L l →
    (∃ i x y k, ref = .async i (.write (.load x y k))) ∨
      (∃ i isB idx, ref = .async i (.mmaRead isB idx))

/-- The output ring, for the layers above the protocols: two conflicting accesses of a staging
byte are ordered at that byte, one way or the other. -/
def StagingOrdered (L : Launch) (X : Execution) : Prop :=
  ∀ e f a b l, Conflict X e f a b → a.Covers l → b.Covers l → IsStaging L l →
    modelCausality L X l e f ∨ modelCausality L X l f e

/-- The output ring, for the progress layer: every byte an issued TMA store of a slice reads has a
source write visible to the store's read of it, and every write visible to such a read has a defined
byte. -/
def OutputSources (L : Launch) (X : Execution) : Prop :=
  ∀ (i : EvId) (a : Nat) (spec : TensorStore.Spec), X.TensorStoreIssue i a spec →
    Step.StoreDone.VisibleReadSources L X i spec

/-- The input ring, for the layers above the protocols: two conflicting accesses of an input
stage byte are ordered at that byte, one way or the other. -/
def InputOrdered (L : Launch) (X : Execution) : Prop :=
  ∀ e f a b l, Conflict X e f a b → a.Covers l → b.Covers l → IsInputStage L l →
    modelCausality L X l e f ∨ modelCausality L X l f e

/-- A byte of a CTA's CLC response buffer. -/
def Region.IsResponse (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 144 ≤ l.addr ∧ l.addr < L.sharedBase + 160

/-- A byte of a CTA's Tensor Memory base word. -/
def Region.IsBase (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + 4

/-- The shared window, for the layers above the protocols: every access of a shared byte is in the
window of a launched CTA, in one of its regions (the Tensor Memory base word, the CLC response
buffer, the input stages, the staging buffers). -/
def SharedWindow (L : Launch) (X : Execution) : Prop :=
  ∀ ref a w l, X.Intent ref a w → a.Covers l → l.space = .shared → l.cta < L.grid ∧
    (Region.IsBase L l ∨ Region.IsResponse L l ∨ IsInputStage L l ∨ IsStaging L l)

/-- The CLC ring, for the layers above the protocols: two conflicting accesses of a response
buffer byte are ordered at that byte, one way or the other. -/
def ResponseOrdered (L : Launch) (X : Execution) : Prop :=
  ConflictsOrdered L X (Region.IsResponse L)

/-- The Tensor Memory base word, for the layers above the protocols: two conflicting accesses of
a base word byte are ordered at that byte, one way or the other. -/
def BaseOrdered (L : Launch) (X : Execution) : Prop :=
  ConflictsOrdered L X (Region.IsBase L)

/-- The MMAs' operand copies, for the layers above the protocols: the two bytes `2 m` and
`2 m + 1` of an MMA operand are bytes of element `(x, y)` of one tensor load's box, whose write of
each byte is visible to the MMA's read of it and is ordered with every other write of the byte:
before the load's write or after the read. -/
def OperandCopies (L : Launch) (X : Execution) : Prop :=
  ∀ i d sp acc mask, X.MmaIssue i d sp acc mask → ∀ (isB : Bool) (m : Nat), m < 4096 →
    ∃ (copy : EvId) (o : TensorCopy.Observation) (x y : Nat), X.tensor copy = some o ∧
      ∀ z, z < 2 → ∃ l, sp.byteLoc (if isB then .b else .a) (2 * m + z) = some l ∧
        TensorCopy.writeLoc o.spec x y z = some l ∧ (∃ v, TensorCopy.writeByte o x y z = some v) ∧
        modelCausality L X l (.async copy (.write (.load x y z)))
            (.async i (.mmaRead isB (2 * m + z))) ∧
        ∀ w a bs, X.MemWrites w a bs → a.Covers l → w = .async copy (.write (.load x y z)) ∨
          modelCausality L X l w (.async copy (.write (.load x y z))) ∨
          modelCausality L X l (.async i (.mmaRead isB (2 * m + z))) w

/-- The MMAs' completions, for the layers above the protocols: once a CTA of an MMA's pair has
exited, the MMA has completed, and its completion finished before an exit of that CTA. -/
def MmaExitDone (L : Launch) (X : Execution) : Prop :=
  ∀ i d sp acc mask, X.MmaIssue i d sp acc mask → ∀ owner,
    (owner = sp.lowCta ∨ owner = sp.highCta) → CtaExited L X owner →
      SharedFinished L kernel Prod X (.async i .mmaDone) owner

/-- The MMAs' operand reads, for the layers above the protocols: once the CTA whose input stage
byte an MMA reads has exited, the read occurred and finished before one of its threads exited. -/
def ReadsFinished (L : Launch) (X : Execution) : Prop :=
  ∀ i isB idx l, X.MmaFootprint i isB idx l → CtaExited L X l.cta →
    SharedFinished L kernel Prod X (.async i (.mmaRead isB idx)) l.cta

/-- The output tiles, for the layers above the protocols: two tensor stores that write one global
byte are one store writing one slot. -/
def OutputUnique (X : Execution) : Prop :=
  ∀ (i j : EvId) (a a' : Nat) (s s' : TensorStore.Spec) (x y k x' y' k' : Nat) (l : Loc),
    X.TensorStoreIssue i a s → X.TensorStoreIssue j a' s' →
    TensorStore.writeLoc s x y k = some l → TensorStore.writeLoc s' x' y' k' = some l →
    i = j ∧ x = x' ∧ y = y' ∧ k = k'

/-- The CLC responses of every reader, for the layers above the protocols: each thread of cluster
`c` that polls its CTA's response barrier, in any role, observes at its `n`-th successful response
poll the request that the cluster's leader scheduler issued after `n` earlier ones, and a read of
its response buffer right after the poll reads that request's response. -/
def ReaderValues (L : Launch) (X : Execution) : Prop :=
  ∀ (c g j pc p : Nat) (acq : Bool) (sc : MbarScope), g / L.block / 2 = c →
    X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
    ∃ i s tg r, X.ClcIssue i s tg ∧ i.1 / L.block = 2 * c ∧ i.1 % L.block / 32 = 10 ∧
      ((X.tr i.1).take i.2).countP (clcIssuesTo (Bar.loc L (2 * c) ⟨.clc, 0, true⟩)) =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) ∧
      ClcObserved L X i (g / L.block) (g, j) ∧ (X.clc i).resolved = some r ∧
      ∀ pcr (src : Acc) bs, X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ →
        src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ →
        bs = (Value.clc r).toBytes.map some

/-- The accumulator ring's values, for the layers above the protocols: the MMAs' output layouts
are injective in the matrix coordinate, and every value a Tensor Memory write leaves in a cell is
a single-precision float. -/
def TmemWords (L : Launch) (X : Execution) : Prop :=
  TcMma.LayoutInjective X ∧ ∀ s cell v, TcMma.Wrote L Prod X s cell v → ∃ r, v = .float .f32 r

/-- The Tensor Memory accesses' lifetimes, for the layers above the protocols: an access's cell is
allocated, covered by a completed allocation published to the access, and the access completes
before the first release attempt of every allocation covering it. -/
def TmemLive (L : Launch) (X : Execution) : Prop :=
  ∀ e cell, Tmem.Pair.Access L X e cell →
    (∃ cta r, r ∈ X.tmemHistory cta ∧ Tmem.Pair.Covers L X r cell.cta e cell.column) ∧
    ∀ cta r, r ∈ X.tmemHistory cta → Tmem.Pair.Covers L X r cell.cta e cell.column →
      ∀ d, Tmem.Pair.ReleaseOf L X r d → TcMma.CompletedBefore L X e d

/-- The accumulator ring's order, for the layers above the protocols. An MMA of MMA thread `g`
(the batch of its buffer numbered by its accumulator commits before it) and a Tensor Memory load
of a consumer `h` of the buffer in its cluster (the tile numbered by its arrivals on the buffer's
empty barrier before it) are ordered: the MMA is observed complete before the load when its batch
is at most the load's tile, and the load is finished before the MMA when its tile is earlier. -/
def TmemOrdered (L : Launch) (X : Execution) : Prop :=
  ∀ (g k h k' d : Nat) (s : TcMma.OperandSpec) (acc : Bool) (mask : List Nat) (a : Nat)
    (vals : List Value) (sh : TcShape), X.MmaIssue (g, k) d s acc mask →
    X.TLd (h, k') a vals sh →
    h / L.block / 2 = g / L.block / 2 → h % L.block / 32 / 4 = g % L.block / 32 % 2 →
    (((X.tr g).take k).countP
        (commitsTo (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩)) ≤
      arrivals (Bar.loc L (2 * (h / L.block / 2)) ⟨.acc, h % L.block / 32 / 4, false⟩)
        ((X.tr h).take k') → TcMma.DoneBefore L X (g, k) (h, k')) ∧
    (arrivals (Bar.loc L (2 * (h / L.block / 2)) ⟨.acc, h % L.block / 32 / 4, false⟩)
        ((X.tr h).take k') <
      ((X.tr g).take k).countP
        (commitsTo (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩)) →
      TcMma.WaitBefore L X .waitLd (h, k') (g, k))

/-- The accumulator ring's completion before the release, for the layers above the protocols: an
MMA is observed complete, and a Tensor Memory load is finished by its wait, before every event of
their cluster that its thread makes past its exit wait. -/
def TmemExitDone (L : Launch) (X : Execution) : Prop :=
  (∀ (i f : EvId) (d : Nat) (s : TcMma.OperandSpec) (acc : Bool) (mask : List Nat) (ev : Event),
    X.MmaIssue i d s acc mask → X.get f = some ev → ExitWaited ((X.tr f.1).take f.2) →
    f.1 / L.block / 2 = i.1 / L.block / 2 → TcMma.DoneBefore L X i f) ∧
  ∀ (i f : EvId) (a : Nat) (vals : List Value) (sh : TcShape) (ev : Event),
    X.TLd i a vals sh →
    X.get f = some ev → ExitWaited ((X.tr f.1).take f.2) → f.1 / L.block / 2 = i.1 / L.block / 2 →
    TcMma.WaitBefore L X .waitLd i f

/-- The CLC responses of the readers, for the layers above the protocols: two readers of one
cluster's responses read the same response bytes after their `n`-th successful polls. -/
def AllResponsesAgree (L : Launch) (X : Execution) : Prop :=
  ∀ (c g1 g2 j1 j2 pc1 pc2 p1 p2 pcr1 pcr2 : Nat) (acq1 acq2 : Bool) (sc1 sc2 : MbarScope)
    (src1 src2 : Acc) (bs1 bs2 : List (Option Byte)),
    g1 / L.block / 2 = c → g2 / L.block / 2 = c →
    X.get (g1, j1) = some ⟨pc1, .wait (Bar.loc L (g1 / L.block) ⟨.clc, 0, true⟩) p1 true acq1 sc1⟩ →
    X.get (g2, j2) = some ⟨pc2, .wait (Bar.loc L (g2 / L.block) ⟨.clc, 0, true⟩) p2 true acq2 sc2⟩ →
    okPolls (Bar.loc L (g1 / L.block) ⟨.clc, 0, true⟩) ((X.tr g1).take j1) =
      okPolls (Bar.loc L (g2 / L.block) ⟨.clc, 0, true⟩) ((X.tr g2).take j2) →
    X.get (g1, j1 + 1) = some ⟨pcr1, .rd src1 bs1⟩ →
    src1.SameFootprint ⟨⟨.shared, g1 / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
        false⟩ →
    X.get (g2, j2 + 1) = some ⟨pcr2, .rd src2 bs2⟩ →
    src2.SameFootprint ⟨⟨.shared, g2 / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
        false⟩ →
    bs1 = bs2

/-- The input ring, for the progress layer: once every commit has notified its targets, an MMA
thread's commits to a slot's empty barrier are at most its warp's notifications on that barrier in
either CTA of the cluster. -/
def CommitsCounted (L : Launch) (X : Execution) : Prop :=
  (∀ i sp rank m, X.Commit i sp → TcCommit.target sp rank = some m → rank ∈ X.tcNotified i) →
  ∀ (h : Nat) (b a : Fin 2) (s : Fin 4), h < L.threads →
    InputRing.consumerThread L (h / L.block / 2) b h = true →
    (X.tr h).countP (commitsTo (inputEmpty L (h / L.block) s)) ≤
      (X.objects (InputRing.emptyLoc L (h / L.block + a.val) s)).countP
        (InputRing.notification L (h / L.block / 2) a b)

/-! ## The output

The output of the kernel, for `ResultGoal`. The write structure (`GlobalWrites`, `OutputCover`,
`OutputUnique`) gives every byte of `D` one writer (`OutputWrites`); the values those writers write
are `OutputValues`. -/

/-- The output row of row `y` of a consumer's warp group, in the tile row `c.m` it is at. -/
def Consumer.outRow (L : Launch) (g : Nat) (c : Consumer.D) (y : Nat) : Nat :=
  outputRow c.m (g / L.block % 2) (Consumer.tidOf L g / 32 / 4) y

/-- The output column of column `x` of slice `s`, in the tile column `c.n` a consumer is at. -/
def Consumer.outCol (c : Consumer.D) (s : Fin 8) (x : Nat) : Nat := outputCol c.n s.val x

/-- The global writes, for the conclusions: every write of a global byte is a one-byte write of a
tensor store's slot, inside the `D` matrix. -/
def GlobalWrites (P : Params) (X : Execution) : Prop :=
  ∀ w a bs, X.MemWrites w a bs → a.loc.space = .global →
    a.size = 1 ∧ a.loc.cta = 0 ∧ P.dBase ≤ a.loc.addr ∧ a.loc.addr < P.dBase + matrixBytes ∧
      ∃ i x y z, w = .async i (.write (.store x y z))

/-- The output tiles' stores, for the conclusions: for every cluster task `t`, CTA rank `r`, warp
group `q` and slice `s`, some consumer of rank `r` and group `q` issued its TMA store of slice `s`
of the tile `(tileM t, tileN t)`, whose slot `(x, y, z)` writes byte `z` of row `y` of the group's
rows and column `x` of the slice's columns of that tile. -/
def OutputCover (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ t, t < 512 → ∀ r, r < 2 → ∀ q, q < 2 → ∀ s : Fin 8, ∃ g k pc a sp c,
    X.get (g, k) = some ⟨pc, .tensorStore a sp⟩ ∧ Frame.stateAt (code L) X g k =
      some (some (.inr (.cons c))) ∧
    c.site = .tma s ∧ c.m = tileM t ∧ c.n = tileN t ∧ g / L.block % 2 = r ∧
    Consumer.tidOf L g / 32 / 4 = q ∧
    ∀ x y z, x < 32 → y < 128 → z < 2 → TensorStore.writeLoc sp x y z =
      some ((elementLoc P.dBase (outputRow (tileM t) r q y) (outputCol (tileN t) s.val x)).at z)

/-- **The output bytes' writers**, for the value half: byte `z` of element `(i, j)` of `D` is
written, and written only, by slot `(x, y, z)` of the TMA store of a consumer at its TMA store of
slice `s` (`Consumer.D.site`), whose row `y` and column `x` are `(i, j)` in its tile
(`Consumer.outRow`, `Consumer.outCol`); the byte written is the store's recorded write. -/
def OutputWrites (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ i, i < 8192 → ∀ j, j < 8192 → ∀ z, z < 2 → ∃ g k pc a sp c, ∃ s : Fin 8, ∃ x y o b,
    X.get (g, k) = some ⟨pc, .tensorStore a sp⟩ ∧ Frame.stateAt (code L) X g k =
      some (some (.inr (.cons c))) ∧
    c.site = .tma s ∧ x < 32 ∧ y < 128 ∧ Consumer.outRow L g c y = i ∧ Consumer.outCol c s x = j ∧
    X.tensorStores (g, k) = some o ∧ TensorStore.writeByte o x y z = some b ∧
    X.MemWrites (.async (g, k) (.write (.store x y z)))
      ⟨(elementLoc P.dBase i j).at z, 1, false, false,
      .cta, 0, false⟩ [b] ∧
    ∀ w a bs, X.MemWrites w a bs → a.Covers ((elementLoc P.dBase i j).at z) →
      w = .async (g, k) (.write (.store x y z))

/-- **The output values**, for the conclusions: every byte a consumer's TMA store of slice `s`
writes at its slot `(x, y, z)` is byte `z` of the half-precision ideal dot product of the slot's
output element. -/
def OutputValues (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g k pc a sp c (s : Fin 8) x y z o b, X.get (g, k) = some ⟨pc, .tensorStore a sp⟩ →
    Frame.stateAt (code L) X g k = some (some (.inr (.cons c))) → c.site = .tma s → x < 32 → y <
      128 → z < 2 →
    X.tensorStores (g, k) = some o → TensorStore.writeByte o x y z = some b →
    b = (Value.float .f16 (dot P (Consumer.outRow L g c y) (Consumer.outCol c s x))).byteAt z

/-! ## The output's values

The sources of the values the output's TMA stores write, for `OutputValues`: the staging bytes a
TMA store reads (`StagingValues`), the MMA a Tensor Memory load reads (`LoadSources`), the
accumulator source of an accumulating MMA (`MmaAccSources`) and the operand elements of an MMA
(`OperandValues`). -/

/-- The output ring's values, for the conclusions: the byte a consumer's TMA store of slice `s`
reads at slot `(x, y, z)` is byte `2 (x % 2) + z` of its group's thread of row `y`'s staging store
of element `4 (x / 8) + x / 2 % 4` of the slice, made before that thread's second output barrier of
the slice (`i'`), one output barrier arrival before the TMA store. -/
def StagingValues (L : Launch) (X : Execution) : Prop :=
  ∀ h k pc a sp (c : Consumer.D) (s : Fin 8) x y z o v,
    X.get (h, k) = some ⟨pc, .tensorStore a sp⟩ → Frame.stateAt (code L) X h k =
      some (some (.inr (.cons c))) →
    c.site = .tma s → x < 32 → y < 128 → z < 2 → X.tensorStores (h, k) = some o →
    TensorStore.readByte o x y z = some v →
    ∃ g' i' c' pc' a' bs, g' = h / L.block * L.block + (128 * (Consumer.tidOf L h / 32 / 4) + y) ∧
      i' < (X.tr g').length ∧ Frame.stateAt (code L) X g' i' = some (some (.inr (.cons c'))) ∧
      c'.site = .barB s ∧
      Consumer.outBars L g' ((X.tr g').take i') + 1 = Consumer.outBars L h ((X.tr h).take k) ∧
      X.get (g', i' - 16 + (4 * (x / 8) + x / 2 % 4)) = some ⟨pc', .wr a' bs⟩ ∧
      bs[2 * (x % 2) + z]? = some v

/-- The accumulator ring's values, for the conclusions: every word of a consumer's Tensor Memory
load of tile `q` (its arrivals on its buffer's empty barrier) is read from the producer's MMA two
events before its accumulator commit numbered `q`, at the load's row and column. -/
def LoadSources (L : Launch) (X : Execution) : Prop :=
  ∀ h k' a vals sh j, X.TLd (h, k') a vals sh → j < vals.length →
    ∃ g jc m pcm dst sp acc mask cell value, g < L.threads ∧
      g / L.block = 2 * (h / L.block / 2) ∧ g % L.block / 32 = 8 + h % L.block / 32 / 4 ∧
      jc ≤ (X.tr g).length ∧ Frame.stateAt (code L) X g jc = some (some (.inr (.mma m))) ∧
      m.site = .accCommit ∧
      ((X.tr g).take jc).countP
          (commitsTo (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩)) =
        arrivals (Bar.loc L (2 * (h / L.block / 2)) ⟨.acc, h % L.block / 32 / 4, false⟩)
          ((X.tr h).take k') ∧
      X.get (g, jc - 2) = some ⟨pcm, .tc (.mma dst sp acc mask)⟩ ∧
      TcMma.writeCell sp dst mask (128 * (h / L.block % 2) + h % L.block % 128)
        (a - 256 * (h % L.block / 32 / 4) + j) = some cell ∧
      X.async.mmaDone (g, jc - 2) = true ∧
      TcMma.LoadCell L X (h, k') j cell ∧ TcMma.ReadSource L X .ld (g, jc - 2) (h, k') cell ∧
      TcMma.Wrote L Prod X (g, jc - 2) cell value

/-- The accumulators' sources, for the conclusions: a completed accumulating MMA's old values come
from the latest earlier MMA of its thread, completed, with no MMA of the thread between. -/
def MmaAccSources (L : Launch) (X : Execution) : Prop :=
  ∀ g k d s mask, X.MmaIssue (g, k) d s true mask → X.async.mmaDone (g, k) = true →
    ∃ k', k' < k ∧ (∃ d' s' acc' mask', X.MmaIssue (g, k') d' s' acc' mask') ∧
      X.async.mmaDone (g, k') = true ∧
      (∀ i pc dst sp acc mask, k' < i → i < k →
        X.get (g, i) ≠ some ⟨pc, .tc (.mma dst sp acc mask)⟩) ∧
      ∀ row col cell, TcMma.writeCell s d mask row col = some cell →
        TcMma.ReadSource L X .acc (g, k') (g, k) cell

/-- The MMAs' operand elements, for the conclusions: element `(row, kk)` of an operand of an MMA of
K step `jj` at slot `s` is the input matrix element at the box origin of a loader's load of tile
`tile` (its warp's A tile, or the B tile) of the slot in the CTA of the row's half, plus
`(16 jj + kk, row % 128)`, the load whose count of issues on the slot's full barrier is three per
earlier commit of the MMA's thread to the slot's empty barrier, plus the tile. -/
def OperandValues (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g km pc dst sp acc mask (m : Mma.D) (s jj : Fin 4) ops,
    X.get (g, km) = some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
    Frame.stateAt (code L) X g km = some (some (.inr (.mma m))) → m.site = .mma s jj →
    X.async.mmaOperands (g, km) = some ops → ∀ (isB : Bool) row kk, row < 256 → kk < 16 →
    ∃ gw kw pcw alw spw, ∃ (lw : Loader.D) (bw : Fin 8) (jw : Fin 3),
      X.get (gw, kw) = some ⟨pcw, .tensorIssue alw spw⟩ ∧
      Frame.stateAt (code L) X gw kw = some (some (.inr (.loader lw))) ∧ lw.site = .load bw jw ∧
      gw / L.block = g / L.block / 2 * 2 + row / 128 ∧ InputRing.slotOf bw = s ∧
      jw.val = (if isB then 2 else g % L.block / 32 % 2) ∧
      ((X.tr gw).take kw).countP (issuesTo (InputRing.fullLoc L (g / L.block / 2) s)) =
        3 * ((X.tr g).take km).countP (commitsTo (inputEmpty L (g / L.block) s.val)) + jw.val ∧
      Assumption.idealMmaElement (.f16 .f16 .f32) (if isB then .b else .a)
          (if isB then ops.b else ops.a) row kk =
        .ok ((if isB then P.b else P.a) ((spw.origin 1).toNat + row % 128)
          ((spw.origin 0).toNat + (16 * jj.val + kk)))

/-- No thread invalidates an mbarrier (`RingEvent.inval`). -/
theorem no_inval {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {i : EvId} {m : Loc} :
    ¬ X.MbInval i m := by
  rintro ⟨pc, he⟩
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  exact (ht.ring_event (Frame.lt_of_get hX he) he hσ).inval m rfl

/-- Every object history has one lifetime: no record invalidates its object. -/
theorem objects_noInval {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) (m : Loc) :
    MBarrier.NoInval (X.objects m) :=
  AsyncCopy.objects_noInval hX.tma.2.2.1 (fun _ _ h => no_inval hX ht h) m

/-- The Tensor Memory resource operations are warp 0's (`ThreadFacts.tmem_event_at`), in the
two-CTA clusters of the launch. -/
theorem ThreadFacts.warpOps {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (ht : ThreadFacts L X) : Tmem.Pair.TmemWarpOps L X 0 where
  launch := hpre.oneDimLaunch
  cluster := hpre.cluster
  warp_lt := by rw [hpre.block]; decide
  event hg he := by
    obtain ⟨h0, hgrp, -, hs, -⟩ := ht.tmem_event_at hg he
    exact ⟨h0, hgrp, hs⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof
