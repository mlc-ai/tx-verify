-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Bars
public import Kernels.FlashAttn4Fwd.Proof.Thread.Common
public import Kernels.FlashAttn4Fwd.Proof.Interface.Cluster
public import Kernels.FlashAttn4Fwd.Proof.Interface.Schedule
public import Kernels.FlashAttn4Fwd.Data.TensorMaps
public import Lemmas.Flow.Polls
public import Lemmas.Flow.NotTensor
public import Lemmas.Flow.NotCommit

@[expose] public section

/-! # What the thread layer exports for the Q and KV rings

The loader (warp 14) of each CTA of a pair fills two rings that the leader CTA's MMA warp
(warp 12 of the even CTA) reads:

* the **Q ring**: stage `st < 2` holds the item's Q tile half `st`, 32768 bytes per CTA from
  offset `68608 + 32768 st`; full barrier `qFull st` (`+8 st`), empty barrier `qEmpty st`
  (`+16 + 8 st`); one use per item;
* the **KV ring**: slot `s < 6` holds a K or a V block, 16384 bytes per CTA from offset
  `134144 + 16384 s`; full barrier `kvFull s` (`+32 + 8 s`), empty barrier `kvEmpty s`
  (`+80 + 8 s`); `2 n` uses per item, K and V alternating, so the even slots hold K blocks
  (two copies of 8192 bytes per CTA) and the odd slots V blocks (one copy of 16384 bytes).

Per use, the leader CTA's loader arrives once on the leader's full barrier expecting the bytes
of both CTAs' copies (`useBytes`: 65536 for a Q stage, 32768 for a KV slot), and each CTA's
loader issues its copies completing on that barrier (`copies`, `copyBytes`; the odd CTA's
copies name the leader's barrier through the peer bit). The leader's MMA warp polls the full
barrier, reads the slot, and commits once to its CTA's empty barrier, multicast to the empty
barrier of both CTAs, which each CTA's loader polls before its next use of the slot (its first
poll passes on the fresh barrier, `FBar.pollOffset`). After its items, the loader polls the six
KV empty barriers and the Q stage 1 empty barrier once more (the drain), and the leader's loader
arrives once more on `qFull 1`, without copies.

Only the lane an election returned arrives, copies or commits (`LeadAt`: an earlier
`elect.sync` with the full member mask returned the thread's lane); every lane of the loader and
of the leader's MMA warp polls. The fields are event-level facts of single threads, from the
run invariants of the loader (`Loader.Counts`) and of the MMA warp (`Mma.Counts`), and the
placement facts of the copies' and MMAs' shared-memory footprints: a copy is of the use of its
loader's last empty poll (`issue_use`), only copies write a ring region (`only_copies`), and
before the commit of a use the use's MMAs read every byte of the slot in both CTAs (`cover`).
Warp 0's elected lane initializes every ring barrier of its CTA once, before its cluster
arrival (`init`, `init_done`, from the prologue's run invariant).

`RingCopies` names each copy's map, coordinates and destination (`copySpec`) as a function of
its loader's earlier copies on the slot: copy `j` of use `u` loads, for the use's item
(`useItem`) and KV block (`useBlock`), the Q rows `512 m + 256 st + 128 r` or the K rows
`128 blk + 64 r` at head-dimension columns `64 j`, or the V rows `128 blk` at columns `64 r`
(`r` the CTA's rank), into box `j` of the region (from the loader's `loader_copy` fact and the
launch's maps, D-TMAP-BOX). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

namespace FBar

/-- The barriers of the Q and KV rings. -/
def ring : FBar → Bool
  | .qFull _ | .qEmpty _ | .kvFull _ | .kvEmpty _ => true
  | _ => false

/-- The full barriers of the rings. -/
def isFull : FBar → Bool
  | .qFull _ | .kvFull _ => true
  | _ => false

/-- The empty barriers of the rings. -/
def isEmpty : FBar → Bool
  | .qEmpty _ | .kvEmpty _ => true
  | _ => false

/-- A ring barrier's partner: the empty barrier of a full one, and the reverse. -/
def partner : FBar → FBar
  | .qFull st => .qEmpty st
  | .qEmpty st => .qFull st
  | .kvFull s => .kvEmpty s
  | .kvEmpty s => .kvFull s
  | b => b

/-- The copies of each CTA per use of a full barrier: two Q boxes, two K boxes (even KV slots),
one V box (odd KV slots). -/
def copies : FBar → Nat
  | .qFull _ => 2
  | .kvFull s => if s.val % 2 = 0 then 2 else 1
  | _ => 0

/-- The bytes of each copy on a full barrier. -/
def copyBytes : FBar → Nat
  | .qFull _ => 16384
  | .kvFull s => if s.val % 2 = 0 then 8192 else 16384
  | _ => 0

/-- The bytes a use of a full barrier expects: both CTAs' copies. -/
def useBytes (b : FBar) : Nat := 2 * b.copies * b.copyBytes

/-- The offset of the shared-memory region a full barrier guards, in each CTA. -/
def regionOff : FBar → Nat
  | .qFull st => 68608 + 32768 * st.val
  | .kvFull s => 134144 + 16384 * s.val
  | _ => 0

/-- The size of the region a full barrier guards, in each CTA. -/
def regionSize : FBar → Nat
  | .qFull _ => 32768
  | .kvFull _ => 16384
  | _ => 0

theorem useBytes_q (st : Fin 2) : (FBar.qFull st).useBytes = 65536 := by
  simp only [useBytes, copies, copyBytes]

theorem useBytes_kv (s : Fin 6) : (FBar.kvFull s).useBytes = 32768 := by
  simp only [useBytes, copies, copyBytes]
  split_ifs <;> simp

end FBar

/-- Byte `l` lies in the region of full barrier `b` in CTA `cta`. -/
def InRegion (L : Launch) (cta : Nat) (b : FBar) (l : Loc) : Prop :=
  l.space = .shared ∧ l.cta = cta ∧ L.sharedBase + b.regionOff ≤ l.addr ∧
    l.addr < L.sharedBase + b.regionOff + b.regionSize

/-- The even CTA of thread `g`'s pair, whose full barriers the copies complete on. -/
def pairBase (L : Launch) (g : Nat) : Nat := 2 * (ctaOf L g / 2)

/-- An election of thread `g` before its event `k`, with the full member mask, returned its
lane. -/
def LeadAt (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  ∃ j < k, ∃ pc inst, X.Elect (g, j) pc 4294967295 inst (laneOf L g)

/-- The thread layer's facts for the Q and KV rings. -/
structure RingFacts (L : Launch) (X : Execution) : Prop where
  /-- A poll of a ring barrier of CTA `c` is a thread of `c`'s: of the even CTA's MMA warp for a
  full barrier, of the loader for an empty one. Its parity is that of its thread's earlier
  successful polls of the barrier plus the barrier's poll offset, and a successful one
  acquires at cluster scope (every ring poll site is a `.cta`-scoped acquire wait that
  `Assumptions.clusterMbar` widens: `fullWaits`, `commitWaits`). -/
  poll : ∀ {g k pc p c : Nat} {b : FBar} {ok acq : Bool} {sc : MbarScope}, g < L.threads →
    X.get (g, k) = some ⟨pc, .wait (b.loc L c) p ok acq sc⟩ → b.ring →
      c = ctaOf L g ∧ (b.isFull → warpOf L g = 12 ∧ ctaOf L g % 2 = 0) ∧
      (b.isEmpty → warpOf L g = 14) ∧
      p % 2 = (okPolls (b.loc L c) ((X.tr g).take k) + b.pollOffset) % 2 ∧
      (ok = true → acq = true ∧ sc = .cluster)
  /-- Every successful poll is the poll of a canonical spin (DEP-CANONICAL-SPIN). -/
  spins : ∀ {g k pc p : Nat} {m : Loc} {acq : Bool} {sc : MbarScope}, g < L.threads →
    X.get (g, k) = some ⟨pc, .wait m p true acq sc⟩ → ∃ exit, kernel.CanonicalSpin pc exit
  /-- An arrival on a ring barrier is the leader CTA's elected loader lane's, on a full barrier
  of its CTA, with one unit expecting the use's bytes, after more successful polls of the
  partner empty barrier than its earlier arrivals on the full barrier. -/
  arrive : ∀ {g k pc tx cnt c : Nat} {b : FBar} {rel : Bool} {sc : MbarScope}, g < L.threads →
    X.get (g, k) = some ⟨pc, .arrive (b.loc L c) tx cnt rel sc⟩ → b.ring →
      b.isFull ∧ c = ctaOf L g ∧ ctaOf L g % 2 = 0 ∧ warpOf L g = 14 ∧ LeadAt L X g k ∧
      tx = b.useBytes ∧ cnt = 1 ∧
      arrivals (b.loc L c) ((X.tr g).take k) + 1 ≤ okPolls (b.partner.loc L c) ((X.tr g).take k)
  /-- A copy completing on a ring barrier is an elected loader lane's, on a full barrier of the
  even CTA of its pair, of the barrier's copy bytes; it has fewer earlier such copies than the
  barrier's copies per successful poll of the partner empty barrier of its own CTA. -/
  issue : ∀ {g k pc a c : Nat} {b : FBar} {sp : TensorCopy.Spec}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar = b.loc L c → b.ring →
      b.isFull ∧ c = pairBase L g ∧ warpOf L g = 14 ∧ LeadAt L X g k ∧
      TensorTransfer.bytes sp.descriptor = b.copyBytes ∧
      ((X.tr g).take k).countP (issuesTo (b.loc L c)) + 1 ≤
        b.copies * okPolls (b.partner.loc L (ctaOf L g)) ((X.tr g).take k)
  /-- A copy on a ring full barrier is of the use of its thread's last successful poll of the
  partner empty barrier of its CTA: its earlier copies there over the barrier's copies per use
  are one fewer than those polls. -/
  issue_use : ∀ {g k pc a c : Nat} {b : FBar} {sp : TensorCopy.Spec}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar = b.loc L c → b.ring →
      ((X.tr g).take k).countP (issuesTo (b.loc L c)) / b.copies + 1 =
        okPolls (b.partner.loc L (ctaOf L g)) ((X.tr g).take k)
  /-- A commit notifying a ring barrier is the leader CTA's elected MMA lane's, to an empty
  barrier of its CTA, multicast over the pair from its CTA (the cluster base, of a cluster of
  two); it follows more successful polls of the partner full barrier than its earlier commits
  to the empty barrier. -/
  commit : ∀ {g k pc c : Nat} {b : FBar} {sp : TcCommit.Spec} {r : Fin 16}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some (b.loc L c) →
    b.ring →
      b.isEmpty ∧ warpOf L g = 12 ∧ ctaOf L g % 2 = 0 ∧ LeadAt L X g k ∧
      sp.mbar = b.loc L (ctaOf L g) ∧ sp.clusterBase = ctaOf L g ∧ sp.clusterSize = 2 ∧
      ((X.tr g).take k).countP (commitsTo sp.mbar) + 1 ≤
        okPolls (b.partner.loc L (ctaOf L g)) ((X.tr g).take k)
  /-- A tensor write is a copy's on a ring full barrier of its pair's even CTA, into that
  barrier's region of its own CTA. -/
  write : ∀ {g k x y z : Nat} {l : Loc}, AsyncCovers X (g, k) (.write (.load x y z)) l →
      ∃ pc a sp, ∃ b : FBar, X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩ ∧ b.isFull ∧
        sp.mbar = b.loc L (pairBase L g) ∧ InRegion L (ctaOf L g) b l
  /-- Every memory write of a byte in a ring region is a tensor copy's. -/
  only_copies : ∀ {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte} {c : Nat} {b : FBar} {l : Loc},
    X.MemWrites w a bs → a.Covers l → b.isFull → InRegion L c b l →
      ∃ i x y z, w = .async i (.write (.load x y z))
  /-- An MMA operand read of a byte in a ring region of CTA `c` is a `cta_group::2` MMA's
  (`PairTc`) by an elected lane of the MMA warp of `c`'s even CTA, between its successful poll of
  the region's full barrier and its commit to the partner empty barrier of that use. -/
  read : ∀ {g k c : Nat} {b : FBar} {isB : Bool} {idx : Nat} {l : Loc},
    AsyncCovers X (g, k) (.mmaRead isB idx) l → b.isFull → InRegion L c b l →
      PairTc X (g, k) ∧ warpOf L g = 12 ∧ ctaOf L g = 2 * (c / 2) ∧ LeadAt L X g k ∧
      ((X.tr g).take k).countP (commitsTo (b.partner.loc L (ctaOf L g))) + 1 ≤
        okPolls (b.loc L (ctaOf L g)) ((X.tr g).take k)
  /-- Before the leader MMA lane's commit to a ring empty barrier, MMAs of the commit's use (as
  many earlier commits to the barrier) read every byte of the partner full barrier's region in
  both CTAs of the pair; each has read it once a wait observes its completion. -/
  cover : ∀ {g jc pc c : Nat} {b : FBar} {sp : TcCommit.Spec} {l : Loc}, g < L.threads →
    X.get (g, jc) = some ⟨pc, .tc (.commit sp)⟩ → b.isFull →
    sp.mbar = b.partner.loc L (ctaOf L g) → InRegion L c b l → c / 2 = ctaOf L g / 2 →
      ∃ kR isB idx, kR < jc ∧ X.TcAsync (g, kR) ∧
        ((X.tr g).take kR).countP (commitsTo sp.mbar) =
          ((X.tr g).take jc).countP (commitsTo sp.mbar) ∧
        AsyncCovers X (g, kR) (.mmaRead isB idx) l ∧
        ∀ w ws, AsyncCopy.AsyncObserved X (g, kR) .mmaDone w true ws →
          X.AsyncPresent (g, kR) (.mmaRead isB idx)
  /-- At its exit, an elected loader lane has polled every ring empty barrier but Q stage 0's
  once more than its uses of the partner full barrier (the drain): its copies there are the
  barrier's copies per use times its successful polls, less one use. -/
  drain : ∀ {g k pc : Nat} {b : FBar}, g < L.threads → X.get (g, k) = some ⟨pc, .exit⟩ →
    warpOf L g = 14 → LeadAt L X g k → b.isFull → b ≠ .qFull 0 →
      (X.tr g).countP (issuesTo (b.loc L (pairBase L g))) + b.copies =
        b.copies * okPolls (b.partner.loc L (ctaOf L g)) (X.tr g)
  /-- An initialization of a ring barrier is an elected lane's, its thread's only one of the
  barrier. -/
  init : ∀ {g k pc c n : Nat} {b : FBar}, g < L.threads →
    X.get (g, k) = some ⟨pc, .mbInit (b.loc L c) n⟩ → b.ring →
      LeadAt L X g k ∧
        ∀ k' pc' n', X.get (g, k') = some ⟨pc', .mbInit (b.loc L c) n'⟩ → k' = k
  /-- A thread of warp 0 that reaches its cluster arrival initialized every ring barrier of its
  CTA before it, unless a full-mask election before it returned another lane. -/
  init_done : ∀ {g : Nat}, g < L.threads → warpOf L g = 0 → clFirst X g < (X.tr g).length →
    (∀ b : FBar, b.ring → ∃ k < clFirst X g, ∃ pc n,
      X.get (g, k) = some ⟨pc, .mbInit (b.loc L (ctaOf L g)) n⟩) ∨
    ∃ k < clFirst X g, ∃ pc inst l, X.Elect (g, k) pc 4294967295 inst l ∧ l ≠ laneOf L g

/-! ### The copies' tensor maps and coordinates -/

/-- The KV blocks of an item: `ceil(seqlen_k / 128)`. -/
def kvBlocks (P : Params) : Nat := (P.sk + 127) / 128

/-- The tensor map of the copies on full barrier `b`: Q for a Q stage, K for an even KV slot,
V for an odd one. -/
def copyMap (P : Params) : FBar → TensorDescriptor.Descriptor 3
  | .kvFull s =>
    if s.val % 2 = 0 then FlashAttn4Fwd.mapK P.kBase P.sk P.h P.b P.kFill P.kClass
    else FlashAttn4Fwd.mapV P.vBase P.sk P.h P.b P.vFill P.vClass
  | _ => FlashAttn4Fwd.mapQ P.qBase P.sq P.h P.b P.qFill P.qClass

/-- The item (of the cluster's schedule) of use `u` of full barrier `b`: the use itself for a Q
stage (one use per item); for KV slot `s` the ring's use `6 u + s` over the item's `2 n`
uses. -/
def useItem (P : Params) (b : FBar) (u : Nat) : Nat :=
  match b with
  | .kvFull s => (6 * u + s.val) / (2 * kvBlocks P)
  | _ => u

/-- The KV block of use `u` of KV slot `s`: the item's uses are its blocks `n - 1, …, 0`, K
before V. -/
def useBlock (P : Params) (b : FBar) (u : Nat) : Nat :=
  match b with
  | .kvFull s => kvBlocks P - 1 - (6 * u + s.val) % (2 * kvBlocks P) / 2
  | _ => 0

/-- The coordinates `{d, row, head, batch}` of copy `j` of use `u` of full barrier `b` by
thread `g` (rank `r` of its pair; batch, head and query block of the use's item): Q rows
`512 m + 256 st + 128 r`, head-dimension columns `64 j`; K rows `128 blk + 64 r`, columns
`64 j`; V rows `128 blk`, columns `64 r` (fa4-structure §2, §6-§7; D-TMAP-BOX). -/
def copyOrigin (P : Params) (L : Launch) (g : Nat) (b : FBar) (u j : Nat) : Fin 4 → Int :=
  let w := coordsOf L (workOf L g (useItem P b u))
  let r := ctaOf L g % 2
  let blk := useBlock P b u
  match b with
  | .qFull st => ![((64 * j : Nat) : Int), ((512 * w.2.2 + 256 * st.val + 128 * r : Nat) : Int),
      (w.2.1 : Int), (w.1 : Int)]
  | .kvFull s =>
    if s.val % 2 = 0 then
      ![((64 * j : Nat) : Int), ((128 * blk + 64 * r : Nat) : Int), (w.2.1 : Int), (w.1 : Int)]
    else ![((64 * r : Nat) : Int), ((128 * blk : Nat) : Int), (w.2.1 : Int), (w.1 : Int)]
  | _ => fun _ => 0

/-- The copy by thread `g` on full barrier `b` with `cnt` earlier ones there: copy
`j = cnt % copies` of use `cnt / copies`, of its map at the use's coordinates, into box `j` of
the barrier's region of the thread's CTA (`copyBytes` apart), completing on the barrier of its
pair's even CTA, a `cta_group::2` copy through a `.shared::cluster` address. -/
def copySpec (P : Params) (L : Launch) (g : Nat) (b : FBar) (cnt : Nat) : TensorCopy.Spec :=
  ⟨⟨3, copyMap P b, copyOrigin P L g b (cnt / b.copies) (cnt % b.copies),
    ⟨.shared, ctaOf L g, L.sharedBase + b.regionOff + cnt % b.copies * b.copyBytes⟩, none⟩,
    b.loc L (pairBase L g), true, .two⟩

/-- The thread layer's facts of the copies' maps and coordinates (from the loader's run
invariant, `loader_copy`, and the launch's maps). -/
structure RingCopies (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- A copy on a ring full barrier is `copySpec` of its thread and its earlier copies there. -/
  copy : ∀ {g k pc a c : Nat} {b : FBar} {sp : TensorCopy.Spec}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar = b.loc L c → b.isFull →
      sp = copySpec P L g b (((X.tr g).take k).countP (issuesTo (b.loc L c)))

end
end PTX.Kernels.FlashAttn4Fwd.Proof
