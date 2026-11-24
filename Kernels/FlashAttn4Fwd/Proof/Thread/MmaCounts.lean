-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaEvents
public import Lemmas.Flow.ElectLead
public import Lemmas.Tmem.PairProtocol
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
public import Lemmas.Flow.PollRounds

@[expose] public section

/-! # The run invariant of the MMA warp

`Mma.Counts` is the one run invariant of an MMA thread: the exact number of each of its
synchronizing events in the trace before the event of a state, as formulas in the item `i`, the
trip `t` and the site, with `n = trips L` KV trips per item.

* Successful polls (every lane): Q-full stage `k`, `i` plus one after the item's poll; KV-full
  slot `s`, the ring uses `U < 2 n i + u` with `U % 6 = s` (`slots`), `u` the uses polled in the
  item; P-ready (`+144 + 8 k`) and second P-ready (`+160 + 8 k`) stage `k`, `n i` plus the trips
  of the item past the poll; the hand-off barrier `+320`, once past `waitDealloc`.
* The hand-off arrival on the peer's `+320` barrier, once past `arrivePeer`.
* Under `ElectLead` (every election returned this lane): the commits to S-full stage `k`
  (`n` per item), to KV-empty slot `s` (the released ring uses, `slots`), to Q-empty and
  O-full stage `k` (one per item), and the MMAs (`32 n` per item).
* Under `ElectNonLead` (no election returned this lane): no commit and no MMA, and the site is
  none of the elected lane's.
* At a site of the elected lane (an MMA, a commit, the elected lane's inner P-ready poll): an
  earlier election with the full member mask returned this lane (`elected`).
* On the odd CTA: no commit and no MMA.
* The warp's start and end, on every lane: the paired Tensor Memory operations (the allocation,
  the relinquishment, the deallocation, `tmemA`), the events on barrier 2 (`bar2A`, each a
  `bar.sync 2, 416`), lane 0's address store right after the allocation, the read-back of the
  base word whose bytes rebuild the carried address `base`, and, past the item loop of the
  leader CTA, every item of the cluster done (`done`).
* Under `ElectLead`: all commits (`comA`, four per loop trip and four more per item).
* A commit site comes right after its election (`commitElect`).
* The elections of every lane (`elects`): the prologue's one, then those of the election sites
  (`elA`, eight per loop trip and four more per item).
* The successful polls at the position of each poll site (`pollsAt`, `pollCnt`): one per item
  for a site before or after the trip loop, one per trip for a site in it (`cntL`: `n - 1` per
  item), one for the hand-off wait.

Each count is `cnt L A m k d = (m n + k) i + A site + m t` (the last term in or after the
loop): `m` events per loop trip, `m n + k` per item, and `A` the events of the item before the
site apart from the done trips, read off an order of the item's sites (`Site.ord`): before the
loop `1 … 16`, a loop trip `100 … 129`, after the loop `200 … 225` (`t = n - 1`).

The step of `next` at the level of sites is `sStep` (`next_eq`), of the event's outcome (a
poll's or an election's) and the site's branch condition; `MmaCountsGen` checks every count's
formula along it by evaluation. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

/-! ### Positions -/

/-- Before the item loop (0), inside an item (1), the end (2). -/
def Site.phase : Site → Nat
  | .setMaxReg | .alloc | .allocWrite | .bar0 | .ldBase | .shflQ => 0
  | .relinquish | .bar1 | .arrivePeer | .waitDealloc | .dealloc | .exit => 2
  | _ => 1

/-- The order of the first site of asm block `b` within the item. -/
def mmaOrd : Fin 8 → Nat
  | 0 => 6 | 1 => 12 | 2 => 106 | 3 => 112 | 4 => 119 | 5 => 125 | 6 => 210 | 7 => 219

/-- The orders of the polls, broadcasts and elections within the item. -/
def qOrd : Fin 2 → Nat
  | 0 => 1 | 1 => 9

def kvOrd : Fin 4 → Nat
  | 0 => 2 | 1 => 100 | 2 => 109 | 3 => 204

def pOrd : Fin 4 → Nat
  | 0 => 101 | 1 => 115 | 2 => 205 | 3 => 215

def p2Ord : Fin 4 → Nat
  | 0 => 107 | 1 => 120 | 2 => 211 | 3 => 220

def shflOrd : Fin 14 → Nat
  | 0 => 3 | 1 => 4 | 2 => 10 | 3 => 102 | 4 => 103 | 5 => 104 | 6 => 110 | 7 => 116
  | 8 => 117 | 9 => 206 | 10 => 207 | 11 => 208 | 12 => 216 | 13 => 217

def elMOrd : Fin 8 → Nat
  | 0 => 5 | 1 => 11 | 2 => 105 | 3 => 111 | 4 => 118 | 5 => 124 | 6 => 209 | 7 => 218

def elCOrd : Fin 12 → Nat
  | 0 => 7 | 1 => 13 | 2 => 15 | 3 => 113 | 4 => 122 | 5 => 126 | 6 => 128 | 7 => 200
  | 8 => 202 | 9 => 213 | 10 => 222 | 11 => 224

/-- The order of a site within an item (0 outside the items): before the loop `1 … 16`, in a
loop trip `100 … 129`, after the loop `200 … 225`. The MMAs of a PV block after its second
P-ready poll come after the poll; a commit follows its election. -/
def Site.ord : Site → Nat
  | .qWait k => qOrd k
  | .kvWait k => kvOrd k
  | .pWait k => pOrd k
  | .p2Wait k _ => p2Ord k
  | .shfl k => shflOrd k
  | .elM b => elMOrd b
  | .mma b j => mmaOrd b + if isPv b = true ∧ 6 ≤ j.val then 2 else 0
  | .elC c => elCOrd c
  | .commit c => elCOrd c + 1
  | _ => 0

/-- One when the site is past the item position `x`. -/
def Site.after (s : Site) (x : Nat) : Nat := if x < s.ord then 1 else 0

/-- One when the site is in a loop trip, past the position `x`. -/
def Site.inTrip (s : Site) (x : Nat) : Nat := if x < s.ord ∧ s.ord < 200 then 1 else 0

/-- One when the site is in or after the loop: its trip `t` counts the loop trips done. -/
def Site.loop (s : Site) : Nat := if 100 ≤ s.ord then 1 else 0

/-- The count of a site's events in the trip loop's part of an item before the site, without
the `t` done trips (`A`), with `m` events per loop trip and `m n + k` per item: before the
event of state `d`, `(m n + k) i + A + m t` (the last term in or after the loop). -/
def cnt (L : Launch) (A : Site → Nat) (m k : Nat) (d : D) : Nat :=
  (m * trips L + k) * d.i + A d.site + m * (d.t * d.site.loop)

/-- A count of loop trips. -/
def cntL (L : Launch) (A : Site → Nat) (d : D) : Nat :=
  (trips L - 1) * d.i + A d.site + d.t * d.site.loop

/-- Q-full polls of stage `k` in the item (`m = 0`, `k = 1`). -/
def qA (k : Fin 2) (s : Site) : Nat := s.after (1 + 8 * k.val)

/-- KV-full polls in the item, the ring uses polled (`m = 2`). -/
def kvA (s : Site) : Nat := s.after 2 + s.inTrip 100 + s.inTrip 109 + s.after 204

/-- P-ready polls of stage `k` (`m = 1`). -/
def pA (k : Fin 2) (s : Site) : Nat := s.inTrip (101 + 14 * k.val) + s.after (205 + 10 * k.val)

/-- Second P-ready polls of stage `k` (`m = 1`). -/
def p2A (k : Fin 2) (s : Site) : Nat := s.inTrip (107 + 13 * k.val) + s.after (211 + 9 * k.val)

/-- KV-empty commits, the ring uses released (`m = 2`). -/
def relA (s : Site) : Nat := s.after 16 + s.inTrip 123 + s.inTrip 129 + s.after 225

/-- S-full commits of stage `k` (`m = 1`). -/
def sA (k : Fin 2) (s : Site) : Nat := s.after (8 + 6 * k.val) + s.inTrip (114 + 13 * k.val)

/-- Q-empty commits of stage `k` (`m = 0`, `k = 1`). -/
def qeA (k : Fin 2) (s : Site) : Nat := s.after (201 + 2 * k.val)

/-- O-full commits of stage `k` (`m = 0`, `k = 1`). -/
def ofA (k : Fin 2) (s : Site) : Nat := s.after (214 + 9 * k.val)

/-- MMAs of the current asm block before the site. -/
def blockPos : Site → Nat
  | .mma _ j => j.val
  | .p2Wait _ _ => 6
  | _ => 0

/-- MMAs: eight per finished block, and those of the current block (`m = 32`). -/
def mmaA (s : Site) : Nat :=
  8 * (s.after 6 + s.after 12) + 8 * (s.inTrip 108 + s.inTrip 112 + s.inTrip 121 +
    s.inTrip 125) + 8 * (s.after 212 + s.after 221) + blockPos s

/-- Successful polls of the own hand-off barrier. -/
def deallocA : Site → Nat
  | .dealloc | .exit => 1
  | _ => 0

/-- Hand-off arrivals on the peer's barrier. -/
def handoffA : Site → Nat
  | .waitDealloc | .dealloc | .exit => 1
  | _ => 0

/-- The ring uses `U < N` of slot `s` (`U % 6 = s`). -/
def slots (N : Nat) (s : Fin 6) : Nat := (N + 5 - s.val) / 6

/-- Sites only an elected lane reaches. -/
def Site.lead : Site → Bool
  | .mma _ _ | .commit _ | .p2Wait _ true => true
  | _ => false

/-- The paired Tensor Memory operations before a site: the allocation, the relinquishment,
the deallocation. -/
def tmemA : Site → Nat
  | .setMaxReg | .alloc => 0
  | .bar1 | .arrivePeer | .waitDealloc | .dealloc => 2
  | .exit => 3
  | _ => 1

/-- The events on barrier 2 before a site: the `bar.sync` after the allocation and the one after
the relinquishment. -/
def bar2A : Site → Nat
  | .setMaxReg | .alloc | .allocWrite | .bar0 => 0
  | .arrivePeer | .waitDealloc | .dealloc | .exit => 2
  | _ => 1

/-- The position of a site in the warp's start: before the allocation (0), at its request (1),
its address store (2), `bar.sync 2` (3), the read-back of the address (4), past it (5). -/
def Site.start : Site → Nat
  | .setMaxReg => 0 | .alloc => 1 | .allocWrite => 2 | .bar0 => 3 | .ldBase => 4 | _ => 5

/-- All commits of the item before the site (`m = 4`, `k = 4`). -/
def comA (s : Site) : Nat :=
  sA 0 s + sA 1 s + relA s + qeA 0 s + qeA 1 s + ofA 0 s + ofA 1 s

/-- A Tensor Core commit. -/
def isTcCommit (e : Event) : Bool :=
  match e.kind with
  | .tc (.commit _) => true
  | _ => false

/-- An election. -/
def isElectE (e : Event) : Bool :=
  match e.kind with
  | .elect .. => true
  | _ => false

/-- The elections of the item before a site: one at each election site (`m = 8`, `k = 4`). -/
def elA (s : Site) : Nat :=
  s.after 5 + s.after 7 + s.after 11 + s.after 13 + s.after 15 +
    (s.inTrip 105 + s.inTrip 111 + s.inTrip 113 + s.inTrip 118 + s.inTrip 122 + s.inTrip 124 +
      s.inTrip 126 + s.inTrip 128) +
    (s.after 200 + s.after 202 + s.after 209 + s.after 213 + s.after 218 + s.after 222 +
      s.after 224)

/-- The poll sites. -/
def Site.isPoll : Site → Bool
  | .qWait _ | .kvWait _ | .pWait _ | .p2Wait _ _ | .waitDealloc => true
  | _ => false

/-- The successful polls at the position of poll site `s0` before the event of state `d`. -/
def pollCnt (L : Launch) (s0 : Site) (d : D) : Nat :=
  if s0 = .waitDealloc then deallocA d.site
  else if region s0 = 2 then cntL L (fun s => s.inTrip s0.ord) d
  else cnt L (fun s => s.after s0.ord) 0 1 d

/-- The base word of the thread's CTA, where the allocation stores the Tensor Memory address. -/
def baseAt (L : Launch) (g : Nat) : Loc := ⟨.shared, g / L.block, L.sharedBase + 328⟩

/-! ### The invariant -/

/-- The run invariant of an MMA thread with trace prefix `es` before the event of state `d`. -/
structure Counts (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop where
  /-- Before the item loop the item is 0. -/
  pre : d.site.phase = 0 → d.i = 0
  qFull : ∀ k : Fin 2, okPolls (bar L g (.qFull k)) es = cnt L (qA k) 0 1 d
  kvFull : ∀ s : Fin 6, okPolls (bar L g (.kvFull s)) es = slots (cnt L kvA 2 0 d) s
  pReady : ∀ k : Fin 2, okPolls (bar L g (.pReady k)) es = cnt L (pA k) 1 0 d
  pReady2 : ∀ k : Fin 2, okPolls (bar L g (.pReady2 k)) es = cnt L (p2A k) 1 0 d
  dealloc : okPolls (bar L g .dealloc) es = deallocA d.site
  handoff : arrivals (FBar.loc L (peer L g) .dealloc) es = handoffA d.site
  sFull : ElectLead L g es → ∀ k : Fin 2,
    es.countP (commitsTo (bar L g (.sFull k))) = cnt L (sA k) 1 0 d
  kvEmpty : ElectLead L g es → ∀ s : Fin 6,
    es.countP (commitsTo (bar L g (.kvEmpty s))) = slots (cnt L relA 2 0 d) s
  qEmpty : ElectLead L g es → ∀ k : Fin 2,
    es.countP (commitsTo (bar L g (.qEmpty k))) = cnt L (qeA k) 0 1 d
  oFull : ElectLead L g es → ∀ k : Fin 2,
    es.countP (commitsTo (bar L g (.oFull k))) = cnt L (ofA k) 0 1 d
  mmas : ElectLead L g es → es.countP isMma = cnt L mmaA 32 0 d
  leadSite : ElectLead L g es → ∀ k, d.site ≠ .p2Wait k false
  nonLead : ElectNonLead L g es →
    d.site.lead = false ∧ (∀ m, es.countP (commitsTo m) = 0) ∧ es.countP isMma = 0
  odd : rank L g ≠ 0 → (∀ m, es.countP (commitsTo m) = 0) ∧ es.countP isMma = 0
  elected : d.site.lead = true → ∃ e ∈ es, ∃ inst, e.kind = .elect 4294967295 inst (laneOf L g)
  /-- The paired Tensor Memory operations. -/
  tmem : Tmem.Pair.tmemOps es = tmemA d.site
  /-- The events on barrier 2, each a `bar.sync 2, 416`. -/
  bar2 : es.countP (Execution.isBarId 2) = bar2A d.site
  bar2Sync : ∀ x ∈ es, Execution.isBarId 2 x = true → x.kind = .bar 2 (some 416) .sync
  /-- Lane 0's address store comes right after its allocation of 512 columns into the base
  word. -/
  allocWrite : d.site = .allocWrite → laneOf L g = 0 ∧
    ∃ x, es.getLast? = some x ∧ x.kind = .tc (.resource .two (some (baseAt L g)) (.alloc 512))
  /-- Past the address store, lane 0 has written the base word, four bytes. -/
  wrote : laneOf L g = 0 → 3 ≤ d.site.start →
    ∃ x ∈ es, ∃ a bs, x.kind = .wr a bs ∧ a.loc = baseAt L g ∧ a.size = 4
  /-- Past the read-back, the read of the base word rebuilds the carried address. -/
  baseRead : 5 ≤ d.site.start →
    ∃ x ∈ es, ∃ a bs, x.kind = .rd a bs ∧ a.loc = baseAt L g ∧ a.size = 4 ∧
      rebuild 3 bs = .ok d.base
  /-- Past the item loop of the leader CTA, every item of the cluster is done. -/
  done : d.site.phase = 2 → rank L g = 0 → totOf L ≤ work L g d.i
  /-- Under `ElectLead`: all commits. -/
  commits : ElectLead L g es → es.countP isTcCommit = cnt L comA 4 4 d
  /-- A commit site comes right after its election, with the full member mask, that returned
  the lane. -/
  commitElect : ∀ c, d.site = .commit c →
    ∃ x inst, es.getLast? = some x ∧ x.kind = .elect 4294967295 inst (laneOf L g)
  /-- The elections of every lane: the prologue's one and the role's. -/
  elects : es.countP isElectE = 1 + cnt L elA 8 4 d
  /-- The successful polls at the position of each poll site. -/
  pollsAt : ∀ s0 : Site, s0.isPoll = true → es.countP (okPollAt s0.pc) = pollCnt L s0 d

/-! ### The objects of a site's event -/

/-- The barrier a site polls. -/
def pollBar (L : Launch) (d : D) : Option FBar :=
  match d.site with
  | .qWait k => some (.qFull k)
  | .kvWait k => some (.kvFull (slotOf L d.i (kvU k d.t)))
  | .pWait k => some (.pReady (stOf k))
  | .p2Wait k _ => some (.pReady2 (stOf k))
  | .waitDealloc => some .dealloc
  | _ => none

/-- The barrier a site commits to. -/
def commitBar (L : Launch) (d : D) : Option FBar :=
  match d.site with
  | .commit c => some (cBar L d c)
  | _ => none

/-- The outcome of a poll (`false` for any other event). -/
def waitOk (e : Event) : Bool :=
  match e.kind with
  | .wait _ _ ok _ _ => ok
  | _ => false

/-- Whether the site is an MMA. -/
def Site.isMma : Site → Bool
  | .mma _ _ => true
  | _ => false

theorem bar_inj {L : Launch} {g : Nat} {b b' : FBar} : bar L g b = bar L g b' ↔ b = b' :=
  ⟨fun h => (FBar.loc_inj h).1, fun h => h ▸ rfl⟩

theorem okPoll_bar {L : Launch} {g : Nat} {e : Event} {B : FBar} {p : Nat} {ok acq : Bool}
    {sc : MbarScope} (h : e.kind = .wait (bar L g B) p ok acq sc) (b : FBar) :
    okPoll (bar L g b) e = (waitOk e && decide (some B = some b)) := by
  obtain ⟨pc, k⟩ := e
  simp only at h
  subst h
  cases ok <;> simp [okPoll, sourceWaitSuccess, waitOk, bar_inj]

theorem notWait_of_quiet {e : Event} (h : ¬ ObjectKind e.kind) :
    ∀ l p ok acq sc, e.kind ≠ .wait l p ok acq sc :=
  fun _ _ _ _ _ he => h (by rw [he]; trivial)

theorem notCommit_of_quiet {e : Event} (h : ¬ ObjectKind e.kind) :
    ∀ sp, e.kind ≠ .tc (.commit sp) :=
  fun _ he => h (by rw [he]; trivial)

theorem notObject_of_mma {e : Event} (h : isMma e = true) : ¬ ObjectKind e.kind := by
  unfold isMma at h
  split at h
  · rename_i heq
    intro hk
    rw [heq] at hk
    exact hk
  · cases h

theorem isMma_of_kind {e : Event} {k : Kind} (h : e.kind = k)
    (hk : ∀ dst sp acc mask, k ≠ .tc (.mma dst sp acc mask)) : isMma e = false := by
  unfold isMma
  rw [h]
  split
  · exact absurd rfl (hk _ _ _ _)
  · rfl

/-- The successful polls of a site's event: on its poll barrier. -/
theorem okPoll_ev {L : Launch} {g : Nat} {d : D} {e : Event} (hev : Ev L g d e) (b : FBar) :
    okPoll (bar L g b) e = (waitOk e && decide (pollBar L d = some b)) := by
  obtain ⟨site, i, t, base, pro⟩ := d
  cases site <;> simp only [Ev] at hev <;> simp only [pollBar]
  case qWait k => obtain ⟨ok, acq, sc, h⟩ := hev; exact okPoll_bar h b
  case kvWait k => obtain ⟨ok, acq, sc, h⟩ := hev; exact okPoll_bar h b
  case pWait k => obtain ⟨ok, acq, sc, h⟩ := hev; exact okPoll_bar h b
  case p2Wait k _ => obtain ⟨ok, acq, sc, h⟩ := hev; exact okPoll_bar h b
  case waitDealloc => obtain ⟨ok, acq, sc, h⟩ := hev; exact okPoll_bar h b
  case arrivePeer =>
    obtain ⟨rel, sc, h⟩ := hev
    simp [okPoll_notWait (m := bar L g b) (e := e) (fun _ _ _ _ _ he => by rw [h] at he; cases he)]
  case commit c => simp [okPoll_notWait (m := bar L g b) (e := e)
    (fun _ _ _ _ _ he => by rw [hev] at he; cases he)]
  case mma => simp [(quiet_of_kind (notObject_of_mma hev) (bar L g b)).1]
  all_goals simp [okPoll_notWait (m := bar L g b) (notWait_of_quiet hev.1)]

/-- The commits of a site's event: on its commit barrier. -/
theorem commitsTo_ev {L : Launch} {g : Nat} {d : D} {e : Event} (hev : Ev L g d e) (b : FBar) :
    commitsTo (bar L g b) e = decide (commitBar L d = some b) := by
  obtain ⟨site, i, t, base, pro⟩ := d
  cases site <;> simp only [Ev] at hev <;> simp only [commitBar]
  case commit c => simp [commitsTo_of_kind hev, cSpec, bar_inj]
  case qWait k | kvWait k | pWait k | p2Wait k _ | waitDealloc =>
    obtain ⟨ok, acq, sc, h⟩ := hev
    simp [commitsTo_of_notCommit (m := bar L g b) (e := e)
      (fun _ he => by rw [h] at he; cases he)]
  case arrivePeer =>
    obtain ⟨rel, sc, h⟩ := hev
    simp [commitsTo_of_notCommit (m := bar L g b) (e := e)
      (fun _ he => by rw [h] at he; cases he)]
  case mma => simp [(quiet_of_kind (notObject_of_mma hev) (bar L g b)).2.2.1]
  all_goals simp [commitsTo_of_notCommit (m := bar L g b) (notCommit_of_quiet hev.1)]

/-- A site that commits nothing commits to no barrier. -/
theorem commitsTo_none {L : Launch} {g : Nat} {d : D} {e : Event} (hev : Ev L g d e)
    (h : commitBar L d = none) (m : Loc) : commitsTo m e = false := by
  obtain ⟨site, i, t, base, pro⟩ := d
  cases site <;> simp only [Ev] at hev <;> simp only [commitBar] at h
  case qWait k | kvWait k | pWait k | p2Wait k _ | waitDealloc =>
    obtain ⟨ok, acq, sc, h⟩ := hev
    exact commitsTo_of_notCommit fun _ he => by rw [h] at he; cases he
  case arrivePeer =>
    obtain ⟨rel, sc, h⟩ := hev
    exact commitsTo_of_notCommit fun _ he => by rw [h] at he; cases he
  case commit c => cases h
  case mma => exact (quiet_of_kind (notObject_of_mma hev) m).2.2.1
  all_goals exact commitsTo_of_notCommit (notCommit_of_quiet hev.1)

/-- Only an MMA site fires an MMA. -/
theorem isMma_ev {L : Launch} {g : Nat} {d : D} {e : Event} (hev : Ev L g d e)
    (h : d.site.isMma = false) : isMma e = false := by
  obtain ⟨site, i, t, base, pro⟩ := d
  cases site <;> simp only [Ev] at hev <;> simp only [Site.isMma] at h
  case qWait k | kvWait k | pWait k | p2Wait k _ | waitDealloc =>
    obtain ⟨ok, acq, sc, h⟩ := hev
    exact isMma_of_kind h fun _ _ _ _ he => by cases he
  case arrivePeer =>
    obtain ⟨rel, sc, h⟩ := hev
    exact isMma_of_kind h fun _ _ _ _ he => by cases he
  case commit c => exact isMma_of_kind hev fun _ _ _ _ he => by cases he
  case mma b j => cases h
  all_goals exact hev.2

/-- An MMA site's event is an MMA. -/
theorem isMma_ev_mma {L : Launch} {g : Nat} {d : D} {e : Event} (hev : Ev L g d e)
    (h : d.site.isMma = true) : isMma e = true := by
  obtain ⟨site, i, t, base, pro⟩ := d
  cases site <;> simp only [Site.isMma, Bool.false_eq_true] at h
  exact hev

/-- The hand-off arrival is the only arrival on the peer's barrier. -/
theorem arrivesOn_ev {L : Launch} {g : Nat} {d : D} {e : Event} (hev : Ev L g d e) :
    arrivesOn (FBar.loc L (peer L g) .dealloc) e = decide (d.site = .arrivePeer) := by
  obtain ⟨site, i, t, base, pro⟩ := d
  cases site <;> simp only [Ev] at hev
  case arrivePeer =>
    obtain ⟨rel, sc, h⟩ := hev
    simp [arrivesOn, sourceArrive, h]
  case qWait k | kvWait k | pWait k | p2Wait k _ | waitDealloc =>
    obtain ⟨ok, acq, sc, h⟩ := hev
    simp [arrivesOn_notArrive (m := FBar.loc L (peer L g) .dealloc) (e := e)
      (fun _ _ _ _ _ he => by rw [h] at he; cases he)]
  case commit c =>
    simp [arrivesOn_notArrive (m := FBar.loc L (peer L g) .dealloc) (e := e)
      (fun _ _ _ _ _ he => by rw [hev] at he; cases he)]
  case mma b j =>
    simp [(quiet_of_kind (notObject_of_mma hev) (FBar.loc L (peer L g) .dealloc)).2.1]
  all_goals simp [(quiet_of_kind hev.1 (FBar.loc L (peer L g) .dealloc)).2.1]

/-! ### The successor at the level of sites -/

/-- How a step changes the item and the trip. -/
inductive Upd where
  | keep | trip | item | reset
  deriving DecidableEq

def Upd.apply : Upd → Nat × Nat → Nat × Nat
  | .keep, p => p
  | .trip, (i, t) => (i, t + 1)
  | .item, (i, _) => (i + 1, 0)
  | .reset, _ => (0, 0)

/-- The site after commit election `c` (`y`: the branch of commits 2, 6, 11). -/
def afterSite (c : Fin 12) (y : Bool) : Site × Upd :=
  match c with
  | 0 => (.qWait 1, .keep)
  | 1 => (.elC 2, .keep)
  | 2 => (if y then .elC 7 else .kvWait 1, .keep)
  | 3 => (.pWait 1, .keep)
  | 4 => (.elM 5, .keep)
  | 5 => (.elC 6, .keep)
  | 6 => (if y then .kvWait 1 else .elC 7, .trip)
  | 7 => (.elC 8, .keep)
  | 8 => (.kvWait 3, .keep)
  | 9 => (.pWait 3, .keep)
  | 10 => (.elC 11, .keep)
  | 11 => (if y then .qWait 0 else .relinquish, .item)

/-- The step of `next` at the level of sites: `x` is the outcome of a poll or of an election,
`y` the branch condition of the site (`cond`). -/
def sStep : Site → Bool → Bool → Site × Upd
  | .setMaxReg, _, _ => (.alloc, .keep)
  | .alloc, _, y => (if y then .allocWrite else .bar0, .keep)
  | .allocWrite, _, _ => (.bar0, .keep)
  | .bar0, _, _ => (.ldBase, .keep)
  | .ldBase, _, _ => (.shflQ, .keep)
  | .shflQ, _, y => (if y then .qWait 0 else .relinquish, .reset)
  | .qWait k, x, _ => (if x then (if k = 0 then .kvWait 0 else .shfl 2) else .qWait k, .keep)
  | .kvWait k, x, _ => (if x then kvNext k else .kvWait k, .keep)
  | .pWait k, x, _ => (if x then pNext k else .pWait k, .keep)
  | .p2Wait k ld, x, _ => (if x then p2Next k ld else .p2Wait k ld, .keep)
  | .shfl k, _, _ => (shflNext k, .keep)
  | .elM b, x, _ => (if x then .mma b 0 else skipGrp b, .keep)
  | .mma b j, _, _ => (mmaNext b j, .keep)
  | .elC c, x, y => if x then (.commit c, .keep) else afterSite c y
  | .commit c, _, y => afterSite c y
  | .relinquish, _, _ => (.bar1, .keep)
  | .bar1, _, _ => (.arrivePeer, .keep)
  | .arrivePeer, _, _ => (.waitDealloc, .keep)
  | .waitDealloc, x, _ => (if x then .dealloc else .waitDealloc, .keep)
  | .dealloc, _, _ => (.exit, .keep)
  | .exit, _, _ => (.exit, .keep)

/-- The branch condition of a commit election. -/
def condC (L : Launch) (g : Nat) (d : D) (c : Fin 12) : Bool :=
  if c = 2 then decide (trips L - 1 < 1)
  else if c = 6 then decide (d.t + 1 < trips L - 1)
  else if c = 11 then decide (work L g (d.i + 1) < totOf L)
  else false

/-- The branch condition of a site. -/
def cond (L : Launch) (g : Nat) (d : D) : Bool :=
  match d.site with
  | .alloc => decide (laneOf L g = 0)
  | .shflQ => decide (rank L g = 0 ∧ work L g 0 < totOf L)
  | .elC c | .commit c => condC L g d c
  | _ => false

/-- Whether an election returned the thread's lane (`false` for any other event). -/
def electLead (L : Launch) (g : Nat) (e : Event) : Bool :=
  match e.kind with
  | .elect _ _ ld => decide (laneOf L g = ld)
  | _ => false

/-- The outcome of an event: of a poll, or of an election. -/
def outcome (L : Launch) (g : Nat) (e : Event) : Bool := waitOk e || electLead L g e

theorem waitOk_of {e : Event} {l : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (h : e.kind = .wait l p ok acq sc) : waitOk e = ok := by
  simp [waitOk, h]

/-- `next` is `sStep` of the event's outcome and the site's condition. -/
theorem next_eq {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : next L g d e = some (some d')) :
    d'.site = (sStep d.site (outcome L g e) (cond L g d)).1 ∧
      (d'.i, d'.t) = (sStep d.site (outcome L g e) (cond L g d)).2.apply (d.i, d.t) := by
  obtain ⟨site, i, t, base, pro⟩ := d
  cases site <;> simp only [next] at hn <;> simp only [sStep, cond]
  case commit c =>
    obtain rfl := Option.some.inj (Option.some.inj hn)
    fin_cases c <;> simp [afterCommit, afterSite, condC, Upd.apply] <;> split_ifs <;> simp
  case elC c =>
    split at hn
    · rename_i mk inst ld heq
      have ho : outcome L g e = decide (laneOf L g = ld) := by
        simp [outcome, waitOk, electLead, heq]
      rw [ho]
      split_ifs at hn with hl
      · obtain rfl := Option.some.inj (Option.some.inj hn)
        simp [hl, Upd.apply]
      · obtain rfl := Option.some.inj (Option.some.inj hn)
        fin_cases c <;> simp [hl, afterCommit, afterSite, condC, Upd.apply] <;> split_ifs <;>
          simp
    · cases hn
  all_goals repeat' split at hn
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals (try simp_all [outcome, waitOk, electLead, Upd.apply, start])
  all_goals (split_ifs <;> simp_all)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
