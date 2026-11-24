-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Correction
public import Lemmas.Flow.EventCount
public import Lemmas.Flow.VoteSeq
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The run invariant of a correction thread

`Counts` is the one run invariant of the correction role: the exact number of each of its
synchronizing events in the thread's trace before the event of a state, as formulas in the
item `i`, the trip `t` and the site, with `n` the number of trips:

* named-barrier syncs of stage `st` (`bar.sync k + 3 + 4 st, 64`): `(n + 1) i + syncPos`;
* credits of the statistics barrier of stage `st` (`+240 + 8 st`): `(n + 1) i + creditPos`;
* O-free arrivals on the leader's P-ready barrier of stage `st` (`+144 + 8 st`): one at the start
  and `n` per item, `n i + freePos`;
* successful polls of the final-accumulator barrier (`+192 + 8 st`): `i + oPos`, of the
  staging-free barrier (`+272 + 8 st`): `i + fPos` (one more for `st = 1` after the tail
  wait), staged arrivals (`+256 + 8 st`): `i + stagedPos`;
* the start barrier `bar.sync 2, 416` once, the end barrier `bar.arrive 2, 416` once, last;
* Tensor Memory: per stage, the loads of the stage's output columns are eight per rescale (a
  vote of the stage with a nonzero ballot) and eight per item (the final part), the stores
  eight per rescale, and every rescale ends with one `tcgen05.wait::st`;
* the votes of stage `st`, whatever their ballots: one per loop trip, `(n - 1) i + votePos`;
* the data of the final part: the event that loaded a final chunk's values (`finLd`), the read
  of the statistics word whose word the state holds (`finSt`, `finA`), the staging stores
  done so far with their footprints (`wrote`), and the fence before a staged arrival
  (`fenced`); in a trip, the load that produced a rescale chunk's values (`rsLd`) and the read of
  `α` (`rsSt`).

The shape of each site's event (`Ev`: its kind, object and program counter) is all the
invariant's step needs; it is a fact of the site machine's step (`Fires` at the site). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

/-! ### Counted events -/

/-- Whether `e` is a vote at `pc` whose ballot is not zero. -/
def nzVote (pc : Nat) (e : Event) : Bool :=
  match e.kind with
  | .vote _ _ b => decide (e.pc = pc ∧ b ≠ 0)
  | _ => false

/-- A barrier at offset `off` of the thread's CTA. -/
abbrev ownLoc (L : Launch) (g off : Nat) : Loc := ⟨.shared, ctaOf L g, sb L + off⟩

/-- A barrier at offset `off` of the cluster's leader CTA. -/
abbrev leadLoc (L : Launch) (g off : Nat) : Loc := ⟨.shared, 2 * (ctaOf L g / 2), sb L + off⟩

/-- The output columns of stage `st` (Tensor Memory addresses of the warp's lanes). -/
abbrev oLo (L : Launch) (g : Nat) (st : Nat) : Nat := tmem L g (256 + 128 * st)
abbrev oHi (L : Launch) (g : Nat) (st : Nat) : Nat := tmem L g (384 + 128 * st)

/-! ### The event of a site -/

/-- The event a site performs: its program counter, kind and object. -/
def Ev (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  e.pc = d.site.pc ∧
  match d.site with
  | .setMaxReg => ∃ inst, e.kind = .setMaxReg false 88 inst
  | .bar0 => e.kind = .bar 2 (some 416) .sync
  | .free st => ∃ rel sc, e.kind = .arrive (leadLoc L g (144 + 8 * st.val)) 0 1 rel sc
  | .sync st _ => e.kind = .bar (kOf L g + 3 + 4 * st.val) (some 64) .sync
  | .credit a =>
    ∃ rel sc, e.kind = .arrive (ownLoc L g (240 + 8 * (a.val % 2))) 0 1 rel sc
  | .ldA st => ∃ ac bs, e.kind = .rd ac bs ∧
    ac.loc = ownLoc L g (332 + 512 * st.val + 4 * rowOf L g)
  | .ldL st => ∃ ac bs, e.kind = .rd ac bs ∧
    ac.loc = ownLoc L g (332 + 512 * st.val + 4 * rowOf L g)
  | .vote _ => ∃ mask p b, e.kind = .vote mask p b
  | .rld st j =>
    ∃ vals, e.kind = .tc (.ld (tmem L g (256 + 128 * st.val + 16 * j.val)) vals .s32x32b)
  | .rldW _ _ | .fldW _ _ => e.kind = .tc .waitLd
  | .rst st j =>
    ∃ vals, e.kind = .tc (.st (tmem L g (256 + 128 * st.val + 16 * j.val)) vals .s32x32b)
  | .rwait _ => e.kind = .tc .waitSt
  | .oFree st _ => ∃ rel sc, e.kind = .arrive (leadLoc L g (144 + 8 * st.val)) 0 1 rel sc
  | .oWait st =>
    ∃ ok acq sc, e.kind = .wait (ownLoc L g (192 + 8 * st.val)) (d.i % 2) ok acq sc
  | .fWait st =>
    ∃ ok acq sc, e.kind = .wait (ownLoc L g (272 + 8 * st.val)) ((d.i + 1) % 2) ok acq sc
  | .fld st j =>
    ∃ vals, e.kind = .tc (.ld (tmem L g (256 + 128 * st.val + 16 * j.val)) vals .s32x32b)
  | .fst _ _ _ _ => ∃ ac bs, e.kind = .wr ac bs
  | .fence _ => e.kind = .fenceProxy (.async (some (.shared .cta))) none
  | .staged st => ∃ rel sc, e.kind = .arrive (ownLoc L g (256 + 8 * st.val)) 0 1 rel sc
  | .tailWait => ∃ ok acq sc, e.kind = .wait (ownLoc L g 280) ((d.i + 1) % 2) ok acq sc
  | .barEnd => e.kind = .bar 2 (some 416) .arrive
  | .exit => e.kind = .exit

/-! ### Positions inside an item -/

/-- Syncs of stage `st`'s named barrier in the current item before the site's event. -/
def syncPos (L : Launch) (st : Nat) (d : D) : Nat :=
  let n := trips L
  match d.site with
  | .sync 0 .first => 0
  | .credit 0 | .sync 1 .first => if st = 0 then 1 else 0
  | .sync 0 .loop => 1 + d.t
  | .ldA 0 | .vote 0 | .rld 0 _ | .rldW 0 _ | .rst 0 _ | .rwait 0 | .oFree 0 false | .credit 1
  | .sync 1 .loop => if st = 0 then 2 + d.t else 1 + d.t
  | .ldA 1 | .vote 1 | .rld 1 _ | .rldW 1 _ | .rst 1 _ | .rwait 1 | .oFree 1 false
  | .credit 2 => 2 + d.t
  | .credit 3 | .sync 0 .last => n
  | .ldL 0 | .credit 4 | .oWait 0 | .fWait 0 | .fld 0 _ | .fldW 0 _ | .fst 0 _ _ _ | .fence 0
  | .oFree 0 true | .staged 0 | .sync 1 .last => if st = 0 then n + 1 else n
  | .ldL 1 | .credit 5 | .oWait 1 | .fWait 1 | .fld 1 _ | .fldW 1 _ | .fst 1 _ _ _ | .fence 1
  | .oFree 1 true | .staged 1 => n + 1
  | _ => 0

/-- Credits of stage `st`'s statistics barrier in the current item before the site's event. -/
def creditPos (L : Launch) (st : Nat) (d : D) : Nat :=
  let n := trips L
  match d.site with
  | .sync 1 .first => if st = 0 then 1 else 0
  | .sync 0 .loop | .ldA 0 | .vote 0 | .rld 0 _ | .rldW 0 _ | .rst 0 _ | .rwait 0 | .oFree 0 false
  | .credit 1 => if st = 0 then 1 + d.t else d.t
  | .sync 1 .loop | .ldA 1 | .vote 1 | .rld 1 _ | .rldW 1 _ | .rst 1 _ | .rwait 1 | .oFree 1 false
  | .credit 2 => if st = 0 then 1 + d.t else d.t + 1
  | .credit 3 => if st = 0 then n else n - 1
  | .sync 0 .last | .ldL 0 | .credit 4 => n
  | .oWait 0 | .fWait 0 | .fld 0 _ | .fldW 0 _ | .fst 0 _ _ _ | .fence 0 | .oFree 0 true | .staged 0
  | .sync 1 .last | .ldL 1 | .credit 5 => if st = 0 then n + 1 else n
  | .oWait 1 | .fWait 1 | .fld 1 _ | .fldW 1 _ | .fst 1 _ _ _ | .fence 1 | .oFree 1 true
  | .staged 1 =>
    n + 1
  | _ => 0

/-- O-free arrivals on the leader's P-ready barrier of stage `st` before the site's event:
the first one, then those of the current item. -/
def freePos (L : Launch) (st : Nat) (d : D) : Nat :=
  let n := trips L
  match d.site with
  | .setMaxReg | .bar0 | .free 0 => 0
  | .free 1 => if st = 0 then 1 else 0
  | .sync 0 .loop | .ldA 0 | .vote 0 | .rld 0 _ | .rldW 0 _ | .rst 0 _ | .rwait 0
  | .oFree 0 false =>
    1 + d.t
  | .credit 1 | .sync 1 .loop | .ldA 1 | .vote 1 | .rld 1 _ | .rldW 1 _ | .rst 1 _ | .rwait 1
  | .oFree 1 false => if st = 0 then 2 + d.t else 1 + d.t
  | .credit 2 => 2 + d.t
  | .credit 3 | .sync 0 .last | .ldL 0 | .credit 4 | .oWait 0 | .fWait 0 | .fld 0 _
  | .fldW 0 _
  | .fst 0 _ _ _ | .fence 0 | .oFree 0 true => n
  | .staged 0 | .sync 1 .last | .ldL 1 | .credit 5 | .oWait 1 | .fWait 1 | .fld 1 _
  | .fldW 1 _
  | .fst 1 _ _ _ | .fence 1 | .oFree 1 true => if st = 0 then n + 1 else n
  | .staged 1 => n + 1
  | _ => 1

/-- Successful polls of stage `st`'s final-accumulator barrier in the current item. -/
def oPos (st : Nat) (d : D) : Nat :=
  match d.site with
  | .fWait 0 | .fld 0 _ | .fldW 0 _ | .fst 0 _ _ _ | .fence 0 | .oFree 0 true | .staged 0
  | .sync 1 .last
  | .ldL 1 | .credit 5 | .oWait 1 => if st = 0 then 1 else 0
  | .fWait 1 | .fld 1 _ | .fldW 1 _ | .fst 1 _ _ _ | .fence 1 | .oFree 1 true | .staged 1 => 1
  | _ => 0

/-- Successful polls of stage `st`'s staging-free barrier in the current item (stage 1: also
the tail's). -/
def fPos (st : Nat) (d : D) : Nat :=
  match d.site with
  | .fld 0 _ | .fldW 0 _ | .fst 0 _ _ _ | .fence 0 | .oFree 0 true | .staged 0 | .sync 1 .last
  | .ldL 1 | .credit 5 | .oWait 1 | .fWait 1 => if st = 0 then 1 else 0
  | .fld 1 _ | .fldW 1 _ | .fst 1 _ _ _ | .fence 1 | .oFree 1 true | .staged 1 => 1
  | .barEnd | .exit => if st = 0 then 0 else 1
  | _ => 0

/-- Staged arrivals of stage `st` in the current item. -/
def stagedPos (st : Nat) (d : D) : Nat :=
  match d.site with
  | .sync 1 .last | .ldL 1 | .credit 5 | .oWait 1 | .fWait 1 | .fld 1 _ | .fldW 1 _ | .fst 1 _ _ _
  | .fence 1 | .oFree 1 true | .staged 1 => if st = 0 then 1 else 0
  | _ => 0

/-- The start barrier is passed after `bar0`, the end barrier at the exit. -/
def bar2Sync (d : D) : Nat :=
  match d.site with
  | .setMaxReg | .bar0 => 0
  | _ => 1

def bar2Arrive (d : D) : Nat :=
  match d.site with
  | .exit => 1
  | _ => 0

/-- Loads of stage `st`'s rescale still to come in the current rescale. -/
def ldLack (st : Nat) (d : D) : Nat :=
  match d.site with
  | .rld s j => if s.val = st then 8 - j.val else 0
  | .rldW s j | .rst s j => if s.val = st then 7 - j.val else 0
  | _ => 0

/-- Stores of stage `st`'s rescale still to come in the current rescale. -/
def stLack (st : Nat) (d : D) : Nat :=
  match d.site with
  | .rld s j | .rldW s j | .rst s j => if s.val = st then 8 - j.val else 0
  | _ => 0

/-- The wait of the current rescale, still to come. -/
def waitLack (d : D) : Nat :=
  match d.site with
  | .rld _ _ | .rldW _ _ | .rst _ _ | .rwait _ => 1
  | _ => 0

/-- Loads of stage `st`'s final part in the current item. -/
def finPos (st : Nat) (d : D) : Nat :=
  match d.site with
  | .fld s j => if s.val = st then j.val else if s.val < st then 0 else 8
  | .fldW s j | .fst s j _ _ => if s.val = st then j.val + 1 else if s.val < st then 0 else 8
  | .fence 0 | .oFree 0 true | .staged 0 | .sync 1 .last | .ldL 1 | .credit 5 | .oWait 1
  | .fWait 1 => if st = 0 then 8 else 0
  | .fence 1 | .oFree 1 true | .staged 1 => 8
  | _ => 0

/-- The warp-collective `tcgen05` events of the current rescale still to come: per chunk a load,
its wait and a store, then the wait for the stores. -/
def tcLack (d : D) : Nat :=
  match d.site with
  | .rld _ j => 25 - 3 * j.val
  | .rldW _ j => 24 - 3 * j.val
  | .rst _ j => 23 - 3 * j.val
  | .rwait _ => 1
  | _ => 0

/-- The warp-collective `tcgen05` events of the current item's final part before the site's
event: per stage and chunk a load and its wait. -/
def finTc (d : D) : Nat :=
  match d.site with
  | .fld s j => 16 * s.val + 2 * j.val
  | .fldW s j => 16 * s.val + 2 * j.val + 1
  | .fst s j _ _ => 16 * s.val + 2 * j.val + 2
  | .fence 0 | .oFree 0 true | .staged 0 | .sync 1 .last | .ldL 1 | .credit 5 | .oWait 1
  | .fWait 1 => 16
  | .fence 1 | .oFree 1 true | .staged 1 => 32
  | _ => 0

/-- The vote of stage `st`. -/
abbrev votePc (st : Nat) : Nat := if st = 0 then Flow.vote_0 else Flow.vote_1

/-- Whether `e` is a ballot (`vote.sync.ballot.b32`). -/
def isVote : Event → Bool
  | ⟨_, .vote ..⟩ => true
  | _ => false

/-- Whether `e` is a vote at `pc` (whatever its ballot). -/
def isVoteAt (pc : Nat) (e : Event) : Bool :=
  match e.kind with
  | .vote _ _ _ => e.pc == pc
  | _ => false

/-- Votes of stage `st` in the current item before the site's event: one per loop trip. -/
def votePos (L : Launch) (st : Nat) (d : D) : Nat :=
  match d.site with
  | .sync 0 .loop | .ldA 0 | .vote 0 => d.t
  | .rld 0 _ | .rldW 0 _ | .rst 0 _ | .rwait 0 | .oFree 0 false | .credit 1 | .sync 1 .loop
  | .ldA 1 | .vote 1 => if st = 0 then d.t + 1 else d.t
  | .rld 1 _ | .rldW 1 _ | .rst 1 _ | .rwait 1 | .oFree 1 false | .credit 2 => d.t + 1
  | .credit 3 | .sync 0 .last | .ldL 0 | .credit 4 | .oWait 0 | .fWait 0 | .fld 0 _ | .fldW 0 _
  | .fst 0 _ _ _ | .fence 0 | .oFree 0 true | .staged 0 | .sync 1 .last | .ldL 1 | .credit 5
  | .oWait 1 | .fWait 1 | .fld 1 _ | .fldW 1 _ | .fst 1 _ _ _ | .fence 1 | .oFree 1 true
  | .staged 1 => trips L - 1
  | _ => 0


/-! ### The data of the final part -/

/-- A final chunk's site after its load: the implicit wait or a store of the chunk. -/
def finChunk (d : D) (st : Fin 2) (j : Fin 8) : Prop :=
  d.site = .fldW st j ∨ ∃ h el, d.site = .fst st j h el

/-- A site of stage `st`'s final part after the credit of its load of `l`: `1 / l'` is known. -/
def finRecip (d : D) (st : Fin 2) : Prop :=
  d.site = .oWait st ∨ d.site = .fWait st ∨ (∃ j, d.site = .fld st j) ∨ ∃ j, finChunk d st j

/-- A site of stage `st`'s final part after its load of `l`. -/
def finStat (d : D) (st : Fin 2) : Prop :=
  (st.val = 0 ∧ d.site = .credit 4) ∨ (st.val = 1 ∧ d.site = .credit 5) ∨ finRecip d st

/-- Element `el` of store `h` of final chunk `j` of stage `st` precedes the site in the item. -/
def wDone (d : D) (st : Fin 2) (j : Fin 8) (h : Fin 2) (el : Fin 4) : Prop :=
  match d.site with
  | .fld s j' | .fldW s j' => s = st ∧ j.val < j'.val
  | .fst s j' h' el' =>
    s = st ∧ (j.val < j'.val ∨ (j = j' ∧ (h.val < h'.val ∨ (h = h' ∧ el.val < el'.val))))
  | .fence s | .oFree s true | .staged s => s = st
  | _ => False

/-- A rescale chunk's site after its load: the implicit wait or the store of the chunk. -/
def rsChunk (d : D) (st : Fin 2) (j : Fin 8) : Prop :=
  d.site = .rldW st j ∨ d.site = .rst st j

/-- A site of stage `st`'s trip after its load of `α`: the vote and the rescale's chunks. -/
def rsSite (d : D) (st : Fin 2) : Prop :=
  d.site = .vote st ∨ (∃ j, d.site = .rld st j) ∨ (∃ j, rsChunk d st j) ∨ d.site = .rwait st ∨
    d.site = .oFree st false

/-- A site of stage `st`'s trip after its vote. -/
def rsAfterVote (d : D) (st : Fin 2) : Prop :=
  (∃ j, d.site = .rld st j) ∨ (∃ j, d.site = .rldW st j) ∨ (∃ j, d.site = .rst st j) ∨
    d.site = .rwait st ∨ d.site = .oFree st false

/-- The store of rescale chunk `j` of stage `st` precedes the site in the rescale. -/
def rsStored (d : D) (st : Fin 2) (j : Fin 8) : Prop :=
  match d.site with
  | .rld s j' | .rldW s j' | .rst s j' => s = st ∧ j.val < j'.val
  | .rwait s => s = st
  | _ => False

/-- The prefix `es` has the store of rescale chunk `j` of stage `st` in the credit `q`. -/
def RsStoredIn (L : Launch) (g : Nat) (es : List Event) (st : Fin 2) (j : Fin 8) (q : Nat) :
    Prop :=
  ∃ r < es.length, ∃ pc vals,
    es[r]? = some ⟨pc, .tc (.st (tmem L g (256 + 128 * st.val + 16 * j.val)) vals .s32x32b)⟩ ∧
    arrivals (leadLoc L g (144 + 8 * st.val)) (es.take r) = q

/-- The predicate of the vote at a vote site (a fact of the site's instruction and registers,
beyond `Ev`): the comparison `α < 1` on the word read (`ltOne`). -/
def VoteAt (d : D) (e : Event) : Prop :=
  ∀ st, d.site = .vote st → ∀ m a b, e.kind = .vote m a b → a = ltOne d.aw

/-- The staging address of element `el` of store `h` of final chunk `j` of stage `st`. -/
def fstLoc (L : Launch) (g : Nat) (st : Fin 2) (j : Fin 8) (h : Fin 2) (el : Fin 4) : Loc :=
  ⟨.shared, ctaOf L g,
    stage L g st.val (2 * (j.val % 4) + h.val) + 16384 * (j.val / 4) + 4 * el.val⟩

/-- The footprint of the write at a staging store site (a fact of the site's instruction and
registers, beyond `Ev`). -/
def WrAt (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  ∀ st j h el, d.site = .fst st j h el → ∀ ac bs, e.kind = .wr ac bs →
    ac.loc = fstLoc L g st j h el ∧ ac.size = 4

/-! ### The invariant -/

/-- The run invariant of a correction thread with trace prefix `es` before the event of
state `d`. -/
structure Counts (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop where
  sync : ∀ st < 2,
    barEvents (kOf L g + 3 + 4 * st) 64 .sync es = (trips L + 1) * d.i + syncPos L st d
  credit : ∀ st < 2,
    arrivals (ownLoc L g (240 + 8 * st)) es = (trips L + 1) * d.i + creditPos L st d
  free : ∀ st < 2,
    arrivals (leadLoc L g (144 + 8 * st)) es = trips L * d.i + freePos L st d
  oFull : ∀ st < 2, okPolls (ownLoc L g (192 + 8 * st)) es = d.i + oPos st d
  oFree : ∀ st < 2, okPolls (ownLoc L g (272 + 8 * st)) es = d.i + fPos st d
  staged : ∀ st < 2, arrivals (ownLoc L g (256 + 8 * st)) es = d.i + stagedPos st d
  bar2 : barEvents 2 416 .sync es = bar2Sync d ∧ barEvents 2 416 .arrive es = bar2Arrive d
  tcLd : ∀ st < 2, tcLdsIn (oLo L g st) (oHi L g st) es + ldLack st d =
    8 * es.countP (nzVote (votePc st)) + 8 * d.i + finPos st d
  tcSt : ∀ st < 2, tcStsIn (oLo L g st) (oHi L g st) es + stLack st d =
    8 * es.countP (nzVote (votePc st))
  waitSt : tcWaitSts es + waitLack d =
    es.countP (nzVote (votePc 0)) + es.countP (nzVote (votePc 1))
  /-- The votes of stage `st`, whatever their ballots: one per loop trip. -/
  votes : ∀ st < 2, es.countP (isVoteAt (votePc st)) = (trips L - 1) * d.i + votePos L st d
  /-- At a final chunk's wait or stores, its values are those of the chunk's load, made at the
  item's final credit of the stage. -/
  finLd : ∀ st j, finChunk d st j → ∃ r < es.length, ∃ pc,
    es[r]? = some ⟨pc, .tc (.ld (tmem L g (256 + 128 * st.val + 16 * j.val)) d.o .s32x32b)⟩ ∧
    arrivals (leadLoc L g (144 + 8 * st.val)) (es.take r) = trips L * d.i + trips L
  /-- At a final chunk's stores, the chunk's products and conversions did not fault. -/
  finOk : ∀ st j h el, d.site = .fst st j h el → finOk d.o (fcPair d) = true
  /-- In stage `st`'s final part, the word last read is the row's statistics word, read after
  the item's last sync of the stage. -/
  finSt : ∀ st, finStat d st → ∃ r < es.length, ∃ pc ac bs, es[r]? = some ⟨pc, .rd ac bs⟩ ∧
    ac.loc = ownLoc L g (332 + 512 * st.val + 4 * rowOf L g) ∧ rebuild 3 bs = .ok d.aw ∧
    barEvents (kOf L g + 3 + 4 * st.val) 64 .sync (es.take r) = (trips L + 1) * d.i + trips L + 1
  /-- After the credit of the load of `l`, its reciprocal did not fault, and the reading is the
  reciprocal's. -/
  finA : ∀ st, finRecip d st → ∃ r, recipE d.aw = .ok r ∧ d.a = rd32 r
  /-- The staging stores of the item done before the site, with their footprints. -/
  wrote : ∀ st j h el, wDone d st j h el → ∃ r < es.length, ∃ pc ac bs,
    es[r]? = some ⟨pc, .wr ac bs⟩ ∧ ac.loc = fstLoc L g st j h el ∧ ac.size = 4 ∧
    arrivals (ownLoc L g (256 + 8 * st.val)) (es.take r) = d.i
  /-- At a rescale chunk's wait or store, its values are those of the chunk's load, made at the
  trip's credit of the stage. -/
  rsLd : ∀ st j, rsChunk d st j → ∃ r < es.length, ∃ pc,
    es[r]? = some ⟨pc, .tc (.ld (tmem L g (256 + 128 * st.val + 16 * j.val)) d.o .s32x32b)⟩ ∧
    arrivals (leadLoc L g (144 + 8 * st.val)) (es.take r) = trips L * d.i + (1 + d.t)
  /-- In stage `st`'s trip after its load of `α`, the word is the row's statistics word, read
  after the trip's sync of the stage. -/
  rsSt : ∀ st, rsSite d st → ∃ r < es.length, ∃ pc ac bs, es[r]? = some ⟨pc, .rd ac bs⟩ ∧
    ac.loc = ownLoc L g (332 + 512 * st.val + 4 * rowOf L g) ∧ rebuild 3 bs = .ok d.aw ∧
    barEvents (kOf L g + 3 + 4 * st.val) 64 .sync (es.take r) = (trips L + 1) * d.i + (2 + d.t)
  /-- The rescale's stores done before the site, in the trip's credit. -/
  rsWrote : ∀ st j, rsStored d st j → RsStoredIn L g es st j (trips L * d.i + (1 + d.t))
  /-- After the vote of a trip: its event with the predicate `α < 1` (`ltOne`), the comparison
  not faulting, and, at the O-free arrival, the stores of every chunk when the ballot was not
  zero. -/
  rsVote : ∀ st, rsAfterVote d st → (∃ b, ltOneE d.aw = .ok b) ∧ ∃ v < es.length, ∃ m a b,
    es[v]? = some ⟨(Site.vote st).pc, .vote m a b⟩ ∧ a = ltOne d.aw ∧
    arrivals (leadLoc L g (144 + 8 * st.val)) (es.take v) = trips L * d.i + (1 + d.t) ∧
    (d.site = .oFree st false → b ≠ 0 → ∀ j, RsStoredIn L g es st j (trips L * d.i + (1 + d.t)))
  /-- The proxy fence and the O-free arrival right before a staged arrival. -/
  fenced : ∀ st : Fin 2,
    (d.site = .oFree st true →
      ∃ pc, es[es.length - 1]? = some ⟨pc, .fenceProxy (.async (some (.shared .cta))) none⟩) ∧
    (d.site = .staged st → ∃ pc pc' rel sc,
      es[es.length - 2]? = some ⟨pc, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      es[es.length - 1]? = some ⟨pc', .arrive (leadLoc L g (144 + 8 * st.val)) 0 1 rel sc⟩)
  /-- All ballot events: one per stage and loop trip. -/
  voteN : es.countP isVote = 2 * (trips L - 1) * d.i + votePos L 0 d + votePos L 1 d
  /-- The warp-collective `tcgen05` events: twenty-five per rescale (a nonzero ballot), sixteen
  per stage of each item's final part. -/
  tcColl : es.countP isTcColl + tcLack d = 25 * es.countP isNzVote + 32 * d.i + finTc d
  /-- In a rescale, the last ballot event is nonzero. -/
  rsNz : 0 < tcLack d → ∃ v < es.length, ∃ pc m a b, es[v]? = some ⟨pc, .vote m a b⟩ ∧ b ≠ 0 ∧
    (es.take v).countP isVote + 1 = es.countP isVote


end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
