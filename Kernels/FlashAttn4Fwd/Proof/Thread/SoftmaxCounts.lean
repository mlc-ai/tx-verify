-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Softmax
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxRef
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxReadings
public import Lemmas.Flow.EventCount
public import Lemmas.Flow.ElectLead
public import Lemmas.Order.WarpBarOrdinal
public import Lemmas.Flow.PollRounds

@[expose] public section

/-! # The run invariant of a softmax thread

`Counts` is the one run invariant of the softmax role: the exact number of each of its
synchronizing events in the thread's trace before the event of a state, as formulas in the
item `i`, the trip `t` and the site, with `n` the number of key-value tiles (`trips`), `st` the
stage and `k` the warp's index in it:

* successful polls of the statistics barrier (`+240 + 8 st`): `n + 1` per item, `(n + 1) i +
  statsPos`, and one more at the tail;
* successful polls of the score barrier (`+128 + 8 st`): `n` per item, `n i + sPos`;
* arrivals on the leader's P-ready barrier (`+144 + 8 st`): `n i + pPos`; on the leader's
  second P-ready barrier (`+160 + 8 st`): `n i + p2Pos` when every election of the trace
  returned this lane (`ElectLead`), none when none did (`ElectNonLead`);
* `bar.arrive k + 3 + 4 st, 64`: `n + 1` per item, `(n + 1) i + genPos`; before each, one more
  successful statistics poll than arrivals (the credit of the correction warp: `genPos + 1 =
  statsPos` at the `gen` sites);
* the start barrier `bar.sync 2, 416` once, the end barrier `bar.arrive 2, 416` once, last;
* Tensor Memory: per tile four loads of the stage's score columns (`tmem 0 … tmem 128`), four
  stores of its probability columns (`tmem 64 … tmem 128`) and two `tcgen05.wait::st`;
* the writes of the statistics word (`+332 + 4 tid`): `n` per item (`α` per loop trip, `l`);
* the warp barriers (`bar.warp.sync`): one per tile, after its P-ready arrival;
* the elections: one per tile, after its warp barrier, and the prologue's fourteen in warp 0;
* all warp-collective `tcgen05` events: per tile the four loads, their four implicit waits, the
  four stores and the two `wait::st`;
* the successful polls at each poll site (its rounds, `roundOf`);
* the words of the state: the values the current tile's loads returned (`words`);
* the reference maximum and the row sum: the recurrence of the loaded scores (`refs`).

The step of the rounds also uses the event's position, the site's (`counts_step`'s `hpc`).

The shape of each site's event (`Ev`: its kind and object) is all the invariant's step needs;
it is a fact of the site machine's step (`Fires` at the site). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A location at offset `off` of the thread's CTA's shared memory. -/
abbrev ownLoc (L : Launch) (g off : Nat) : Loc := ⟨.shared, ctaOf L g, sb L + off⟩

/-- A location at offset `off` of the cluster's leader CTA's shared memory. -/
abbrev leadLoc (L : Launch) (g off : Nat) : Loc := ⟨.shared, 2 * (ctaOf L g / 2), sb L + off⟩

/-- The thread's statistics word (`α`, `l`). -/
abbrev statsWord (L : Launch) (g : Nat) : Loc := ownLoc L g (332 + 4 * tidOf L g)

/-! ### The event of a site -/

/-- The event a site performs: its kind and object. -/
def Ev (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  let st := stOf L g
  match d.site with
  | .setMaxReg => ∃ inst, e.kind = .setMaxReg true 176 inst
  | .bar0 => e.kind = .bar 2 (some 416) .sync
  | .statsW _ => ∃ p ok acq sc, e.kind = .wait (ownLoc L g (240 + 8 * st)) p ok acq sc
  | .sW _ => ∃ p ok acq sc, e.kind = .wait (ownLoc L g (128 + 8 * st)) p ok acq sc
  | .ld _ c => ∃ vals, e.kind = .tc (.ld (tmem L g (32 * c.val)) vals .s32x32b)
  | .ldW _ _ => e.kind = .tc .waitLd
  | .alphaSt | .lSt =>
    ∃ sz acq rel sc el rx bs, e.kind = .wr ⟨statsWord L g, sz, acq, rel, sc, el, rx⟩ bs
  | .gen _ => e.kind = .bar (kOf L g + 3 + 4 * st) (some 64) .arrive
  | .pst _ c => ∃ vals, e.kind = .tc (.st (tmem L g (64 + 16 * c.val)) vals .s32x32b)
  | .pwait _ _ => e.kind = .tc .waitSt
  | .pArr _ => ∃ tx c rel sc, e.kind = .arrive (leadLoc L g (144 + 8 * st)) tx c rel sc
  | .warpBar _ => ∃ m inst, e.kind = .warpBar m inst
  | .el _ => ∃ m inst ld, e.kind = .elect m inst ld
  | .p2Arr _ => ∃ tx c rel sc, e.kind = .arrive (leadLoc L g (160 + 8 * st)) tx c rel sc
  | .barEnd => e.kind = .bar 2 (some 416) .arrive
  | .exit => e.kind = .exit

/-! ### Positions inside an item -/

/-- Sites of the first tile after its score poll. -/
def Site.tile0Ld : Site → Bool
  | .statsW 0 | .sW false => false
  | s => s.tile0

/-- Successful statistics polls in the current item before the site's event (at a site of an
item). -/
def statsPos (d : D) : Nat :=
  match d.site with
  | .statsW 0 => 0
  | s => if s.tile0 then 1 else 2 + d.t

/-- Successful score polls in the current item before the site's event. -/
def sPos (d : D) : Nat :=
  match d.site with
  | .sW true => 1 + d.t
  | .lSt | .gen 2 => 1 + d.t
  | s => if s.tile0Ld then 1 else if s.inTrip then 2 + d.t else 0

/-- Whether the site follows the tile's P-ready arrival (`+144`). -/
def Site.afterP : Site → Bool
  | .pst _ 3 | .pwait _ 1 | .warpBar _ | .el _ | .p2Arr _ | .statsW 1 | .statsW 2 => true
  | _ => false

/-- Whether the site follows the tile's elected arrival (`+160`). -/
def Site.afterP2 : Site → Bool
  | .statsW 1 | .statsW 2 => true
  | _ => false

/-- Whether the site follows the tile's named-barrier arrival. -/
def Site.afterGen : Site → Bool
  | .ld _ _ | .ldW _ _ | .statsW 0 | .sW _ | .alphaSt | .gen _ => false
  | s => s.tile0 || s.inTrip

/-- The tile index of the site inside the item: the first tile `0`, loop trip `t` is `t + 1`;
the item's end counts its `n = t + 1` tiles. -/
def tileNo (d : D) : Nat := if d.site.tile0 then 0 else d.t + 1

/-- Arrivals on the leader's P-ready barrier in the current item. -/
def pPos (d : D) : Nat :=
  if d.site.tile0 || d.site.inTrip || d.site = .lSt || d.site = .gen 2 then
    tileNo d + (if d.site.afterP then 1 else 0)
  else 0

/-- Elected arrivals on the leader's second P-ready barrier in the current item. -/
def p2Pos (d : D) : Nat :=
  if d.site.tile0 || d.site.inTrip || d.site = .lSt || d.site = .gen 2 then
    tileNo d + (if d.site.afterP2 then 1 else 0)
  else 0

/-- Named-barrier arrivals in the current item. -/
def genPos (d : D) : Nat :=
  if d.site.tile0 || d.site.inTrip || d.site = .lSt || d.site = .gen 2 then
    tileNo d + (if d.site.afterGen then 1 else 0)
  else 0

/-- Score loads in the current item. -/
def ldPos (d : D) : Nat :=
  if d.site.tile0 || d.site.inTrip || d.site = .lSt || d.site = .gen 2 then
    4 * tileNo d + match d.site with
      | .statsW 0 | .sW _ => 0
      | .ld _ c => c.val
      | .ldW _ c => c.val + 1
      | .lSt | .gen 2 => 0
      | _ => 4
  else 0

/-- Probability stores in the current item. -/
def stPos (d : D) : Nat :=
  if d.site.tile0 || d.site.inTrip || d.site = .lSt || d.site = .gen 2 then
    4 * tileNo d + match d.site with
      | .pst _ c => c.val
      | .pwait _ 0 | .pArr _ => 3
      | .pwait _ 1 | .warpBar _ | .el _ | .p2Arr _ | .statsW 1 | .statsW 2 => 4
      | _ => 0
  else 0

/-- `tcgen05.wait::st` in the current item. -/
def waitPos (d : D) : Nat :=
  if d.site.tile0 || d.site.inTrip || d.site = .lSt || d.site = .gen 2 then
    2 * tileNo d + match d.site with
      | .pArr _ | .pst _ 3 | .pwait _ 1 => 1
      | .warpBar _ | .el _ | .p2Arr _ | .statsW 1 | .statsW 2 => 2
      | _ => 0
  else 0

/-- Implicit `tcgen05.wait::ld` in the current item. -/
def wlPos (d : D) : Nat :=
  if d.site.tile0 || d.site.inTrip || d.site = .lSt || d.site = .gen 2 then
    4 * tileNo d + match d.site with
      | .statsW 0 | .sW _ => 0
      | .ld _ c => c.val
      | .ldW _ c => c.val
      | .lSt | .gen 2 => 0
      | _ => 4
  else 0

/-- Warp-collective `tcgen05` events (loads, their waits, stores, `wait::st`) in the current
item: fourteen per tile. -/
def tcPos (d : D) : Nat := ldPos d + wlPos d + stPos d + waitPos d

/-- Whether the site follows a loop trip's store of `α`. -/
def Site.afterAlpha : Site → Bool
  | .gen 1 | .pst true _ | .pwait true _ | .pArr true | .warpBar true | .el true | .p2Arr true
  | .statsW 2 | .gen 2 => true
  | _ => false

/-- Writes of the statistics word in the current item. -/
def wrPos (d : D) : Nat :=
  if d.site.inTrip || d.site = .lSt || d.site = .gen 2 then
    d.t + (if d.site.afterAlpha then 1 else 0)
  else 0

/-- Whether the site follows the tile's warp barrier. -/
def Site.afterWB : Site → Bool
  | .el _ | .p2Arr _ | .statsW 1 | .statsW 2 => true
  | _ => false

/-- Warp barriers in the current item. -/
def wbPos (d : D) : Nat :=
  if d.site.tile0 || d.site.inTrip || d.site = .lSt || d.site = .gen 2 then
    tileNo d + (if d.site.afterWB then 1 else 0)
  else 0

/-- An election. -/
def isElectE (e : Event) : Bool :=
  match e.kind with
  | .elect .. => true
  | _ => false

/-- Whether the site follows the tile's election. -/
def Site.afterEl : Site → Bool
  | .p2Arr _ | .statsW 1 | .statsW 2 => true
  | _ => false

/-- Elections in the current item. -/
def elPos (d : D) : Nat :=
  if d.site.tile0 || d.site.inTrip || d.site = .lSt || d.site = .gen 2 then
    tileNo d + (if d.site.afterEl then 1 else 0)
  else 0

/-- The start barrier is passed after `bar0`, the end barrier at the exit. -/
def bar2Sync (d : D) : Nat :=
  match d.site with
  | .setMaxReg | .bar0 => 0
  | _ => 1

def bar2Arrive (d : D) : Nat :=
  match d.site with
  | .exit => 1
  | _ => 0

/-- The statistics polls after the items (the tail's). -/
def tailPos (d : D) : Nat :=
  match d.site with
  | .barEnd | .exit => 1
  | _ => 0

/-- The poll sites. -/
def Site.isPoll : Site → Bool
  | .statsW _ | .sW _ => true
  | _ => false

/-- Whether the site follows the trip's S-full poll (inside a loop trip). -/
def Site.afterS1 : Site → Bool
  | .sW true => false
  | s => s.inTrip

/-- The successful polls at poll site `s` before the state's event (its rounds): one poll of
`statsW 0`, `statsW 1` and `sW false` per item, one of `statsW 2` and `sW true` per loop trip,
one of `statsW 3` at the tail. -/
def roundOf (L : Launch) (d : D) : Site → Nat
  | .statsW 0 => d.i + (if d.site.inItem && d.site != .statsW 0 then 1 else 0)
  | .statsW 1 => d.i + (if d.site.inItem && !d.site.tile0 then 1 else 0)
  | .statsW 2 => (trips L - 1) * d.i +
      (if d.site.inTrip || d.site == .lSt || d.site == .gen 2 then d.t else 0)
  | .statsW 3 => tailPos d
  | .sW false => d.i +
      (if d.site.inItem && d.site != .statsW 0 && d.site != .sW false then 1 else 0)
  | .sW true => (trips L - 1) * d.i +
      (if d.site.inTrip || d.site == .lSt || d.site == .gen 2 then
        d.t + (if d.site.afterS1 then 1 else 0) else 0)
  | _ => 0

/-- The 32-column chunks of the current tile the thread has loaded before the site's event. -/
def chunks (d : D) : Nat :=
  match d.site with
  | .ld _ c => c.val
  | .ldW _ c => c.val + 1
  | .alphaSt | .gen 0 | .gen 1 | .pst _ _ | .pwait _ _ | .pArr _ | .warpBar _ | .el _
  | .p2Arr _ | .statsW 1 | .statsW 2 => 4
  | _ => 0

/-- The sites of the first tile after its row maximum, where the words are the selected
halves. -/
def Site.halved : Site → Bool
  | .gen 0 | .pst false _ | .pwait false _ | .pArr false | .warpBar false | .el false
  | .p2Arr false | .statsW 1 => true
  | _ => false

/-- The `o`-th load of the stage's score columns among `es`, of chunk `c`, returned `vals`. -/
def LoadOrd (L : Launch) (g : Nat) (es : List Event) (o c : Nat) (vals : List Value) : Prop :=
  ∃ k pc, es[k]? = some ⟨pc, .tc (.ld (tmem L g (32 * c)) vals .s32x32b)⟩ ∧
    (es.take k).countP (tcLdAt (tmem L g 0) (tmem L g 128)) = o

/-! ### The invariant -/

/-- The run invariant of a softmax thread with trace prefix `es` before the event of state
`d`. -/
structure Counts (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop where
  stats : okPolls (ownLoc L g (240 + 8 * stOf L g)) es =
    (trips L + 1) * d.i + (if d.site.inItem then statsPos d else tailPos d)
  score : okPolls (ownLoc L g (128 + 8 * stOf L g)) es = trips L * d.i + sPos d
  pReady : arrivals (leadLoc L g (144 + 8 * stOf L g)) es = trips L * d.i + pPos d
  pReady2 : ElectLead L g es →
    arrivals (leadLoc L g (160 + 8 * stOf L g)) es = trips L * d.i + p2Pos d
  pReady2Non : ElectNonLead L g es → arrivals (leadLoc L g (160 + 8 * stOf L g)) es = 0
  gen : barEvents (kOf L g + 3 + 4 * stOf L g) 64 .arrive es = (trips L + 1) * d.i + genPos d
  bar2 : barEvents 2 416 .sync es = bar2Sync d ∧ barEvents 2 416 .arrive es = bar2Arrive d
  tcLd : tcLdsIn (tmem L g 0) (tmem L g 128) es = 4 * trips L * d.i + ldPos d
  tcSt : tcStsIn (tmem L g 64) (tmem L g 128) es = 4 * trips L * d.i + stPos d
  waitSt : tcWaitSts es = 2 * trips L * d.i + waitPos d
  word : writesAt (statsWord L g) es = trips L * d.i + wrPos d
  /-- At the elected lane's arrival the trace's last election returned this lane. -/
  lead : ∀ lp, d.site = .p2Arr lp → ¬ ElectNonLead L g es
  /-- The warp barriers: one per tile. -/
  warpBar : es.countP Execution.isWarpBar = trips L * d.i + wbPos d
  /-- The elections: one per tile, after its warp barrier; a thread of warp 0 also made the
  prologue's fourteen. -/
  elects : es.countP isElectE = (if warpOf L g = 0 then 14 else 0) + trips L * d.i + elPos d
  /-- The warp-collective `tcgen05` events: fourteen per tile. -/
  tcColl : es.countP isTcColl = 14 * trips L * d.i + tcPos d
  /-- The rounds of each poll site. -/
  rounds : ∀ s : Site, s.isPoll = true → es.countP (okPollAt s.pc) = roundOf L d s
  /-- The words: the loaded chunks of the current tile are the values the loads of the tile
  returned (`R`), as loaded or, after the first tile's row maximum, their selected halves. -/
  words : ∃ R : Nat → Value,
    (∀ c < chunks d, ∀ j < 32, ∃ vals,
      LoadOrd L g es (4 * (trips L * d.i + tileNo d) + c) c vals ∧
      R (32 * c + j) = vals.getD j (b32 0)) ∧
    ∀ k < 32 * chunks d, d.w k = if d.site.halved then half R k else R k
  /-- The reference maximum and the row sum: when every load returned single-precision
  numbers (and the scale word reads as a number), after the first tile's row maximum the reference
  is the tile's (`refM`), and in a loop trip `t` (and at the item's end) the reference and the row
  sum are those after tile `n i + t`. -/
  refs : LoadsF32 es → ScaleOk L →
    (d.site.halved = true →
      d.m = .float .f32 (refM (sc L) (trips L) (tsc L g es) (trips L * d.i))) ∧
    (d.site.inTrip = true ∨ d.site = .lSt ∨ d.site = .gen 2 →
      d.m = .float .f32 (refM (sc L) (trips L) (tsc L g es) (trips L * d.i + d.t)) ∧
      d.l = .float .f32 (rowL (sc L) (trips L) (tsc L g es) (trips L * d.i + d.t)))

/-- The case analysis of a counting step: every site, its event's shape (`hev`) and the
successor (`hn`), with the successor state substituted. -/
syntax "soft_cases" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| soft_cases) => `(tactic| (
      rcases site with _ | _ | w | lp | ⟨lp, c⟩ | ⟨lp, c⟩ | _ | j | ⟨lp, c⟩ | ⟨lp, c⟩ | lp |
        lp | lp | lp | _ | _ | _
      all_goals (try rcases fin4_cases w with rfl | rfl | rfl | rfl)
      all_goals (try rcases fin3_cases j with rfl | rfl | rfl)
      all_goals (try rcases fin4_cases c with rfl | rfl | rfl | rfl)
      all_goals (try rcases fin2_cases c with rfl | rfl)
      all_goals (try cases lp)
      all_goals simp only [Ev] at hev
      all_goals repeat' (first | (obtain rfl := hev) | (obtain ⟨_, hev⟩ := hev))
      all_goals simp only [next, nextItem, afterStats, afterLoad] at hn
      all_goals repeat' (first | split_ifs at hn | split at hn)
      all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
      all_goals (try simp only [Bool.not_eq_true] at *)
      all_goals (try subst hn)
      all_goals subst_vars))

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
