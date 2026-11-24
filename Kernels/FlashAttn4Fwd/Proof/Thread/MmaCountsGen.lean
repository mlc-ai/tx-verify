-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaCounts
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # One step of a count formula

A count formula `cnt L A m k` (`(m n + k) i + A site + m t`, the last term in or after the
loop) moves by one exactly at the sites `ev` names, along every step of the site machine, when
a finite check over the sites holds (`check`, decided by evaluation): on a step that keeps
the item and the trip, `A` moves by the event; on the step to the next loop trip, `A` drops
`m`; on the step to the next item, `A` drops `m + k`. The trip facts of `Inv` (`TripOk`) turn
these into the formula's step (`cnt_next`). Steps an invariant does not follow (an election
that skips the elected lane's part) are left out by `valid`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- Every site. -/
def allSites : List Site :=
  [.setMaxReg, .alloc, .allocWrite, .bar0, .ldBase, .shflQ, .relinquish, .bar1, .arrivePeer,
    .waitDealloc, .dealloc, .exit] ++ (List.finRange 2).map .qWait ++
    (List.finRange 4).map .kvWait ++ (List.finRange 4).map .pWait ++
    (List.finRange 4).flatMap (fun k => [.p2Wait k false, .p2Wait k true]) ++
    (List.finRange 14).map .shfl ++ (List.finRange 8).map .elM ++
    (List.finRange 8).flatMap (fun b => (List.finRange 8).map (.mma b)) ++
    (List.finRange 12).map .elC ++ (List.finRange 12).map .commit

theorem mem_allSites (s : Site) : s ∈ allSites := by
  cases s <;> simp [allSites]
  case p2Wait k ld => cases ld <;> simp

/-- The check of one step from site `s` with outcome `x` and branch `y`. -/
def checkOne (A : Site → Nat) (m k : Nat) (ev valid : Site → Bool → Bool) (s : Site)
    (x y : Bool) : Bool :=
  !valid s x ||
    let r := sStep s x y
    let e := if ev s x then 1 else 0
    match r.2 with
    | .keep => A r.1 == A s + e && (r.1.loop == s.loop || region s == 1)
    | .trip => A r.1 + m == A s + e && s.loop == 1 && r.1.loop == 1
    | .item => A r.1 + m + k == A s + e && s.loop == 1 && region s == 3 && r.1.loop == 0
    | .reset => A r.1 == A s + e && r.1.loop == 0 && s.loop == 0 && s.phase == 0

/-- The check of every step. -/
def check (A : Site → Nat) (m k : Nat) (ev valid : Site → Bool → Bool) : Bool :=
  allSites.all fun s => [false, true].all fun x => [false, true].all fun y =>
    checkOne A m k ev valid s x y

theorem checkOne_of {A : Site → Nat} {m k : Nat} {ev valid : Site → Bool → Bool}
    (hc : check A m k ev valid = true) (s : Site) (x y : Bool) :
    checkOne A m k ev valid s x y = true := by
  simp only [check, List.all_eq_true] at hc
  exact hc s (mem_allSites s) x (by cases x <;> simp) y (by cases y <;> simp)

/-- A count formula moves by the event along a step, under its check. -/
theorem cnt_next {L : Launch} {g : Nat} {d d' : D} {e : Event} {A : Site → Nat} {m k : Nat}
    {ev valid : Site → Bool → Bool} (hc : check A m k ev valid = true)
    (hi : Inv L g d) (hpre : d.site.phase = 0 → d.i = 0)
    (hn : next L g d e = some (some d')) (hv : valid d.site (outcome L g e) = true) :
    cnt L A m k d' = cnt L A m k d + if ev d.site (outcome L g e) then 1 else 0 := by
  obtain ⟨hs, hit⟩ := next_eq hn
  have h1 := checkOne_of hc d.site (outcome L g e) (cond L g d)
  have htr := hi.trip
  simp only [checkOne, hv, Bool.not_true, Bool.false_or] at h1
  unfold TripOk at htr
  unfold cnt
  rw [hs]
  generalize sStep d.site (outcome L g e) (cond L g d) = r at h1 hit
  generalize (if ev d.site (outcome L g e) = true then 1 else 0) = ee at h1 ⊢
  obtain ⟨s', u⟩ := r
  obtain ⟨site, i, t, base, pro⟩ := d
  obtain ⟨site', i', t', base', pro'⟩ := d'
  simp only at hit hpre htr ⊢
  cases u <;> simp only [Upd.apply, Prod.mk.injEq] at hit <;> obtain ⟨rfl, rfl⟩ := hit <;>
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h1
  · obtain ⟨hA, hl | hr⟩ := h1
    · rw [hl]; omega
    · rw [hr] at htr; simp only at htr; subst htr; simp; omega
  · obtain ⟨⟨hA, hl⟩, hl'⟩ := h1
    rw [hl, hl']; simp only [Nat.mul_one, Nat.mul_add]; omega
  · obtain ⟨⟨⟨hA, hl⟩, hr⟩, hl'⟩ := h1
    rw [hr] at htr; simp only at htr
    rw [hl, hl', ← htr]
    simp only [Nat.mul_zero, Nat.mul_add, Nat.add_mul, Nat.mul_succ]
    omega
  · obtain ⟨⟨⟨hA, hl'⟩, hl⟩, hp⟩ := h1
    rw [hpre hp, hl, hl']; simp; omega

/-! ### Counts of the loop trips

A count with one event per loop trip and none outside the loop has `n - 1` events per item:
`cntL L A d = (n - 1) i + A site + t` (the last term in or after the loop). Its step check is
`check`'s with the item step keeping `A` (the item's `n - 1` events are the `t = n - 1` done
trips). -/

def checkLOne (A : Site → Nat) (ev valid : Site → Bool → Bool) (s : Site) (x y : Bool) : Bool :=
  !valid s x ||
    let r := sStep s x y
    let e := if ev s x then 1 else 0
    match r.2 with
    | .keep => A r.1 == A s + e && (r.1.loop == s.loop || region s == 1)
    | .trip => A r.1 + 1 == A s + e && s.loop == 1 && r.1.loop == 1
    | .item => A r.1 == A s + e && s.loop == 1 && region s == 3 && r.1.loop == 0
    | .reset => A r.1 == A s + e && r.1.loop == 0 && s.loop == 0 && s.phase == 0

def checkL (A : Site → Nat) (ev valid : Site → Bool → Bool) : Bool :=
  allSites.all fun s => [false, true].all fun x => [false, true].all fun y =>
    checkLOne A ev valid s x y

/-- A count of loop trips moves by the event along a step, under its check. -/
theorem cntL_next {L : Launch} {g : Nat} {d d' : D} {e : Event} {A : Site → Nat}
    {ev valid : Site → Bool → Bool} (hc : checkL A ev valid = true)
    (hi : Inv L g d) (hpre : d.site.phase = 0 → d.i = 0)
    (hn : next L g d e = some (some d')) (hv : valid d.site (outcome L g e) = true) :
    cntL L A d' = cntL L A d + if ev d.site (outcome L g e) then 1 else 0 := by
  obtain ⟨hs, hit⟩ := next_eq hn
  have h1 : checkLOne A ev valid d.site (outcome L g e) (cond L g d) = true := by
    simp only [checkL, List.all_eq_true] at hc
    exact hc _ (mem_allSites _) _ (by cases outcome L g e <;> simp) _
      (by cases cond L g d <;> simp)
  have htr := hi.trip
  simp only [checkLOne, hv, Bool.not_true, Bool.false_or] at h1
  unfold TripOk at htr
  unfold cntL
  rw [hs]
  generalize sStep d.site (outcome L g e) (cond L g d) = r at h1 hit
  generalize (if ev d.site (outcome L g e) = true then 1 else 0) = ee at h1 ⊢
  obtain ⟨s', u⟩ := r
  obtain ⟨site, i, t, base, pro⟩ := d
  obtain ⟨site', i', t', base', pro'⟩ := d'
  simp only at hit hpre htr ⊢
  cases u <;> simp only [Upd.apply, Prod.mk.injEq] at hit <;> obtain ⟨rfl, rfl⟩ := hit <;>
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h1
  · obtain ⟨hA, hl | hr⟩ := h1
    · rw [hl]; omega
    · rw [hr] at htr; simp only at htr; subst htr; simp; omega
  · obtain ⟨⟨hA, hl⟩, hl'⟩ := h1
    rw [hl, hl']; simp only [Nat.mul_one]; omega
  · obtain ⟨⟨⟨hA, hl⟩, hr⟩, hl'⟩ := h1
    rw [hr] at htr; simp only at htr
    rw [hl, hl']
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.mul_add]
    omega
  · obtain ⟨⟨⟨hA, hl'⟩, hl⟩, hp⟩ := h1
    rw [hpre hp, hl, hl']; simp; omega

/-! ### The sites of each count -/

/-- Every step is followed. -/
def allValid (_ : Site) (_ : Bool) : Bool := true

/-- The steps of the elected lane: an election that returned the lane, and none of the
other lanes' polls inside a PV block. -/
def leadValid (s : Site) (x : Bool) : Bool :=
  match s with
  | .elM _ | .elC _ => x
  | .p2Wait _ false => false
  | _ => true

/-- A successful poll at a site of the given kind. -/
def qEv (k : Fin 2) (s : Site) (x : Bool) : Bool :=
  x && match s with
  | .qWait k' => decide (k' = k)
  | _ => false

def kvEv (s : Site) (x : Bool) : Bool :=
  x && match s with
  | .kvWait _ => true
  | _ => false

def pEv (k : Fin 2) (s : Site) (x : Bool) : Bool :=
  x && match s with
  | .pWait k' => decide (k'.val % 2 = k.val)
  | _ => false

def p2Ev (k : Fin 2) (s : Site) (x : Bool) : Bool :=
  x && match s with
  | .p2Wait k' _ => decide (k'.val % 2 = k.val)
  | _ => false

def deallocEv (s : Site) (x : Bool) : Bool := x && decide (s = .waitDealloc)

def handoffEv (s : Site) (_ : Bool) : Bool := decide (s = .arrivePeer)

/-- The class of commit `c`'s barrier: S-full 0/1, KV-empty, Q-empty 0/1, O-full 0/1. -/
def cKind : Fin 12 → Nat
  | 0 | 3 => 0 | 1 | 5 => 1 | 2 | 4 | 6 | 11 => 2 | 7 => 3 | 8 => 4 | 9 => 5 | 10 => 6

/-- A commit of the given class. -/
def cEv (j : Nat) (s : Site) (_ : Bool) : Bool :=
  match s with
  | .commit c => decide (cKind c = j)
  | _ => false

def mmaEv (s : Site) (_ : Bool) : Bool := s.isMma

theorem check_q : ∀ k : Fin 2, check (qA k) 0 1 (qEv k) allValid = true := by decide +kernel
theorem check_kv : check kvA 2 0 kvEv allValid = true := by decide +kernel
theorem check_p : ∀ k : Fin 2, check (pA k) 1 0 (pEv k) allValid = true := by decide +kernel
theorem check_p2 : ∀ k : Fin 2, check (p2A k) 1 0 (p2Ev k) allValid = true := by
  decide +kernel
theorem check_dealloc : check deallocA 0 0 deallocEv allValid = true := by decide +kernel
theorem check_handoff : check handoffA 0 0 handoffEv allValid = true := by decide +kernel
theorem check_s : ∀ k : Fin 2, check (sA k) 1 0 (cEv k.val) leadValid = true := by
  decide +kernel
theorem check_rel : check relA 2 0 (cEv 2) leadValid = true := by decide +kernel
theorem check_qe : ∀ k : Fin 2, check (qeA k) 0 1 (cEv (3 + k.val)) leadValid = true := by
  decide +kernel
theorem check_of : ∀ k : Fin 2, check (ofA k) 0 1 (cEv (5 + k.val)) leadValid = true := by
  decide +kernel
theorem check_mma : check mmaA 32 0 mmaEv leadValid = true := by decide +kernel

/-- The paired Tensor Memory operations, the events on barrier 2 and the commits. -/
def tmemEv (s : Site) (_ : Bool) : Bool :=
  decide (s = .alloc) || decide (s = .relinquish) || decide (s = .dealloc)

def bar2Ev (s : Site) (_ : Bool) : Bool := decide (s = .bar0) || decide (s = .bar1)

def comEv (s : Site) (_ : Bool) : Bool :=
  match s with
  | .commit _ => true
  | _ => false

theorem check_tmem : check tmemA 0 0 tmemEv allValid = true := by decide +kernel
theorem check_bar2 : check bar2A 0 0 bar2Ev allValid = true := by decide +kernel
theorem check_com : check comA 4 4 comEv leadValid = true := by decide +kernel

/-- A successful poll at the position of poll site `s0`. -/
def pollEv (s0 s : Site) (x : Bool) : Bool := x && s.isPoll && decide (s.pc = s0.pc)

/-- A count formula without per-item or per-trip terms is its site term. -/
theorem cnt_zero (L : Launch) (A : Site → Nat) (d : D) : cnt L A 0 0 d = A d.site := by
  simp [cnt]

/-! ### Site facts along the steps -/

def Site.isElect : Site → Bool
  | .elM _ | .elC _ => true
  | _ => false

def Site.p2Other : Site → Bool
  | .p2Wait _ false => true
  | _ => false

/-- The elections. -/
theorem check_elect : check elA 8 4 (fun s _ => s.isElect) allValid = true := by decide +kernel

/-- The sites before the item loop are entered only from such sites, keeping the item. -/
theorem check_pre : allSites.all (fun s => [false, true].all fun x => [false, true].all fun y =>
    (sStep s x y).1.phase != 0 || (s.phase == 0 && (sStep s x y).2 == .keep)) = true := by
  decide +kernel

/-- The elected lane's steps reach no other lane's poll. -/
theorem check_lead : allSites.all (fun s => [false, true].all fun x => [false, true].all fun y =>
    !leadValid s x || !(sStep s x y).1.p2Other) = true := by
  decide +kernel

/-- The other lanes' steps reach no elected lane's site. -/
theorem check_nonLead : allSites.all (fun s => [false, true].all fun x =>
    [false, true].all fun y => s.lead || (s.isElect && x) || !(sStep s x y).1.lead) = true := by
  decide +kernel

/-- The end is entered only from the end, from the start when the leader CTA has no item, or
from the last commit when the cluster has no next item. -/
theorem check_done : allSites.all (fun s => [false, true].all fun x => [false, true].all fun y =>
    (sStep s x y).1.phase != 2 || (s.phase == 2 && (sStep s x y).2 == .keep) ||
      (!y && ((decide (s = .shflQ) && (sStep s x y).2 == .reset) ||
        ((decide (s = .elC 11) || decide (s = .commit 11)) && (sStep s x y).2 == .item)))) =
    true := by
  decide +kernel

/-- The warp's start is passed in order: the address store only from the allocation of lane 0,
`bar.sync 2` from the store or from the allocation of another lane, past the read-back only from
it. -/
theorem check_start : allSites.all (fun s => [false, true].all fun x =>
    [false, true].all fun y =>
      (!decide ((sStep s x y).1 = .allocWrite) || (decide (s = .alloc) && y)) &&
      (!decide (3 ≤ (sStep s x y).1.start) || decide (3 ≤ s.start) ||
        decide (s = .allocWrite) || (decide (s = .alloc) && !y)) &&
      (!decide (5 ≤ (sStep s x y).1.start) || decide (5 ≤ s.start) || decide (s = .ldBase))) =
    true := by
  decide +kernel

/-- A commit site is entered only from its election, by the elected lane. -/
theorem check_commitElect : allSites.all (fun s => [false, true].all fun x =>
    [false, true].all fun y => (List.finRange 12).all fun c =>
      !decide ((sStep s x y).1 = .commit c) || (decide (s = .elC c) && x)) = true := by
  decide +kernel

theorem check_pollsLoop : allSites.all (fun s0 => !(s0.isPoll && region s0 == 2) ||
    checkL (fun s => s.inTrip s0.ord) (pollEv s0) allValid) = true := by
  decide +kernel

theorem check_pollsItem : allSites.all (fun s0 =>
    !(s0.isPoll && region s0 != 2 && !decide (s0 = .waitDealloc)) ||
    check (fun s => s.after s0.ord) 0 1 (pollEv s0) allValid) = true := by
  decide +kernel

theorem check_pollsDealloc : check deallocA 0 0 (pollEv .waitDealloc) allValid = true := by
  decide +kernel

theorem all_of {p : Site → Bool → Bool → Bool}
    (h : allSites.all (fun s => [false, true].all fun x => [false, true].all fun y => p s x y) =
      true) (s : Site) (x y : Bool) : p s x y = true := by
  simp only [List.all_eq_true] at h
  exact h s (mem_allSites s) x (by cases x <;> simp) y (by cases y <;> simp)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
