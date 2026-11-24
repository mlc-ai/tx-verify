-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedWarpQuiet

@[expose] public section

/-! # The loader warp's warp collectives (`WarpRoleSched` of warp 14)

A thread of warp 14 makes the prologue's four shuffles, then the loader's: one rank broadcast at
each item's head (`Loader.shfls`) and the elections of its sites (`Loader.Counts.elects`), none
of them a warp barrier or a ballot (`loader_noWV`). So its warp collectives before a state are
`collL` (`loader_count`).

The schedule `loadS` is the prologue's shuffle times, then an item table (`tabL`): the head's
broadcast and the elections of the head's four uses in slot 0, the elections of a trip's K and V
uses in the trip's slot, at the loader's offsets (`Time.loader`). On the leader CTA every use
starts with the arrival's election (`r0 = 1`); on the other only the copies elect. After the
items: the tail's election at `+14` on the leader CTA, then times past the exit.

A state of an item is at the schedule's time when it is an election or the head, and earlier
otherwise (`loader_item`, from the per-site check `check_sites`). Every time of the schedule is
even, and so is every loader time but the polls', the arrivals' and the copies' (offset odd), at
which the machine never stops (`loader_tight`); hence the strict clause of a stopped machine. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### Warp collectives: shuffles, elections, warp barriers and ballots -/

/-- A warp barrier or a ballot. -/
def isWV (e : Event) : Bool :=
  match e.kind with
  | .warpBar .. | .vote .. => true
  | _ => false

/-- The warp collectives are the shuffles, the elections, the warp barriers and the ballots. -/
theorem warpColl_split (l : List Event) :
    l.countP Sched.isWarpColl =
      l.countP Execution.isShfl + l.countP Loader.isElectE + l.countP isWV := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [List.countP_cons, ih]
    obtain ⟨pc, k⟩ := e
    cases k <;> simp [Sched.isWarpColl, Execution.isShfl, Loader.isElectE, isWV] <;> omega

theorem isWV_warp {e : Event} (h : isWV e = true) : Sched.isWarpColl e = true := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp_all [isWV, Sched.isWarpColl]

theorem prologue_isWV {e : Event} (h : Prologue.ProKind e.kind) : isWV e = false := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp_all [isWV, Prologue.ProKind]

/-- The prologue's election count is the loader's. -/
theorem elects_pro (l : List Event) :
    l.countP Loader.isElectE = l.countP (fun x => Prologue.isElect x.kind) :=
  List.countP_congr fun x _ => by
    obtain ⟨pc, k⟩ := x
    cases k <;> simp [Loader.isElectE, Prologue.isElect]

/-! ### The count -/

/-- The elections before a state of warp 14. -/
def elCntL (L : Launch) (g : Nat) : ThreadD → Nat
  | .inl p => p.site.elects (warpOf L g)
  | .inr (.loader l) => Loader.electOf L g l
  | _ => 0

/-- The warp collectives before a state of warp 14. -/
def collL (L : Launch) (g : Nat) (d : ThreadD) : Nat := shflCnt L g d + elCntL L g d

/-! ### The schedule -/

/-- One on an even CTA (the leader of its pair). -/
def r0c (c : Nat) : Nat := if c % 2 = 0 then 1 else 0

theorem r0c_eq (L : Launch) (g : Nat) : r0c (ctaOf L g) = Loader.r0 L g := rfl

theorem r0_cases (L : Launch) (g : Nat) : Loader.r0 L g = 0 ∨ Loader.r0 L g = 1 := by
  unfold Loader.r0; split_ifs <;> simp

/-- The loader's item table: on the leader CTA (`r0 = 1`) each use's arrival election `+2`
before its copy elections `+4`, `+6`; the head's broadcast at `0`; bands of 16. -/
def tabL : Nat → Sched.ItemTab
  | 1 => ⟨[0, 2, 4, 6, 18, 20, 22, 34, 36, 38, 50, 52], [2, 4, 6, 18, 20], []⟩
  | _ => ⟨[0, 4, 6, 20, 22, 36, 38, 52], [4, 6, 20], []⟩

/-- The prologue's four shuffles. -/
def fixL : List Nat := [0, 2, 4, prologue .shfl3]

/-- The tail: the leader's election at `+14`, then past the exit at `+18`. -/
def tailL (r0 j : Nat) : Nat := if r0 = 1 ∧ j = 0 then 14 else 20 + 2 * j

/-- The warp collectives' schedule of warp 14. -/
def loadS (L : Launch) (c : Nat × Nat) (k : Nat) : Nat :=
  (tabL (r0c c.1)).sched slotTime fixL (tailL (r0c c.1)) (Work.n L) (Tc L c.1) (Tc L c.1) k

theorem tabL_ok (r0 : Nat) : (tabL r0).Ok span := by
  unfold tabL Sched.ItemTab.Ok; split <;> decide

theorem tabL_even (r0 : Nat) : Sched.ItemTab.EvenOk (tabL r0).pre = true ∧
    Sched.ItemTab.EvenOk (tabL r0).trip = true ∧ Sched.ItemTab.EvenOk (tabL r0).post = true := by
  unfold tabL; split <;> decide

theorem tailL_gap (r0 j : Nat) : tailL r0 j + 1 < tailL r0 (j + 1) := by
  unfold tailL
  by_cases h1 : j = 0 <;> by_cases h2 : r0 = 1 <;> simp [h1, h2] <;> omega

theorem loadS_gap (hpre : Pre P L mem0) (c : Nat × Nat) (k : Nat) :
    loadS L c k + 1 < loadS L c (k + 1) := by
  have hn : 1 ≤ Work.n L := by
    have := skOf_eq hpre; have := hpre.skPos
    unfold Work.n Work.sk; omega
  exact Sched.ItemTab.sched_gap slotClock (tabL_ok _) (by decide) (tailL_gap _) hn le_rfl k

theorem loadS_even (c : Nat × Nat) (k : Nat) : loadS L c k % 2 = 0 := by
  obtain ⟨h1, h2, h3⟩ := tabL_even (r0c c.1)
  exact Sched.ItemTab.sched_even slotClock (by decide) h1 h2 h3
    (fun j => by unfold tailL; by_cases h : r0c c.1 = 1 ∧ j = 0 <;> simp [h]) k

theorem tabL_len (L : Launch) (g : Nat) (n : Nat) (hn : n = Work.n L) :
    (tabL (Loader.r0 L g)).len n = 1 + Loader.itemElects L g := by
  subst hn
  unfold Loader.itemElects
  rcases r0_cases L g with h | h <;> rw [h] <;> simp [tabL, Sched.ItemTab.len] <;> ring

/-! ### The sites of an item -/

/-- The region of an item site: the head and the head's uses (1), a trip's uses (2). -/
def regionL : Loader.Site → Nat
  | .head => 1
  | .wait u | .elA u | .arrive u | .elC u _ | .copy u _ => if u.trip then 2 else 1
  | _ => 0

/-- The collectives of the region before use `u`. -/
def uOff (r0 : Nat) : Loader.UseK → Nat
  | .k0 => 1 | .q0 => r0 + 3 | .q1 => 2 * r0 + 5 | .v0 => 3 * r0 + 7 | .k => 0 | .v => r0 + 2

/-- The collectives of the region before an item site. -/
def idxL (r0 : Nat) : Loader.Site → Nat
  | .head => 0
  | .wait u | .elA u => uOff r0 u
  | .arrive u => uOff r0 u + 1
  | .elC u j => uOff r0 u + r0 + j.val
  | .copy u j => uOff r0 u + r0 + j.val + 1
  | _ => 0

/-- The offset of an item site in its slot (`Time.loader`). -/
def offL : Loader.Site → Nat
  | .head => 0
  | .wait u => 16 * loaderBand u + 1
  | .elA u => 16 * loaderBand u + 2
  | .arrive u => 16 * loaderBand u + 3
  | .elC u j => 16 * loaderBand u + 4 + 2 * j.val
  | .copy u j => 16 * loaderBand u + 5 + 2 * j.val
  | _ => 0

/-- The item sites. -/
def itemSitesL : List Loader.Site :=
  .head :: [Loader.UseK.k0, .q0, .q1, .v0, .k, .v].flatMap fun u =>
    [.wait u, .elA u, .arrive u, .elC u 0, .elC u 1, .copy u 0, .copy u 1]

/-- The sites a thread with `r0` visits: the arrivals on the leader CTA, the copies a use has. -/
def validL (r0 : Nat) (s : Loader.Site) : Bool :=
  (!s.leadOnly || r0 == 1) &&
    match s with
    | .elC u j | .copy u j => decide (j.val < u.copies)
    | _ => true

/-- The check of an item site against the item table. -/
def siteOkL (r0 : Nat) (s : Loader.Site) : Bool :=
  let l := (tabL r0).rlist (regionL s)
  let a := idxL r0 s
  if loaderKind s == .warp then decide (a < l.length) && l.getD a 0 == offL s
  else (decide (a < l.length) && decide (offL s < l.getD a 0)) || a == l.length

theorem check_sites : ∀ r0 ∈ [0, 1], itemSitesL.all (fun s => !validL r0 s || siteOkL r0 s) := by
  decide

theorem siteOkL_spec {r0 : Nat} {s : Loader.Site} (h : siteOkL r0 s = true) :
    (loaderKind s = .warp → idxL r0 s < ((tabL r0).rlist (regionL s)).length ∧
      ((tabL r0).rlist (regionL s)).getD (idxL r0 s) 0 = offL s) ∧
    (loaderKind s ≠ .warp →
      (idxL r0 s < ((tabL r0).rlist (regionL s)).length ∧
        offL s < ((tabL r0).rlist (regionL s)).getD (idxL r0 s) 0) ∨
      idxL r0 s = ((tabL r0).rlist (regionL s)).length) := by
  unfold siteOkL at h
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · simp only [hk] at h; simpa using h
  · have : (loaderKind s == .warp) = false := by
      cases h' : loaderKind s <;> simp_all
    simp only [this] at h; simpa using h

theorem loaderBand_le (u : Loader.UseK) : loaderBand u ≤ 3 := by cases u <;> decide

theorem offL_lt (s : Loader.Site) : offL s < 64 := by
  cases s <;> simp only [offL] <;> (try have := loaderBand_le ‹Loader.UseK›) <;>
    (try have := (‹Fin 2›).isLt) <;> omega

variable {g : Nat} {l : Loader.D}

/-- The time of an item site. -/
theorem time_itemL {n T : Nat} (hit : l.site.inItem = true) :
    loader n T l = slotTime n l.i (Sched.ItemTab.rslot n l.t (regionL l.site)) (offL l.site) := by
  obtain ⟨s, i, t, a, b, c⟩ := l
  cases s <;> simp only [Loader.Site.inItem, Bool.false_eq_true] at hit
  all_goals (try (rename_i u _; cases u))
  all_goals (try (rename_i u; cases u))
  all_goals simp [loader, loaderUse, loaderSlot, loaderBand, regionL, offL, Sched.ItemTab.rslot,
    Loader.UseK.trip]
  all_goals congr 1; omega

/-- The count of an item site. -/
theorem coll_itemL (hit : l.site.inItem = true) :
    collL L g (.inr (.loader l)) = fixL.length + ((tabL (Loader.r0 L g)).len (Work.n L) * l.i +
      (Sched.ItemTab.rbase (tabL (Loader.r0 L g)) (Work.n L) l.t (regionL l.site) +
        idxL (Loader.r0 L g) l.site)) := by
  rw [tabL_len L g _ rfl]
  obtain ⟨s, i, t, a, b, c⟩ := l
  unfold collL elCntL shflCnt
  rcases r0_cases L g with h | h
  all_goals cases s <;> simp only [Loader.Site.inItem, Bool.false_eq_true] at hit
  all_goals (try (rename_i u _; cases u))
  all_goals (try (rename_i u; cases u))
  all_goals simp only [Loader.shfls, Loader.electOf, Loader.preElects, idxL, uOff, regionL,
    Loader.UseK.trip, Sched.ItemTab.rbase, h, tabL, fixL, List.length_cons, List.length_nil,
    Loader.itemElects]
  all_goals simp
  all_goals ring

/-- **An item site of the loader against the schedule.** -/
theorem loader_item (hn : 1 ≤ Work.n L) (hi : Loader.Inv L g l) (hit : l.site.inItem = true) :
    (loaderKind l.site = .warp →
      loader (Work.n L) (Work.T L g) l = loadS L (warpKey L g) (collL L g (.inr (.loader l)))) ∧
    (loaderKind l.site ≠ .warp →
      loader (Work.n L) (Work.T L g) l < loadS L (warpKey L g) (collL L g (.inr (.loader l)))) := by
  have hiT : l.i < Work.T L g := hi.item hit
  have hmem : l.site ∈ itemSitesL := by
    obtain ⟨s, i, t, a, b, c⟩ := l
    cases s <;> simp only [Loader.Site.inItem, Bool.false_eq_true] at hit
    all_goals (try (rename_i u j; cases u <;> fin_cases j))
    all_goals (try (rename_i u; cases u))
    all_goals simp [itemSitesL]
  have hval : validL (Loader.r0 L g) l.site = true := by
    have hl := hi.lead
    have h1 := hi.one
    obtain ⟨s, i, t, a, b, c⟩ := l
    simp only at hl h1
    cases s <;> simp only [Loader.Site.inItem, Bool.false_eq_true] at hit
    all_goals simp only [validL, Loader.Site.leadOnly, Bool.not_true, Bool.false_or,
      Bool.not_false, Bool.true_or, Bool.true_and, Bool.and_true]
    all_goals (try simp [Loader.r0, hl rfl])
    all_goals (try (rename_i u j; simpa using h1 u j (.inl rfl)))
    all_goals (try (rename_i u j; simpa using h1 u j (.inr rfl)))
  have hchk : siteOkL (Loader.r0 L g) l.site = true := by
    have h := check_sites (Loader.r0 L g) (by rcases r0_cases L g with h | h <;> simp [h])
    rw [List.all_eq_true] at h
    simpa [hval] using h _ hmem
  have hreg : Sched.ItemTab.RegOk (Work.n L) l.t (regionL l.site) := by
    have htr := hi.trip
    obtain ⟨s, i, t, a, b, c⟩ := l
    simp only at htr ⊢
    cases s <;> simp only [Loader.Site.inItem, Bool.false_eq_true] at hit
    all_goals (try (rename_i u _; cases u))
    all_goals (try (rename_i u; cases u))
    all_goals simp [regionL, Loader.UseK.trip, Sched.ItemTab.RegOk, Loader.Site.inTrip] at htr ⊢
    all_goals omega
  have ho : offL l.site < span := (offL_lt _).trans (by decide)
  obtain ⟨hw, hnw⟩ := siteOkL_spec hchk
  unfold loadS
  rw [show (warpKey L g).1 = ctaOf L g from rfl, r0c_eq, coll_itemL hit, time_itemL hit]
  have hT : Tc L (ctaOf L g) = Work.T L g := rfl
  rw [hT]
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · obtain ⟨ha, hget⟩ := hw hk
    rw [Sched.ItemTab.sched_reg hreg hiT ha, hget]
  · exact Sched.ItemTab.lt_sched_reg slotClock hn hreg hiT le_rfl ho (hnw hk)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
