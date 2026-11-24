-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingCommitEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingPrelude
public import Lemmas.Flow.TraceInduction
public import Lemmas.Flow.Polls

@[expose] public section

/-! # The MMA role's poll and commit ordinals -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1MmaGemmTrace

open PTX PTX.Flow
open Wg1Mma (D)

/-- The two inputs acquired by the MMA issuer and the two completion streams it issues. -/
inductive Stream where
  | dequant
  | qk
  | score
  | pv
  deriving DecidableEq

def Stream.base : Stream → Nat
  | .dequant => 222792
  | .qk => 222904
  | .score => 222920
  | .pv => 222936

def Stream.loc (s : Stream) (L : Launch) (g : Nat) (slot : Fin 2) : Loc :=
  ⟨.shared, ctaOf L g, L.sharedBase + (s.base + 8 * slot.val)⟩

/-- The event counted at this stream for the corresponding slot. -/
def Stream.tick (s : Stream) (L : Launch) (g : Nat) (slot : Fin 2) (e : Event) : Bool :=
  match s with
  | .dequant | .score => okPoll (s.loc L g slot) e
  | .qk | .pv => commitsTo (s.loc L g slot) e

private def uses (slot : Fin 2) (blocks : Nat) : Nat := (blocks + (1 - slot.val)) / 2

private theorem uses_succ (slot : Fin 2) (blocks : Nat) :
    uses slot (blocks + 1) = uses slot blocks + if blocks % 2 = slot.val then 1 else 0 := by
  have := slot.isLt
  unfold uses
  split <;> omega

private theorem uses_here {slot : Fin 2} {block : Nat} (h : block % 2 = slot.val) :
    uses slot block = block / 2 := by
  have := slot.isLt
  unfold uses
  omega

def completed (s : Stream) (site : Wg1Mma.Site) : Bool :=
  match s, site with
  | .dequant, .kvFence | .dequant, .qkMma _ | .dequant, .qkCommit | .dequant, .soWait
  | .dequant, .soFence | .dequant, .pvMma _ | .dequant, .pvCommit
  | .qk, .soWait | .qk, .soFence | .qk, .pvMma _ | .qk, .pvCommit
  | .score, .soFence | .score, .pvMma _ | .score, .pvCommit => true
  | _, _ => false

private def expected (s : Stream) (slot : Fin 2) (d : D) : Nat :=
  uses slot d.i + if d.i % 2 = slot.val ∧ completed s d.site then 1 else 0

private def updates (s : Stream) (site : Wg1Mma.Site) (k : Kind) : Bool :=
  match k with
  | .wait _ _ ok _ _ =>
    (decide (s = .dequant ∧ site = .kvWait ∨ s = .score ∧ site = .soWait) && ok)
  | .tc (.commit _) => decide (s = .qk ∧ site = .qkCommit ∨ s = .pv ∧ site = .pvCommit)
  | _ => false

private theorem loc_eq_iff {s : Stream} {L : Launch} {g off : Nat} {slot : Fin 2} :
    (⟨.shared, g / L.block, L.sharedBase + off⟩ : Loc) = s.loc L g slot ↔
      off = s.base + 8 * slot.val := by
  constructor
  · intro same
    exact Nat.add_left_cancel (congrArg Loc.addr same)
  · intro same
    simp [Stream.loc, ctaOf, same]

private theorem loc_eq_iff' {s : Stream} {L : Launch} {g off : Nat} {slot : Fin 2} :
    (⟨.shared, ctaOf L g, L.sharedBase + off⟩ : Loc) = s.loc L g slot ↔
      off = s.base + 8 * slot.val :=
  loc_eq_iff

private theorem no_update {site : Wg1Mma.Site}
    (hd : site ≠ .kvWait ∧ site ≠ .soWait ∧ site ≠ .qkCommit ∧ site ≠ .pvCommit)
    (s : Stream) (k : Kind) : updates s site k = false := by
  cases k <;> try rfl
  case wait => simp [updates, hd.1, hd.2.1]
  case tc k =>
    cases k <;> try rfl
    simp [updates, hd.2.2.1, hd.2.2.2]

set_option linter.unusedSimpArgs false in
private theorem tick_at_mma {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {slot : Fin 2}
    {d : D} {e : Event} {o : Option TState} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hf : (Machine.machine P L g).Fired (some (.mma d)) e o) (s : Stream) :
    s.tick L g slot e = (decide (d.i % 2 = slot.val) && updates s d.site e.kind) := by
  have hb := slot.isLt
  cases hk : e.kind <;> try (cases s <;> simp [Stream.tick, okPoll, sourceWaitSuccess,
    commitsTo, updates, hk] <;> done)
  case wait m p ok acq sc =>
    have hd := RingSourceSites.poll_site hf hk
    obtain ⟨ok', h⟩ := RingEvents.mma_wait_exact hpre hd hf
    have hOk := (Kind.wait.inj (hk.symm.trans h)).2.2.1
    subst ok'
    rcases hd with hd | hd | hd | hd
    · simp [hd] at h
      cases s <;> cases ok <;> simp [Stream.tick, okPoll, sourceWaitSuccess, commitsTo,
        updates, h, hk, hd, loc_eq_iff, Stream.base]
      all_goals omega
    · simp [hd] at h
      cases s <;> cases ok <;> simp [Stream.tick, okPoll, sourceWaitSuccess, commitsTo,
        updates, h, hk, hd, loc_eq_iff, Stream.base]
      all_goals omega
    · simp [hd] at h
      cases s <;> cases ok <;> simp [Stream.tick, okPoll, sourceWaitSuccess, commitsTo,
        updates, h, hk, hd, loc_eq_iff, Stream.base]
      all_goals omega
    · simp [hd] at h
      cases s <;> cases ok <;> simp [Stream.tick, okPoll, sourceWaitSuccess, commitsTo,
        updates, h, hk, hd, loc_eq_iff, Stream.base]
      all_goals omega
  case tc k =>
    cases k <;> try (cases s <;> simp [Stream.tick, okPoll, sourceWaitSuccess,
      commitsTo, updates, hk] <;> done)
    case commit sp =>
      have hd := RingCommitEvents.commit_site hf hk
      obtain ⟨sp', he, hm, _⟩ := RingCommitEvents.commit_issue hpre hg hd hf
      obtain rfl := TcKind.commit.inj (Kind.tc.inj (hk.symm.trans he))
      rcases hd with hd | hd | hd
      · simp [hd] at hm
        cases s <;> simp [Stream.tick, okPoll, sourceWaitSuccess, commitsTo,
          updates, hk, hd, hm, loc_eq_iff', Stream.base]
        all_goals omega
      · simp [hd] at hm
        cases s <;> simp [Stream.tick, okPoll, sourceWaitSuccess, commitsTo,
          updates, hk, hd, hm, loc_eq_iff', Stream.base]
        all_goals omega
      · simp [hd] at hm
        cases s <;> simp [Stream.tick, okPoll, sourceWaitSuccess, commitsTo,
          updates, hk, hd, hm, loc_eq_iff', Stream.base]
        all_goals omega

set_option linter.unusedSimpArgs false in
private theorem expected_step {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {slot : Fin 2} {d d' : D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hg : g < L.threads)
    (hf : (Machine.machine P L g).Fired (some (.mma d)) e o)
    (hn : Wg1Mma.next P L g d e = some (some d')) (s : Stream) :
    expected s slot d' = expected s slot d + if s.tick L g slot e then 1 else 0 := by
  rw [tick_at_mma hpre hg hf]
  cases hd : d.site <;> simp only [Wg1Mma.next, hd, Wg1Mma.nextSite,
    Wg1Mma.startSite, Wg1Mma.afterTopk] at hn
  case kvWait =>
    cases hk : e.kind <;> simp only [hk, reduceCtorEq] at hn
    rename_i m p ok acq sc
    cases ok <;> cases hn <;> cases s <;> simp [expected, completed, updates, hd]
  case soWait =>
    cases hk : e.kind <;> simp only [hk, reduceCtorEq] at hn
    rename_i m p ok acq sc
    cases ok <;> cases hn <;> cases s <;> simp [expected, completed, updates, hd]
  case qkCommit =>
    obtain ⟨sp, he, _, _⟩ := RingCommitEvents.commit_issue hpre hg (.inr (.inl hd)) hf
    cases hn
    cases s <;> simp [expected, completed, updates, hd, he]
  case pvCommit =>
    obtain ⟨sp, he, _, _⟩ := RingCommitEvents.commit_issue hpre hg (.inr (.inr hd)) hf
    split at hn <;> cases hn <;> cases s <;>
      simp [expected, completed, updates, hd, he, uses_succ]
  all_goals
    repeat' split at hn
    all_goals try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    all_goals cases hn
    all_goals rw [no_update (by simp [hd])]
    all_goals cases s <;> simp [expected, completed, hd]

private def prefixCounts (L : Launch) (g : Nat) (slot : Fin 2) (s : Stream)
    (d : Option Machine.ThreadD) (es : List Event) : Prop :=
  match d with
  | some (.prologue _) | some .head => es.countP (s.tick L g slot) = 0
  | some (.mma d) => es.countP (s.tick L g slot) = expected s slot d
  | _ => True

private theorem entry_no_tick {P : Params} {L : Launch} {g : Nat} {slot : Fin 2}
    {d : Machine.ThreadD} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some d) e o)
    (hd : d = .head ∨ ∃ st, d = .prologue st) (s : Stream) : s.tick L g slot e = false := by
  have hn : ∀ m, okPoll m e = false := by
    intro m
    rcases hd with rfl | ⟨st, rfl⟩
    · exact (RingPrelude.head_no_counts hf m m).2
    · exact (RingPrelude.prologue_no_counts hf m m).2
  have hc : ∀ (sp : TcCommit.Spec), e.kind ≠ .tc (.commit sp) := by
    intro sp he
    have hsite := RingCommitEvents.commit_site hf he
    rcases hd with rfl | ⟨st, rfl⟩
    all_goals exact hsite.elim
  cases s <;> simp only [Stream.tick, hn]
  all_goals
    cases hk : e.kind <;> simp only [commitsTo, hk]
    rename_i tk
    cases tk <;> simp only
    exact (hc _ hk).elim

private theorem prefix_step {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {slot : Fin 2} {d d' : Option Machine.ThreadD} {e : Event} {es : List Event}
    {o : Option TState} (hpre : Pre P L mem0) (hg : g < L.threads) {s : Stream}
    (h : prefixCounts L g slot s d es)
    (hf : (Machine.machine P L g).Fired d e o)
    (hn : (Machine.machine P L g).next d e = some d') :
    prefixCounts L g slot s d' (es ++ [e]) := by
  cases d
  case none =>
    change some none = some d' at hn
    cases hn
    trivial
  case some d =>
    change Machine.next P L g d e = some d' at hn
    cases d
    case prologue st =>
      have hz : (es ++ [e]).countP (s.tick L g slot) = 0 := by
        change es.countP _ = 0 at h
        simp [List.countP_append, h, entry_no_tick hf (.inr ⟨st, rfl⟩) s]
      have handoff (w : Fin 3)
          (hh : some (if wgOf L g = w.val then some (Machine.roleStart P L g w) else none) =
            some d') : prefixCounts L g slot s d' (es ++ [e]) := by
        split at hh
        · fin_cases w <;> cases hh <;> first | exact hz | trivial
        · cases hh
          trivial
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        exact hz
      · split at hn
        · exact handoff _ hn
        · cases hn
          trivial
      · cases hn
    case head =>
      have hz : (es ++ [e]).countP (s.tick L g slot) = 0 := by
        change es.countP _ = 0 at h
        simp [List.countP_append, h, entry_no_tick hf (.inl rfl) s]
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn <;> try trivial
      change _ = expected s slot ⟨.elect, 0⟩
      rw [hz]
      have := slot.isLt
      cases s <;> simp [expected, completed, uses] <;> omega
    case mma d =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i d' he
        cases hn
        change _ = expected s slot d'
        change _ = expected s slot d at h
        rw [expected_step hpre hg hf he s]
        simp [List.countP_append, h]
      · split_ifs at hn <;> cases hn <;> trivial
      · split_ifs at hn
        all_goals cases hn
        all_goals trivial
    all_goals
      simp only [Machine.next] at hn
      all_goals repeat' split at hn
      all_goals cases hn
      all_goals trivial

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
include hpre

/-- The prefix of a tracked MMA state counts exactly its earlier uses of each stream. -/
private theorem composed_count (hg : g < L.threads) (slot : Fin 2) (s : Stream) {es : List Event}
    {i : Nat} {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hd : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.mma d))) :
    (es.take i).countP (s.tick L g slot) =
      uses slot d.i + if d.i % 2 = slot.val ∧ completed s d.site then 1 else 0 :=
  ht.prefix_induction (prefixCounts L g slot s) rfl (fun _ _ _ _ _ => prefix_step hpre hg)
    i (some (.mma d)) hd

/-- In the current slot the stream ordinal is the generation plus the current site's status. -/
theorem composed_count_here (hg : g < L.threads) (s : Stream) {slot : Fin 2} {es : List Event}
    {i : Nat} {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hd : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.mma d))) (hb : d.i % 2 = slot.val) :
    (es.take i).countP (s.tick L g slot) = d.i / 2 + if completed s d.site then 1 else 0 := by
  rw [composed_count hpre hg slot s ht hd, uses_here hb]
  simp [hb]

/-- At any QK issue, the MMA lane has acquired every earlier probability publication. -/
theorem score_polls_before_qk (hg : g < L.threads) (slot : Fin 2) {es : List Event} {i : Nat}
    {d : D} {k : Fin 16} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hd : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.mma d))) (hsite : d.site = .qkMma k) :
    (es.take i).countP ((.score : Stream).tick L g slot) = (d.i + (1 - slot.val)) / 2 := by
  rw [composed_count hpre hg slot .score ht hd]
  simp [uses, completed, hsite]

/-- A slot's QK commits count earlier blocks and the current block once it has committed. -/
theorem qk_commits_of_state (hg : g < L.threads) (slot : Fin 2) {es : List Event} {i : Nat} {d : D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hd : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.mma d))) :
    (es.take i).countP ((.qk : Stream).tick L g slot) = (d.i + (1 - slot.val)) / 2 +
      if d.i % 2 = slot.val ∧ completed .qk d.site then 1 else 0 :=
  composed_count hpre hg slot .qk ht hd

/-- The current block follows the PV commits of all earlier blocks on either slot. -/
theorem pv_commits_before_block (hg : g < L.threads) (slot : Fin 2) {es : List Event} {i : Nat}
    {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hd : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.mma d))) :
    (es.take i).countP ((.pv : Stream).tick L g slot) = (d.i + (1 - slot.val)) / 2 := by
  rw [composed_count hpre hg slot .pv ht hd]
  simp [uses, completed]

/-- The MMA lane has already issued one slot-one PV commit per earlier odd-numbered block. -/
theorem slot_one_pv_commits_before_block (hg : g < L.threads) {es : List Event} {i : Nat} {d : D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hd : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.mma d))) :
    (es.take i).countP ((.pv : Stream).tick L g 1) = d.i / 2 := by
  rw [composed_count hpre hg 1 .pv ht hd]
  simp [uses, completed]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1MmaGemmTrace
