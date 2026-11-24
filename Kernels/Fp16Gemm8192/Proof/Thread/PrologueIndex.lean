-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface
public import Kernels.Fp16Gemm8192.Proof.Thread.Warp
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderDiscipline
public import Lemmas.Flow.TraceInduction
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The index of each prologue event along a thread's run

The prologue is a fixed path through the sites of `Prologue.lean`, one event per site. Along a
thread's run, `Prologue.index L g p` is the number of events before the prologue state `p`: the
shuffle is event 0 and, for warp 0, the election is event 1. Thread 0 (`first`) then performs the
eighteen barrier initializations (events 2 to 19) and, in warp 0, the Tensor Memory allocation;
lane 0 writes the returned column at the next event. Every thread then fences, arrives on and
waits at the cluster barrier; the warps 8 to 11 then lower their register count at index
`fenceIdx` plus four.

`stateAt_prologue` places each prologue state of the run at its index. `init_event` names the
mbarrier that each initialization of thread 0 fires. `cluster_before_role` says that a role state
is reached after the cluster arrive and wait. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000


namespace Prologue

/-- The index of the fence site: thread 0 fences after its initializations and warp 0's
allocation (`first`), the other threads of warp 0 after the election, and the other warps
directly after the shuffle. -/
def fenceIdx (L : Launch) (g w : Nat) : Nat :=
  if w = 0 then (if first L g then 23 else 4) else 1

/-- The number of events the thread performs before the prologue state `p` on its path. -/
def index (L : Launch) (g : Nat) (p : D) : Nat :=
  match p.site with
  | .shfl => 0
  | .elect => 1
  | .init i => 2 + i.val
  | .alloc => if first L g then 20 else 2
  | .allocWrite => if first L g then 21 else 3
  | .warpBar => if first L g then 22 else 3
  | .fence => fenceIdx L g p.w
  | .fenceInit => fenceIdx L g p.w + 1
  | .arrive => fenceIdx L g p.w + 2
  | .wait => fenceIdx L g p.w + 3
  | .setMaxReg => fenceIdx L g p.w + 4
  | .roleElect => fenceIdx L g p.w + 5

/-- The facts of a prologue state that hold along a run: the sites of warp 0 after the election
carry `w = 0`, the barrier initializations and the Tensor Memory write occur only in thread 0
(`first`), only warps 8 to 11 reach the register reallocation, and only warp 11 the role
election. -/
def Canon (L : Launch) (g : Nat) (p : D) : Prop :=
  (p.site = .elect ∨ p.site = .alloc ∨ p.site = .warpBar → p.w = 0) ∧
    (∀ i, p.site = .init i → first L g = true) ∧ (p.site = .allocWrite → first L g = true) ∧
    (p.site = .setMaxReg → p.w / 4 = 2) ∧ (p.site = .roleElect → p.w = 11)

/-- The shared offset of the mbarrier that initialization `i` initializes. -/
def initOff (i : Fin 18) : Nat :=
  match i.val with
  | 0 => 8 | 1 => 16 | 2 => 24 | 3 => 32 | 4 => 40 | 5 => 48 | 6 => 56 | 7 => 64 | 8 => 72
  | 9 => 80 | 10 => 88 | 11 => 96 | 12 => 104 | 13 => 112 | 14 => 120 | 15 => 128
  | 16 => 160 | _ => 168

/-- The arrival count initialization `i` gives its mbarrier. -/
def initCount (i : Fin 18) : Nat :=
  match i.val with
  | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | 8 => 1 | 9 => 1
  | 10 => 256 | 11 => 256 | 12 => 1 | 13 => 1 | 14 => 1 | 15 => 10 | 16 => 1 | _ => 1

/-- The register that holds the mbarrier address of initialization `i`. -/
def initBase (i : Fin 18) : Nat :=
  match i.val with
  | 0 => 65 | 1 => 67 | 2 => 68 | 3 => 69 | 4 => 70 | 5 => 72
  | 6 => 73 | 7 => 74 | 8 => 75 | 9 => 76 | 10 => 77 | 11 => 79
  | 12 => 80 | 13 => 81 | 14 => 82 | 15 => 83 | 16 => 85 | _ => 86

/-- The register that holds the arrival count of initialization `i`. -/
def initReg (i : Fin 18) : Nat :=
  match i.val with
  | 0 => 66 | 1 => 66 | 2 => 66 | 3 => 66 | 4 => 71 | 5 => 71
  | 6 => 71 | 7 => 71 | 8 => 66 | 9 => 66 | 10 => 78 | 11 => 78
  | 12 => 66 | 13 => 66 | 14 => 66 | 15 => 84 | 16 => 66 | _ => 66

/-- The mbarrier that initialization `i` of thread `g` initializes: in the thread's CTA. -/
def initLoc (L : Launch) (g : Nat) (i : Fin 18) : Loc :=
  ⟨.shared, g / L.block, L.sharedBase + initOff i⟩

theorem first_iff (L : Launch) (g : Nat) : first L g = true ↔ g % L.block = 0 := by
  simp [first]

theorem warpOf_of_first {L : Launch} {g : Nat} (hf : first L g = true) : warpOf L g = 0 := by
  rw [first_iff] at hf
  simp [warpOf, hf]

theorem laneOf_of_first {L : Launch} {g : Nat} (hf : first L g = true) : laneOf L g = 0 := by
  rw [first_iff] at hf
  simp [laneOf, hf]

theorem first_of_warp_lane {L : Launch} {g : Nat} (hw : warpOf L g = 0)
    (hl : laneOf L g = 0) : first L g = true := by
  rw [first_iff]
  simp only [warpOf, laneOf] at hw hl
  generalize g % L.block = m at hw hl ⊢
  omega

theorem first_false_of_warp {L : Launch} {g : Nat} (hw : warpOf L g ≠ 0) :
    first L g = false := by
  cases h : first L g
  · rfl
  · exact absurd (warpOf_of_first h) hw

theorem fenceIdx_pos (L : Launch) (g w : Nat) : 1 ≤ fenceIdx L g w := by
  unfold fenceIdx
  split_ifs <;> omega

theorem site_ne_shfl {L : Launch} {g : Nat} {p : D} (h : 1 ≤ index L g p) :
    p.site ≠ .shfl := by
  intro hs
  simp [index, hs] at h

/-- Warp 0's Tensor Memory allocation: lane 0 goes on to its address store, the other lanes go
to the warp barrier. -/
theorem alloc_cases {L : Launch} {g w : Nat} {e : Event} {q : D}
    (hn : next L g ⟨.alloc, w⟩ e = some (some (.inl q))) :
    (laneOf L g = 0 ∧ q = ⟨.allocWrite, w⟩) ∨
      (laneOf L g ≠ 0 ∧ q = ⟨.warpBar, w⟩) := by
  simp only [next] at hn
  split at hn
  · split_ifs at hn with hl
    · left
      simp only [Option.some.injEq, Sum.inl.injEq] at hn
      exact ⟨hl, hn.symm⟩
    · right
      simp only [Option.some.injEq, Sum.inl.injEq] at hn
      exact ⟨hl, hn.symm⟩
  · simp at hn

/-- Warp 11's election never continues to a prologue state. -/
theorem roleElect_not_inl {L : Launch} {g w : Nat} {e : Event} {q : D}
    (hn : next L g ⟨.roleElect, w⟩ e = some (some (.inl q))) : False := by
  simp only [next] at hn
  split at hn
  all_goals (try split_ifs at hn)
  all_goals simp at hn

set_option maxHeartbeats 4000000 in
/-- The transitions along the path: a prologue state with the thread's warp index and canonical
facts continues to the state at the next index, with the same warp index. -/
theorem trans_of_next {L : Launch} {g : Nat} {p p' : D} {e : Event}
    (hw : p.w = warpOf L g) (hc : Canon L g p) (hs : p.site ≠ .shfl)
    (hn : next L g p e = some (some (.inl p'))) :
    index L g p' = index L g p + 1 ∧ p'.w = p.w ∧ Canon L g p' := by
  obtain ⟨s, w⟩ := p
  obtain ⟨hA, hB, hC, -, -⟩ := hc
  cases s with
  | shfl => exact (hs rfl).elim
  | elect =>
    simp only [next, Option.some.injEq, Sum.inl.injEq] at hn
    subst hn
    have hw0 : w = 0 := hA (Or.inl rfl)
    subst hw0
    cases hf : first L g <;> simp [index, Canon, afterElect, afterInits, hf]
  | init i =>
    simp only [next] at hn
    have hf : first L g = true := hB i rfl
    have hw0 : w = 0 := hw.trans (warpOf_of_first hf)
    subst hw0
    split at hn
    · simp only [Option.some.injEq, Sum.inl.injEq] at hn
      subst hn
      refine ⟨by simp only [index]; omega, rfl, ?_, fun _ _ => hf, ?_, ?_, ?_⟩
      all_goals (intro h1; simp at h1)
    · simp only [Option.some.injEq, Sum.inl.injEq] at hn
      subst hn
      have hi : i.val = 17 := by
        have := i.isLt
        omega
      refine ⟨by simp [index, afterInits, hf, hi], rfl, fun _ => rfl, fun _ _ => hf, ?_, ?_, ?_⟩
      all_goals (intro h1; simp [afterInits] at h1)
  | alloc =>
    have hw0 : w = 0 := hA (Or.inr (Or.inl rfl))
    subst hw0
    rcases alloc_cases hn with ⟨hl, rfl⟩ | ⟨hl, rfl⟩
    · have hf : first L g = true := first_of_warp_lane (by rw [← hw]) hl
      refine ⟨by simp [index, hf], rfl, ?_⟩
      simp [Canon, hf]
    · cases hf : first L g
      · refine ⟨by simp [index, hf], rfl, ?_⟩
        simp [Canon]
      · exact absurd (laneOf_of_first hf) hl
  | allocWrite =>
    simp only [next, Option.some.injEq, Sum.inl.injEq] at hn
    subst hn
    have hf : first L g = true := hC rfl
    refine ⟨by simp [index, hf], rfl, ?_⟩
    exact ⟨fun _ => hw.trans (warpOf_of_first hf), fun j h1 => by simp at h1, fun _ => hf,
      fun h1 => by simp at h1, fun h1 => by simp at h1⟩
  | warpBar =>
    simp only [next, Option.some.injEq, Sum.inl.injEq] at hn
    subst hn
    have hw0 : w = 0 := hA (Or.inr (Or.inr rfl))
    subst hw0
    refine ⟨?_, rfl, ?_⟩
    · cases hf : first L g <;> simp [index, fenceIdx, hf]
    · simp [Canon]
  | fence | fenceInit | arrive =>
    simp only [next, Option.some.injEq, Sum.inl.injEq] at hn
    subst hn
    refine ⟨by simp only [index], rfl, ?_⟩
    simp [Canon]
  | wait =>
    simp only [next] at hn
    split at hn
    · rename_i hw2
      simp only [Option.some.injEq, Sum.inl.injEq] at hn
      subst hn
      refine ⟨by simp only [index], rfl, ?_⟩
      simp [Canon, hw2]
    · split at hn <;> simp at hn
  | setMaxReg =>
    simp only [next] at hn
    split_ifs at hn with h11
    · simp only [Option.some.injEq, Sum.inl.injEq] at hn
      subst hn
      refine ⟨by simp only [index], rfl, ?_⟩
      simp [Canon, h11]
    all_goals simp at hn
  | roleElect => exact (roleElect_not_inl hn).elim

/-- A prologue state that continues to a role is the cluster wait or a later state. -/
theorem wait_le_of_role {L : Launch} {g : Nat} {p : D} {e : Event} {r : Role}
    (hn : next L g p e = some (some (.inr r))) :
    index L g ⟨.wait, p.w⟩ ≤ index L g p := by
  obtain ⟨s, w⟩ := p
  cases s
  case wait => exact le_rfl
  case setMaxReg => simp only [index]; omega
  case roleElect => simp only [index]; omega
  all_goals
    simp only [next] at hn
    repeat' split at hn
    all_goals simp_all

end Prologue

open Prologue

/-- The state before the shuffle, the first event of every thread. -/
theorem stateAt_zero (L : Launch) (X : Execution) (g : Nat) :
    Frame.stateAt (code L) X g 0 = some (some (.inl ⟨.shfl, 0⟩)) := rfl

/-- A prologue state's successor, when the state before is a prologue state. -/
theorem stateAt_succ_inl {L : Launch} {X : Execution} {g k : Nat} {e : Event} {p : Prologue.D}
    (he : (X.tr g)[k]? = some e) (hs : Frame.stateAt (code L) X g k = some (some (.inl p))) :
    Frame.stateAt (code L) X g (k + 1) = Prologue.next L g p e := by
  rw [Frame.stateAt_succ he, hs]
  rfl

/-- A role's successor, mapped into the role states, is never a prologue state. -/
private theorem map_inr_ne {β : Type} {f : β → Prologue.Role} {o : Option (Option β)}
    {q : Prologue.D} (h : Option.map (Option.map (Sum.inr ∘ f)) o = some (some (.inl q))) :
    False := by
  rcases o with _ | _ | b <;> simp at h

/-- A role state's successor is never a prologue state. -/
theorem roleNext_not_inl {L : Launch} {g : Nat} {r : Prologue.Role} {e : Event} {q : Prologue.D}
    (h : (code L g).toMachine.next (some (.inr r)) e = some (some (.inl q))) : False := by
  cases r with
  | loader l => exact map_inr_ne (f := Prologue.Role.loader) (o := Loader.next L g l e) h
  | mma m => exact map_inr_ne (f := Prologue.Role.mma) (o := Mma.next L g m e) h
  | sched s => exact map_inr_ne (f := Prologue.Role.sched) (o := Scheduler.next L g s e) h
  | cons c => exact map_inr_ne (f := Prologue.Role.cons) (o := Consumer.next L g c e) h

set_option maxHeartbeats 4000000 in
/-- The first event of the thread is the shuffle, and the state after it is the election (warp 0)
or the fence (the other warps), with the warp index. -/
theorem stateAt_one {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads)
    (h0 : 0 < (X.tr g).length) :
    Frame.stateAt (code L) X g 1 = some (some (.inl ⟨if Prologue.warpOf L g = 0 then .elect
      else Prologue.afterElect L g (Prologue.warpOf L g), Prologue.warpOf L g⟩)) := by
  obtain ⟨e0, he0⟩ : ∃ e, (X.tr g)[0]? = some e := ⟨_, List.getElem?_eq_getElem h0⟩
  have hfirst := first_event hpre hX hg (show X.get (g, 0) = some e0 from he0)
  have hw12 := Prologue.warpOf_lt hpre g
  have hv : (BitVec.ofNat 64 (Prologue.warpOf L g)).toNat = Prologue.warpOf L g := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have h1 : Frame.stateAt (code L) X g 1 = Prologue.next L g ⟨.shfl, 0⟩ e0 :=
    stateAt_succ_inl he0 (stateAt_zero L X g)
  rw [h1, hfirst]
  simp [Prologue.next, b32, hv, hw12]

/-- What the run of thread `g` looks like before its `k`-th event: a prologue state is at index `k`
(with its canonical facts), and a role state is past the cluster arrive and wait. -/
def OnPath (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  (∀ p, Frame.stateAt (code L) X g k = some (some (.inl p)) →
      k = Prologue.index L g p ∧ (0 < k → p.w = Prologue.warpOf L g) ∧ Prologue.Canon L g p) ∧
  (∀ r, Frame.stateAt (code L) X g k = some (some (.inr r)) →
      Prologue.index L g ⟨.wait, Prologue.warpOf L g⟩ < k)

theorem onPath_zero (L : Launch) (X : Execution) (g : Nat) : OnPath L X g 0 := by
  refine ⟨fun p hp => ?_, fun r hr => ?_⟩
  · rw [stateAt_zero] at hp
    simp only [Option.some.injEq, Sum.inl.injEq] at hp
    subst hp
    refine ⟨rfl, fun h => absurd h (lt_irrefl 0), ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  · rw [stateAt_zero] at hr
    simp at hr

set_option maxHeartbeats 4000000 in
theorem onPath_one {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads)
    (h0 : 0 < (X.tr g).length) : OnPath L X g 1 := by
  refine ⟨fun p hp => ?_, fun r hr => ?_⟩
  · rw [stateAt_one hpre hX hg h0] at hp
    simp only [Option.some.injEq, Sum.inl.injEq] at hp
    subst hp
    by_cases hw : Prologue.warpOf L g = 0
    · simp [hw, Prologue.index, Prologue.Canon]
    · have hF := Prologue.first_false_of_warp hw
      simp [hw, Prologue.afterElect, Prologue.afterInits, hF, Prologue.index,
        Prologue.fenceIdx, Prologue.Canon]
  · rw [stateAt_one hpre hX hg h0] at hr
    simp at hr

set_option maxHeartbeats 4000000 in
theorem onPath_succ {L : Launch} {X : Execution} {g k : Nat} {e : Event}
    (hk : 1 ≤ k) (he : (X.tr g)[k]? = some e) (hO : OnPath L X g k) :
    OnPath L X g (k + 1) := by
  obtain ⟨hP, hR⟩ := hO
  refine ⟨fun p hp => ?_, fun r hr => ?_⟩
  · rw [Frame.stateAt_succ he] at hp
    cases hs : Frame.stateAt (code L) X g k with
    | none => rw [hs] at hp; simp at hp
    | some σ =>
      rw [hs] at hp
      cases σ with
      | none =>
        have h' : (some none : Option (Option ThreadD)) = some (some (.inl p)) := hp
        simp at h'
      | some d =>
        cases d with
        | inl q =>
          obtain ⟨hq, hqw, hqc⟩ := hP q hs
          have hn : Prologue.next L g q e = some (some (.inl p)) := hp
          have hk1 : 1 ≤ Prologue.index L g q := by omega
          have hw : q.w = Prologue.warpOf L g := hqw (by omega)
          obtain ⟨hidx, hwp, hcp⟩ :=
            Prologue.trans_of_next hw hqc (Prologue.site_ne_shfl hk1) hn
          exact ⟨by omega, fun _ => hwp.trans hw, hcp⟩
        | inr r' => exact (roleNext_not_inl hp).elim
  · rw [Frame.stateAt_succ he] at hr
    cases hs : Frame.stateAt (code L) X g k with
    | none => rw [hs] at hr; simp at hr
    | some σ =>
      rw [hs] at hr
      cases σ with
      | none =>
        have h' : (some none : Option (Option ThreadD)) = some (some (.inr r)) := hr
        simp at h'
      | some d =>
        cases d with
        | inl q =>
          obtain ⟨hq, hqw, hqc⟩ := hP q hs
          have hn : Prologue.next L g q e = some (some (.inr r)) := hr
          have hk1 : 1 ≤ Prologue.index L g q := by omega
          have hw : q.w = Prologue.warpOf L g := hqw (by omega)
          have h := Prologue.wait_le_of_role hn
          rw [hw] at h
          omega
        | inr r' =>
          have := hR r' hs
          omega

set_option maxHeartbeats 4000000 in
/-- Along the whole run, the path invariant holds before every event. -/
theorem onPath_all {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads) :
    ∀ k, k ≤ (X.tr g).length → OnPath L X g k := by
  intro k
  induction k with
  | zero => intro _; exact onPath_zero L X g
  | succ k ih =>
    intro hk
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    cases k with
    | zero => exact onPath_one hpre hX hg (by omega)
    | succ j => exact onPath_succ (by omega) he (ih (by omega))

/-- **The prologue's index.** A prologue state of thread `g` before its `k`-th event is at index
`k` (the number of events before it), and after the shuffle its warp index is the thread's. -/
theorem stateAt_prologue {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat} (hg : g < L.threads)
    (hk : k ≤ (X.tr g).length) {p : Prologue.D} (h : Frame.stateAt (code L) X g k =
      some (some (.inl p))) :
    k = Prologue.index L g p ∧ (0 < k → p.w = Prologue.warpOf L g) := by
  obtain ⟨h1, h2, -⟩ := (onPath_all hpre hX hg k hk).1 p h
  exact ⟨h1, h2⟩

set_option maxHeartbeats 4000000 in
/-- The states of a thread whose first events are the shuffle, the election and the
initializations: with `first`, the state before event `2 + j` is initialization `j`. -/
theorem stateAt_init_chain {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads)
    (hf : first L g = true) :
    ∀ j (hj : j < 18), 2 + j < (X.tr g).length →
      Frame.stateAt (code L) X g (2 + j) = some (some (.inl ⟨.init ⟨j, hj⟩, 0⟩)) := by
  have hW : Prologue.warpOf L g = 0 := warpOf_of_first hf
  intro j
  induction j with
  | zero =>
    intro hj hlen
    have h0 : 0 < (X.tr g).length := by omega
    obtain ⟨e1, he1⟩ : ∃ e, (X.tr g)[1]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have s1 : Frame.stateAt (code L) X g 1 = some (some (.inl ⟨.elect, 0⟩)) := by
      rw [stateAt_one hpre hX hg h0, hW]
      simp
    have s2 : Frame.stateAt (code L) X g 2 = some (some (.inl ⟨.init ⟨0, hj⟩, 0⟩)) := by
      show Frame.stateAt (code L) X g (1 + 1) = _
      rw [stateAt_succ_inl he1 s1]
      simp [Prologue.next, Prologue.afterElect, hf]
    exact s2
  | succ j ih =>
    intro hj hlen
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[2 + j]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hprev := ih (by omega) (by omega)
    show Frame.stateAt (code L) X g (2 + j + 1) = _
    rw [stateAt_succ_inl he hprev]
    simp [Prologue.next, hj]

/-- The initializations' offsets and arrival counts fit the bounds of an mbarrier address and
count. -/
theorem initOff_facts : ∀ i : Fin 18,
    initOff i ≤ 168 ∧ initOff i % 8 = 0 ∧ 0 < initCount i ∧ initCount i < 2 ^ 20 := by
  decide

theorem initBase_value (L : Launch) (g : Nat) (i : Fin 18) :
    valueOf L g ⟨.init i, 0⟩ (initBase i) = b32 (L.sharedBase + initOff i) := by
  fin_cases i <;> simp only [initBase, initOff] <;> pro_values

theorem initReg_value (L : Launch) (g : Nat) (i : Fin 18) :
    valueOf L g ⟨.init i, 0⟩ (initReg i) = b32 (initCount i) := by
  fin_cases i <;> simp only [initReg, initCount] <;> pro_values

theorem init_live (i : Fin 18) :
    initBase i ∈ Flow.live (Prologue.Site.init i).pc ∧
      initReg i ∈ Flow.live (Prologue.Site.init i).pc := by
  fin_cases i <;> table_decide

/-- Initialization `i` is the instruction `mbarrier.init [base], reg`. -/
theorem code_init_op (i : Fin 18) :
    kernel.code[(Prologue.Site.init i).pc]? =
      some ⟨none, .mbarInit (initBase i) 0 (.reg (initReg i))⟩ := by
  fin_cases i <;> first
    | exact Flow.code_mbarInit_0 | exact Flow.code_mbarInit_1 | exact Flow.code_mbarInit_2
    | exact Flow.code_mbarInit_3 | exact Flow.code_mbarInit_4 | exact Flow.code_mbarInit_5
    | exact Flow.code_mbarInit_6 | exact Flow.code_mbarInit_7 | exact Flow.code_mbarInit_8
    | exact Flow.code_mbarInit_9 | exact Flow.code_mbarInit_10 | exact Flow.code_mbarInit_11
    | exact Flow.code_mbarInit_12 | exact Flow.code_mbarInit_13 | exact Flow.code_mbarInit_14
    | exact Flow.code_mbarInit_15 | exact Flow.code_mbarInit_16 | exact Flow.code_mbarInit_17

theorem init_regs (L : Launch) (g : Nat) (i : Fin 18) {t : TState}
    (h : Holds t.regs (Prologue.facts L g ⟨.init i, 0⟩)) :
    t.regs (initBase i) = some (b32 (L.sharedBase + initOff i)) ∧
      t.regs (initReg i) = some (b32 (initCount i)) := by
  refine ⟨?_, ?_⟩
  · rw [← initBase_value L g i]
    exact holds_mem h (Flow.mem_factsFrom (init_live i).1)
  · rw [← initReg_value L g i]
    exact holds_mem h (Flow.mem_factsFrom (init_live i).2)

/-- A barrier initialization (`mbarrier.init`) fires the initialization of the mbarrier its
address register names, with the count its count register holds. -/
theorem fires_mbInit_reg {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {base cnt : Nat} {a n pc : Nat} {e : Event} {o : Option TState}
    (hb : t.regs base = some (b32 a)) (ha : a < 2 ^ 32) (ha8 : a % 8 = 0)
    (hc : t.regs cnt = some (b32 n)) (hn : 0 < n) (hn' : n < 2 ^ 20)
    (hf : Fires pc (eventTmpl A L g t (.mbarInit base 0 (.reg cnt))) e o) :
    e = ⟨pc, .mbInit ⟨.shared, g / L.block, a⟩ n⟩ := by
  have hm := mbarLoc_b32 (L := L) (g := g) hb ha ha8
  have hq : readBits L g t 32 (.reg cnt) = .ok (truncBits 32 (BitVec.ofNat 64 n)) := by
    simp [readBits, readReg, hc, b32, bind, Except.bind, pure, Except.pure]
  have hnt : (truncBits 32 (BitVec.ofNat 64 n)).toNat = n := by
    rw [truncBits_ofNat (show n < 2 ^ 32 by omega) (by norm_num), toNat_ofNat_lt (by omega)]
  simp only [eventTmpl, widenMbarScope, tmaTmpl, hm, hq, bind, Except.bind, pure, Except.pure,
    ofExec, hnt, hn, hn', and_self, ↓reduceIte, ite_self] at hf
  exact hf.1

/-- **Initialization events.** On a CTA's thread 0, event `2 + i` is initialization `i`: it
initializes the mbarrier at offset `initOff i` of the CTA's shared memory, with the arrival count
`initCount i`. -/
theorem init_event {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads)
    (hf : g % L.block = 0) (i : Fin 18) {e : Event} (he : X.get (g, 2 + i.val) = some e) :
    e.kind = .mbInit (Prologue.initLoc L g i) (Prologue.initCount i) := by
  have he' : (X.tr g)[2 + i.val]? = some e := he
  have hlen : 2 + i.val < (X.tr g).length := by
    obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp he'
    exact h
  have hs := stateAt_init_chain hpre hX hg ((first_iff L g).2 hf) i.val i.isLt hlen
  obtain ⟨t, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he' hs
  have hc' : kernel.code[(Prologue.Site.init i).pc]? = some ins := hc
  rw [code_init_op i] at hc'
  obtain rfl := Option.some.inj hc'.symm
  obtain ⟨hb, hcnt⟩ := init_regs L g i hat.2.2.2.2
  obtain ⟨hoff, hal, hpos, hlt⟩ := initOff_facts i
  have hbase := hpre.sharedRange
  have halign := hpre.sharedAlignment
  unfold sharedBytes at hbase
  have hmk := fires_mbInit_reg hb (by omega) (by omega) hcnt hpos hlt hfire
  rw [hmk]
  rfl

/-- **The cluster barrier before the role.** A role state is reached after the cluster arrive
and the cluster wait of the thread. -/
theorem cluster_before_role {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat} (hg : g < L.threads)
    (hk : k ≤ (X.tr g).length) {r : Prologue.Role}
    (h : Frame.stateAt (code L) X g k = some (some (.inr r))) :
    Prologue.index L g ⟨.arrive, Prologue.warpOf L g⟩ + 1 < k := by
  have h' := (onPath_all hpre hX hg k hk).2 r h
  simp only [Prologue.index] at h' ⊢
  omega

end
end PTX.Kernels.Fp16Gemm8192.Proof
