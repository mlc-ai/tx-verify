-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Dependency

/-! Completeness checks of DEP-ORDER (`KindNeeds`, `Ready`, `Witness`).

Manual oracles: for each blocking or observing family, `ManualWait.<family>` states the wait
condition of the manual sentence quoted in its comment, without the definitions of
`Core/Assembly/Dependency.lean`. `ready_iff_manual_<family>` proves that `Ready` agrees with it for
the events of the family, and `witness_of_manual_<family>` proves that every event the sentence
names as executed or exited is a `Witness` of the waiting event. A need that is missing, an exit
that is not accepted, or a `Ready` that is `False` breaks one of the two theorems.

Non-vacuity examples: for each blocking kind whose manual condition names another thread, on small
concrete executions, `blocks_<kind>` (the other participant has neither its event nor its exit, and
the event is not ready), `ready_<kind>` (the full instance is present, and the event is ready) and
`witness_other_<kind>` (the other participant's event is a witness), with `witness_exit_<kind>` (the
other participant's exit is a witness) for the kinds whose sentence says "non-exited".

Observing dependency: `spin_shape_A` and `spin_shape_B` check the two canonical spins, `poll_unused`
a poll whose result nobody reads, and the `poll_shape_unsafe_*` kernels the poll uses that are
neither. -/

namespace PTX.Tests.DependencyCoverage

noncomputable section

/-! ## Common facts -/

/-- A need is filled in `X`: a present node with its property, or a condition that holds. -/
def Filled (X : Execution) : Need → Prop
  | .node fills => ∃ x, X.RefPresent x ∧ fills x
  | .cond holds => holds

theorem ready_iff_filled (L : Launch) (X : Execution) (e : EvId) :
    Ready L X e ↔ ∀ n ∈ Needs L X e, Filled X n := by
  unfold Ready
  constructor <;> intro h n hn <;> have := h n hn <;> cases n <;> exact this

theorem ready_get {L : Launch} {X : Execution} {e : EvId} {pc : Nat} {k : Kind}
    (he : X.get e = some ⟨pc, k⟩) : Ready L X e ↔ ∀ n ∈ KindNeeds L X k e, Filled X n := by
  rw [ready_iff_filled]; simp [Needs, he]

theorem witness_get {L : Launch} {X : Execution} {e : EvId} {pc : Nat} {k : Kind}
    (he : X.get e = some ⟨pc, k⟩) (x : AsyncCopy.Ref) :
    Witness L X x e ↔ ∃ fills, Need.node fills ∈ KindNeeds L X k e ∧ X.RefPresent x ∧ fills x := by
  simp [Witness, Needs, he]

theorem refPresent_thread {X : Execution} {y : EvId} :
    X.RefPresent (.thread y) ↔ ∃ ev, X.get y = some ev := Iff.rfl

/-- The lane of lane `l` of the warp of `g` is `l`, when that thread is in the warp of `g`. -/
theorem laneOf_warpLane {L : Launch} {g l : Nat} (hl : l < 32)
    (hw : SameWarp L (warpLane L g l) g) : laneOf L (warpLane L g l) = l := by
  obtain ⟨⟨hg, -, hq⟩, -⟩ := hw
  unfold laneOf
  unfold warpLane laneOf at hq ⊢
  have hB : 0 < L.block := by
    rcases Nat.eq_zero_or_pos L.block with h | h
    · simp [Launch.threads, h] at hg
    · exact h
  have h1 := Nat.div_add_mod g L.block
  have h2 := Nat.div_add_mod (g % L.block) 32
  have h3 := Nat.div_add_mod (g - g % L.block % 32 + l) L.block
  have hs : g % L.block % 32 ≤ g % L.block := Nat.mod_le _ _
  have hr : g % L.block < L.block := Nat.mod_lt _ hB
  rw [hq] at h3
  generalize L.block * (g / L.block) = A at h1 h3
  generalize g % L.block = r at h1 h2 h3 hs hr
  generalize 32 * (r / 32) = C at h2
  have : (g - r % 32 + l) % L.block = C + l := by omega
  rw [this]
  omega

/-! ## Masked warp collectives: shfl.sync, vote.sync, redux.sync, match.sync -/

namespace ManualWait

variable (L : Launch)

/-- The number of instructions of class `c` with member mask `m` that the thread of `y` executed
before `y`. -/
def ord {Q V : Type} (c : Kind → Option (WarpPart Q V)) (X : Execution) (m : Nat) (y : EvId) :
    Nat :=
  ((X.tr y.1).take y.2).countP fun ev => (c ev.kind).any (·.mask == m)

/-- `y` is an execution of an instruction of class `c` with the member mask and the qualifiers of
`p`, the `n`-th such execution with that mask of its thread. -/
def Executed {Q V : Type} (c : Kind → Option (WarpPart Q V)) (X : Execution) (p : WarpPart Q V)
    (n : Nat) (y : EvId) : Prop :=
  ∃ pc k p', X.get y = some ⟨pc, k⟩ ∧ c k = some p' ∧ p'.mask = p.mask ∧ p'.qual = p.qual ∧
    ord c X p.mask y = n

/-- `y` is the exit of a thread that executed fewer than `n + 1` instructions of class `c` with
member mask `m`. -/
def ExitedBefore {Q V : Type} (c : Kind → Option (WarpPart Q V)) (X : Execution) (m n : Nat)
    (y : EvId) : Prop :=
  ∃ pc, X.get y = some ⟨pc, .exit⟩ ∧ ord c X m y ≤ n

/-- The wait of a masked warp collective of class `c`: every lane of the member mask of `e` that
has not exited has executed the instruction with the same qualifiers and the same member mask, as
the execution with the same per-mask ordinal as `e`. -/
def Masked {Q V : Type} (c : Kind → Option (WarpPart Q V)) (X : Execution) (e : EvId) : Prop :=
  ∀ pc k p, X.get e = some ⟨pc, k⟩ → c k = some p →
    ∀ l < 32, p.mask.testBit l → ∃ j,
      Executed c X p (ord c X p.mask e) (warpLane L e.1 l, j) ∨
        ExitedBefore c X p.mask (ord c X p.mask e) (warpLane L e.1 l, j)

/-- §9.7.10.6: "shfl.sync will cause executing thread to wait until all non-exited threads
corresponding to membermask have executed shfl.sync with the same qualifiers and same membermask
value before resuming execution." -/
def shfl (X : Execution) (e : EvId) : Prop := Masked L shflClass X e

/-- §9.7.15.10: "vote.sync will cause executing thread to wait until all non-exited threads
corresponding to membermask have executed vote.sync with the same qualifiers and same membermask
value before resuming execution." -/
def vote (X : Execution) (e : EvId) : Prop := Masked L voteClass X e

/-- §9.7.15.13: "redux.sync will cause the executing thread to wait until all non-exited threads
corresponding to membermask have executed redux.sync with the same qualifiers and same membermask
value before resuming execution." -/
def redux (X : Execution) (e : EvId) : Prop := Masked L reduxClass X e

/-- §9.7.15.11: "match.sync will cause executing thread to wait until all non-exited threads from
membermask have executed match.sync with the same qualifiers and same membermask value before
resuming execution." -/
def match_ (X : Execution) (e : EvId) : Prop := Masked L matchClass X e

end ManualWait

section Masked

variable {L : Launch} {Q V : Type} {c : Kind → Option (WarpPart Q V)} {X : Execution} {e : EvId}
  {pc : Nat} {k : Kind} {p : WarpPart Q V}

theorem maskWait_iff (he : X.get e = some ⟨pc, k⟩) (hc : c k = some p) {l j : Nat} (hl : l < 32)
    (hw : SameWarp L (warpLane L e.1 l) e.1) :
    MaskWait L c X (warpLane L e.1 l, j) e ↔
      ManualWait.Executed c X p (ManualWait.ord c X p.mask e) (warpLane L e.1 l, j) ∨
        (p.mask.testBit l = true ∧
          ManualWait.ExitedBefore c X p.mask (ManualWait.ord c X p.mask e)
            (warpLane L e.1 l, j)) := by
  have hlane := laneOf_warpLane hl hw
  simp only [MaskWait, Execution.MaskAt, Execution.MaskK, Execution.MaskExitK,
    ManualWait.Executed, ManualWait.ExitedBefore, ManualWait.ord, he, hlane]
  constructor
  · rintro ⟨-, m, n, q, ⟨⟨⟨ev, p1, h1, h2, h3⟩, h4⟩, ev', p2, h5, h6, h7⟩, h8⟩
    cases h1; cases h5; simp only [hc, Option.some.injEq] at h2 h6; subst h2 h6 h3 h4 h7
    rcases h8 with ⟨⟨⟨ev, p3, h9, h10, h11⟩, h12⟩, ev', p4, h13, h14, h15⟩ | ⟨h9, ⟨pc', h10⟩, h11⟩
    · rw [h9] at h13; cases h13; rw [h10] at h14; cases h14
      exact .inl ⟨ev.pc, ev.kind, p3, h9, h10, h11, h15, h12⟩
    · exact .inr ⟨h9, pc', h10, h11⟩
  · rintro (⟨pc', k', p', h1, h2, h3, h4, h5⟩ | ⟨h1, pc', h2, h3⟩)
    · exact ⟨hw, p.mask, _, p.qual, ⟨⟨⟨_, p, rfl, hc, rfl⟩, rfl⟩, _, p, rfl, hc, rfl⟩,
        .inl ⟨⟨⟨_, p', h1, h2, h3⟩, h5⟩, _, p', h1, h2, h4⟩⟩
    · exact ⟨hw, p.mask, _, p.qual, ⟨⟨⟨_, p, rfl, hc, rfl⟩, rfl⟩, _, p, rfl, hc, rfl⟩,
        .inr ⟨h1, ⟨pc', h2⟩, h3⟩⟩

theorem ready_iff_masked (he : X.get e = some ⟨pc, k⟩) (hc : c k = some p)
    (hk : KindNeeds L X k e = maskNeeds L c X e)
    (hw : ∀ l < 32, p.mask.testBit l → SameWarp L (warpLane L e.1 l) e.1) :
    Ready L X e ↔ ManualWait.Masked L c X e := by
  rw [ready_get he, hk]
  simp only [maskNeeds, he, Option.bind_some, hc, List.forall_mem_map, List.mem_filter,
    List.mem_range, Filled]
  constructor
  · intro h pc' k' p' he' hc' l hl hm
    rw [he] at he'; cases he'; rw [hc] at hc'; cases hc'
    obtain ⟨x, -, j, rfl, hmw⟩ := h l ⟨hl, hm⟩
    refine ⟨j, ?_⟩
    rcases (maskWait_iff he hc hl (hw l hl hm)).mp hmw with h | ⟨-, h⟩
    · exact .inl h
    · exact .inr h
  · rintro h l ⟨hl, hm⟩
    obtain ⟨j, hj⟩ := h pc k p he hc l hl hm
    refine ⟨.thread (warpLane L e.1 l, j), ?_, j, rfl,
      (maskWait_iff he hc hl (hw l hl hm)).mpr (hj.imp id fun h => ⟨hm, h⟩)⟩
    rcases hj with ⟨pc', k', -, h1, -⟩ | ⟨pc', h1, -⟩
    · exact ⟨_, h1⟩
    · exact ⟨_, h1⟩

theorem witness_of_masked (he : X.get e = some ⟨pc, k⟩) (hc : c k = some p)
    (hk : KindNeeds L X k e = maskNeeds L c X e) {l j : Nat} (hl : l < 32)
    (hm : p.mask.testBit l = true) (hw : SameWarp L (warpLane L e.1 l) e.1)
    (hy : ManualWait.Executed c X p (ManualWait.ord c X p.mask e) (warpLane L e.1 l, j) ∨
      ManualWait.ExitedBefore c X p.mask (ManualWait.ord c X p.mask e) (warpLane L e.1 l, j)) :
    Witness L X (.thread (warpLane L e.1 l, j)) e := by
  rw [witness_get he, hk]
  refine ⟨fun x => ∃ j, x = .thread (warpLane L e.1 l, j) ∧ MaskWait L c X (warpLane L e.1 l, j) e,
    ?_, ?_, j, rfl, (maskWait_iff he hc hl hw).mpr (hy.imp id fun h => ⟨hm, h⟩)⟩
  · simp only [maskNeeds, he, Option.bind_some, hc]
    exact List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨List.mem_range.mpr hl, hm⟩, rfl⟩
  · rcases hy with ⟨pc', k', -, h1, -⟩ | ⟨pc', h1, -⟩
    · exact ⟨_, h1⟩
    · exact ⟨_, h1⟩

end Masked

section MaskedFamilies

variable {L : Launch} {X : Execution} {e : EvId} {pc : Nat}

theorem ready_iff_manual_shfl {mode : ShflMode} {a : Value} {b c : Nat} {recv : Value} {ok : Bool}
    (he : X.get e = some ⟨pc, .shfl mode a b c recv ok⟩)
    (hw : ∀ l < 32, SameWarp L (warpLane L e.1 l) e.1) :
    Ready L X e ↔ ManualWait.shfl L X e :=
  ready_iff_masked he rfl rfl fun l hl _ => hw l hl

theorem witness_of_manual_shfl {mode : ShflMode} {a : Value} {b c : Nat} {recv : Value}
    {ok : Bool} (he : X.get e = some ⟨pc, .shfl mode a b c recv ok⟩) {l j : Nat} (hl : l < 32)
    (hw : SameWarp L (warpLane L e.1 l) e.1)
    (hy : ManualWait.Executed shflClass X ⟨2 ^ 32 - 1, mode, a⟩
        (ManualWait.ord shflClass X (2 ^ 32 - 1) e) (warpLane L e.1 l, j) ∨
      ManualWait.ExitedBefore shflClass X (2 ^ 32 - 1)
        (ManualWait.ord shflClass X (2 ^ 32 - 1) e) (warpLane L e.1 l, j)) :
    Witness L X (.thread (warpLane L e.1 l, j)) e :=
  witness_of_masked (p := ⟨2 ^ 32 - 1, mode, a⟩) he rfl rfl hl
    (by rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hl) hw hy

theorem ready_iff_manual_vote {mask : Nat} {a : Bool} {b : BitVec 32}
    (he : X.get e = some ⟨pc, .vote mask a b⟩)
    (hw : ∀ l < 32, mask.testBit l → SameWarp L (warpLane L e.1 l) e.1) :
    Ready L X e ↔ ManualWait.vote L X e :=
  ready_iff_masked he rfl rfl hw

theorem witness_of_manual_vote {mask : Nat} {a : Bool} {b : BitVec 32}
    (he : X.get e = some ⟨pc, .vote mask a b⟩) {l j : Nat} (hl : l < 32)
    (hm : mask.testBit l = true) (hw : SameWarp L (warpLane L e.1 l) e.1)
    (hy : ManualWait.Executed voteClass X ⟨mask, .ballot, a⟩
        (ManualWait.ord voteClass X mask e) (warpLane L e.1 l, j) ∨
      ManualWait.ExitedBefore voteClass X mask (ManualWait.ord voteClass X mask e)
        (warpLane L e.1 l, j)) :
    Witness L X (.thread (warpLane L e.1 l, j)) e :=
  witness_of_masked (p := ⟨mask, .ballot, a⟩) he rfl rfl hl hm hw hy

theorem ready_iff_manual_voteMode {mode : VoteMode} {mask : Nat} {a d : Bool}
    (he : X.get e = some ⟨pc, .voteMode mode mask a d⟩)
    (hw : ∀ l < 32, mask.testBit l → SameWarp L (warpLane L e.1 l) e.1) :
    Ready L X e ↔ ManualWait.vote L X e :=
  ready_iff_masked he rfl rfl hw

theorem witness_of_manual_voteMode {mode : VoteMode} {mask : Nat} {a d : Bool}
    (he : X.get e = some ⟨pc, .voteMode mode mask a d⟩) {l j : Nat} (hl : l < 32)
    (hm : mask.testBit l = true) (hw : SameWarp L (warpLane L e.1 l) e.1)
    (hy : ManualWait.Executed voteClass X ⟨mask, mode, a⟩
        (ManualWait.ord voteClass X mask e) (warpLane L e.1 l, j) ∨
      ManualWait.ExitedBefore voteClass X mask (ManualWait.ord voteClass X mask e)
        (warpLane L e.1 l, j)) :
    Witness L X (.thread (warpLane L e.1 l, j)) e :=
  witness_of_masked (p := ⟨mask, mode, a⟩) he rfl rfl hl hm hw hy

theorem ready_iff_manual_redux {op : ReduxOp} {signed : Bool} {mask : Nat} {a d : BitVec 32}
    (he : X.get e = some ⟨pc, .redux op signed mask a d⟩)
    (hw : ∀ l < 32, mask.testBit l → SameWarp L (warpLane L e.1 l) e.1) :
    Ready L X e ↔ ManualWait.redux L X e :=
  ready_iff_masked he rfl rfl hw

theorem witness_of_manual_redux {op : ReduxOp} {signed : Bool} {mask : Nat} {a d : BitVec 32}
    (he : X.get e = some ⟨pc, .redux op signed mask a d⟩) {l j : Nat} (hl : l < 32)
    (hm : mask.testBit l = true) (hw : SameWarp L (warpLane L e.1 l) e.1)
    (hy : ManualWait.Executed reduxClass X ⟨mask, (op, signed), a⟩
        (ManualWait.ord reduxClass X mask e) (warpLane L e.1 l, j) ∨
      ManualWait.ExitedBefore reduxClass X mask (ManualWait.ord reduxClass X mask e)
        (warpLane L e.1 l, j)) :
    Witness L X (.thread (warpLane L e.1 l, j)) e :=
  witness_of_masked (p := ⟨mask, (op, signed), a⟩) he rfl rfl hl hm hw hy

theorem ready_iff_manual_match {all wide : Bool} {mask : Nat} {a : BitVec 64} {d : BitVec 32}
    {q : Bool} (he : X.get e = some ⟨pc, .match_ all wide mask a d q⟩)
    (hw : ∀ l < 32, mask.testBit l → SameWarp L (warpLane L e.1 l) e.1) :
    Ready L X e ↔ ManualWait.match_ L X e :=
  ready_iff_masked he rfl rfl hw

theorem witness_of_manual_match {all wide : Bool} {mask : Nat} {a : BitVec 64} {d : BitVec 32}
    {q : Bool} (he : X.get e = some ⟨pc, .match_ all wide mask a d q⟩) {l j : Nat} (hl : l < 32)
    (hm : mask.testBit l = true) (hw : SameWarp L (warpLane L e.1 l) e.1)
    (hy : ManualWait.Executed matchClass X ⟨mask, (all, wide), a⟩
        (ManualWait.ord matchClass X mask e) (warpLane L e.1 l, j) ∨
      ManualWait.ExitedBefore matchClass X mask (ManualWait.ord matchClass X mask e)
        (warpLane L e.1 l, j)) :
    Witness L X (.thread (warpLane L e.1 l, j)) e :=
  witness_of_masked (p := ⟨mask, (all, wide), a⟩) he rfl rfl hl hm hw hy

end MaskedFamilies

/-! ## elect.sync and bar.warp.sync -/

namespace ManualWait

variable (L : Launch)

/-- §9.7.15.15: "The mandatory .sync qualifier indicates that elect causes the executing thread to
wait until all threads in the membermask execute the elect instruction before resuming
execution." Every lane of the member mask has executed the election of the same instance. -/
def elect (X : Execution) (e : EvId) : Prop :=
  ∀ pc mask inst leader, X.get e = some ⟨pc, .elect mask inst leader⟩ →
    ∀ l < 32, mask.testBit l →
      ∃ j pc' leader', X.get (warpLane L e.1 l, j) = some ⟨pc', .elect mask inst leader'⟩

/-- §9.7.15.2: "bar.warp.sync will cause executing thread to wait until all threads corresponding
to membermask have executed a bar.warp.sync with the same membermask value before resuming
execution." Every lane of the member mask has executed the `bar.warp.sync` of the same instance. -/
def warpBar (X : Execution) (e : EvId) : Prop :=
  ∀ pc mask inst, X.get e = some ⟨pc, .warpBar mask inst⟩ →
    ∀ l < 32, mask.testBit l →
      ∃ j pc', X.get (warpLane L e.1 l, j) = some ⟨pc', .warpBar mask inst⟩

end ManualWait

section ElectWarpBar

variable {L : Launch} {X : Execution} {e : EvId} {pc : Nat}

theorem ready_iff_manual_elect {mask inst leader : Nat}
    (he : X.get e = some ⟨pc, .elect mask inst leader⟩) :
    Ready L X e ↔ ManualWait.elect L X e := by
  rw [ready_get he]
  simp only [KindNeeds, List.forall_mem_map, List.mem_filter, List.mem_range, Filled,
    ManualWait.elect, he, Option.some.injEq, Event.mk.injEq, Kind.elect.injEq]
  constructor
  · rintro h pc' mask' inst' leader' ⟨-, rfl, rfl, -⟩ l hl hm
    obtain ⟨x, -, j, pc'', leader'', rfl, h⟩ := h l ⟨hl, hm⟩
    exact ⟨j, pc'', leader'', h⟩
  · rintro h l ⟨hl, hm⟩
    obtain ⟨j, pc', leader', h⟩ := h pc mask inst leader ⟨rfl, rfl, rfl, rfl⟩ l hl hm
    exact ⟨.thread _, ⟨_, h⟩, j, pc', leader', rfl, h⟩

theorem witness_of_manual_elect {mask inst leader : Nat}
    (he : X.get e = some ⟨pc, .elect mask inst leader⟩) {l j pc' leader' : Nat} (hl : l < 32)
    (hm : mask.testBit l = true)
    (hy : X.get (warpLane L e.1 l, j) = some ⟨pc', .elect mask inst leader'⟩) :
    Witness L X (.thread (warpLane L e.1 l, j)) e := by
  rw [witness_get he]
  refine ⟨fun x => ∃ j pc leader, x = .thread (warpLane L e.1 l, j) ∧
    X.get (warpLane L e.1 l, j) = some ⟨pc, .elect mask inst leader⟩, ?_, ⟨_, hy⟩,
    j, pc', leader', rfl, hy⟩
  exact List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨List.mem_range.mpr hl, hm⟩, rfl⟩

theorem ready_iff_manual_warpBar {mask inst : Nat} (he : X.get e = some ⟨pc, .warpBar mask inst⟩) :
    Ready L X e ↔ ManualWait.warpBar L X e := by
  rw [ready_get he]
  simp only [KindNeeds, List.forall_mem_map, List.mem_filter, List.mem_range, Filled,
    ManualWait.warpBar, he, Option.some.injEq, Event.mk.injEq, Kind.warpBar.injEq,
    Execution.WarpBar]
  constructor
  · rintro h pc' mask' inst' ⟨-, rfl, rfl⟩ l hl hm
    obtain ⟨x, -, j, rfl, pc'', h⟩ := h l ⟨hl, hm⟩
    exact ⟨j, pc'', h⟩
  · rintro h l ⟨hl, hm⟩
    obtain ⟨j, pc', h⟩ := h pc mask inst ⟨rfl, rfl, rfl⟩ l hl hm
    exact ⟨.thread _, ⟨_, h⟩, j, rfl, pc', h⟩

theorem witness_of_manual_warpBar {mask inst : Nat}
    (he : X.get e = some ⟨pc, .warpBar mask inst⟩) {l j pc' : Nat} (hl : l < 32)
    (hm : mask.testBit l = true)
    (hy : X.get (warpLane L e.1 l, j) = some ⟨pc', .warpBar mask inst⟩) :
    Witness L X (.thread (warpLane L e.1 l, j)) e := by
  rw [witness_get he]
  refine ⟨fun x => ∃ j, x = .thread (warpLane L e.1 l, j) ∧
    X.WarpBar (warpLane L e.1 l, j) mask inst, ?_, ⟨_, hy⟩, j, rfl, pc', hy⟩
  exact List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨List.mem_range.mpr hl, hm⟩, rfl⟩

end ElectWarpBar

/-! ## Warp-level matrix instructions, setmaxnreg and the warp-collective tcgen05 instructions -/

namespace ManualWait

variable (L : Launch)

/-- §9.7.16.5.14: "The mandatory .sync qualifier indicates that mma instruction causes the
executing thread to wait until all threads in the warp execute the same mma instruction before
resuming execution." (ldmatrix, stmatrix, movmatrix and mma.sp have the same sentence.) Every lane
of the warp has executed its matrix instruction with the same per-thread ordinal as `e`, or has
exited having executed no more matrix instructions than `e`'s ordinal. The short exit fills the
need only so that the instance exists; `MatrixUnsafe` reports it as the undefined behaviour the
manual states, and it also reports an instance whose lanes execute different instructions. -/
def matrix (X : Execution) (e : EvId) : Prop :=
  ∀ pc op own recv, X.get e = some ⟨pc, .matrix op own recv⟩ →
    ∀ l < 32, ∃ j,
      (∃ pc' op' own' recv', X.get (warpLane L e.1 l, j) = some ⟨pc', .matrix op' own' recv'⟩ ∧
        ((X.tr (warpLane L e.1 l)).take j).countP isMatrix =
          ((X.tr e.1).take e.2).countP isMatrix) ∨
      (∃ pc', X.get (warpLane L e.1 l, j) = some ⟨pc', .exit⟩ ∧
        (X.tr (warpLane L e.1 l)).countP isMatrix ≤ ((X.tr e.1).take e.2).countP isMatrix)

/-- §9.7.21.5: "The mandatory .sync qualifier indicates that setmaxnreg instruction causes the
executing thread to wait until all threads in the warp execute the same setmaxnreg instruction
before resuming execution." Every lane of the warp has executed the request with the same
per-thread ordinal, at the same source position, with the same direction and count. -/
def setMaxReg (X : Execution) (e : EvId) : Prop :=
  ∀ pc inc n inst, X.get e = some ⟨pc, .setMaxReg inc n inst⟩ →
    ∀ l < 32, ∃ j inst', X.get (warpLane L e.1 l, j) = some ⟨pc, .setMaxReg inc n inst'⟩ ∧
      SetMaxNReg.ordinal X (warpLane L e.1 l, j) = SetMaxNReg.ordinal X e

/-- §9.7.18.8.3: "The mandatory .sync qualifier indicates that tcgen05.ld causes the executing
thread to wait until all threads in the warp execute the same tcgen05.ld instruction before
resuming execution." (tcgen05.st, §9.7.18.8.4, and tcgen05.wait::ld and tcgen05.wait::st,
§9.7.18.8.5, have the same sentence.) Every thread of the warp has executed its warp-collective
tcgen05 instruction with the same per-thread ordinal as `e`. That the instructions agree is checked
by the agreement rules of the collective, outside the wait. -/
def tc (X : Execution) (e : EvId) : Prop :=
  ∀ l < warpSize L e.1, ∃ j ev, X.get (warpLane L e.1 l, j) = some ev ∧ isTcColl ev = true ∧
    ((X.tr (warpLane L e.1 l)).take j).countP isTcColl = ((X.tr e.1).take e.2).countP isTcColl

/-- Record `j` of the allocator history of the CTA of the allocation `e` is a deallocation of a
column of the range that `e` was given, and no deallocation between it and the record of `e` frees
that column again: the release whose column the allocation reuses. -/
def LastFreed (X : Execution) (e : EvId) (j : Nat) : Prop :=
  ∃ i r d n base b' n', (X.tmemHistory (e.1 / L.block))[i]? = some r ∧
    Tmem.Pair.Participates L r.own e ∧ r.action = .alloc n base ∧
    (X.tmemHistory (e.1 / L.block))[j]? = some d ∧ j < i ∧ d.action = .dealloc b' n' ∧
    ∃ col, base ≤ col ∧ col < base + n ∧ b' ≤ col ∧ col < b' + n' ∧
      ∀ k d' b'' n'', j < k → k < i → (X.tmemHistory (e.1 / L.block))[k]? = some d' →
        d'.action = .dealloc b'' n'' → ¬ (b'' ≤ col ∧ col < b'' + n'')

/-- §9.7.18.7.1: "The mandatory .sync qualifier indicates that the instruction causes the
executing thread to wait until all threads in the warp execute the same instruction before
resuming execution."; "The tcgen05.alloc blocks if the requested amount of Tensor Memory is not
available and unblocks as soon as the requested amount of Tensor Memory becomes available for
allocation."; "When .cta_group::2 is specified, one warp from each of the peer CTAs must
collectively perform the allocation and de-allocation."; "tcgen05.dealloc may block to
collectively performs the deallocation with the other peer CTA ’s warp".

Stated over the replayed allocator history: the warp condition of `tc`; the allocator has
performed the request; and, when the instruction waits for its operation (an allocation, a
`cta_group::1` instruction, or a deallocation or relinquishment whose peer-wait choice is set), the
operation is complete, every lane of the peer CTA's warp of a `cta_group::2` operation has executed
its instruction, and for an allocation every lane of each release whose column it reuses has
executed that release. For a nonleader allocating lane, its warp leader has published the
local result (EXT-TMEM-ALLOC-RESULT-ORDER). -/
def alloc (X : Execution) (e : EvId) : Prop :=
  ∀ pc group dst request, X.get e = some ⟨pc, .tc (.resource group dst request)⟩ →
    (tc L X e ∧ Tmem.Pair.Performed L X e ∧
    (Tmem.Pair.MustWait X e → Tmem.Pair.Covered L X e ∧
      (group = .two → ∀ l : Fin 32, ∃ q ∈ X.tmemPairing,
        (Tmem.Pair.Participates L q.1 e ∧ X.RefPresent (.thread (q.2.event L l))) ∨
          (Tmem.Pair.Participates L q.2 e ∧ X.RefPresent (.thread (q.1.event L l)))) ∧
      (∀ n, request = .alloc n → ∀ j, LastFreed L X e j → ∀ l : Fin 32,
        ∃ d, (X.tmemHistory (e.1 / L.block))[j]? = some d ∧
          X.RefPresent (.thread (d.own.event L l))))) ∧
    (∀ count, request = .alloc count → laneOf L e.1 ≠ 0 →
      ∃ store loc, Tmem.Pair.AllocResult L X store e loc)

end ManualWait

theorem isMatrix_iff (ev : Event) :
    isMatrix ev = true ↔ ∃ pc op own recv, ev = ⟨pc, .matrix op own recv⟩ := by
  obtain ⟨pc, k⟩ := ev
  cases k <;> simp [isMatrix]

section WarpSync

variable {L : Launch} {X : Execution} {e : EvId} {pc : Nat}

theorem ready_iff_manual_matrix {op : MatrixOp} {own recv : List (Option Byte)}
    (he : X.get e = some ⟨pc, .matrix op own recv⟩) :
    Ready L X e ↔ ManualWait.matrix L X e := by
  rw [ready_get he]
  simp only [KindNeeds, List.forall_mem_map, List.mem_range, Filled, ManualWait.matrix, he,
    Option.some.injEq, Event.mk.injEq, Execution.MatrixK, Execution.ExitedShort, isMatrix_iff]
  constructor
  · rintro h pc' op' own' recv' - l hl
    obtain ⟨x, -, j, rfl, h⟩ := h l hl
    refine ⟨j, h.imp ?_ ?_⟩
    · rintro ⟨⟨ev, h1, pc'', op'', own'', recv'', rfl⟩, h2⟩
      exact ⟨pc'', op'', own'', recv'', h1, h2⟩
    · rintro ⟨⟨pc'', h1⟩, h2⟩
      exact ⟨pc'', h1, h2⟩
  · intro h l hl
    obtain ⟨j, hj⟩ := h pc op own recv ⟨rfl, rfl⟩ l hl
    refine ⟨.thread (warpLane L e.1 l, j), ?_, j, rfl, hj.imp ?_ ?_⟩
    · rcases hj with ⟨pc', op', own', recv', h1, -⟩ | ⟨pc', h1, -⟩
      · exact ⟨_, h1⟩
      · exact ⟨_, h1⟩
    · rintro ⟨pc', op', own', recv', h1, h2⟩
      exact ⟨⟨_, h1, pc', op', own', recv', rfl⟩, h2⟩
    · rintro ⟨pc', h1, h2⟩
      exact ⟨⟨pc', h1⟩, h2⟩

theorem witness_of_manual_matrix {op : MatrixOp} {own recv : List (Option Byte)}
    (he : X.get e = some ⟨pc, .matrix op own recv⟩) {l j : Nat} (hl : l < 32)
    (hy : (∃ pc' op' own' recv', X.get (warpLane L e.1 l, j) = some ⟨pc', .matrix op' own' recv'⟩ ∧
        ((X.tr (warpLane L e.1 l)).take j).countP isMatrix =
          ((X.tr e.1).take e.2).countP isMatrix) ∨
      (∃ pc', X.get (warpLane L e.1 l, j) = some ⟨pc', .exit⟩ ∧
        (X.tr (warpLane L e.1 l)).countP isMatrix ≤ ((X.tr e.1).take e.2).countP isMatrix)) :
    Witness L X (.thread (warpLane L e.1 l, j)) e := by
  rw [witness_get he]
  refine ⟨fun x => ∃ j, x = .thread (warpLane L e.1 l, j) ∧
    (X.MatrixK (warpLane L e.1 l, j) (((X.tr e.1).take e.2).countP isMatrix) ∨
      X.ExitedShort isMatrix (warpLane L e.1 l, j) (((X.tr e.1).take e.2).countP isMatrix)),
    List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩, ?_, j, rfl, ?_⟩
  · rcases hy with ⟨pc', op', own', recv', h1, -⟩ | ⟨pc', h1, -⟩
    · exact ⟨_, h1⟩
    · exact ⟨_, h1⟩
  · rcases hy with ⟨pc', op', own', recv', h1, h2⟩ | ⟨pc', h1, h2⟩
    · exact .inl ⟨⟨_, h1, rfl⟩, h2⟩
    · exact .inr ⟨⟨pc', h1⟩, h2⟩

theorem ready_iff_manual_setMaxReg {inc : Bool} {n inst : Nat}
    (he : X.get e = some ⟨pc, .setMaxReg inc n inst⟩)
    (hw : ∀ l < 32, SameWarp L (warpLane L e.1 l) e.1) :
    Ready L X e ↔ ManualWait.setMaxReg L X e := by
  rw [ready_get he]
  simp only [KindNeeds, List.forall_mem_map, List.mem_range, Filled, ManualWait.setMaxReg, he,
    Option.some.injEq, Event.mk.injEq, Kind.setMaxReg.injEq, SetMaxNReg.SameRequest,
    SetMaxNReg.Request]
  constructor
  · rintro h pc' inc' n' inst' ⟨rfl, rfl, rfl, rfl⟩ l hl
    obtain ⟨x, -, j, rfl, -, ho, pc'', inc'', n'', ei, fi, h1, h2⟩ := h l hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
    exact ⟨j, fi, h2, ho.symm⟩
  · intro h l hl
    obtain ⟨j, inst', h1, h2⟩ := h pc inc n inst ⟨rfl, rfl, rfl, rfl⟩ l hl
    obtain ⟨⟨a, b, c⟩, d⟩ := hw l hl
    exact ⟨.thread _, ⟨_, h1⟩, j, rfl, ⟨⟨b, a, c.symm⟩, d.symm⟩, h2.symm, pc, inc, n, inst,
      inst', ⟨rfl, rfl, rfl, rfl⟩, h1⟩

theorem witness_of_manual_setMaxReg {inc : Bool} {n inst : Nat}
    (he : X.get e = some ⟨pc, .setMaxReg inc n inst⟩) {l j inst' : Nat} (hl : l < 32)
    (hw : SameWarp L (warpLane L e.1 l) e.1)
    (hy : X.get (warpLane L e.1 l, j) = some ⟨pc, .setMaxReg inc n inst'⟩)
    (ho : SetMaxNReg.ordinal X (warpLane L e.1 l, j) = SetMaxNReg.ordinal X e) :
    Witness L X (.thread (warpLane L e.1 l, j)) e := by
  rw [witness_get he]
  obtain ⟨⟨a, b, c⟩, d⟩ := hw
  exact ⟨_, List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩, ⟨_, hy⟩, j, rfl,
    ⟨⟨b, a, c.symm⟩, d.symm⟩, ho.symm, pc, inc, n, inst, inst', he, hy⟩

theorem tcNeeds_filled_iff : (∀ n ∈ tcNeeds L X e, Filled X n) ↔ ManualWait.tc L X e := by
  simp only [tcNeeds, warpLanes, List.map_map, List.forall_mem_map, List.mem_range, Filled,
    Function.comp, Execution.TcK, ManualWait.tc]
  constructor
  · intro h l hl
    obtain ⟨x, -, j, rfl, ⟨ev, h1, h2⟩, h3⟩ := h l hl
    exact ⟨j, ev, h1, h2, h3⟩
  · intro h l hl
    obtain ⟨j, ev, h1, h2, h3⟩ := h l hl
    exact ⟨.thread _, ⟨_, h1⟩, j, rfl, ⟨ev, h1, h2⟩, h3⟩

/-- The tcgen05 kinds whose needs are the lanes of the warp only: `ld`, `st` and the two waits. -/
def TcLane : TcKind → Prop
  | .ld .. | .st .. | .waitLd | .waitSt => True
  | _ => False

theorem ready_iff_manual_tc {k : TcKind} (he : X.get e = some ⟨pc, .tc k⟩) (hk : TcLane k) :
    Ready L X e ↔ ManualWait.tc L X e := by
  rw [ready_get he, ← tcNeeds_filled_iff]
  cases k <;> simp_all [TcLane, KindNeeds]

theorem witness_of_manual_tc {k : TcKind} (he : X.get e = some ⟨pc, .tc k⟩) (hk : TcLane k)
    {l j : Nat} {ev : Event} (hl : l < warpSize L e.1)
    (hy : X.get (warpLane L e.1 l, j) = some ev) (hc : isTcColl ev = true)
    (ho : ((X.tr (warpLane L e.1 l)).take j).countP isTcColl =
      ((X.tr e.1).take e.2).countP isTcColl) :
    Witness L X (.thread (warpLane L e.1 l, j)) e := by
  rw [witness_get he]
  have hn : KindNeeds L X (.tc k) e = tcNeeds L X e := by
    cases k <;> simp_all [TcLane, KindNeeds]
  rw [hn]
  refine ⟨_, List.mem_map.mpr ⟨warpLane L e.1 l,
    List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩, rfl⟩, ⟨_, hy⟩, j, rfl, ⟨ev, hy, hc⟩, ho⟩

end WarpSync

/-! ## Tensor Memory allocation management -/

section Resource

variable {L : Launch} {X : Execution} {e : EvId} {pc : Nat}

theorem peer_filled_iff :
    (∀ n ∈ (List.finRange 32).map (fun l => Need.node fun x => ∃ q ∈ X.tmemPairing,
        (Tmem.Pair.Participates L q.1 e ∧ x = .thread (q.2.event L l)) ∨
          (Tmem.Pair.Participates L q.2 e ∧ x = .thread (q.1.event L l))), Filled X n) ↔
      ∀ l : Fin 32, ∃ q ∈ X.tmemPairing,
        (Tmem.Pair.Participates L q.1 e ∧ X.RefPresent (.thread (q.2.event L l))) ∨
          (Tmem.Pair.Participates L q.2 e ∧ X.RefPresent (.thread (q.1.event L l))) := by
  simp only [List.forall_mem_map, List.mem_finRange, true_implies, Filled]
  refine forall_congr' fun l => ⟨?_, ?_⟩
  · rintro ⟨x, hx, q, hq, (⟨h1, rfl⟩ | ⟨h1, rfl⟩)⟩
    · exact ⟨q, hq, .inl ⟨h1, hx⟩⟩
    · exact ⟨q, hq, .inr ⟨h1, hx⟩⟩
  · rintro ⟨q, hq, (⟨h1, hx⟩ | ⟨h1, hx⟩)⟩
    · exact ⟨_, hx, q, hq, .inl ⟨h1, rfl⟩⟩
    · exact ⟨_, hx, q, hq, .inr ⟨h1, rfl⟩⟩

theorem reuse_filled_iff :
    (∀ n ∈ (List.range (X.tmemHistory (e.1 / L.block)).length).flatMap (fun j =>
        needsIf (ReuseRelease L X e j) ((List.finRange 32).map fun l => Need.node fun x =>
          ∃ d, (X.tmemHistory (e.1 / L.block))[j]? = some d ∧ x = .thread (d.own.event L l))),
        Filled X n) ↔
      ∀ j, ManualWait.LastFreed L X e j → ∀ l : Fin 32,
        ∃ d, (X.tmemHistory (e.1 / L.block))[j]? = some d ∧
          X.RefPresent (.thread (d.own.event L l)) := by
  classical
  simp only [List.forall_mem_flatMap, List.mem_range, needsIf]
  constructor
  · intro h j hj l
    have hlt : j < (X.tmemHistory (e.1 / L.block)).length := by
      obtain ⟨-, -, d, -, -, -, -, -, -, -, h4, -⟩ := hj
      exact (List.getElem?_eq_some_iff.mp h4).1
    have := h j hlt
    simp only [show ReuseRelease L X e j from hj, ↓reduceIte] at this
    obtain ⟨x, hx, d, hd, rfl⟩ := this _ (List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩)
    exact ⟨d, hd, hx⟩
  · intro h j _ n hn
    split at hn
    · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hn
      obtain ⟨d, hd, hx⟩ := h j (by assumption) l
      exact ⟨_, hx, d, hd, rfl⟩
    · cases hn

theorem resourceNeeds_filled_iff (group : CtaGroup) (request : Tmem.Request) :
    (∀ n ∈ resourceNeeds L X e group request, Filled X n) ↔
      (ManualWait.tc L X e ∧ Tmem.Pair.Performed L X e ∧
      (Tmem.Pair.MustWait X e → Tmem.Pair.Covered L X e ∧
        (group = .two → ∀ l : Fin 32, ∃ q ∈ X.tmemPairing,
          (Tmem.Pair.Participates L q.1 e ∧ X.RefPresent (.thread (q.2.event L l))) ∨
            (Tmem.Pair.Participates L q.2 e ∧ X.RefPresent (.thread (q.1.event L l)))) ∧
        (∀ n, request = .alloc n → ∀ j, ManualWait.LastFreed L X e j → ∀ l : Fin 32,
          ∃ d, (X.tmemHistory (e.1 / L.block))[j]? = some d ∧
            X.RefPresent (.thread (d.own.event L l))))) ∧
      (∀ count, request = .alloc count → laneOf L e.1 ≠ 0 →
        ∃ store loc, Tmem.Pair.AllocResult L X store e loc) := by
  classical
  unfold resourceNeeds
  rw [List.forall_mem_append]
  have hpublish : (∀ n ∈ Tmem.Pair.allocResultNeeds L X e request, Filled X n) ↔
      (∀ count, request = .alloc count → laneOf L e.1 ≠ 0 →
        ∃ store loc, Tmem.Pair.AllocResult L X store e loc) := by
    cases request with
    | dealloc => simp [Tmem.Pair.allocResultNeeds]
    | relinquish => simp [Tmem.Pair.allocResultNeeds]
    | alloc n =>
      simp only [Tmem.Pair.allocResultNeeds, Tmem.Request.alloc.injEq, forall_eq']
      by_cases hlead : laneOf L e.1 = 0
      · simp [hlead]
      · simp only [hlead, ↓reduceIte, List.forall_mem_singleton, Filled]
        constructor
        · rintro ⟨store | ⟨i, p⟩, hpres, hf⟩ _
          · obtain ⟨loc, hstore⟩ := hf
            exact ⟨store, loc, hstore⟩
          · exact hf.elim
        · intro h
          obtain ⟨store, loc, hs⟩ := h hlead
          obtain ⟨w, site, loc', bytes, heq, hget⟩ :=
            Tmem.Pair.AllocResultFill.written L (i := e) (x := .thread store) ⟨loc, hs⟩
          cases heq
          exact ⟨.thread store, ⟨_, hget⟩, loc, hs⟩
  rw [hpublish]
  apply and_congr _ Iff.rfl
  simp only [List.forall_mem_append, List.forall_mem_cons, tcNeeds_filled_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  by_cases hw : Tmem.Pair.MustWait X e
  · rw [needsIf, ite_eq_left_of_eq_true _ _ (eq_true hw)]
    simp only [hw, true_implies, List.forall_mem_cons, List.forall_mem_append, and_assoc]
    refine and_congr Iff.rfl (and_congr ?_ ?_)
    · cases group
      · simp
      · simp only [peer_filled_iff, true_implies]
    · cases request
      · simp only [reuse_filled_iff, Tmem.Request.alloc.injEq, forall_eq']
      · simp
      · simp
  · rw [needsIf, ite_eq_right_of_eq_false _ _ (eq_false hw)]
    simp [hw]

theorem ready_iff_manual_alloc {group : CtaGroup} {dst : Option Loc}
    {request : Tmem.Request} (he : X.get e = some ⟨pc, .tc (.resource group dst request)⟩) :
    Ready L X e ↔ ManualWait.alloc L X e := by
  rw [ready_get he]
  simp only [KindNeeds, resourceNeeds_filled_iff, ManualWait.alloc, he, Option.some.injEq,
    Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq]
  constructor
  · rintro h pc' group' dst' request' ⟨-, rfl, rfl, rfl⟩
    exact h
  · intro h
    exact h pc group dst request ⟨rfl, rfl, rfl, rfl⟩

/-- Every lane of the warp, every lane of the peer warp of a waiting `cta_group::2` operation, and
every lane of a release whose column a waiting allocation reuses is a witness. -/
theorem witness_of_manual_alloc {group : CtaGroup} {dst : Option Loc}
    {request : Tmem.Request} (he : X.get e = some ⟨pc, .tc (.resource group dst request)⟩) :
    (∀ l j ev, l < warpSize L e.1 → X.get (warpLane L e.1 l, j) = some ev →
      isTcColl ev = true →
      ((X.tr (warpLane L e.1 l)).take j).countP isTcColl = ((X.tr e.1).take e.2).countP isTcColl →
      Witness L X (.thread (warpLane L e.1 l, j)) e) ∧
    (Tmem.Pair.MustWait X e → group = .two → ∀ (l : Fin 32) q, q ∈ X.tmemPairing →
      (Tmem.Pair.Participates L q.1 e → X.RefPresent (.thread (q.2.event L l)) →
        Witness L X (.thread (q.2.event L l)) e) ∧
      (Tmem.Pair.Participates L q.2 e → X.RefPresent (.thread (q.1.event L l)) →
        Witness L X (.thread (q.1.event L l)) e)) ∧
    (Tmem.Pair.MustWait X e → ∀ n, request = .alloc n → ∀ j d (l : Fin 32),
      ManualWait.LastFreed L X e j → (X.tmemHistory (e.1 / L.block))[j]? = some d →
      X.RefPresent (.thread (d.own.event L l)) → Witness L X (.thread (d.own.event L l)) e) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro l j ev hl hy hc ho
    rw [witness_get he]
    refine ⟨fun x => ∃ j', x = .thread (warpLane L e.1 l, j') ∧
      X.TcK (warpLane L e.1 l, j') (((X.tr e.1).take e.2).countP isTcColl), ?_, ⟨_, hy⟩, j, rfl,
      ⟨ev, hy, hc⟩, ho⟩
    simp only [KindNeeds, resourceNeeds]
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    unfold tcNeeds warpLanes
    exact List.mem_map.mpr ⟨warpLane L e.1 l, List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩,
      rfl⟩
  · rintro hw rfl l q hq
    have hmem := covered_witnessed L X e he hw l
    refine ⟨fun h1 hx => ⟨_, hmem, hx, q, hq, .inl ⟨h1, rfl⟩⟩,
      fun h1 hx => ⟨_, hmem, hx, q, hq, .inr ⟨h1, rfl⟩⟩⟩
  · rintro hw n rfl j d l hj hd hx
    rw [witness_get he]
    have hlt : j < (X.tmemHistory (e.1 / L.block)).length :=
      (List.getElem?_eq_some_iff.mp hd).1
    refine ⟨fun x => ∃ d, (X.tmemHistory (e.1 / L.block))[j]? = some d ∧
      x = .thread (d.own.event L l), ?_, hx, d, hd, rfl⟩
    simp only [KindNeeds, resourceNeeds, needsIf, hw, ↓reduceIte]
    refine List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_append_right _ ?_))))
    exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hlt, by
      simp only [show ReuseRelease L X e j from hj, ↓reduceIte]
      exact List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩⟩

end Resource

/-! ## CTA barriers and cluster barriers -/

namespace ManualWait

variable (L : Launch)

/-- §9.7.15.1: "barrier{.cta} instruction causes executing thread to wait for all non-exited
threads from its warp and marks warps’ arrival at barrier." Every thread of the warp of `e` has
its arrival in the warp record that contains `e`, or its exit is recorded before that record. -/
def barWarp (X : Execution) (e : EvId) : Prop :=
  ∀ l < warpSize L e.1, ∃ i, ∃ r : CtaBarrier.Record EvId, ∃ y,
    (X.barriers (e.1 / L.block))[i]? = some r ∧ e ∈ r.refs ∧ y.1 = warpLane L e.1 l ∧
    X.RefPresent (.thread y) ∧
    (y ∈ r.refs ∨ ∃ (j g : Nat), j < i ∧
      (X.barriers (e.1 / L.block))[j]? = some (CtaBarrier.Record.exit g y))

/-- `y` is counted by the release of the generation of the `bar.sync` `e`: an arrival of that
generation, or an exit recorded up to the release. -/
def BarCounted (X : Execution) (e y : EvId) : Prop :=
  ∃ key ic, CtaBarK L X e key ∧
    CtaBarrier.CompletesAt L.block (X.barriers (e.1 / L.block)) ic (key % 16) (key / 16) ∧
    ∃ i, ∃ r : CtaBarrier.Record EvId, (X.barriers (e.1 / L.block))[i]? = some r ∧ y ∈ r.refs ∧
      i ≤ ic ∧
      ((∃ w count lanes s, r = .arrival (key % 16) w count lanes ∧
          CtaBarrier.At L.block (X.barriers (e.1 / L.block)) i s ∧
          (s.slots (key % 16)).generation = key / 16) ∨
        ∃ g, r = CtaBarrier.Record.exit g y)

/-- §9.7.15.1: "barrier{.cta} instruction causes executing thread to wait for all non-exited
threads from its warp and marks warps’ arrival at barrier." and "In addition to signaling its
arrival at the barrier, the barrier{.cta}.red and barrier{.cta}.sync instructions causes executing
thread to wait for non-exited threads of all other warps participating in the barrier to arrive."

Stated over the replayed barrier history: the warp condition `barWarp`; for `bar.sync`, also the
generation of `e` is released and every arrival of that generation and every exit recorded up to
the release has executed. -/
def bar (X : Execution) (e : EvId) : Prop :=
  ∀ pc id count mode, X.get e = some ⟨pc, .bar id count mode⟩ →
    barWarp L X e ∧
    (mode = .sync →
      (∃ key, CtaBarK L X e key ∧
        CtaBarrier.Released L.block (X.barriers (e.1 / L.block)) (key % 16) (key / 16)) ∧
      ∀ y, BarCounted L X e y → X.RefPresent (.thread y))

/-- §9.7.15.3: "In addition, barrier.cluster instructions cause the executing thread to wait for
all non-exited threads from its warp." Every thread of the warp of `e` has its event in the
record that contains `e`, or its exit is recorded before that record. -/
def clusterWarp (X : Execution) (e : EvId) : Prop :=
  ∀ l < warpSize L e.1, ∃ i, ∃ r : ClusterBarrier.Record EvId, ∃ y,
    (X.clusters (L.clusterOfCta (e.1 / L.block)))[i]? = some r ∧ e ∈ r.refs ∧
    y.1 = warpLane L e.1 l ∧ X.RefPresent (.thread y) ∧
    (y ∈ r.refs ∨ ∃ (j g : Nat), j < i ∧
      (X.clusters (L.clusterOfCta (e.1 / L.block)))[j]? = some (ClusterBarrier.Record.exit g y))

/-- `y` is counted by the completion of the phase that the cluster wait `e` waits for: an arrival
of that phase, or an exit of the cluster recorded before the record of `e`. -/
def ClusterCounted (X : Execution) (e y : EvId) : Prop :=
  (∃ phase release,
    ClusterBarrier.WaitOf L.block (L.clusterSizeAt (L.clusterOfCta (e.1 / L.block)))
      (X.clusters (L.clusterOfCta (e.1 / L.block))) e phase ∧
    ClusterBarrier.ArrivalOf L.block (L.clusterSizeAt (L.clusterOfCta (e.1 / L.block)))
      (X.clusters (L.clusterOfCta (e.1 / L.block))) y phase release) ∨
  ∃ (i j : Nat), ∃ r : ClusterBarrier.Record EvId, ∃ g : Nat,
    (X.clusters (L.clusterOfCta (e.1 / L.block)))[i]? = some r ∧ e ∈ r.refs ∧
    (∃ cta w lanes, r = ClusterBarrier.Record.wait cta w lanes) ∧ j < i ∧
    (X.clusters (L.clusterOfCta (e.1 / L.block)))[j]? = some (ClusterBarrier.Record.exit g y)

/-- §9.7.15.3: "In addition, barrier.cluster instructions cause the executing thread to wait for
all non-exited threads from its warp." and "barrier.cluster.wait instruction causes the executing
thread to wait for all non-exited threads of the cluster to perform barrier.cluster.arrive ."

Stated over the replayed cluster barrier history: the warp condition `clusterWarp`; for a wait,
also every arrival of the phase it waits for and every exit of the cluster recorded before its
record has executed. -/
def cluster (X : Execution) (e : EvId) : Prop :=
  ∀ pc op, X.get e = some ⟨pc, .cluster op⟩ →
    clusterWarp L X e ∧
    (∀ aligned, op = .wait aligned → ∀ y, ClusterCounted L X e y → X.RefPresent (.thread y))

end ManualWait

section Barriers

variable {L : Launch} {X : Execution} {e : EvId} {pc : Nat}

theorem barCounted_iff (y : EvId) : ManualWait.BarCounted L X e y ↔ CtaBarCounted L X e y :=
  Iff.rfl

theorem clusterCounted_iff (y : EvId) :
    ManualWait.ClusterCounted L X e y ↔ ClusterCounted L X e y := Iff.rfl

theorem ctaBarWarpNeeds_filled_iff :
    (∀ n ∈ ctaBarWarpNeeds L X e, Filled X n) ↔ ManualWait.barWarp L X e := by
  simp only [ctaBarWarpNeeds, warpLanes, List.map_map, List.forall_mem_map, List.mem_range,
    Filled, Function.comp, ManualWait.barWarp]
  refine forall_congr' fun l => forall_congr' fun _ => ⟨?_, ?_⟩
  · rintro ⟨x, hx, i, r, y, h1, h2, rfl, h3, h4⟩
    exact ⟨i, r, y, h1, h2, h3, hx, h4⟩
  · rintro ⟨i, r, y, h1, h2, h3, hx, h4⟩
    exact ⟨_, hx, i, r, y, h1, h2, rfl, h3, h4⟩

theorem clusterWarpNeeds_filled_iff :
    (∀ n ∈ clusterWarpNeeds L X e, Filled X n) ↔ ManualWait.clusterWarp L X e := by
  simp only [clusterWarpNeeds, warpLanes, List.map_map, List.forall_mem_map, List.mem_range,
    Filled, Function.comp, ManualWait.clusterWarp]
  refine forall_congr' fun l => forall_congr' fun _ => ⟨?_, ?_⟩
  · rintro ⟨x, hx, i, r, y, h1, h2, rfl, h3, h4⟩
    exact ⟨i, r, y, h1, h2, h3, hx, h4⟩
  · rintro ⟨i, r, y, h1, h2, h3, hx, h4⟩
    exact ⟨_, hx, i, r, y, h1, h2, rfl, h3, h4⟩

/-- The counted references of a history, as needs: filled exactly when every counted reference
is present. -/
theorem counted_filled_iff {α : Type} (h : List α) (refs : α → List EvId) (P : EvId → Prop)
    (hP : ∀ y, P y → y ∈ h.flatMap refs) :
    (∀ n ∈ (h.flatMap refs).flatMap (fun y => needsIf (P y) [Need.node (· = .thread y)]),
      Filled X n) ↔ ∀ y, P y → X.RefPresent (.thread y) := by
  classical
  constructor
  · intro H y hy
    have := H (.node (· = .thread y)) (List.mem_flatMap.mpr ⟨y, hP y hy, by simp [needsIf, hy]⟩)
    obtain ⟨x, hx, rfl⟩ := this
    exact hx
  · intro H n hn
    obtain ⟨y, -, hn⟩ := List.mem_flatMap.mp hn
    unfold needsIf at hn
    split at hn
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      subst hn
      exact ⟨_, H y (by assumption), rfl⟩
    · cases hn

theorem ready_iff_manual_bar {id : Nat} {count : Option Nat} {mode : BarMode}
    (he : X.get e = some ⟨pc, .bar id count mode⟩) : Ready L X e ↔ ManualWait.bar L X e := by
  rw [ready_get he]
  simp only [KindNeeds, ctaBarNeeds, List.forall_mem_append, ctaBarWarpNeeds_filled_iff,
    ManualWait.bar, he, Option.some.injEq, Event.mk.injEq, Kind.bar.injEq]
  have hm : (∀ n ∈ (match mode with
      | .sync => Need.cond (∃ key, CtaBarK L X e key ∧ CtaBarDone L X (e.1 / L.block) key) ::
          ((X.barriers (e.1 / L.block)).flatMap CtaBarrier.Record.refs).flatMap fun y =>
            needsIf (CtaBarCounted L X e y) [Need.node (· = AsyncCopy.Ref.thread y)]
      | .arrive => []), Filled X n) ↔
      (mode = .sync →
        (∃ key, CtaBarK L X e key ∧
          CtaBarrier.Released L.block (X.barriers (e.1 / L.block)) (key % 16) (key / 16)) ∧
        ∀ y, ManualWait.BarCounted L X e y → X.RefPresent (.thread y)) := by
    cases mode
    · simp only [List.forall_mem_cons, true_implies]
      refine and_congr Iff.rfl ?_
      rw [counted_filled_iff]
      · rfl
      · rintro y ⟨-, -, -, -, i, r, h1, h2, -⟩
        exact List.mem_flatMap.mpr ⟨r, List.mem_of_getElem? h1, h2⟩
    · simp
  constructor
  · rintro ⟨h1, h2⟩ pc' id' count' mode' ⟨-, rfl, rfl, rfl⟩
    exact ⟨h1, hm.mp h2⟩
  · intro h
    obtain ⟨h1, h2⟩ := h pc id count mode ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨h1, hm.mpr h2⟩

/-- Every thread of the warp whose arrival or prior exit the warp condition names, and for
`bar.sync` every counted arrival or exit, is a witness. -/
theorem witness_of_manual_bar {id : Nat} {count : Option Nat} {mode : BarMode}
    (he : X.get e = some ⟨pc, .bar id count mode⟩) :
    (∀ l i (r : CtaBarrier.Record EvId) y, l < warpSize L e.1 →
      (X.barriers (e.1 / L.block))[i]? = some r → e ∈ r.refs → y.1 = warpLane L e.1 l →
      X.RefPresent (.thread y) →
      (y ∈ r.refs ∨ ∃ (j g : Nat), j < i ∧
        (X.barriers (e.1 / L.block))[j]? = some (CtaBarrier.Record.exit g y)) →
      Witness L X (.thread y) e) ∧
    (mode = .sync → ∀ y, ManualWait.BarCounted L X e y → X.RefPresent (.thread y) →
      Witness L X (.thread y) e) := by
  refine ⟨?_, ?_⟩
  · intro l i r y hl h1 h2 h3 hx h4
    rw [witness_get he]
    refine ⟨fun x => ∃ i, ∃ r : CtaBarrier.Record EvId, ∃ y,
      (X.barriers (e.1 / L.block))[i]? = some r ∧ e ∈ r.refs ∧ x = .thread y ∧
      y.1 = warpLane L e.1 l ∧ (y ∈ r.refs ∨ ∃ (j g : Nat), j < i ∧
        (X.barriers (e.1 / L.block))[j]? = some (CtaBarrier.Record.exit g y)), ?_, hx,
      i, r, y, h1, h2, rfl, h3, h4⟩
    simp only [KindNeeds, ctaBarNeeds]
    refine List.mem_append_left _ ?_
    unfold ctaBarWarpNeeds warpLanes
    exact List.mem_map.mpr ⟨warpLane L e.1 l, List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩,
      rfl⟩
  · rintro rfl y hy hx
    have hy' := hy
    obtain ⟨-, -, -, -, i, r, h1, h2, -⟩ := hy'
    exact ⟨_, ctaBarCounted_witnessed L X e y he
      (List.mem_flatMap.mpr ⟨r, List.mem_of_getElem? h1, h2⟩) hy, hx, rfl⟩

theorem clusterCounted_mem {y : EvId} (hy : ClusterCounted L X e y) :
    y ∈ (X.clusters (L.clusterOfCta (e.1 / L.block))).flatMap ClusterBarrier.Record.refs := by
  rcases hy with ⟨phase, release, hw, i, s, t, cta, warp, lanes, g, h1, hs, h2, hr⟩ |
    ⟨i, j, r, g, hi, he, hr, hj, h1⟩
  · exact List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? h1,
      List.mem_map.mpr ⟨(g, y), h2, rfl⟩⟩
  · exact List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? h1, List.mem_singleton_self y⟩

theorem ready_iff_manual_cluster {op : ClusterOp} (he : X.get e = some ⟨pc, .cluster op⟩) :
    Ready L X e ↔ ManualWait.cluster L X e := by
  rw [ready_get he]
  simp only [KindNeeds, clusterNeeds, List.forall_mem_append, clusterWarpNeeds_filled_iff,
    ManualWait.cluster, he, Option.some.injEq, Event.mk.injEq, Kind.cluster.injEq]
  have hm : (∀ n ∈ (match op with
      | .wait _ =>
        ((X.clusters (L.clusterOfCta (e.1 / L.block))).flatMap
          ClusterBarrier.Record.refs).flatMap
          fun y => needsIf (ClusterCounted L X e y) [Need.node (· = AsyncCopy.Ref.thread y)]
      | .arrive .. => []), Filled X n) ↔
      (∀ aligned, op = .wait aligned → ∀ y, ManualWait.ClusterCounted L X e y →
        X.RefPresent (.thread y)) := by
    cases op
    · simp
    · simp only [ClusterOp.wait.injEq, forall_eq']
      exact counted_filled_iff _ _ _ fun y hy => clusterCounted_mem hy
  constructor
  · rintro ⟨h1, h2⟩ pc' op' ⟨-, rfl⟩
    exact ⟨h1, hm.mp h2⟩
  · intro h
    obtain ⟨h1, h2⟩ := h pc op ⟨rfl, rfl⟩
    exact ⟨h1, hm.mpr h2⟩

/-- Every thread of the warp whose event or prior exit the warp condition names, and for a wait
every counted arrival or exit, is a witness. -/
theorem witness_of_manual_cluster {op : ClusterOp} (he : X.get e = some ⟨pc, .cluster op⟩) :
    (∀ l i (r : ClusterBarrier.Record EvId) y, l < warpSize L e.1 →
      (X.clusters (L.clusterOfCta (e.1 / L.block)))[i]? = some r → e ∈ r.refs →
      y.1 = warpLane L e.1 l → X.RefPresent (.thread y) →
      (y ∈ r.refs ∨ ∃ (j g : Nat), j < i ∧ (X.clusters (L.clusterOfCta (e.1 / L.block)))[j]? =
        some (ClusterBarrier.Record.exit g y)) →
      Witness L X (.thread y) e) ∧
    (∀ aligned, op = .wait aligned → ∀ y, ManualWait.ClusterCounted L X e y →
      X.RefPresent (.thread y) → Witness L X (.thread y) e) := by
  classical
  refine ⟨?_, ?_⟩
  · intro l i r y hl h1 h2 h3 hx h4
    rw [witness_get he]
    refine ⟨fun x => ∃ i, ∃ r : ClusterBarrier.Record EvId, ∃ y,
      (X.clusters (L.clusterOfCta (e.1 / L.block)))[i]? = some r ∧ e ∈ r.refs ∧
      x = .thread y ∧ y.1 = warpLane L e.1 l ∧
      (y ∈ r.refs ∨ ∃ (j g : Nat), j < i ∧ (X.clusters (L.clusterOfCta (e.1 / L.block)))[j]? =
        some (ClusterBarrier.Record.exit g y)), ?_, hx, i, r, y, h1, h2, rfl, h3, h4⟩
    simp only [KindNeeds, clusterNeeds]
    refine List.mem_append_left _ ?_
    unfold clusterWarpNeeds warpLanes
    exact List.mem_map.mpr ⟨warpLane L e.1 l, List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩,
      rfl⟩
  · rintro aligned rfl y hy hx
    rw [witness_get he]
    refine ⟨(· = .thread y), ?_, hx, rfl⟩
    simp only [KindNeeds, clusterNeeds]
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨y, clusterCounted_mem hy, ?_⟩)
    simp [needsIf, show ClusterCounted L X e y from hy]

end Barriers

/-! ## Group waits and the successful poll -/

namespace ManualWait

variable (L : Launch)

/-- The completion state of the bulk operations of `X`: a tensor store has finished reading when
its reads are done and is complete when its writes are done; a linear copy has finished reading
when its read is present and is complete when its write is present. -/
def bulkCompletion (X : Execution) : BulkGroup.Completion EvId where
  reads i := match (X.get i).map Event.kind with
    | some (.tensorStore ..) => X.AsyncPresent i .readsDone
    | _ => X.AsyncPresent i (.read .copy)
  full i := match (X.get i).map Event.kind with
    | some (.tensorStore ..) => X.AsyncPresent i .fullDone
    | _ => X.AsyncPresent i (.write .copy)

/-- §9.7.10.28.6.2: "cp.async.bulk.wait_group instruction will cause the executing thread to wait
until only N or fewer of the most recent bulk async-groups are pending and all the prior bulk
async-groups committed by the executing threads are complete." and "The optional .read modifier
indicates that the waiting has to be done until all the bulk async operations in the specified
bulk async-group have completed: reading from the tensormap the reading from their source
locations." Every operation of the groups the wait covers has finished, as its mode requires
(`BulkGroup.WaitReady`). -/
def bulkWait (X : Execution) (e : EvId) : Prop :=
  ∀ pc mode remaining, X.get e = some ⟨pc, .bulkWait mode remaining⟩ →
    BulkGroup.WaitReady (bulkStateBefore X e) (bulkCompletion X) mode remaining

/-- The completion state of the `cp.async` operations of `X`: a copy has finished reading when its
read is present and is complete when its write is present. -/
def asyncCompletion (X : Execution) : BulkGroup.Completion EvId where
  reads i := X.AsyncPresent i (.read .copy)
  full i := X.AsyncPresent i (.write .copy)

/-- §9.7.10.28.3.3: "cp.async.wait_group instruction will cause executing thread to wait till only
N or fewer of the most recent cp.async-group s are pending and all the prior cp.async-group s
committed by the executing threads are complete." Every copy of the groups the wait covers is
complete. -/
def asyncWait (X : Execution) (e : EvId) : Prop :=
  ∀ pc remaining, X.get e = some ⟨pc, .asyncWait remaining⟩ →
    BulkGroup.WaitReady (asyncStateBefore X e) (asyncCompletion X) .full remaining

/-- §9.7.15.16.19: "mbarrier.test_wait is a non-blocking instruction which tests for the
completion of the phase." and "Suspended thread resumes execution when the specified phase
completes OR before the phase completes following a system-dependent time limit." A successful
poll reports a completed phase: every counter update of the phase it observed (`MbarObserved`) is
present. -/
def wait (X : Execution) (e : EvId) : Prop :=
  ∀ pc m q acq sc, X.get e = some ⟨pc, .wait m q true acq sc⟩ →
    ∀ r ∈ X.objects m, MbarObserved X r.id (.thread e) → X.RefPresent r.id

end ManualWait

section Groups

variable {L : Launch} {X : Execution} {e : EvId} {pc : Nat}

/-- An operation that a wait observes is an earlier event of the waiting thread. -/
theorem observes_before {act : Nat → Nat → Kind → Option (BulkGroup.Action EvId)}
    (hact : ∀ g index k i, act g index k = some (.issue i) → i = (g, index)) {i : EvId}
    {remaining : Nat}
    (h : BulkGroup.Observes (BulkGroup.run ((((X.tr e.1).take e.2).zipIdx).filterMap
      fun (event, index) => act e.1 index event.kind)) remaining i) :
    i = (e.1, i.2) ∧ i.2 < e.2 ∧
      ∃ ev, X.get i = some ev ∧ act e.1 i.2 ev.kind = some (.issue i) := by
  obtain ⟨h1, ev, hev, hk⟩ := issue_mem_actions hact (BulkGroup.issue_of_observes h)
  rw [List.getElem?_take] at hev
  split at hev
  · refine ⟨Prod.ext h1 rfl, by assumption, ev, ?_, hk⟩
    simpa [Execution.get, h1] using hev
  · cases hev

theorem bulkAction_issue (g index : Nat) (k : Kind) (i : EvId)
    (h : bulkAction g index k = some (.issue i)) : i = (g, index) := by
  unfold bulkAction at h
  split at h <;> grind

theorem asyncAction_issue (g index : Nat) (k : Kind) (i : EvId)
    (h : asyncAction g index k = some (.issue i)) : i = (g, index) := by
  unfold asyncAction at h
  split at h <;> grind

theorem groupNeeds_filled_iff (k : GroupWait) :
    (∀ n ∈ groupNeeds X e k, Filled X n) ↔
      ∀ j < e.2, GroupWaitsFor X k (e.1, j) e →
        ∀ p ∈ GroupWaitStages X (e.1, j) k, X.AsyncPresent (e.1, j) p := by
  classical
  simp only [groupNeeds, List.forall_mem_flatMap, List.mem_range, needsIf]
  refine forall_congr' fun j => forall_congr' fun _ => ⟨?_, ?_⟩
  · intro h hw p hp
    simp only [hw, ↓reduceIte, List.forall_mem_map, Filled] at h
    obtain ⟨x, hx, rfl⟩ := h p hp
    exact hx
  · intro h n hn
    split at hn
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
      exact ⟨.async (e.1, j) p, h (by assumption) p hp, rfl⟩
    · cases hn

theorem done_bulk_iff (mode : BulkGroup.WaitMode) (i : EvId) :
    BulkGroup.Done (ManualWait.bulkCompletion X) mode i ↔
      ∀ p ∈ GroupWaitStages X i (.bulk mode), X.AsyncPresent i p := by
  rcases h : (X.get i).map Event.kind with _ | k
  · cases mode <;> simp [BulkGroup.Done, ManualWait.bulkCompletion, GroupWaitStages, h]
  · cases k <;> cases mode <;> simp [BulkGroup.Done, ManualWait.bulkCompletion, GroupWaitStages, h]

theorem ready_iff_manual_bulkWait {mode : BulkGroup.WaitMode} {remaining : Nat}
    (he : X.get e = some ⟨pc, .bulkWait mode remaining⟩) :
    Ready L X e ↔ ManualWait.bulkWait X e := by
  rw [ready_get he]
  simp only [KindNeeds, groupNeeds_filled_iff, ManualWait.bulkWait, GroupWaitsFor, BulkWaitsFor,
    BulkGroup.WaitReady, done_bulk_iff]
  constructor
  · intro h pc' mode' remaining' he' i hi
    rw [he] at he'; cases he'
    obtain ⟨hi1, hi2, -⟩ := observes_before bulkAction_issue hi
    rw [hi1] at hi ⊢
    exact h i.2 hi2 ⟨pc, remaining, he, hi⟩
  · rintro h j - ⟨pc', remaining', he', hj⟩
    rw [he] at he'; cases he'
    exact h pc mode remaining he _ hj

theorem witness_of_manual_bulkWait {mode : BulkGroup.WaitMode} {remaining : Nat}
    (he : X.get e = some ⟨pc, .bulkWait mode remaining⟩) {i : EvId}
    (hi : BulkGroup.Observes (bulkStateBefore X e) remaining i)
    {p : AsyncCopy.Part} (hp : p ∈ GroupWaitStages X i (.bulk mode)) (hx : X.AsyncPresent i p) :
    Witness L X (.async i p) e := by
  classical
  obtain ⟨hi1, hi2, -⟩ := observes_before bulkAction_issue hi
  rw [witness_get he]
  rw [hi1] at hi hp hx ⊢
  refine ⟨(· = .async (e.1, i.2) p), ?_, hx, rfl⟩
  simp only [KindNeeds, groupNeeds]
  refine List.mem_flatMap.mpr ⟨i.2, List.mem_range.mpr hi2, ?_⟩
  have hw : GroupWaitsFor X (.bulk mode) (e.1, i.2) e := ⟨pc, remaining, he, hi⟩
  simp only [needsIf, hw, ↓reduceIte]
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

theorem stages_cpAsync {i : EvId} {ev : Event} (hev : X.get i = some ev)
    (hk : asyncAction i.1 i.2 ev.kind = some (.issue i)) :
    GroupWaitStages X i .cpAsync = [.read .copy, .write .copy] := by
  obtain ⟨pc'', k⟩ := ev
  unfold asyncAction at hk
  cases k <;> simp_all [GroupWaitStages]

theorem ready_iff_manual_asyncWait {remaining : Nat}
    (he : X.get e = some ⟨pc, .asyncWait remaining⟩) :
    Ready L X e ↔ ManualWait.asyncWait X e := by
  rw [ready_get he]
  simp only [KindNeeds, groupNeeds_filled_iff, ManualWait.asyncWait, GroupWaitsFor,
    AsyncGroupWaitsFor, BulkGroup.WaitReady]
  constructor
  · intro h pc' remaining' he' i hi
    rw [he] at he'; cases he'
    obtain ⟨hi1, hi2, ev, hev, hk⟩ := observes_before asyncAction_issue hi
    rw [hi1] at hi hev hk ⊢
    have hs := h i.2 hi2 ⟨pc, remaining, he, hi⟩
    rw [stages_cpAsync hev hk] at hs
    exact ⟨hs (.read .copy) (by simp), hs (.write .copy) (by simp)⟩
  · rintro h j - ⟨pc', remaining', he', hj⟩ p hp
    rw [he] at he'; cases he'
    obtain ⟨hi1, hi2, ev, hev, hk⟩ := observes_before asyncAction_issue hj
    have hd := h pc remaining he _ hj
    rw [stages_cpAsync hev hk] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hd.1
    · exact hd.2

theorem witness_of_manual_asyncWait {remaining : Nat}
    (he : X.get e = some ⟨pc, .asyncWait remaining⟩) {i : EvId}
    (hi : BulkGroup.Observes (asyncStateBefore X e) remaining i)
    {p : AsyncCopy.Part} (hp : p = .read .copy ∨ p = .write .copy) (hx : X.AsyncPresent i p) :
    Witness L X (.async i p) e := by
  classical
  obtain ⟨hi1, hi2, ev, hev, hk⟩ := observes_before asyncAction_issue hi
  rw [witness_get he]
  rw [hi1] at hi hx hev hk ⊢
  refine ⟨(· = .async (e.1, i.2) p), ?_, hx, rfl⟩
  simp only [KindNeeds, groupNeeds]
  refine List.mem_flatMap.mpr ⟨i.2, List.mem_range.mpr hi2, ?_⟩
  have hw : GroupWaitsFor X .cpAsync (e.1, i.2) e := ⟨pc, remaining, he, hi⟩
  simp only [needsIf, hw, ↓reduceIte, stages_cpAsync hev hk]
  rcases hp with rfl | rfl <;> simp

theorem ready_iff_manual_wait {m : Loc} {q : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get e = some ⟨pc, .wait m q true acq sc⟩) : Ready L X e ↔ ManualWait.wait X e := by
  classical
  rw [ready_get he]
  simp only [KindNeeds, ↓reduceIte, pollNeeds, List.forall_mem_flatMap, needsIf,
    ManualWait.wait]
  constructor
  · intro h pc' m' q' acq' sc' he' r hr ho
    rw [he] at he'; cases he'
    have := h r hr
    simp only [ho, ↓reduceIte, List.forall_mem_cons, List.not_mem_nil, false_implies,
      implies_true, and_true, Filled] at this
    obtain ⟨x, hx, rfl⟩ := this
    exact hx
  · intro h r hr n hn
    split at hn
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      subst hn
      exact ⟨_, h pc m q acq sc he r hr (by assumption), rfl⟩
    · cases hn

/-- A failed poll has no need. -/
theorem ready_failed_poll {m : Loc} {q : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get e = some ⟨pc, .wait m q false acq sc⟩) : Ready L X e := by
  rw [ready_get he]
  simp [KindNeeds]

theorem witness_of_manual_wait {m : Loc} {q : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get e = some ⟨pc, .wait m q true acq sc⟩) {r : MBarrier.Record AsyncCopy.Ref}
    (hr : r ∈ X.objects m) (ho : MbarObserved X r.id (.thread e)) : Witness L X r.id e := by
  classical
  rw [witness_get he]
  refine ⟨(· = r.id), ?_, ho.1, rfl⟩
  simp only [KindNeeds, ↓reduceIte, pollNeeds]
  exact List.mem_flatMap.mpr ⟨r, hr, by simp [needsIf, ho]⟩

end Groups

/-! ## Non-vacuity: warp collectives

One CTA of one full warp (`L1`). Lane 0 executes the instruction at its first event; lane 1's trace
is `other`; lanes 2 to 31 execute the instruction too. The masked collectives use member mask 3
(lanes 0 and 1), `shfl.sync` the full mask. -/

/-- One CTA of 32 threads. -/
def L1 : Launch := { grid := 1, block := 32, params := fun _ => none }

/-- Lane 1 runs `other`; every other lane of the warp executes `k` once. -/
def warpX (k : Kind) (other : List Event) : Execution where
  tr g := if g = 1 then other else if g < 32 then [⟨0, k⟩] else []
  rf _ _ := none

theorem warpX_get (k : Kind) (other : List Event) (g j : Nat) :
    (warpX k other).get (g, j) =
      if g = 1 then other[j]? else if g < 32 then [(⟨0, k⟩ : Event)][j]? else none := by
  simp only [Execution.get, warpX]
  split_ifs <;> simp

theorem warpX_e (k : Kind) (other : List Event) : (warpX k other).get (0, 0) = some ⟨0, k⟩ := by
  simp [warpX_get]

theorem warpX_lane {k : Kind} {other : List Event} {l : Nat} (hl : l < 32) (h1 : l ≠ 1) :
    (warpX k other).get (l, 0) = some ⟨0, k⟩ := by
  simp [warpX_get, hl, h1]

theorem warpX_one {k : Kind} {other : List Event} {j : Nat} :
    (warpX k other).get (1, j) = other[j]? := by
  simp [warpX_get]

theorem L1_warpLane (l : Nat) : warpLane L1 0 l = l := by
  simp [warpLane, laneOf]

theorem L1_sameWarp {l : Nat} (hl : l < 32) : SameWarp L1 (warpLane L1 0 l) 0 := by
  rw [L1_warpLane]
  simp only [SameWarp, SameCta, Launch.threads, L1]
  omega

theorem L1_warpSize : warpSize L1 0 = 32 := by
  simp [warpSize, L1]

theorem mask3 {l : Nat} (h : Nat.testBit 3 l = true) : l = 0 ∨ l = 1 := by
  rcases l with _ | _ | l
  · exact .inl rfl
  · exact .inr rfl
  · simp [Nat.testBit_succ] at h

/-- With every lane executing the same masked collective, the wait is satisfied. -/
theorem masked_full {Q V : Type} {c : Kind → Option (WarpPart Q V)} {k : Kind}
    {p : WarpPart Q V} (hc : c k = some p) : ManualWait.Masked L1 c (warpX k [⟨0, k⟩]) (0, 0) := by
  intro pc k' p' he hc' l hl _
  rw [warpX_e] at he
  cases he
  rw [hc] at hc'
  cases hc'
  refine ⟨0, .inl ⟨0, k, p, ?_, hc, rfl, rfl, by simp [ManualWait.ord]⟩⟩
  rw [L1_warpLane]
  by_cases h1 : l = 1
  · subst h1; simp [warpX_one]
  · exact warpX_lane hl h1

/-- When lane 1 of the mask has neither executed the collective nor exited, the wait is not
satisfied. -/
theorem masked_blocks {Q V : Type} {c : Kind → Option (WarpPart Q V)} {k : Kind}
    {p : WarpPart Q V} (hc : c k = some p) (hm : p.mask.testBit 1 = true) :
    ¬ ManualWait.Masked L1 c (warpX k []) (0, 0) := by
  intro h
  obtain ⟨j, hj⟩ := h 0 k p (warpX_e k []) hc 1 (by decide) hm
  rw [L1_warpLane] at hj
  rcases hj with ⟨pc, k', p', hg, -⟩ | ⟨pc, hg, -⟩ <;> simp [warpX_one] at hg

theorem exit_before {Q V : Type} {c : Kind → Option (WarpPart Q V)} {k : Kind} {m : Nat} :
    ManualWait.ExitedBefore c (warpX k [⟨0, .exit⟩]) m
      (ManualWait.ord c (warpX k [⟨0, .exit⟩]) m (0, 0)) (warpLane L1 0 1, 0) := by
  rw [L1_warpLane]
  exact ⟨0, by simp [warpX_one], by simp [ManualWait.ord]⟩

theorem executed_one {Q V : Type} {c : Kind → Option (WarpPart Q V)} {k : Kind}
    {p : WarpPart Q V} (hc : c k = some p) :
    ManualWait.Executed c (warpX k [⟨0, k⟩]) p
      (ManualWait.ord c (warpX k [⟨0, k⟩]) p.mask (0, 0)) (warpLane L1 0 1, 0) := by
  rw [L1_warpLane]
  exact ⟨0, k, p, by simp [warpX_one], hc, rfl, rfl, by simp [ManualWait.ord]⟩

section MaskedExamples

/-- `shfl.sync.idx` of lane 0's value 0 from lane 0. -/
abbrev shflK : Kind := .shfl .idx (.bits 32 0) 0 31 (.bits 32 0) true
abbrev voteK : Kind := .vote 3 true 3
abbrev voteModeK : Kind := .voteMode .all 3 true true
abbrev reduxK : Kind := .redux .add false 3 1 2
abbrev matchK : Kind := .match_ true false 3 0 3 true

theorem blocks_shfl : ¬ Ready L1 (warpX shflK []) (0, 0) := by
  rw [ready_iff_manual_shfl (warpX_e shflK _) fun l hl => L1_sameWarp hl]
  exact masked_blocks rfl (by decide)

theorem ready_shfl : Ready L1 (warpX shflK [⟨0, shflK⟩]) (0, 0) := by
  rw [ready_iff_manual_shfl (warpX_e shflK _) fun l hl => L1_sameWarp hl]
  exact masked_full rfl

theorem witness_other_shfl : Witness L1 (warpX shflK [⟨0, shflK⟩]) (.thread (1, 0)) (0, 0) := by
  have := witness_of_manual_shfl (L := L1) (j := 0) (warpX_e shflK _) (by decide : 1 < 32)
    (L1_sameWarp (by decide)) (.inl (executed_one rfl))
  rwa [L1_warpLane] at this

theorem witness_exit_shfl : Witness L1 (warpX shflK [⟨0, .exit⟩]) (.thread (1, 0)) (0, 0) := by
  have := witness_of_manual_shfl (L := L1) (j := 0) (warpX_e shflK _) (by decide : 1 < 32)
    (L1_sameWarp (by decide)) (.inr exit_before)
  rwa [L1_warpLane] at this

theorem blocks_vote : ¬ Ready L1 (warpX voteK []) (0, 0) := by
  rw [ready_iff_manual_vote (warpX_e voteK _) fun l hl _ => L1_sameWarp hl]
  exact masked_blocks rfl (by decide)

theorem ready_vote : Ready L1 (warpX voteK [⟨0, voteK⟩]) (0, 0) := by
  rw [ready_iff_manual_vote (warpX_e voteK _) fun l hl _ => L1_sameWarp hl]
  exact masked_full rfl

theorem witness_other_vote : Witness L1 (warpX voteK [⟨0, voteK⟩]) (.thread (1, 0)) (0, 0) := by
  have := witness_of_manual_vote (L := L1) (j := 0) (warpX_e voteK _) (by decide : 1 < 32)
    (by decide) (L1_sameWarp (by decide)) (.inl (executed_one rfl))
  rwa [L1_warpLane] at this

theorem witness_exit_vote : Witness L1 (warpX voteK [⟨0, .exit⟩]) (.thread (1, 0)) (0, 0) := by
  have := witness_of_manual_vote (L := L1) (j := 0) (warpX_e voteK _) (by decide : 1 < 32)
    (by decide) (L1_sameWarp (by decide)) (.inr exit_before)
  rwa [L1_warpLane] at this

theorem blocks_voteMode : ¬ Ready L1 (warpX voteModeK []) (0, 0) := by
  rw [ready_iff_manual_voteMode (warpX_e voteModeK _) fun l hl _ => L1_sameWarp hl]
  exact masked_blocks rfl (by decide)

theorem ready_voteMode : Ready L1 (warpX voteModeK [⟨0, voteModeK⟩]) (0, 0) := by
  rw [ready_iff_manual_voteMode (warpX_e voteModeK _) fun l hl _ => L1_sameWarp hl]
  exact masked_full rfl

theorem witness_other_voteMode :
    Witness L1 (warpX voteModeK [⟨0, voteModeK⟩]) (.thread (1, 0)) (0, 0) := by
  have := witness_of_manual_voteMode (L := L1) (j := 0) (warpX_e voteModeK _) (by decide : 1 < 32)
    (by decide) (L1_sameWarp (by decide)) (.inl (executed_one rfl))
  rwa [L1_warpLane] at this

theorem witness_exit_voteMode :
    Witness L1 (warpX voteModeK [⟨0, .exit⟩]) (.thread (1, 0)) (0, 0) := by
  have := witness_of_manual_voteMode (L := L1) (j := 0) (warpX_e voteModeK _) (by decide : 1 < 32)
    (by decide) (L1_sameWarp (by decide)) (.inr exit_before)
  rwa [L1_warpLane] at this

theorem blocks_redux : ¬ Ready L1 (warpX reduxK []) (0, 0) := by
  rw [ready_iff_manual_redux (warpX_e reduxK _) fun l hl _ => L1_sameWarp hl]
  exact masked_blocks rfl (by decide)

theorem ready_redux : Ready L1 (warpX reduxK [⟨0, reduxK⟩]) (0, 0) := by
  rw [ready_iff_manual_redux (warpX_e reduxK _) fun l hl _ => L1_sameWarp hl]
  exact masked_full rfl

theorem witness_other_redux : Witness L1 (warpX reduxK [⟨0, reduxK⟩]) (.thread (1, 0)) (0, 0) := by
  have := witness_of_manual_redux (L := L1) (j := 0) (warpX_e reduxK _) (by decide : 1 < 32)
    (by decide) (L1_sameWarp (by decide)) (.inl (executed_one rfl))
  rwa [L1_warpLane] at this

theorem witness_exit_redux : Witness L1 (warpX reduxK [⟨0, .exit⟩]) (.thread (1, 0)) (0, 0) := by
  have := witness_of_manual_redux (L := L1) (j := 0) (warpX_e reduxK _) (by decide : 1 < 32)
    (by decide) (L1_sameWarp (by decide)) (.inr exit_before)
  rwa [L1_warpLane] at this

theorem blocks_match : ¬ Ready L1 (warpX matchK []) (0, 0) := by
  rw [ready_iff_manual_match (warpX_e matchK _) fun l hl _ => L1_sameWarp hl]
  exact masked_blocks rfl (by decide)

theorem ready_match : Ready L1 (warpX matchK [⟨0, matchK⟩]) (0, 0) := by
  rw [ready_iff_manual_match (warpX_e matchK _) fun l hl _ => L1_sameWarp hl]
  exact masked_full rfl

theorem witness_other_match : Witness L1 (warpX matchK [⟨0, matchK⟩]) (.thread (1, 0)) (0, 0) := by
  have := witness_of_manual_match (L := L1) (j := 0) (warpX_e matchK _) (by decide : 1 < 32)
    (by decide) (L1_sameWarp (by decide)) (.inl (executed_one rfl))
  rwa [L1_warpLane] at this

theorem witness_exit_match : Witness L1 (warpX matchK [⟨0, .exit⟩]) (.thread (1, 0)) (0, 0) := by
  have := witness_of_manual_match (L := L1) (j := 0) (warpX_e matchK _) (by decide : 1 < 32)
    (by decide) (L1_sameWarp (by decide)) (.inr exit_before)
  rwa [L1_warpLane] at this

end MaskedExamples

theorem full_get {k : Kind} {l : Nat} (hl : l < 32) :
    (warpX k [⟨0, k⟩]).get (warpLane L1 0 l, 0) = some ⟨0, k⟩ := by
  rw [L1_warpLane]
  by_cases h1 : l = 1
  · subst h1; simp [warpX_one]
  · exact warpX_lane hl h1

theorem none_one {k : Kind} {j : Nat} : (warpX k []).get (warpLane L1 0 1, j) = none := by
  rw [L1_warpLane]; simp [warpX_one]

section WarpExamples

abbrev electK : Kind := .elect 3 7 0
abbrev warpBarK : Kind := .warpBar 3 7
abbrev matrixK : Kind := .matrix .transpose [] []
abbrev setMaxRegK : Kind := .setMaxReg true 240 0
abbrev tcLdK : Kind := .tc (.ld 0 [] .s32x32b)
abbrev tcStK : Kind := .tc (.st 0 [] .s32x32b)
abbrev tcWaitLdK : Kind := .tc .waitLd
abbrev tcWaitStK : Kind := .tc .waitSt

theorem blocks_elect : ¬ Ready L1 (warpX electK []) (0, 0) := by
  rw [ready_iff_manual_elect (warpX_e electK _)]
  intro h
  obtain ⟨j, pc, leader, hg⟩ := h 0 3 7 0 (warpX_e _ _) 1 (by decide) (by decide)
  rw [none_one] at hg
  cases hg

theorem ready_elect : Ready L1 (warpX electK [⟨0, electK⟩]) (0, 0) := by
  rw [ready_iff_manual_elect (warpX_e electK _)]
  intro pc mask inst leader he l hl _
  rw [warpX_e] at he
  cases he
  exact ⟨0, 0, 0, full_get hl⟩

theorem witness_other_elect : Witness L1 (warpX electK [⟨0, electK⟩]) (.thread (1, 0)) (0, 0) := by
  have := witness_of_manual_elect (L := L1) (warpX_e electK _) (by decide : 1 < 32) (by decide)
    (full_get (by decide))
  rwa [L1_warpLane] at this

theorem blocks_warpBar : ¬ Ready L1 (warpX warpBarK []) (0, 0) := by
  rw [ready_iff_manual_warpBar (warpX_e warpBarK _)]
  intro h
  obtain ⟨j, pc, hg⟩ := h 0 3 7 (warpX_e _ _) 1 (by decide) (by decide)
  rw [none_one] at hg
  cases hg

theorem ready_warpBar : Ready L1 (warpX warpBarK [⟨0, warpBarK⟩]) (0, 0) := by
  rw [ready_iff_manual_warpBar (warpX_e warpBarK _)]
  intro pc mask inst he l hl _
  rw [warpX_e] at he
  cases he
  exact ⟨0, 0, full_get hl⟩

theorem witness_other_warpBar :
    Witness L1 (warpX warpBarK [⟨0, warpBarK⟩]) (.thread (1, 0)) (0, 0) := by
  have := witness_of_manual_warpBar (L := L1) (warpX_e warpBarK _) (by decide : 1 < 32)
    (by decide) (full_get (by decide))
  rwa [L1_warpLane] at this

theorem blocks_matrix : ¬ Ready L1 (warpX matrixK []) (0, 0) := by
  rw [ready_iff_manual_matrix (warpX_e matrixK _)]
  intro h
  obtain ⟨j, ⟨pc, op, own, recv, hg, -⟩ | ⟨pc, hg, -⟩⟩ := h 0 _ _ _ (warpX_e _ _) 1 (by decide) <;>
    rw [none_one] at hg <;> cases hg

theorem ready_matrix : Ready L1 (warpX matrixK [⟨0, matrixK⟩]) (0, 0) := by
  rw [ready_iff_manual_matrix (warpX_e matrixK _)]
  intro pc op own recv he l hl
  exact ⟨0, .inl ⟨0, _, _, _, full_get hl, by simp⟩⟩

theorem witness_other_matrix :
    Witness L1 (warpX matrixK [⟨0, matrixK⟩]) (.thread (1, 0)) (0, 0) := by
  have := witness_of_manual_matrix (L := L1) (j := 0) (warpX_e matrixK _) (by decide : 1 < 32)
    (.inl ⟨0, _, _, _, full_get (by decide), by simp⟩)
  rwa [L1_warpLane] at this

theorem witness_exit_matrix :
    Witness L1 (warpX matrixK [⟨0, .exit⟩]) (.thread (1, 0)) (0, 0) := by
  have := witness_of_manual_matrix (L := L1) (j := 0) (warpX_e matrixK [⟨0, .exit⟩])
    (by decide : 1 < 32) (.inr ⟨0, by rw [L1_warpLane]; simp [warpX_one], by
      rw [L1_warpLane]; simp [warpX, isMatrix]⟩)
  rwa [L1_warpLane] at this

theorem blocks_setMaxReg : ¬ Ready L1 (warpX setMaxRegK []) (0, 0) := by
  rw [ready_iff_manual_setMaxReg (warpX_e setMaxRegK _) fun l hl => L1_sameWarp hl]
  intro h
  obtain ⟨j, inst, hg, -⟩ := h _ _ _ _ (warpX_e _ _) 1 (by decide)
  rw [none_one] at hg
  cases hg

theorem ready_setMaxReg : Ready L1 (warpX setMaxRegK [⟨0, setMaxRegK⟩]) (0, 0) := by
  rw [ready_iff_manual_setMaxReg (warpX_e setMaxRegK _) fun l hl => L1_sameWarp hl]
  intro pc inc n inst he l hl
  rw [warpX_e] at he
  cases he
  exact ⟨0, 0, full_get hl, by simp [SetMaxNReg.ordinal]⟩

theorem witness_other_setMaxReg :
    Witness L1 (warpX setMaxRegK [⟨0, setMaxRegK⟩]) (.thread (1, 0)) (0, 0) := by
  have := witness_of_manual_setMaxReg (L := L1) (j := 0) (warpX_e setMaxRegK _)
    (by decide : 1 < 32) (L1_sameWarp (by decide)) (full_get (by decide))
    (by simp [SetMaxNReg.ordinal])
  rwa [L1_warpLane] at this

theorem tc_blocks {k : TcKind} : ¬ ManualWait.tc L1 (warpX (.tc k) []) (0, 0) := by
  intro h
  obtain ⟨j, ev, hg, -⟩ := h 1 (by rw [L1_warpSize]; decide)
  rw [none_one] at hg
  cases hg

theorem tc_full {k : TcKind} (hk : isTcColl ⟨0, .tc k⟩ = true) :
    ManualWait.tc L1 (warpX (.tc k) [⟨0, .tc k⟩]) (0, 0) := by
  intro l hl
  rw [L1_warpSize] at hl
  exact ⟨0, _, full_get hl, hk, by simp⟩

theorem tc_other {k : TcKind} (hk : TcLane k) (hc : isTcColl ⟨0, .tc k⟩ = true) :
    Witness L1 (warpX (.tc k) [⟨0, .tc k⟩]) (.thread (1, 0)) (0, 0) := by
  have := witness_of_manual_tc (L := L1) (j := 0) (warpX_e (.tc k) _) hk
    (by rw [L1_warpSize]; decide : 1 < warpSize L1 0) (full_get (by decide)) hc (by simp)
  rwa [L1_warpLane] at this

theorem blocks_tcLd : ¬ Ready L1 (warpX tcLdK []) (0, 0) := by
  rw [ready_iff_manual_tc (warpX_e tcLdK _) trivial]; exact tc_blocks

theorem ready_tcLd : Ready L1 (warpX tcLdK [⟨0, tcLdK⟩]) (0, 0) := by
  rw [ready_iff_manual_tc (warpX_e tcLdK _) trivial]; exact tc_full rfl

theorem witness_other_tcLd : Witness L1 (warpX tcLdK [⟨0, tcLdK⟩]) (.thread (1, 0)) (0, 0) :=
  tc_other trivial rfl

theorem blocks_tcSt : ¬ Ready L1 (warpX tcStK []) (0, 0) := by
  rw [ready_iff_manual_tc (warpX_e tcStK _) trivial]; exact tc_blocks

theorem ready_tcSt : Ready L1 (warpX tcStK [⟨0, tcStK⟩]) (0, 0) := by
  rw [ready_iff_manual_tc (warpX_e tcStK _) trivial]; exact tc_full rfl

theorem witness_other_tcSt : Witness L1 (warpX tcStK [⟨0, tcStK⟩]) (.thread (1, 0)) (0, 0) :=
  tc_other trivial rfl

theorem blocks_tcWaitLd : ¬ Ready L1 (warpX tcWaitLdK []) (0, 0) := by
  rw [ready_iff_manual_tc (warpX_e tcWaitLdK _) trivial]; exact tc_blocks

theorem ready_tcWaitLd : Ready L1 (warpX tcWaitLdK [⟨0, tcWaitLdK⟩]) (0, 0) := by
  rw [ready_iff_manual_tc (warpX_e tcWaitLdK _) trivial]; exact tc_full rfl

theorem witness_other_tcWaitLd :
    Witness L1 (warpX tcWaitLdK [⟨0, tcWaitLdK⟩]) (.thread (1, 0)) (0, 0) :=
  tc_other trivial rfl

theorem blocks_tcWaitSt : ¬ Ready L1 (warpX tcWaitStK []) (0, 0) := by
  rw [ready_iff_manual_tc (warpX_e tcWaitStK _) trivial]; exact tc_blocks

theorem ready_tcWaitSt : Ready L1 (warpX tcWaitStK [⟨0, tcWaitStK⟩]) (0, 0) := by
  rw [ready_iff_manual_tc (warpX_e tcWaitStK _) trivial]; exact tc_full rfl

theorem witness_other_tcWaitSt :
    Witness L1 (warpX tcWaitStK [⟨0, tcWaitStK⟩]) (.thread (1, 0)) (0, 0) :=
  tc_other trivial rfl

end WarpExamples

/-! ## Non-vacuity: Tensor Memory allocation management -/

section ResourceExamples

abbrev allocK : Kind := .tc (.resource .one none (.alloc 32))

/-- The warp request of warp 0 of CTA `cta`, each lane at its first event. -/
def warpReq (cta : Nat) : Tmem.Pair.WarpRequest :=
  { cta, warp := 0, indices := fun _ => 0, pc := 0, dst := none, request := .alloc 32 }

/-- The allocations of warp 0 of CTA 0 (`cta_group::1`), recorded as performed. -/
def resX (other : List Event) : Execution :=
  { warpX allocK other with
    tmemHistory := fun c => if c = 0 then [⟨warpReq 0, .one, .alloc 32 0⟩] else [] }

theorem resX_get (other : List Event) (e : EvId) :
    (resX other).get e = (warpX allocK other).get e := rfl

theorem resX_tc (other : List Event) :
    ManualWait.tc L1 (resX other) (0, 0) ↔ ManualWait.tc L1 (warpX allocK other) (0, 0) :=
  Iff.rfl

theorem blocks_alloc : ¬ Ready L1 (resX []) (0, 0) := by
  rw [ready_iff_manual_alloc (by rw [resX_get]; exact warpX_e allocK [])]
  intro h
  exact tc_blocks ((resX_tc []).mp (h _ _ _ _ (by rw [resX_get]; exact warpX_e allocK [])).1.1)

theorem ready_alloc : Ready L1 (resX [⟨0, allocK⟩]) (0, 0) := by
  rw [ready_iff_manual_alloc (by rw [resX_get]; exact warpX_e allocK _)]
  intro pc group dst request he
  rw [resX_get, warpX_e] at he
  cases he
  have hmem : (⟨warpReq 0, .one, .alloc 32 0⟩ : Tmem.Pair.Requests) ∈
      (resX [⟨0, allocK⟩]).tmemHistory 0 := by simp [resX]
  have hp : Tmem.Pair.Participates L1 (warpReq 0) (0, 0) := ⟨0, by simp [warpReq,
    Tmem.Pair.WarpRequest.event, L1]⟩
  refine ⟨⟨(resX_tc _).mpr (tc_full rfl), ⟨0, _, hmem, hp⟩, fun _ => ⟨?_, ?_, ?_⟩⟩, ?_⟩
  · exact ⟨[warpReq 0], .inl ⟨0, _, hmem, rfl, rfl⟩, warpReq 0, by simp, hp⟩
  · intro h; cases h
  · rintro n - j ⟨i, r, d, -, -, -, -, h1, -, -, h4, h5, -⟩
    simp only [resX, L1, Nat.zero_div, ↓reduceIte, List.getElem?_cons, List.getElem?_nil] at h1 h4
    split_ifs at h1 h4
    simp_all
  · intro _ _ hn
    exact (hn rfl).elim

theorem witness_other_alloc : Witness L1 (resX [⟨0, allocK⟩]) (.thread (1, 0)) (0, 0) := by
  have := (witness_of_manual_alloc (L := L1)
    (by rw [resX_get]; exact warpX_e allocK [⟨0, allocK⟩])).1 1 0 _ (by rw [L1_warpSize]; decide)
    (by rw [resX_get]; exact full_get (by decide)) rfl (by simp)
  rwa [L1_warpLane] at this

/-- Two CTAs of one cluster of two. -/
def L2 : Launch := { grid := 2, block := 32, params := fun _ => none, clusterSize := 2 }

abbrev alloc2K : Kind := .tc (.resource .two none (.alloc 32))

/-- Warp 0 of CTA 0 issues a `cta_group::2` allocation; warp 0 of CTA 1 has issued nothing. The
allocator history and the pairing are given as if the operation had completed, so that only the
peer lanes are missing. -/
def peerX : Execution where
  tr g := if g < 32 then [⟨0, alloc2K⟩] else []
  rf _ _ := none
  tmemHistory c := if c = 0 then [⟨warpReq 0, .two, .alloc 32 0⟩] else []
  tmemPairing := [(warpReq 0, warpReq 1)]

/-- A `cta_group::2` allocation whose peer warp has not issued its allocation is not ready, with
the peer-wait choice `tmemPairBlocks` false (the default). -/
theorem alloc_group2_peer_needed :
    peerX.tmemPairBlocks (0, 0) = false ∧ ¬ Ready L2 peerX (0, 0) := by
  have he : peerX.get (0, 0) = some ⟨0, alloc2K⟩ := by simp [Execution.get, peerX]
  refine ⟨rfl, ?_⟩
  rw [ready_iff_manual_alloc he]
  intro h
  obtain ⟨-, -, hw⟩ := (h _ _ _ _ he).1
  obtain ⟨-, hpeer, -⟩ := hw ⟨0, _, _, _, he, trivial⟩
  obtain ⟨q, hq, h1 | h1⟩ := hpeer rfl 0
  · simp only [peerX, List.mem_singleton] at hq
    subst hq
    obtain ⟨ev, hev⟩ := h1.2
    simp [Execution.get, peerX, warpReq, Tmem.Pair.WarpRequest.event, L2] at hev
  · simp only [peerX, List.mem_singleton] at hq
    subst hq
    obtain ⟨lane, hl⟩ := h1.1
    simp [warpReq, Tmem.Pair.WarpRequest.event, L2] at hl

end ResourceExamples

/-! ## Non-vacuity: CTA barriers and cluster barriers -/

section BarrierExamples

/-- One CTA of one warp of two threads. -/
def L4 : Launch := { grid := 1, block := 2, params := fun _ => none }

/-- One CTA of two warps: threads 0 to 31, and thread 32. -/
def L3 : Launch := { grid := 1, block := 33, params := fun _ => none }

theorem L4_warpLane (l : Nat) : warpLane L4 0 l = l := by simp [warpLane, laneOf]

theorem L4_warpSize : warpSize L4 0 = 2 := by simp [warpSize, L4]

theorem L4_cluster : L4.clusterOfCta (0 / L4.block) = 0 := by decide

/-- Two threads of one warp: thread 0 runs `t0`, thread 1 runs `t1`. -/
def twoX (t0 t1 : List Event) : Execution where
  tr g := if g = 0 then t0 else if g = 1 then t1 else []
  rf _ _ := none

theorem twoX_get (t0 t1 : List Event) (g j : Nat) :
    (twoX t0 t1).get (g, j) = if g = 0 then t0[j]? else if g = 1 then t1[j]? else none := by
  simp only [Execution.get, twoX]
  split_ifs <;> simp

abbrev arriveK : Kind := .bar 0 none .arrive
abbrev syncK : Kind := .bar 0 none .sync

/-- The warp record of a barrier arrival of both threads. -/
def pairRec : CtaBarrier.Record EvId := .arrival 0 0 none [(0, (0, 0)), (1, (1, 0))]

/-- Thread 0 arrives with `bar.arrive`; thread 1 runs `t1`; the warp record names both. -/
def arriveX (t1 : List Event) : Execution where
  tr := (twoX [⟨0, arriveK⟩] t1).tr
  rf _ _ := none
  barriers _ := [pairRec]

theorem arriveX_get (t1 : List Event) (g j : Nat) :
    (arriveX t1).get (g, j) = (twoX [⟨0, arriveK⟩] t1).get (g, j) := rfl

theorem arriveX_e (t1 : List Event) : (arriveX t1).get (0, 0) = some ⟨0, arriveK⟩ := by
  simp [arriveX_get, twoX_get]

theorem blocks_barArrive : ¬ Ready L4 (arriveX []) (0, 0) := by
  rw [ready_iff_manual_bar (arriveX_e [])]
  intro h
  obtain ⟨i, r, y, -, -, hy, ⟨ev, hev⟩, -⟩ :=
    (h _ _ _ _ (arriveX_e [])).1 1 (by rw [L4_warpSize]; decide)
  rw [L4_warpLane] at hy
  obtain ⟨g, j⟩ := y
  simp only at hy
  subst hy
  simp [arriveX_get, twoX_get] at hev

theorem pairRec_refs {l : Nat} (hl : l < 2) : (l, 0) ∈ pairRec.refs := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [pairRec, CtaBarrier.Record.refs]

theorem ready_barArrive : Ready L4 (arriveX [⟨0, arriveK⟩]) (0, 0) := by
  rw [ready_iff_manual_bar (arriveX_e _)]
  intro pc id count mode he'
  rw [arriveX_e] at he'
  cases he'
  refine ⟨fun l hl => ?_, fun h => by cases h⟩
  rw [L4_warpSize] at hl
  refine ⟨0, pairRec, (l, 0), rfl, pairRec_refs (by decide), by rw [L4_warpLane], ?_,
    .inl (pairRec_refs hl)⟩
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
    exact ⟨_, by simp [arriveX_get, twoX_get]; rfl⟩

theorem witness_other_barArrive :
    Witness L4 (arriveX [⟨0, arriveK⟩]) (.thread (1, 0)) (0, 0) :=
  (witness_of_manual_bar (arriveX_e _)).1 1 0 pairRec (1, 0) (by rw [L4_warpSize]; decide) rfl
    (pairRec_refs (by decide)) (by rw [L4_warpLane]) ⟨_, by simp [arriveX_get, twoX_get]; rfl⟩
    (.inl (pairRec_refs (by decide)))

/-- Thread 1 exits, then thread 0 performs `k`, whose warp record lists only thread 0. -/
def exitBarX (k : Kind) : Execution where
  tr := (twoX [⟨0, k⟩] [⟨0, .exit⟩]).tr
  rf _ _ := none
  barriers _ := [.exit 1 (1, 0), .arrival 0 0 none [(0, (0, 0))]]

theorem exitBar_witness (id : Nat) (count : Option Nat) (mode : BarMode) :
    Witness L4 (exitBarX (.bar id count mode)) (.thread (1, 0)) (0, 0) := by
  have he : (exitBarX (.bar id count mode)).get (0, 0) = some ⟨0, .bar id count mode⟩ := by
    change (twoX [⟨0, .bar id count mode⟩] [⟨0, .exit⟩]).get (0, 0) = _
    simp [twoX_get]
  exact (witness_of_manual_bar he).1 1 1 _ (1, 0) (by rw [L4_warpSize]; decide) rfl
    (by simp [CtaBarrier.Record.refs]) (by rw [L4_warpLane])
    ⟨⟨0, .exit⟩, by
      change (twoX [⟨0, .bar id count mode⟩] [⟨0, .exit⟩]).get (1, 0) = _; simp [twoX_get]⟩
    (.inr ⟨0, 1, by decide, rfl⟩)

theorem witness_exit_barArrive : Witness L4 (exitBarX arriveK) (.thread (1, 0)) (0, 0) :=
  exitBar_witness _ _ _

theorem witness_exit_barSync : Witness L4 (exitBarX syncK) (.thread (1, 0)) (0, 0) :=
  exitBar_witness _ _ _

/-- The arrival record of warp 0 of `L3` (threads 0 to 31). -/
def w0rec : CtaBarrier.Record EvId := .arrival 0 0 none ((List.range 32).map fun g => (g, (g, 0)))

/-- The arrival record of warp 1 of `L3` (thread 32). -/
def w1rec : CtaBarrier.Record EvId := .arrival 0 1 none [(32, (32, 0))]

/-- Thread 32 (warp 1) performs `bar.sync 0`; with `warp0`, warp 0 does too, and its arrival is
recorded first. -/
def syncX (warp0 : Bool) : Execution where
  tr g := if g = 32 ∨ (warp0 = true ∧ g < 32) then [⟨0, syncK⟩] else []
  rf _ _ := none
  barriers _ := if warp0 then [w0rec, w1rec] else [w1rec]

theorem syncX_e (warp0 : Bool) : (syncX warp0).get (32, 0) = some ⟨0, syncK⟩ := by
  simp [Execution.get, syncX]

theorem L3_warpSize : warpSize L3 32 = 1 := by simp [warpSize, L3]

theorem L3_warpLane : warpLane L3 32 0 = 32 := by simp [warpLane, laneOf, L3]

theorem syncX_key (warp0 : Bool) {key : Nat} (h : CtaBarK L3 (syncX warp0) (32, 0) key) :
    key % 16 = 0 := by
  obtain ⟨-, ⟨count, pc, hb⟩, -⟩ := h
  simp only [Execution.IsBarrier, syncX_e, Option.some.injEq, Event.mk.injEq, Kind.bar.injEq]
    at hb
  exact hb.2.1.symm

theorem syncX_barK : CtaBarK L3 (syncX true) (32, 0) 0 := by
  refine ⟨by decide, ⟨none, 0, syncX_e true⟩, 1, _, 1, none, [(32, (32, 0))], 32, rfl, rfl,
    by simp, by decide, _, rfl⟩

theorem syncX_completes : CtaBarrier.CompletesAt L3.block ((syncX true).barriers (32 / L3.block))
    1 (0 % 16) (0 / 16) :=
  ⟨w1rec, _, _, rfl, rfl, rfl, by decide⟩

theorem syncX_present {y : EvId} {i : Nat} {r : CtaBarrier.Record EvId}
    (h1 : ((syncX true).barriers (32 / L3.block))[i]? = some r) (h2 : y ∈ r.refs) :
    (syncX true).RefPresent (.thread y) := by
  have hr : r = w0rec ∨ r = w1rec := by
    simp only [syncX, ↓reduceIte] at h1
    rcases i with _ | _ | i <;> simp_all
  rcases hr with rfl | rfl
  · simp only [w0rec, CtaBarrier.Record.refs, List.map_map, List.mem_map, List.mem_range,
      Function.comp] at h2
    obtain ⟨g, hg, rfl⟩ := h2
    exact ⟨⟨0, syncK⟩, by simp [Execution.get, syncX, hg]⟩
  · simp only [w1rec, CtaBarrier.Record.refs, List.map_cons, List.map_nil,
      List.mem_singleton] at h2
    subst h2
    exact ⟨_, syncX_e true⟩

theorem blocks_barSync : ¬ Ready L3 (syncX false) (32, 0) := by
  rw [ready_iff_manual_bar (syncX_e false)]
  intro h
  obtain ⟨⟨key, hk, i, r, s, t, hr, hs, ht, hg0, hg1⟩, -⟩ := (h _ _ _ _ (syncX_e false)).2 rfl
  have h16 := syncX_key false hk
  rw [h16] at hg0 hg1
  have hi : i = 0 ∧ r = w1rec := by
    simp only [syncX, Bool.false_eq_true, ↓reduceIte] at hr
    rcases i with _ | i <;> simp_all
  obtain ⟨rfl, rfl⟩ := hi
  have hs0 : s = {} := by
    simp only [CtaBarrier.At, List.take_zero, CtaBarrier.run] at hs
    exact (Except.ok.inj hs).symm
  subst hs0
  have hmap : Except.map (fun t : CtaBarrier.State => (t.slots 0).generation)
      (w1rec.perform L3.block ({} : CtaBarrier.State)) = .ok 0 := rfl
  rw [ht] at hmap
  have : (t.slots 0).generation = 0 := Except.ok.inj hmap
  simp at hg0
  omega

theorem ready_barSync : Ready L3 (syncX true) (32, 0) := by
  rw [ready_iff_manual_bar (syncX_e true)]
  intro pc id count mode he'
  rw [syncX_e] at he'
  cases he'
  refine ⟨fun l hl => ?_, fun _ => ⟨⟨0, syncX_barK, 1, syncX_completes⟩, ?_⟩⟩
  · rw [L3_warpSize] at hl
    obtain rfl : l = 0 := by omega
    refine ⟨1, w1rec, (32, 0), rfl, by simp [w1rec, CtaBarrier.Record.refs], by rw [L3_warpLane],
      ⟨_, syncX_e true⟩, .inl (by simp [w1rec, CtaBarrier.Record.refs])⟩
  · rintro y ⟨-, -, -, -, i, r, h1, h2, -⟩
    exact syncX_present h1 h2

/-- The arrival of thread 0, in the other warp, is a witness of thread 32's `bar.sync`. -/
theorem witness_other_barSync : Witness L3 (syncX true) (.thread (0, 0)) (32, 0) := by
  refine (witness_of_manual_bar (syncX_e true)).2 rfl (0, 0)
    ⟨0, 1, syncX_barK, syncX_completes, 0, w0rec, rfl, by simp [w0rec, CtaBarrier.Record.refs],
      by decide, .inl ⟨0, none, _, {}, rfl, rfl, rfl⟩⟩ ⟨⟨0, syncK⟩, by simp [Execution.get, syncX]⟩

/-- Threads 0 and 1 of `L4` run `t0` and `t1`, and the cluster barrier history is `recs`. -/
def clX (t0 t1 : List Event) (recs : List (ClusterBarrier.Record EvId)) : Execution where
  tr := (twoX t0 t1).tr
  rf _ _ := none
  clusters _ := recs

theorem clX_get (t0 t1 : List Event) (recs : List (ClusterBarrier.Record EvId)) (e : EvId) :
    (clX t0 t1 recs).get e = (twoX t0 t1).get e := rfl

/-- A cluster barrier event whose warp condition holds and whose history names only present
events is ready. -/
theorem cl_ready {t0 t1 : List Event} {recs : List (ClusterBarrier.Record EvId)} {e : EvId}
    {pc : Nat} {op : ClusterOp} (he : (clX t0 t1 recs).get e = some ⟨pc, .cluster op⟩)
    (hw : ManualWait.clusterWarp L4 (clX t0 t1 recs) e)
    (hrefs : ∀ y ∈ recs.flatMap ClusterBarrier.Record.refs,
      (clX t0 t1 recs).RefPresent (.thread y)) : Ready L4 (clX t0 t1 recs) e := by
  rw [ready_iff_manual_cluster he]
  intro pc' op' he'
  rw [he] at he'
  cases he'
  exact ⟨hw, fun _ _ y hy => hrefs y (clusterCounted_mem hy)⟩

abbrev clArriveK : Kind := .cluster (.arrive true true)
abbrev clWaitK : Kind := .cluster (.wait true)

/-- The arrival record of both threads. -/
def clArr : ClusterBarrier.Record EvId := .arrival 0 0 true [(0, (0, 0)), (1, (1, 0))]

/-- The wait record of both threads. -/
def clWait : ClusterBarrier.Record EvId := .wait 0 0 [(0, (0, 1)), (1, (1, 1))]

theorem blocks_clusterArrive : ¬ Ready L4 (clX [⟨0, clArriveK⟩] [] [clArr]) (0, 0) := by
  have he : (clX [⟨0, clArriveK⟩] [] [clArr]).get (0, 0) = some ⟨0, clArriveK⟩ := by
    simp [clX_get, twoX_get]
  rw [ready_iff_manual_cluster he]
  intro h
  obtain ⟨i, r, ⟨g, j⟩, -, -, hy, ⟨ev, hev⟩, -⟩ :=
    (h _ _ he).1 1 (by rw [L4_warpSize]; decide)
  rw [L4_warpLane] at hy
  simp only at hy
  subst hy
  simp [clX_get, twoX_get] at hev

theorem ready_clusterArrive :
    Ready L4 (clX [⟨0, clArriveK⟩] [⟨0, clArriveK⟩] [clArr]) (0, 0) := by
  refine cl_ready (pc := 0) (op := .arrive true true) (by simp [clX_get, twoX_get])
    (fun l hl => ?_) ?_
  · rw [L4_warpSize] at hl
    refine ⟨0, clArr, (l, 0), rfl, by simp [clArr, ClusterBarrier.Record.refs],
      by rw [L4_warpLane], ?_, .inl ?_⟩ <;>
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
      simp [clX_get, twoX_get, clArr, ClusterBarrier.Record.refs, Execution.RefPresent]
  · simp [clArr, ClusterBarrier.Record.refs, clX_get, twoX_get, Execution.RefPresent]

theorem witness_other_clusterArrive :
    Witness L4 (clX [⟨0, clArriveK⟩] [⟨0, clArriveK⟩] [clArr]) (.thread (1, 0)) (0, 0) :=
  (witness_of_manual_cluster (pc := 0) (op := .arrive true true)
    (by simp [clX_get, twoX_get])).1 1 0 clArr (1, 0)
    (by rw [L4_warpSize]; decide) rfl (by simp [clArr, ClusterBarrier.Record.refs])
    (by rw [L4_warpLane]) ⟨⟨0, clArriveK⟩, by simp [clX_get, twoX_get]⟩
    (.inl (by simp [clArr, ClusterBarrier.Record.refs]))

/-- Thread 1 exits, then thread 0 arrives and waits alone. -/
def clExitRecs : List (ClusterBarrier.Record EvId) :=
  [.exit 1 (1, 0), .arrival 0 0 true [(0, (0, 0))], .wait 0 0 [(0, (0, 1))]]

theorem witness_exit_clusterArrive :
    Witness L4 (clX [⟨0, clArriveK⟩, ⟨1, clWaitK⟩] [⟨0, .exit⟩] clExitRecs) (.thread (1, 0))
      (0, 0) :=
  (witness_of_manual_cluster (pc := 0) (op := .arrive true true)
    (by simp [clX_get, twoX_get])).1 1 1 _ (1, 0)
    (by rw [L4_warpSize]; decide) rfl (by simp [ClusterBarrier.Record.refs])
    (by rw [L4_warpLane]) ⟨⟨0, .exit⟩, by simp [clX_get, twoX_get]⟩ (.inr ⟨0, 1, by decide, rfl⟩)

theorem blocks_clusterWait :
    ¬ Ready L4 (clX [⟨0, clArriveK⟩, ⟨1, clWaitK⟩] [] [clArr, clWait]) (0, 1) := by
  have he : (clX [⟨0, clArriveK⟩, ⟨1, clWaitK⟩] [] [clArr, clWait]).get (0, 1) =
      some ⟨1, clWaitK⟩ := by simp [clX_get, twoX_get]
  rw [ready_iff_manual_cluster he]
  intro h
  obtain ⟨i, r, ⟨g, j⟩, -, -, hy, ⟨ev, hev⟩, -⟩ :=
    (h _ _ he).1 1 (by rw [L4_warpSize]; decide)
  rw [L4_warpLane] at hy
  simp only at hy
  subst hy
  simp [clX_get, twoX_get] at hev

theorem ready_clusterWait :
    Ready L4 (clX [⟨0, clArriveK⟩, ⟨1, clWaitK⟩] [⟨0, clArriveK⟩, ⟨1, clWaitK⟩] [clArr, clWait])
      (0, 1) := by
  refine cl_ready (pc := 1) (op := .wait true) (by simp [clX_get, twoX_get])
    (fun l hl => ?_) ?_
  · rw [L4_warpSize] at hl
    refine ⟨1, clWait, (l, 1), rfl, by simp [clWait, ClusterBarrier.Record.refs],
      by rw [L4_warpLane], ?_, .inl ?_⟩ <;>
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
      simp [clX_get, twoX_get, clWait, ClusterBarrier.Record.refs, Execution.RefPresent]
  · simp [clArr, clWait, ClusterBarrier.Record.refs, clX_get, twoX_get, Execution.RefPresent]

theorem witness_other_clusterWait :
    Witness L4 (clX [⟨0, clArriveK⟩, ⟨1, clWaitK⟩] [⟨0, clArriveK⟩, ⟨1, clWaitK⟩]
      [clArr, clWait]) (.thread (1, 1)) (0, 1) :=
  (witness_of_manual_cluster (pc := 1) (op := .wait true)
    (by simp [clX_get, twoX_get])).1 1 1 clWait (1, 1)
    (by rw [L4_warpSize]; decide) rfl (by simp [clWait, ClusterBarrier.Record.refs])
    (by rw [L4_warpLane]) ⟨⟨1, clWaitK⟩, by simp [clX_get, twoX_get]⟩
    (.inl (by simp [clWait, ClusterBarrier.Record.refs]))

theorem witness_exit_clusterWait :
    Witness L4 (clX [⟨0, clArriveK⟩, ⟨1, clWaitK⟩] [⟨0, .exit⟩] clExitRecs) (.thread (1, 0))
      (0, 1) :=
  (witness_of_manual_cluster (pc := 1) (op := .wait true)
    (by simp [clX_get, twoX_get])).1 1 2 _ (1, 0)
    (by rw [L4_warpSize]; decide) rfl (by simp [ClusterBarrier.Record.refs])
    (by rw [L4_warpLane]) ⟨⟨0, .exit⟩, by simp [clX_get, twoX_get]⟩ (.inr ⟨0, 1, by decide, rfl⟩)

end BarrierExamples

/-! ## Non-vacuity: group waits

Thread 0 issues one copy, commits its group and waits for every committed group. The copy's read
and write stages are present when `rd` and `wr` are true. -/

section GroupExamples

/-- A copy of 4 bytes from global to shared memory whose completion is `c`. -/
def cpSpec (c : AsyncCopy.Completion) : AsyncCopy.Spec :=
  { src := { loc := ⟨.global, 0, 0⟩, size := 4 }, dst := { loc := ⟨.shared, 0, 0⟩, size := 4 },
    completion := c, generic := true }

/-- Thread 0 runs `copy; commit; wait`; the copy's stages are present as `rd` and `wr` say. -/
def groupX (c : AsyncCopy.Completion) (commit wait : Kind) (rd wr : Bool) : Execution where
  tr g := if g = 0 then [⟨0, .copy (cpSpec c)⟩, ⟨1, commit⟩, ⟨2, wait⟩] else []
  rf _ _ := none
  async := { copies := fun _ =>
    { readBytes := if rd then some [] else none, writeBytes := if wr then some [] else none } }

theorem groupX_wait (c : AsyncCopy.Completion) (commit wait : Kind) (rd wr : Bool) :
    (groupX c commit wait rd wr).get (0, 2) = some ⟨2, wait⟩ := by
  simp [Execution.get, groupX]

abbrev bulkWaitK : Kind := .bulkWait .full 0
abbrev asyncWaitK : Kind := .asyncWait 0

/-- The bulk execution with the read stage present as `rd` and the write stage as `wr`. -/
abbrev bulkX (rd wr : Bool) : Execution := groupX .bulkGroup .bulkCommit bulkWaitK rd wr

/-- The `cp.async` execution with the read stage present as `rd` and the write stage as `wr`. -/
abbrev asyncX (rd wr : Bool) : Execution := groupX .asyncGroup .asyncCommit asyncWaitK rd wr

theorem bulk_observes (rd wr : Bool) :
    BulkGroup.Observes (bulkStateBefore (bulkX rd wr) (0, 2)) 0 (0, 0) := by
  simp [BulkGroup.Observes, BulkGroup.required, BulkGroup.run, bulkStateBefore, bulkActions,
    groupX, cpSpec, bulkAction, BulkGroup.step, List.zipIdx]

theorem async_observes (rd wr : Bool) :
    BulkGroup.Observes (asyncStateBefore (asyncX rd wr) (0, 2)) 0 (0, 0) := by
  simp [BulkGroup.Observes, BulkGroup.required, BulkGroup.run, asyncStateBefore, asyncActions,
    groupX, cpSpec, asyncAction, BulkGroup.step, List.zipIdx]

/-- The only operation a wait of these executions observes is the copy `(0, 0)`. -/
theorem bulk_observes_only {rd wr : Bool} {i : EvId}
    (h : BulkGroup.Observes (bulkStateBefore (bulkX rd wr) (0, 2)) 0 i) : i = (0, 0) := by
  simpa [BulkGroup.Observes, BulkGroup.required, BulkGroup.run, bulkStateBefore, bulkActions,
    groupX, cpSpec, bulkAction, BulkGroup.step, List.zipIdx] using h

theorem async_observes_only {rd wr : Bool} {i : EvId}
    (h : BulkGroup.Observes (asyncStateBefore (asyncX rd wr) (0, 2)) 0 i) : i = (0, 0) := by
  simpa [BulkGroup.Observes, BulkGroup.required, BulkGroup.run, asyncStateBefore, asyncActions,
    groupX, cpSpec, asyncAction, BulkGroup.step, List.zipIdx] using h

/-- A `cp.async.bulk.wait_group 0` whose committed copy has not written its destination is not
ready. -/
theorem blocks_bulkWait : ¬ Ready L1 (bulkX true false) (0, 2) := by
  rw [ready_iff_manual_bulkWait (groupX_wait ..)]
  intro h
  have := (h _ _ _ (groupX_wait ..) _ (bulk_observes _ _)).2
  simp [ManualWait.bulkCompletion, Execution.get, groupX, Execution.AsyncPresent] at this

theorem ready_bulkWait : Ready L1 (bulkX true true) (0, 2) := by
  rw [ready_iff_manual_bulkWait (groupX_wait ..)]
  intro pc mode remaining he i hi
  rw [groupX_wait] at he
  cases he
  obtain rfl := bulk_observes_only hi
  simp [BulkGroup.Done, ManualWait.bulkCompletion, Execution.get, groupX,
    Execution.AsyncPresent]

/-- The read stage of the covered copy is a witness of the wait. -/
theorem witness_other_bulkWait :
    Witness L1 (bulkX true true) (.async (0, 0) (.read .copy)) (0, 2) :=
  witness_of_manual_bulkWait (groupX_wait ..) (bulk_observes _ _)
    (by simp [GroupWaitStages, Execution.get, groupX]) (by simp [Execution.AsyncPresent, groupX])

/-- A `cp.async.wait_group 0` whose committed copy has not written its destination is not
ready. -/
theorem blocks_asyncWait : ¬ Ready L1 (asyncX true false) (0, 2) := by
  rw [ready_iff_manual_asyncWait (groupX_wait ..)]
  intro h
  have := (h _ _ (groupX_wait ..) _ (async_observes _ _)).2
  simp [ManualWait.asyncCompletion, Execution.AsyncPresent, groupX] at this

theorem ready_asyncWait : Ready L1 (asyncX true true) (0, 2) := by
  rw [ready_iff_manual_asyncWait (groupX_wait ..)]
  intro pc remaining he i hi
  rw [groupX_wait] at he
  cases he
  obtain rfl := async_observes_only hi
  simp [BulkGroup.Done, ManualWait.asyncCompletion, Execution.AsyncPresent, groupX]

/-- The read stage of the covered copy is a witness of the wait. -/
theorem witness_other_asyncWait :
    Witness L1 (asyncX true true) (.async (0, 0) (.read .copy)) (0, 2) :=
  witness_of_manual_asyncWait (groupX_wait ..) (async_observes _ _) (.inl rfl)
    (by simp [Execution.AsyncPresent, groupX])

end GroupExamples

/-! ## Non-vacuity: the successful poll

Thread 1 arrives on the mbarrier at `mbarLoc` and thread 0 polls it successfully, observing the
phase that the arrival completed. A successful poll needs each counter update of the phase it
observed (`pollNeeds`), and `MbarObserved` requires that update to be present, so the needs of a
successful poll are always filled: `Ready` of a poll is never false. What a poll depends on is
carried by its witnesses, which the dependency order places before its return. `blocks_wait`
states that edge: the observed arrival precedes the return of the poll. -/

section PollExamples

def mbarLoc : Loc := ⟨.shared, 0, 0⟩

abbrev pollK : Kind := .wait mbarLoc 0 true false .cta
abbrev mbArriveK : Kind := .arrive mbarLoc 0 1 false .cta

/-- An object state in phase 0 with one arrival pending. -/
def st0 : MBarrier.State := { phase := 0, expected := 1, pending := 1, tx := 0, observed := true }

/-- The object history: an initialization, thread 1's arrival in phase 0, and thread 0's
successful poll observing phase 0. -/
def pollLog : List (MBarrier.Record AsyncCopy.Ref) :=
  [{ id := .thread (2, 0), action := .init 1, reply := { state := some st0 } },
   { id := .thread (1, 0), action := .arrive 1,
     reply := { state := some { st0 with phase := 1 } } },
   { id := .thread (0, 0), action := .pollParity 0 true,
     reply := { state := some { st0 with phase := 1 }, waited := some true, completed := some 0 } }]

/-- Thread 0 polls the object; thread 1 runs `t1`. -/
def pollX (t1 : List Event) : Execution where
  tr g := if g = 0 then [⟨0, pollK⟩] else if g = 1 then t1 else []
  rf _ _ := none
  objects m := if m = mbarLoc then pollLog else []

theorem pollX_e (t1 : List Event) : (pollX t1).get (0, 0) = some ⟨0, pollK⟩ := by
  simp [Execution.get, pollX]

theorem pollX_observed :
    MbarObserved (pollX [⟨0, mbArriveK⟩]) (.thread (1, 0)) (.thread (0, 0)) := by
  refine ⟨⟨⟨0, mbArriveK⟩, by simp [Execution.get, pollX]⟩, (0, 0), mbarLoc, false, .cta, rfl,
    ⟨⟨0, 0, pollX_e _⟩, 1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      ?_⟩, ?_⟩
  · intro k s h1 h2
    omega
  · intro r hr hid
    simp only [pollX, ↓reduceIte, pollLog, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp_all [CounterUpdate]

theorem pollLog_mem : (pollLog[1]'(by decide)) ∈ (pollX [⟨0, mbArriveK⟩]).objects mbarLoc := by
  simp [pollX, pollLog]

/-- The arrival that the successful poll observed precedes the poll's return in the dependency
order. -/
theorem blocks_wait (K : Kernel) :
    DepStep L1 K (pollX [⟨0, mbArriveK⟩]) (.thread (1, 0), false) (.thread (0, 0), true) :=
  DepStep.of_witness L1 (witness_of_manual_wait (pollX_e _) pollLog_mem pollX_observed)

theorem ready_wait : Ready L1 (pollX [⟨0, mbArriveK⟩]) (0, 0) := by
  rw [ready_iff_manual_wait (pollX_e _)]
  intro pc m q acq sc he r hr ho
  exact ho.1

/-- The observed arrival of the other thread is a witness of the successful poll. -/
theorem witness_other_wait : Witness L1 (pollX [⟨0, mbArriveK⟩]) (.thread (1, 0)) (0, 0) :=
  witness_of_manual_wait (pollX_e _) pollLog_mem pollX_observed

end PollExamples

/-! ## Observing dependency: canonical spins and unsafe poll shapes

Each kernel is a list of instructions; the predicates of DEP-CANONICAL-SPIN and ERR-POLL-SHAPE are
evaluated on it. Register 0 is the poll predicate and register 1 holds the address of the polled
object. -/

section PollShapes

/-- `mbarrier.try_wait.parity.relaxed.cta.shared::cta.b64 p, [base + off], 0`. -/
def pollI (p base : Nat) (off : Int) : Instr := { op := .mbarWait p base off (.imm 0) false .cta }
/-- `mbarrier.arrive.relaxed.cta.shared::cta.b64 _, [base + off]`. -/
def arriveI (base : Nat) (off : Int) : Instr :=
  { op := .mbarArrive base off (.imm 0) (.imm 1) false false .cta }
def braI (t : Nat) : Instr := { op := .bra t false }
/-- `@p bra t` (`neg` false) or `@!p bra t` (`neg` true). -/
def braIf (p : Nat) (neg : Bool) (t : Nat) : Instr := { guard := some (p, neg), op := .bra t false }
def exitI : Instr := { op := .exit }

/-- Thread 0 performs a poll at position `pc` with result `ok`, then an arrival at position
`next`. -/
def spinX (pc next : Nat) (ok : Bool) : Execution where
  tr g := if g = 0 then [⟨pc, .wait mbarLoc 0 ok false .cta⟩, ⟨next, mbArriveK⟩] else []
  rf _ _ := none

theorem spinX_poll {pc next : Nat} {ok : Bool} {e : EvId} {pc' : Nat} {m : Loc} {q : Nat}
    {ok' acq : Bool} {sc : MbarScope}
    (he : (spinX pc next ok).get e = some ⟨pc', .wait m q ok' acq sc⟩) : pc' = pc := by
  obtain ⟨g, j⟩ := e
  simp only [Execution.get, spinX] at he
  split_ifs at he
  · rcases j with _ | _ | j <;> simp_all
  · simp at he

/-- Every poll of `spinX pc` is at position `pc`; when that position is a canonical spin, no poll
of the execution has an unsafe shape. -/
theorem spinX_safe {K : Kernel} {pc next ex : Nat} {ok : Bool} (hs : K.CanonicalSpin pc ex) :
    ¬ PollShapeUnsafe K (spinX pc next ok) := by
  rintro ⟨e, pc', m, q, ok', acq, sc, he, h1, -⟩
  obtain rfl := spinX_poll he
  exact h1 ⟨ex, hs⟩

/-- The arrival of `spinX` follows the successful poll in thread 0. -/
theorem spinX_before (pc next : Nat) : TraceBefore (spinX pc next true) (0, 0) (0, 1) := by
  simp [TraceBefore, spinX]

/-- Shape A: `L: poll p; @p bra D; bra L; D: arrive`. -/
def shapeACode : Kernel where
  name := "shapeA"
  params := []
  code := [pollI 0 1 0, braIf 0 false 3, braI 0, arriveI 1 8, exitI]

/-- Shape B: `L: poll p; @!p bra L; arrive`. -/
def shapeBCode : Kernel where
  name := "shapeB"
  params := []
  code := [pollI 0 1 0, braIf 0 true 0, arriveI 1 8, exitI]

/-- Shape A is a canonical spin exiting to position 3; an execution with its poll is safe, and the
arrival after the exit depends on the successful poll. -/
theorem spin_shape_A :
    shapeACode.CanonicalSpin 0 3 ∧ ¬ PollShapeUnsafe shapeACode (spinX 0 3 true) ∧
    Resumes shapeACode (spinX 0 3 true) (0, 0) (0, 1) := by
  have hs : shapeACode.CanonicalSpin 0 3 := ⟨rfl, 0, rfl, rfl⟩
  refine ⟨hs, spinX_safe hs, spinX_before 0 3, ?_⟩
  simp only [Execution.get, spinX, ↓reduceIte, List.getElem?_cons_zero, Option.map_some,
    Kind.resume]
  exact ⟨0, 3, mbarLoc, 0, false, .cta, by simp [Execution.get], hs, spinX_before 0 3⟩

/-- Shape B is a canonical spin exiting to position 2; an execution with its poll is safe, and the
arrival after the exit depends on the successful poll. -/
theorem spin_shape_B :
    shapeBCode.CanonicalSpin 0 2 ∧ ¬ PollShapeUnsafe shapeBCode (spinX 0 2 true) ∧
    Resumes shapeBCode (spinX 0 2 true) (0, 0) (0, 1) := by
  have hs : shapeBCode.CanonicalSpin 0 2 := ⟨rfl, 0, rfl, rfl⟩
  refine ⟨hs, spinX_safe hs, spinX_before 0 2, ?_⟩
  simp only [Execution.get, spinX, ↓reduceIte, List.getElem?_cons_zero, Option.map_some,
    Kind.resume]
  exact ⟨0, 2, mbarLoc, 0, false, .cta, by simp [Execution.get], hs, spinX_before 0 2⟩

/-- A single poll whose result no instruction reads, followed by an arrival. -/
def unusedCode : Kernel where
  name := "unused"
  params := []
  code := [pollI 0 1 0, arriveI 1 8, exitI]

/-- The unused poll is safe, and even when it succeeds the later arrival does not depend on it. -/
theorem poll_unused : unusedCode.PollUnused 0 ∧ ¬ PollShapeUnsafe unusedCode (spinX 0 1 true) ∧
    ¬ Resumes unusedCode (spinX 0 1 true) (0, 0) (0, 1) := by
  have hn : ¬ ∃ ex, unusedCode.CanonicalSpin 0 ex := by
    rintro ⟨ex, hsh, -⟩
    simp [Kernel.SpinShape] at hsh
    cases hsh
  have hu : unusedCode.PollUnused 0 := ⟨⟨0, rfl, rfl⟩, hn⟩
  refine ⟨hu, ?_, ?_⟩
  · rintro ⟨e, pc', m, q, ok', acq, sc, he, -, h2⟩
    obtain rfl := spinX_poll he
    exact h2 hu
  · rintro ⟨-, hr⟩
    simp only [Execution.get, spinX, ↓reduceIte, List.getElem?_cons_zero, Option.map_some,
      Kind.resume] at hr
    obtain ⟨pc, ex, m, q, acq, sc, hw, hs, -⟩ := hr
    obtain rfl : pc = 0 := by simp [Execution.get] at hw; exact hw.1.symm
    exact hn ⟨ex, hs⟩

/-- A poll at a position whose predicate some instruction reads other than as the branch of a
canonical spin is neither a canonical spin nor unused, so every execution containing it is
unsafe. -/
theorem pollShapeUnsafe_of {K : Kernel} {X : Execution} {e : EvId} {pc q p : Nat} {m : Loc}
    {ok acq : Bool} {sc : MbarScope} (he : X.get e = some ⟨pc, .wait m q ok acq sc⟩)
    (hreg : K.pollReg pc = some p) (hdst : K.pollDst pc = none ∨ K.pollDst pc = some p)
    (hsp : K.spinPred p = false) : PollShapeUnsafe K X := by
  refine ⟨e, pc, m, q, ok, acq, sc, he, ?_, ?_⟩
  · rintro ⟨ex, -, p', hp', hs⟩
    rcases hdst with h | h <;> rw [h] at hp' <;> cases hp'
    exact absurd hs (by simp [Kernel.SpinPred, hsp])
  · rintro ⟨⟨p', hp', hs⟩, -⟩
    rw [hreg] at hp'
    cases hp'
    exact absurd hs (by simp [Kernel.SpinPred, hsp])

/-- A loop that polls two objects and leaves when either poll succeeds. -/
def multiCode : Kernel where
  name := "multi"
  params := []
  code := [pollI 0 1 0, braIf 0 false 5, pollI 0 1 8, braIf 0 false 5, braI 0,
    arriveI 1 16, exitI]

theorem poll_shape_unsafe_multi : PollShapeUnsafe multiCode (spinX 0 5 false) :=
  pollShapeUnsafe_of (e := (0, 0)) rfl rfl (.inr rfl) rfl

/-- `outer: i = 0; saved = false; inner: first = (i == 0); addr = first ? A : C; poll(addr) -> p;
@first mov saved, p; i++; if i < 2 goto inner; if !saved goto outer; arrive B`. Registers: 0 the
poll predicate, 2 the address, 3 and 4 the addresses of `A` and `C`, 5 the address of `B`, 6 the
counter, 7 `saved`, 8 `first`, 9 the loop condition. -/
def savedCode : Kernel where
  name := "saved"
  params := []
  code := [{ op := .move ⟨.scalar, .int .u 32, [some 6], [.imm 0]⟩ },
    { op := .move ⟨.scalar, .pred, [some 7], [.imm 0]⟩ },
    { op := .int ⟨.setp .eq none, .int .u 32, false, [some 8], [.reg 6, .imm 0]⟩ },
    { op := .int ⟨.selp, .int .u 32, false, [some 2], [.reg 3, .reg 4, .reg 8]⟩ },
    pollI 0 2 0,
    { guard := some (8, false), op := .move ⟨.scalar, .pred, [some 7], [.reg 0]⟩ },
    { op := .int ⟨.add, .int .u 32, false, [some 6], [.reg 6, .imm 1]⟩ },
    { op := .int ⟨.setp .lt none, .int .u 32, false, [some 9], [.reg 6, .imm 2]⟩ },
    braIf 9 false 2, braIf 7 true 0, arriveI 5 0, exitI]

theorem poll_shape_unsafe_saved : PollShapeUnsafe savedCode (spinX 4 10 true) :=
  pollShapeUnsafe_of (e := (0, 0)) rfl rfl (.inr rfl) rfl

/-- `loop: q = true; test_wait A -> p; @p test_wait C -> q; @q bra loop; arrive B`. Registers: 0
is `p`, 1 is `q`, 2, 3 and 4 hold the addresses of `A`, `C` and `B`. -/
def chainCode : Kernel where
  name := "chain"
  params := []
  code := [{ op := .move ⟨.scalar, .pred, [some 1], [.imm 1]⟩ }, pollI 0 2 0,
    { guard := some (0, false), op := .mbarWait 1 3 0 (.imm 0) false .cta }, braIf 1 false 0,
    arriveI 4 0, exitI]

/-- Both polls of the guarded chain are unsafe: the first, whose result guards the second, and the
guarded second poll. -/
theorem poll_shape_unsafe_guarded_chain :
    PollShapeUnsafe chainCode (spinX 1 4 true) ∧ PollShapeUnsafe chainCode (spinX 2 4 false) :=
  ⟨pollShapeUnsafe_of (e := (0, 0)) rfl rfl (.inr rfl) rfl,
    pollShapeUnsafe_of (e := (0, 0)) rfl rfl (.inl rfl) rfl⟩

/-- `poll p; selp r2, r3, r4, p; arrive [r2]`. -/
def selpCode : Kernel where
  name := "selp"
  params := []
  code := [pollI 0 1 0,
    { op := .int ⟨.selp, .int .u 32, false, [some 2], [.reg 3, .reg 4, .reg 0]⟩ },
    arriveI 2 0, exitI]

theorem poll_shape_unsafe_selp : PollShapeUnsafe selpCode (spinX 0 2 true) :=
  pollShapeUnsafe_of (e := (0, 0)) rfl rfl (.inr rfl) rfl

/-- One poll whose result a branch reads, both arms executing the same arrival. -/
def singleBranchCode : Kernel where
  name := "singleBranch"
  params := []
  code := [pollI 0 1 0, braIf 0 false 4, arriveI 1 8, braI 5, arriveI 1 8, exitI]

theorem poll_shape_unsafe_single_branch : PollShapeUnsafe singleBranchCode (spinX 0 4 true) :=
  pollShapeUnsafe_of (e := (0, 0)) rfl rfl (.inr rfl) rfl

/-- Nested retry loops: `L0: poll p; @p bra D; L1: poll p; @!p bra L1; bra L0; D: arrive`. -/
def nestedCode : Kernel where
  name := "nested"
  params := []
  code := [pollI 0 1 0, braIf 0 false 5, pollI 0 1 0, braIf 0 true 2, braI 0, arriveI 1 8, exitI]

/-- The inner loop has the shape of a spin, but the outer branch reads its predicate, so the inner
poll is no canonical spin and an execution with it is unsafe. -/
theorem poll_shape_unsafe_nested :
    nestedCode.SpinShape 2 4 ∧ PollShapeUnsafe nestedCode (spinX 2 5 true) :=
  ⟨rfl, pollShapeUnsafe_of (e := (0, 0)) rfl rfl (.inr rfl) rfl⟩

/-- A loop whose success branch returns to the poll: `L: poll p; @p bra L; bra L; arrive`. -/
def selfExitCode : Kernel where
  name := "selfExit"
  params := []
  code := [pollI 0 1 0, braIf 0 false 0, braI 0, arriveI 1 8, exitI]

/-- A loop whose success branch targets the second branch of the loop:
`L: poll p; @p bra B; B: bra L; arrive`. -/
def innerExitCode : Kernel where
  name := "innerExit"
  params := []
  code := [pollI 0 1 0, braIf 0 false 2, braI 0, arriveI 1 8, exitI]

/-- A shape-A loop whose exit target is the poll or lies inside the loop is no canonical spin,
because a successful poll does not leave the loop; an execution with such a poll is unsafe. -/
theorem poll_shape_unsafe_exit_in_loop :
    selfExitCode.spinExit? 0 = none ∧ PollShapeUnsafe selfExitCode (spinX 0 3 true) ∧
      innerExitCode.spinExit? 0 = none ∧ PollShapeUnsafe innerExitCode (spinX 0 3 true) :=
  ⟨rfl, pollShapeUnsafe_of (e := (0, 0)) rfl rfl (.inr rfl) rfl,
    rfl, pollShapeUnsafe_of (e := (0, 0)) rfl rfl (.inr rfl) rfl⟩

end PollShapes

end

end PTX.Tests.DependencyCoverage
