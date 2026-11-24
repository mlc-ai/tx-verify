-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution

/-! The waiting dependency of the warp collectives that pair lanes by order (DEP-WARP-INSTANCE,
`MaskWait`, `maskNeeds`, DEP-ORDER).

Opposite orders: in a warp of 32 threads, lane 0 executes `vote.sync.all.pred` and then
`redux.sync.add.u32`, lane 1 executes the same two instructions in the other order, both with member
mask 3, and both lanes then exit. On hardware each lane waits at its first instruction for the
other lane, which never arrives there. Whatever results the events carry, the dependency order of
these traces has a cycle: two `Witness` steps (the needs of `maskNeeds` filled through `MaskWait`)
and two `Resumes` steps. `DependencyOk.acyclic` fails (`cross_not_dependencyOk`), so no execution
with these traces is consistent (`cross_not_consistent`): the complete execution in which the votes
form one instance and the reductions another is excluded, and progress cannot be proved for such a
program.

Exit: lane 0 executes `vote.sync` and exits, lane 1 executes `redux.sync` and exits, both with
member mask 3. On hardware lane 0 waits at the vote for lane 1, which has not exited, and lane 1
waits at the reduction for lane 0. The exits fill the needs of the returns they let pass, so no
execution with these traces is consistent (`exit_not_consistent`).

Aligned: both lanes execute the vote and then the reduction. Each instance relates the events of
both lanes (`aligned_vote`, `aligned_redux`), and the dependency order of the execution has no
cycle (`aligned_acyclic`). -/
namespace PTX.Tests.WarpWait
noncomputable section

private def L : Launch := { grid := 1, block := 32, params := fun _ => none }

private theorem warp01 : SameWarp L 0 1 := by
  unfold SameWarp SameCta Launch.threads L; decide

private theorem warp10 : SameWarp L 1 0 := by
  unfold SameWarp SameCta Launch.threads L; decide

private theorem lane0 : laneOf L 0 = 0 := by unfold laneOf L; decide

private theorem lane1 : laneOf L 1 = 1 := by unfold laneOf L; decide

/-- A lane's `n`-th event of a class, with the mask and qualifiers of its part, is a `MaskAt`. -/
private theorem maskAt_mk {Q V : Type} {c : Kind → Option (WarpPart Q V)} {X : Execution}
    {e : EvId} {ev : Event} {p : WarpPart Q V} {n : Nat} (hg : X.get e = some ev)
    (hc : c ev.kind = some p)
    (hn : ((X.tr e.1).take e.2).countP (fun ev => (c ev.kind).any (·.mask == p.mask)) = n) :
    X.MaskAt c e p.mask n p.qual :=
  ⟨⟨⟨ev, p, hg, hc, rfl⟩, hn⟩, ev, p, hg, hc, rfl⟩

/-- A `MaskWait` source is a witness of the needs of the return, once the needs are those of
`maskNeeds` and the lane is in the member mask. -/
private theorem witness_mask {Q V : Type} {c : Kind → Option (WarpPart Q V)} {X : Execution}
    {e f : EvId} {l : Nat} {p : WarpPart Q V}
    (hn : Needs L X f = maskNeeds L c X f) (hp : (X.get f).bind (fun ev => c ev.kind) = some p)
    (hl : warpLane L f.1 l = e.1) (hl32 : l < 32) (hb : p.mask.testBit l = true)
    (hw : MaskWait L c X e f) : Witness L X (.thread e) f := by
  have hpres : X.RefPresent (.thread e) := by
    rcases hw.src with ⟨pc, k, -, h, -⟩ | ⟨pc, h⟩ <;> exact ⟨_, h⟩
  refine ⟨fun x => ∃ j, x = .thread (warpLane L f.1 l, j) ∧
    MaskWait L c X (warpLane L f.1 l, j) f, ?_, hpres, e.2, by rw [hl], by rw [hl]; exact hw⟩
  rw [hn]
  simp only [maskNeeds, hp, List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨l, ⟨hl32, hb⟩, rfl⟩

/-- A witness step of the dependency order. -/
private theorem wstep {K : Kernel} {X : Execution} {e f : EvId} (h : Witness L X (.thread e) f) :
    DepStep L K X (.thread e, false) (.thread f, true) :=
  .inr (.inr (.inl ⟨rfl, rfl, f, rfl, h⟩))

/-- A resume step of the dependency order: a blocking return before a later event of its thread. -/
private theorem rstep {K : Kernel} {X : Execution} {w f : EvId} (h : Resumes K X w f) :
    DepStep L K X (.thread w, true) (.thread f, false) :=
  .inr (.inr (.inr ⟨rfl, rfl, w, f, rfl, rfl, h⟩))

/-- A cycle of four dependency steps violates `DependencyOk.acyclic`; the order of an mbarrier
object adds nothing. -/
private theorem cycle {K : Kernel} {X : Execution} {a b c d : AsyncCopy.Ref × Bool}
    (h1 : DepStep L K X a b) (h2 : DepStep L K X b c) (h3 : DepStep L K X c d)
    (h4 : DepStep L K X d a) : ¬ DependencyOk L K X :=
  fun h => h.acyclic (.mbar ⟨.shared, 0, 0⟩) trivial a
    (.tail (.tail (.tail (.single (.inl h1)) (.inl h2)) (.inl h3)) (.inl h4))

/-! ## Opposite orders -/

/-- The traces of the opposite-order program, with any returned values. -/
def crossTr (v0 v1 : Bool) (r0 r1 : BitVec 32) : Nat → List Event
  | 0 => [⟨0, .voteMode .all 3 true v0⟩, ⟨1, .redux .add false 3 1 r0⟩, ⟨2, .exit⟩]
  | 1 => [⟨3, .redux .add false 3 1 r1⟩, ⟨4, .voteMode .all 3 true v1⟩, ⟨5, .exit⟩]
  | g => if g < 32 then [⟨6, .exit⟩] else []

section Cross
variable {X : Execution} {v0 v1 : Bool} {r0 r1 : BitVec 32}

theorem cross_not_dependencyOk (htr : ∀ g, X.tr g = crossTr v0 v1 r0 r1 g) (K : Kernel) :
    ¬ DependencyOk L K X := by
  have hv00 : X.MaskAt voteClass (0, 0) 3 0 VoteMode.all :=
    maskAt_mk (X := X) (c := voteClass) (e := (0, 0))
      (p := ⟨3, VoteMode.all, true⟩) (ev := ⟨0, .voteMode .all 3 true v0⟩)
      (by simp [Execution.get, htr, crossTr]) rfl (by simp [htr, crossTr])
  have hv11 : X.MaskAt voteClass (1, 1) 3 0 VoteMode.all :=
    maskAt_mk (X := X) (c := voteClass) (e := (1, 1))
      (p := ⟨3, VoteMode.all, true⟩) (ev := ⟨4, .voteMode .all 3 true v1⟩)
      (by simp [Execution.get, htr, crossTr]) rfl (by simp [htr, crossTr, voteClass])
  have hr01 : X.MaskAt reduxClass (0, 1) 3 0 (.add, false) :=
    maskAt_mk (X := X) (c := reduxClass) (e := (0, 1))
      (p := ⟨3, (.add, false), 1⟩) (ev := ⟨1, .redux .add false 3 1 r0⟩)
      (by simp [Execution.get, htr, crossTr]) rfl (by simp [htr, crossTr, reduxClass])
  have hr10 : X.MaskAt reduxClass (1, 0) 3 0 (.add, false) :=
    maskAt_mk (X := X) (c := reduxClass) (e := (1, 0))
      (p := ⟨3, (.add, false), 1⟩) (ev := ⟨3, .redux .add false 3 1 r1⟩)
      (by simp [Execution.get, htr, crossTr]) rfl (by simp [htr, crossTr])
  have wv : MaskWait L voteClass X (1, 1) (0, 0) := ⟨warp10, 3, 0, VoteMode.all, hv00, .inl hv11⟩
  have wr : MaskWait L reduxClass X (0, 1) (1, 0) := ⟨warp01, 3, 0, _, hr10, .inl hr01⟩
  -- return of lane 1's reduction → its vote → return of lane 0's vote → its reduction →
  -- return of lane 1's reduction
  exact cycle
    (rstep (w := (1, 0)) (f := (1, 1)) ⟨⟨rfl, by decide, by simp [htr, crossTr]⟩,
      by simp [Execution.get, htr, crossTr, Kind.resume]⟩)
    (wstep (witness_mask (c := voteClass) (e := (1, 1)) (f := (0, 0)) (l := 1)
      (p := ⟨3, VoteMode.all, true⟩)
      (by simp [Needs, Execution.get, htr, crossTr, KindNeeds])
      (by simp [Execution.get, htr, crossTr, voteClass]) (by unfold warpLane; rw [lane0]; rfl)
      (by decide) (by decide) wv))
    (rstep (w := (0, 0)) (f := (0, 1)) ⟨⟨rfl, by decide, by simp [htr, crossTr]⟩,
      by simp [Execution.get, htr, crossTr, Kind.resume]⟩)
    (wstep (witness_mask (c := reduxClass) (e := (0, 1)) (f := (1, 0)) (l := 0)
      (p := ⟨3, (.add, false), 1⟩)
      (by simp [Needs, Execution.get, htr, crossTr, KindNeeds])
      (by simp [Execution.get, htr, crossTr, reduxClass]) (by unfold warpLane; rw [lane1]; rfl)
      (by decide) (by decide) wr))

/-- No execution of the opposite-order program is consistent. -/
theorem cross_not_consistent (htr : ∀ g, X.tr g = crossTr v0 v1 r0 r1 g) (K : Kernel)
    (A : List Assumption) (mem0 : Mem0) : ¬ Consistent L K A mem0 X :=
  fun hc => cross_not_dependencyOk htr K hc.dependency

end Cross

/-! ## Exit -/

/-- The traces of the exit program, with any returned values. -/
def exitTr (v : Bool) (r : BitVec 32) : Nat → List Event
  | 0 => [⟨0, .voteMode .all 3 true v⟩, ⟨1, .exit⟩]
  | 1 => [⟨2, .redux .add false 3 1 r⟩, ⟨3, .exit⟩]
  | g => if g < 32 then [⟨4, .exit⟩] else []

section Exit
variable {X : Execution} {v : Bool} {r : BitVec 32}

theorem exit_not_dependencyOk (htr : ∀ g, X.tr g = exitTr v r g) (K : Kernel) :
    ¬ DependencyOk L K X := by
  have hv : X.MaskAt voteClass (0, 0) 3 0 VoteMode.all :=
    maskAt_mk (X := X) (c := voteClass) (e := (0, 0)) (p := ⟨3, VoteMode.all, true⟩)
      (ev := ⟨0, .voteMode .all 3 true v⟩) (by simp [Execution.get, htr, exitTr]) rfl
      (by simp [htr, exitTr])
  have hr : X.MaskAt reduxClass (1, 0) 3 0 (.add, false) :=
    maskAt_mk (X := X) (c := reduxClass) (e := (1, 0)) (p := ⟨3, (.add, false), 1⟩)
      (ev := ⟨2, .redux .add false 3 1 r⟩) (by simp [Execution.get, htr, exitTr]) rfl
      (by simp [htr, exitTr])
  have hx0 : X.MaskExitK reduxClass (0, 1) 3 0 :=
    ⟨⟨1, by simp [Execution.get, htr, exitTr]⟩, by simp [htr, exitTr, reduxClass]⟩
  have hx1 : X.MaskExitK voteClass (1, 1) 3 0 :=
    ⟨⟨3, by simp [Execution.get, htr, exitTr]⟩, by simp [htr, exitTr, voteClass]⟩
  have wv : MaskWait L voteClass X (1, 1) (0, 0) :=
    ⟨warp10, 3, 0, VoteMode.all, hv, .inr ⟨by rw [lane1]; decide, hx1⟩⟩
  have wr : MaskWait L reduxClass X (0, 1) (1, 0) :=
    ⟨warp01, 3, 0, _, hr, .inr ⟨by rw [lane0]; decide, hx0⟩⟩
  -- return of lane 0's vote → its exit → return of lane 1's reduction → its exit → return of
  -- lane 0's vote
  exact cycle
    (rstep (w := (0, 0)) (f := (0, 1)) ⟨⟨rfl, by decide, by simp [htr, exitTr]⟩,
      by simp [Execution.get, htr, exitTr, Kind.resume]⟩)
    (wstep (witness_mask (c := reduxClass) (e := (0, 1)) (f := (1, 0)) (l := 0)
      (p := ⟨3, (.add, false), 1⟩)
      (by simp [Needs, Execution.get, htr, exitTr, KindNeeds])
      (by simp [Execution.get, htr, exitTr, reduxClass]) (by unfold warpLane; rw [lane1]; rfl)
      (by decide) (by decide) wr))
    (rstep (w := (1, 0)) (f := (1, 1)) ⟨⟨rfl, by decide, by simp [htr, exitTr]⟩,
      by simp [Execution.get, htr, exitTr, Kind.resume]⟩)
    (wstep (witness_mask (c := voteClass) (e := (1, 1)) (f := (0, 0)) (l := 1)
      (p := ⟨3, VoteMode.all, true⟩)
      (by simp [Needs, Execution.get, htr, exitTr, KindNeeds])
      (by simp [Execution.get, htr, exitTr, voteClass]) (by unfold warpLane; rw [lane0]; rfl)
      (by decide) (by decide) wv))

/-- No execution of the exit program is consistent. -/
theorem exit_not_consistent (htr : ∀ g, X.tr g = exitTr v r g) (K : Kernel)
    (A : List Assumption) (mem0 : Mem0) : ¬ Consistent L K A mem0 X :=
  fun hc => exit_not_dependencyOk htr K hc.dependency

end Exit

/-! ## Aligned -/

/-- Lanes 0 and 1 both vote, reduce and exit. -/
def alignedTr : Nat → List Event
  | 0 | 1 => [⟨10, .voteMode .all 3 true true⟩, ⟨11, .redux .add false 3 1 2⟩, ⟨12, .exit⟩]
  | _ => []

def aligned : Execution := { tr := alignedTr, rf := fun _ _ => none }

private theorem aligned_get {e : EvId} {pc : Nat} {k : Kind}
    (h : aligned.get e = some ⟨pc, k⟩) : (e.1 = 0 ∨ e.1 = 1) ∧
      ((e.2 = 0 ∧ k = .voteMode .all 3 true true) ∨ (e.2 = 1 ∧ k = .redux .add false 3 1 2) ∨
        (e.2 = 2 ∧ k = .exit)) := by
  obtain ⟨g, i⟩ := e
  unfold Execution.get aligned at h
  rcases g with _ | _ | g <;> rcases i with _ | _ | _ | i <;> simp [alignedTr] at h <;>
    (obtain ⟨-, rfl⟩ := h) <;> simp

private theorem aligned_kind {e : EvId} {pc : Nat} {k : Kind}
    (h : aligned.get e = some ⟨pc, k⟩) :
    k = .voteMode .all 3 true true ∨ k = .redux .add false 3 1 2 ∨ k = .exit := by
  rcases (aligned_get h).2 with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]

theorem aligned_vote : MaskWait L voteClass aligned (0, 0) (1, 0) :=
  ⟨warp01, 3, 0, VoteMode.all,
    maskAt_mk (X := aligned) (c := voteClass) (e := (1, 0)) (p := ⟨3, VoteMode.all, true⟩)
      (ev := ⟨10, .voteMode .all 3 true true⟩) rfl rfl rfl,
    .inl (maskAt_mk (X := aligned) (c := voteClass) (e := (0, 0))
      (p := ⟨3, VoteMode.all, true⟩) (ev := ⟨10, .voteMode .all 3 true true⟩) rfl rfl rfl)⟩

theorem aligned_redux : MaskWait L reduxClass aligned (1, 1) (0, 1) :=
  ⟨warp10, 3, 0, (ReduxOp.add, false),
    maskAt_mk (X := aligned) (c := reduxClass) (e := (0, 1))
      (p := ⟨3, (ReduxOp.add, false), 1⟩) (ev := ⟨11, .redux .add false 3 1 2⟩) rfl rfl
      (by simp [aligned, alignedTr, reduxClass]),
    .inl (maskAt_mk (X := aligned) (c := reduxClass) (e := (1, 1))
      (p := ⟨3, (ReduxOp.add, false), 1⟩) (ev := ⟨11, .redux .add false 3 1 2⟩) rfl rfl
      (by simp [aligned, alignedTr, reduxClass]))⟩

private theorem aligned_async (i : EvId) (p : AsyncCopy.Part) : ¬ aligned.AsyncPresent i p := by
  intro h
  unfold Execution.AsyncPresent at h
  split at h <;> simp_all [aligned, Execution.MmaRead]

private theorem aligned_stageEdge (e f : AsyncCopy.Ref) : ¬ StageEdge aligned e f := by
  intro h
  unfold StageEdge at h
  split at h <;> simp_all [aligned_async]

/-- In a waiting dependency of the aligned execution, the source is no later in its trace than the
return in its own. -/
private theorem aligned_maskWait {Q V : Type} {c : Kind → Option (WarpPart Q V)} {e f : EvId}
    (h : MaskWait L c aligned e f) : e.2 ≤ f.2 := by
  obtain ⟨g, i⟩ := e
  obtain ⟨g', i'⟩ := f
  obtain ⟨-, m, n, q, ⟨⟨⟨⟨pf, kf⟩, pa, hf, hcf, hm⟩, hnf⟩, -⟩, he⟩ := h
  obtain ⟨hg', hi'⟩ := aligned_get hf
  have hk : ∀ {pe ke}, aligned.get (g, i) = some ⟨pe, ke⟩ →
      ((aligned.tr g).take i).countP (fun ev => (c ev.kind).any (·.mask == m)) ≤ n →
      i ≤ i' := by
    intro pe ke he hne
    obtain ⟨hg, hi⟩ := aligned_get he
    simp only at hg hi hg' hi' hnf ⊢
    rcases hg with rfl | rfl <;> rcases hg' with rfl | rfl <;>
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      rcases hi' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp_all [aligned, alignedTr, List.countP_cons] <;> omega
  rcases he with ⟨⟨⟨⟨pe, ke⟩, pb, he, -, -⟩, hne⟩, -⟩ | ⟨-, ⟨pe, he⟩, hne⟩
  · exact hk he hne.le
  · exact hk he hne

/-- A witness in the aligned execution is an event of a thread, no later in its trace than the
return it fills. -/
private theorem aligned_witness {x : AsyncCopy.Ref} {f : EvId}
    (h : Witness L aligned x f) : ∃ e, x = .thread e ∧ e.2 ≤ f.2 := by
  obtain ⟨fills, hmem, -, hfx⟩ := h
  cases hget : aligned.get f with
  | none => simp [Needs, hget] at hmem
  | some ev =>
    obtain ⟨pc, k⟩ := ev
    rcases aligned_kind hget with rfl | rfl | rfl
    · simp only [Needs, hget, KindNeeds, maskNeeds, voteClass, Option.bind_some,
        List.mem_map] at hmem
      obtain ⟨l, -, hn⟩ := hmem
      obtain rfl := Need.node.inj hn
      obtain ⟨j, rfl, hw⟩ := hfx
      exact ⟨_, rfl, aligned_maskWait hw⟩
    · simp only [Needs, hget, KindNeeds, maskNeeds, reduxClass, Option.bind_some,
        List.mem_map] at hmem
      obtain ⟨l, -, hn⟩ := hmem
      obtain rfl := Need.node.inj hn
      obtain ⟨j, rfl, hw⟩ := hfx
      exact ⟨_, rfl, aligned_maskWait hw⟩
    · simp [Needs, hget, KindNeeds] at hmem

/-- Program position: every dependency step of the aligned execution moves forward in it. -/
private def rank : AsyncCopy.Ref × Bool → Nat
  | (.thread e, b) => 2 * e.2 + b.toNat
  | (.async _ _, _) => 0

theorem aligned_acyclic (K : Kernel) :
    ∀ o, o.Enabling → ∀ n, ¬ Relation.TransGen
      (fun a c => DepStep L K aligned a c ∨ ObjectOrder L aligned o a c) n n := by
  intro o ho n hn
  have step : ∀ a c, (DepStep L K aligned a c ∨ ObjectOrder L aligned o a c) →
      rank a < rank c := by
    rintro ⟨e, b⟩ ⟨f, b'⟩ (h | h)
    · rcases h with (⟨rfl, rfl, rfl, hp⟩ | ⟨-, -, h⟩) | ⟨-, -, i, p, -, -, -, hp, -⟩ |
          ⟨rfl, rfl, j, rfl, hw⟩ | ⟨rfl, rfl, w, j, rfl, rfl, ⟨-, hlt, -⟩, -⟩
      · cases e with
        | thread e => simp [rank]
        | async i p => exact (aligned_async i p hp).elim
      · exact (aligned_stageEdge _ _ h).elim
      · exact (aligned_async i p hp).elim
      · obtain ⟨x, rfl, hx⟩ := aligned_witness hw
        simp [rank]; omega
      · simp [rank]; omega
    · cases o with
      | mbar m => simp [ObjectOrder, aligned, MBarrier.Before] at h
      | ctaBar c id => simp [ObjectOrder, aligned] at h
      | cluster c => simp [ObjectOrder, aligned] at h
      | tmem c => exact ho.elim
  have chain : ∀ a c, Relation.TransGen
      (fun a c => DepStep L K aligned a c ∨ ObjectOrder L aligned o a c) a c →
      rank a < rank c := by
    intro a c h
    induction h with
    | single h => exact step _ _ h
    | tail _ h ih => exact ih.trans (step _ _ h)
  exact lt_irrefl _ (chain _ _ hn)

end

end PTX.Tests.WarpWait
