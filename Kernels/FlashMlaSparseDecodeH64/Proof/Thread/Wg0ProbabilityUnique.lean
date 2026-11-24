-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.BoundMachine
public import Lemmas.Kernel.Frame
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix

@[expose] public section

/-! # A packed probability store occurs once at its lane, block, site and element -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0ProbabilityUnique

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem rank_step_in_trace {g i : Nat} {d q : Machine.ThreadD} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hq : Frame.stateAt (Machine.code P L) X g (i + 1) = some (some q)) :
    Bound.rank P L g q + (if e.counts then 1 else 0) ≤ Bound.rank P L g d := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hf⟩ := (hs.produces (hX.thr g hg)).fired_at he hd
  have hi : (Machine.code P L g).inv d := (Exists.choose_spec hf).1.2
  have hn := Frame.stateAt_succ (C := Machine.code P L) he
  rw [hd, hq] at hn
  exact Bound.rank_step hpre hi hf hn.symm

private theorem rank_antitone {g i j : Nat} {d q : Machine.ThreadD}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound)
    (hj : j ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some q))
    (hij : i ≤ j) : Bound.rank P L g q ≤ Bound.rank P L g d := by
  by_cases h : i < j
  · obtain ⟨s, hss⟩ := FollowedPrefix.state_at hq (show i + 1 ≤ j by omega)
    have hi : i < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e := ⟨_, List.getElem?_eq_getElem hi⟩
    have hstep := rank_step_in_trace hpre hX hs he hd hss
    have hrec := rank_antitone hpre hX hs hj hss hq (by omega : i + 1 ≤ j)
    omega
  · have heq : i = j := by omega
    subst j
    rw [hd] at hq
    obtain rfl := Option.some.inj (Option.some.inj hq)
    rfl
termination_by j - i
decreasing_by omega

variable {g i j : Nat}

/-- A counted event strictly decreases the rank of any later tracked state in its trace. -/
theorem actual_rank_strict_of_counted {d q : Machine.ThreadD} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, i) = some e) (hcount : e.counts = true) (hj : j ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some q)) (hij : i < j)
    : Bound.rank P L g q < Bound.rank P L g d := by
  obtain ⟨s, hss⟩ := FollowedPrefix.state_at hq (show i + 1 ≤ j by omega)
  have hbefore := rank_step_in_trace hpre hX hs he hd hss
  have hlater := rank_antitone hpre hX hs hj hss hq (by omega)
  simp only [hcount, ↓reduceIte] at hbefore
  omega

theorem rank_strict_of_counted {d q : Machine.ThreadD} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X) (he : X.get (g, i) = some e)
    (hcount : e.counts = true) (hj : j ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some q)) (hij : i < j)
    : Bound.rank P L g q < Bound.rank P L g d :=
  actual_rank_strict_of_counted hpre hX hs he hcount hj hd hq hij

private theorem rank_strict_of_write {d q : Machine.ThreadD} {a : Acc} {bs : List Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hw : X.Writes (g, i) a bs) (hj : j ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some q)) (hij : i < j)
    : Bound.rank P L g q < Bound.rank P L g d := by
  obtain ⟨tag, he⟩ := hw
  exact actual_rank_strict_of_counted hpre hX hs he rfl hj hd hq hij

/-- All write events at the same packed-probability position in one block are the same event. -/
theorem actual_write_unique {d q : Wg0.D} {k : Fin 4} {a fp : Acc} {bs raw : List Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hi : X.Writes (g, i) a bs) (hj : X.Writes (g, j) fp raw)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)))
    (hdSite : d.site = .pStore k) (hqSite : q.site = .pStore k) (hblock : d.block = q.block)
    (hsub : d.sub = q.sub) : i = j := by
  have hrank : Bound.rank P L g (.wg0 d) = Bound.rank P L g (.wg0 q) := by
    simp only [Bound.rank, Bound.wg0Rank, Bound.wg0Block, hdSite, hqSite, hblock, hsub]
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h := rank_strict_of_write hpre hX hs hi (PTX.len_of_get hj.choose_spec).le hd hq hlt
    omega
  · have h := rank_strict_of_write hpre hX hs hj (PTX.len_of_get hi.choose_spec).le hq hd hlt
    omega

theorem write_unique {d q : Wg0.D} {k : Fin 4} {a fp : Acc} {bs raw : List Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (_ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.Writes (g, i) a bs) (hj : X.Writes (g, j) fp raw)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)))
    (hdSite : d.site = .pStore k) (hqSite : q.site = .pStore k) (hblock : d.block = q.block)
    (hsub : d.sub = q.sub) : i = j :=
  actual_write_unique hpre hX hs hi hj hd hq hdSite hqSite hblock hsub

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0ProbabilityUnique
