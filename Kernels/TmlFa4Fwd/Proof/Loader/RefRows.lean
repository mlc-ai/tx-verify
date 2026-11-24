-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Move
public import Kernels.TmlFa4Fwd.Proof.Loader.ShapeAll
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's reference invariant is kept along a packet's rows

`ref_step_rows`: a step of the counted machine from a state inside a packet (its address loads,
shuffles, copies and commit) on an event of the state's shape that is not undefined behaviour
keeps the ring conjuncts (`RefRing`: the site stays in its period and the ring words are not
written) and the count conjuncts (`RefCounts`: a copy adds one to the copies and moves the
packet's copy count, a commit adds one to the commits, the loads and shuffles are counted by no
class). `next_ne_stop`: the machine does not stop on an event whose returned value has the
site's kind. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

/-- The sites inside a packet. -/
def Site.inRows : Site → Bool
  | .lw .. | .xl .. | .xh .. | .cp .. | .commit .. => true
  | _ => false

/-- An event counted by no class of the ledger leaves the counts unchanged. -/
theorem bump_quiet {n : Cnt → Nat} {e : Event} (h : ∀ c, cls L g c e = false) :
    Code.bump (cls L g) n e = n := by
  funext c; simp [Code.bump, h c]

theorem not14_14 : not14 14 = false := by decide
theorem not14_15 : not14 15 = true := by decide

/-- The step obligation at a successor: `RefE` and the step spec. -/
abbrev Post (p : Params) (L : Launch) (g w : Nat) (dn : D × (Cnt → Nat)) (e : Event)
    (d' : D) : Prop :=
  RefE p L g w (d', Code.bump (cls L g) dn.2 e) ∧ Move L g w dn e d'

/-- A conditional successor: both branches satisfy the obligation. -/
theorem post_ite {c : Bool} {a b : D} {dn : D × (Cnt → Nat)} {e : Event}
    (ha : Post p L g w dn e a) (hb : Post p L g w dn e b) : Post p L g w dn e (D.ite c a b) := by
  cases c
  · exact hb
  · exact ha

theorem post_iteS {c : Bool} {a b : D} {dn : D × (Cnt → Nat)} {e : Event}
    (ha : Post p L g w dn e ⟨a.site, a.v, 0⟩) (hb : Post p L g w dn e ⟨b.site, b.v, 0⟩) :
    Post p L g w dn e (D.iteS c a b) := by
  cases c
  · exact hb
  · exact ha

theorem tag_cp {per : Per} {b : Bool} {i : Fin 16} {c : Fin 2} {s' : Site}
    (h : s' ≠ .cp per b i c) : tag (.cp per b i c) s' = .copy := by
  simp [tag, h]

/-- The event's class from its kind, and the edge's tag. -/
theorem cnt_of {e : Event} {X T : Option Cnt} (h : ∀ c, cls L g c e = decide (X = some c))
    (hT : T = X) : ∀ c, cls L g c e = decide (T = some c) := by
  rw [hT]; exact h

theorem cls_none {e : Event} (h : ∀ c, cls L g c e = false) :
    ∀ c, cls L g c e = decide (none = some c) := by
  intro c; rw [h c]; simp

theorem cls_wait {e : Event} {l par a sc} (hk : e.kind = .wait l par true a sc) :
    ∀ c, cls L g c e = decide (some (.acquire l) = some c) := by
  intro c; cases c <;> simp [cls, hk, eq_comm]

theorem cls_arr {e : Event} {l b c' r sc} (hk : e.kind = .arrive l b c' r sc) :
    ∀ c, cls L g c e = decide (some (.arrive l) = some c) := by
  intro c; cases c <;> simp [cls, hk, eq_comm]

theorem cls_async {e : Event} {l a} (hk : e.kind = .asyncArrive l a) :
    ∀ c, cls L g c e = decide (some (.asyncArrive l) = some c) := by
  intro c; cases c <;> simp [cls, hk, eq_comm]

theorem cls_copy {e : Event} (hk : (∃ sz, e.kind = .copy sz) ∨ ∃ a s, e.kind = .tensorIssue a s) :
    ∀ c, cls L g c e = decide (some .copy = some c) := by
  intro c
  rcases hk with ⟨_, hk⟩ | ⟨_, _, hk⟩ <;> cases c <;> simp [cls, hk]

theorem cls_commit {e : Event} (hk : e.kind = .asyncCommit) :
    ∀ c, cls L g c e = decide (some .commit = some c) := by
  intro c; cases c <;> simp [cls, hk]

theorem cls_won {e : Event} {mk inst ld} (hk : e.kind = .elect mk inst ld) (hl : laneOf L g = ld) :
    ∀ c, cls L g c e = decide (some (.won e.pc) = some c) := by
  intro c; cases c <;> simp [cls, hk, hl, eq_comm]

theorem cls_store {e : Event} {a : Acc} {bs : List Byte} {o0 : Nat} (hk : e.kind = .wr a bs)
    (hloc : a.loc = ⟨.local, g, L.localBase + o0⟩) :
    ∀ c, cls L g c e = decide (some (.lst o0) = some c) := by
  intro c; cases c <;> simp [cls, hk, hloc, eq_comm]

set_option hygiene false in
/-- The edge of a branch whose successor is substituted. -/
macro "edge_tac" : tactic => `(tactic| first
  | exact .inl rfl
  | (refine .inr ?_
     simp (config := { decide := true }) only [nexts, passNexts, tailNexts, warmNexts,
       groupNexts, List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil,
       Epilogue.Scan.late, Epilogue.loopOf, Fin.isValue, ↓reduceIte, ↓reduceDIte,
       Fin.val_zero, Fin.val_one, Fin.val_two, Bool.false_eq_true, true_or, or_true,
       reduceCtorEq, Site.slot.injEq, Site.word.injEq, Site.down.injEq, Site.pgSt.injEq,
       Site.pgLd.injEq, Site.tw.injEq, Site.dw.injEq, not14_14, not14_15] <;> done)
  | (have hn14 : not14 w = false := by
       first
         | exact (by simpa using ‹¬not14 w = true› : not14 w = false)
         | (have h := ‹¬(not14 w || _) = true›
            simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at h
            exact h.1)
     refine .inr ?_
     simp (config := { decide := true }) only [nexts, passNexts, tailNexts, warmNexts,
       groupNexts, List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil,
       Fin.isValue, ↓reduceIte, Bool.false_eq_true, true_or, or_true, reduceCtorEq, hn14] <;>
       done)
  | (have hn14 : not14 w = true := ‹not14 w = true›
     refine .inr ?_
     simp (config := { decide := true }) only [nexts, passNexts, tailNexts, warmNexts,
       groupNexts, List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil,
       Fin.isValue, ↓reduceIte, Bool.false_eq_true, true_or, or_true, reduceCtorEq, hn14] <;>
       done)
  | (refine .inr ?_
     rcases Bool.eq_false_or_eq_true (not14 w) with hn14 | hn14 <;>
       simp (config := { decide := true }) only [nexts, passNexts, tailNexts, warmNexts,
         groupNexts, List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil,
         Fin.isValue, ↓reduceIte, Bool.false_eq_true, true_or, or_true, reduceCtorEq, hn14] <;>
       done))

/-- The tag of a branch's edge, as `Tag.cnt`. -/
macro "tag_tac" : tactic => `(tactic| first
  | rfl
  | (simp (config := { decide := true }) only [tag_self, tag, Tag.cnt, reduceCtorEq,
      ↓reduceIte, Site.lw.injEq, Site.xl.injEq, Site.xh.injEq, Site.cp.injEq, Fin.isValue,
      and_false, false_and, and_self, and_true, true_and, Nat.add_zero, ptOff] <;> done))

set_option hygiene false in
/-- The step spec at a branch whose successor is substituted, from the event's class `hcls` and
a proof `t` of the tag's class. -/
macro "move_with " t:term : tactic => `(tactic| (
  refine ⟨?_, fun f hf => ?_, cnt_of hcls $t⟩
  · edge_tac
  -- a written field first: `rfl` on it would unfold its new value
  · cases f <;> first | (simp [wr] at hf; done) | exact rfl))

/-- The step spec at a branch whose successor is substituted, from the event's class `hcls`. -/
macro "move_tac" : tactic => `(tactic| move_with (by tag_tac))

/-- The step spec at a branch, with the event's class given by `h`. -/
macro "move_cls " h:term : tactic => `(tactic| (
  refine ⟨?_, fun f hf => ?_, cnt_of $h (by tag_tac)⟩
  · edge_tac
  -- a written field first: `rfl` on it would unfold its new value
  · cases f <;> first | (simp [wr] at hf; done) | exact rfl))

set_option hygiene false in
/-- The count fields after a step inside a packet: unfold, rewrite the old equations, and close the
arithmetic. -/
macro "rows_counts" : tactic => `(tactic| (
  obtain ⟨h3, h6⟩ := hC
  refine ⟨?_, fun o ho => ?_⟩
  all_goals
    try simp only [Code.bump, cls, arrAt, inPkt, reduceCtorEq, decide_false, Bool.false_and,
      Bool.and_false, Nat.add_zero, Bool.false_eq_true, ↓reduceIte] at h3 h6 ⊢
  all_goals first
    | exact h6 o ho
    | omega
    | (rw [h3]; omega)))

set_option maxHeartbeats 4000000 in
/-- **The reference invariant is kept along a packet's rows.** -/
theorem ref_step_rows {d : D} {n : Cnt → Nat} {e : Event} {d' : D} {k A : Nat}
    (hJ : RefRing p L g w d k A) (hC : RefCounts L g w (d, n) k A) (hrows : d.site.inRows = true)
    (hev : Ev p L g w d e) (hub : ∀ f, e.kind ≠ .ub f)
    (hn : succ p L g w d e = some (some d')) :
    Post p L g w (d, n) e d' := by
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s with
  | lw per b h =>
    simp only [Ev] at hev
    obtain ⟨bs, hk⟩ := hev
    subst hk
    simp only [succ] at hn
    split at hn
    · rename_i x hx
      simp only [word32] at hn
      split at hn
      · rename_i y
        split at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;>
          refine ⟨⟨k, A, refRing_congr hJ (by cases per <;> rfl) rfl rfl rfl rfl rfl rfl, ?_⟩,
            by move_cls (cls_none fun c => by cases c <;> rfl)⟩ <;>
          (rw [bump_quiet (fun c => by cases c <;> rfl)]
           rows_counts)
      · simp at hn
    · simp at hn
  | xl per b i | xh per b i =>
    simp only [Ev] at hev
    obtain ⟨recv, ok, hk⟩ := hev
    subst hk
    simp only [succ, word32] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      refine ⟨⟨k, A, refRing_congr hJ (by cases per <;> rfl) rfl rfl rfl rfl rfl rfl, ?_⟩,
        by move_cls (cls_none fun c => by cases c <;> rfl)⟩
      rw [bump_quiet (fun c => by cases c <;> rfl)]
      rows_counts
    · simp at hn
  | cp per b i c =>
    simp only [Ev] at hev
    rcases hev with ⟨sz, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [succ] at hn
      split_ifs at hn with hc hi7 hi15 <;> simp only [Option.some.injEq, D.mk'] at hn <;>
        subst hn <;>
        refine ⟨⟨k, A, refRing_congr hJ (by cases per <;> rfl) rfl rfl rfl rfl rfl rfl, ?_⟩,
          by refine ⟨?_, fun f hf => ?_, cnt_of (cls_copy (.inl ⟨_, rfl⟩)) ?_⟩
             · refine .inr ?_
               first
                 | (simp only [nexts, List.mem_singleton, *, ↓reduceIte]; done)
                 | (simp only [nexts, List.mem_singleton, *, ↓reduceIte]; simp_all)
             · cases f <;> exact rfl
             · rw [tag_cp (by first
                 | (intro h; cases h; done)
                 | (intro h; cases h; exact absurd ‹(1 : Fin 2).val = 0› (by decide)))]
               rfl⟩ <;>
        rows_counts
    · exact absurd hk (hub f)
  | commit per b =>
    simp only [Ev] at hev
    subst hev
    simp only [succ] at hn
    cases hn
    refine ⟨⟨k, A, refRing_congr hJ (by cases per <;> rfl) rfl rfl rfl rfl rfl rfl, ?_⟩,
      by move_cls (cls_commit rfl)⟩
    rows_counts
  | _ => simp [Site.inRows] at hrows

/-- **The machine does not stop on an event whose returned value has the site's kind** (the first
conjunct of `ref_next`, from `stop_iff`). -/
theorem next_ne_stop {d : D} {e : Event} (hi : (code p L g w ent).inv d)
    (hev : Ev p L g w d e) (hacc : (ret d).accepts e) :
    (code p L g w ent).next d e ≠ some none :=
  fun h => (stop_iff d hi hev).mp h hacc

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
