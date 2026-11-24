-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Protocol.Wit
public import Lemmas.Kernel.MbarBulk

@[expose] public section

/-! # `tc_gemm`: the events of an execution, kind by kind

From an execution's description by whole traces (`Wit`): every event, by its position
(`Wit.get`, `Wit.cases`), and the events of each kind with their positions and operands: the
writes (thread 0's address store and the row stores), the reads of the address, the barriers and
their ordinals (`Wit.barK`), the MMA, the commit, the polls, the Tensor Memory loads, allocations
and deallocations and their warp-collective ordinals (`Wit.tcK`), the fences, the mbarrier
initializations and the arrival, the linear copies and the exits; and the kinds that do not occur
(tensor copies and stores, CLC requests, shuffles, `nc` reads, atomics, thread fences,
`cp.async.mbarrier.arrive`, prefetches, Tensor Memory stores, copies and shifts, invalidations). -/

namespace PTX.Kernels.TcGemm.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}

set_option hygiene false in
/-- Split `hc` from `Wit.cases` into its 25 positions and close those whose event is of
another kind. -/
macro "gemm_leaves" : tactic => `(tactic|
  (rcases hc with (c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c
    | c | c | c | c)) <;>
    first | (simp [allocE, tslotE, init0E, init1E, fenceE, arriveE, bulkAE, bulkBE, bar0E, rdE,
    wait0E, mmaE, commitE, wait1E, fa1E, ldE, wldE, stE, fbE, bar1E, fa2E, deallocE,
      exitE] at c; done) | skip)

section
variable {S : Nat} {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}
  (hW : Wit A B D S X P m u)
include hW

theorem Wit.length (g : Nat) (hg : g < 128) : (X.tr g).length = m g + (u g).length := by
  rw [hW.tr g hg, List.length_append, List.length_take, Nat.min_eq_left (hW.len g hg)]

/-- Every event of an execution, by its position. -/
theorem Wit.get {e : EvId} {ev : Event} (h : X.get e = some ev) :
    e.1 < 128 ∧ ((e.2 < m e.1 ∧ fullAt A B D S e.1 (P e.1) e.2 = some ev) ∨
      (e.2 = m e.1 ∧ ∃ pc f, ev = ⟨pc, .ub f⟩ ∧ u e.1 = [ev])) := by
  obtain ⟨g, j⟩ := e
  have hg : g < 128 := by
    by_contra hg
    simp [Execution.get, hW.out g (by omega)] at h
  refine ⟨hg, ?_⟩
  simp only [Execution.get] at h
  rw [hW.tr g hg] at h
  have hlt : ((fullE A B D S g (P g)).take (m g)).length = m g := by
    rw [List.length_take, Nat.min_eq_left (hW.len g hg)]
  by_cases hj : j < m g
  · rw [List.getElem?_append_left (by omega), List.getElem?_take, ite_eq_left hj, full_get] at h
    exact .inl ⟨hj, h⟩
  · rw [List.getElem?_append_right (by omega), hlt] at h
    rcases hW.ub g hg with hu | ⟨pc, f, hu, -⟩
    · rw [hu] at h; simp at h
    · rw [hu] at h
      obtain ⟨k, rfl⟩ : ∃ k, j = m g + k := ⟨j - m g, by omega⟩
      rw [Nat.add_sub_cancel_left] at h
      rcases k with _ | k
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        exact .inr ⟨by simp, pc, f, rfl, hu⟩
      · simp at h

/-- Every event of an execution, case by case. -/
theorem Wit.cases {g j : Nat} {ev : Event} (h : X.get (g, j) = some ev) : g < 128 ∧
    ((j < m g ∧ (
      (g / 32 = 0 ∧ j = 0 ∧ ev = allocE S) ∨
      (g = 0 ∧ j = 1 ∧ ev = tslotE S (P g).col) ∨
      (g = 0 ∧ j = 2 ∧ ev = init0E S) ∨ (g = 0 ∧ j = 3 ∧ ev = init1E S) ∨
      (g = 0 ∧ j = 4 ∧ ev = fenceE) ∨ (g = 0 ∧ j = 5 ∧ ev = arriveE S) ∨
      (g = 0 ∧ j = 6 ∧ ev = bulkAE A S) ∨ (g = 0 ∧ j = 7 ∧ ev = bulkBE B S) ∨
      (j + 1 = hd g ∧ ev = bar0E) ∨
      (j = hd g ∧ ev = rdE S (P g).rd) ∨
      (g = 0 ∧ hd g < j ∧ j < hd g + 1 + (P g).n0 ∧ ev = wait0E S false) ∨
      (g = 0 ∧ j = hd g + 1 + (P g).n0 ∧ ev = wait0E S true) ∨
      (g = 0 ∧ j = hd g + 2 + (P g).n0 ∧ ev = mmaE S (P g).c) ∨
      (g = 0 ∧ j = hd g + 3 + (P g).n0 ∧ ev = commitE S) ∨
      (tl g (P g) ≤ j ∧ j < tl g (P g) + (P g).n1 ∧ ev = wait1E S false) ∨
      (j = tl g (P g) + (P g).n1 ∧ ev = wait1E S true) ∨
      (j = tl g (P g) + (P g).n1 + 1 ∧ ev = fa1E) ∨
      (j = ldIdx g (P g) ∧ ev = ldE g (P g).c (P g).vals) ∨
      (j = ldIdx g (P g) + 1 ∧ ev = wldE) ∨
      (∃ k < 8, j = ldIdx g (P g) + 2 + k ∧ ev = stE D g (P g).vals k) ∨
      (j = ldIdx g (P g) + 10 ∧ ev = fbE) ∨
      (j = ldIdx g (P g) + 11 ∧ ev = bar1E) ∨
      (j = ldIdx g (P g) + 12 ∧ ev = fa2E) ∨
      (g / 32 = 0 ∧ j = ldIdx g (P g) + 13 ∧ ev = deallocE (P g).c) ∨
      (j = ldIdx g (P g) + (if g / 32 = 0 then 14 else 13) ∧ ev = exitE))) ∨
    (j = m g ∧ ∃ pc f, ev = ⟨pc, .ub f⟩ ∧ u g = [ev])) := by
  obtain ⟨hg, ⟨hj, hf⟩ | hub⟩ := hW.get h
  swap; · exact ⟨hg, .inr hub⟩
  dsimp only at hg hj hf
  refine ⟨hg, .inl ⟨hj, ?_⟩⟩
  rcases full_cases hf with ⟨-, hh⟩ | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | ⟨hlt, hp⟩
  · rcases head_cases hh with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9
    exacts [.inl c1,
      .inr (.inl c2),
      .inr (.inr (.inl c3)),
      .inr (.inr (.inr (.inl c4))),
      .inr (.inr (.inr (.inr (.inl c5)))),
      .inr (.inr (.inr (.inr (.inr (.inl c6))))),
      .inr (.inr (.inr (.inr (.inr (.inr (.inl c7)))))),
      .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl c8))))))),
      .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl c9))))))))]
  all_goals iterate 9 refine .inr ?_
  · exact .inl h2
  · exact .inr (.inl h3)
  · exact .inr (.inr (.inl h4))
  · exact .inr (.inr (.inr (.inl h5)))
  · exact .inr (.inr (.inr (.inr (.inl h6))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl h7)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h8))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h9)))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h10))))))))
  iterate 9 refine .inr ?_
  rcases post_cases hp with ⟨hk, rfl⟩ | ⟨k, hk8, hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩ |
    ⟨hg32, hk, rfl⟩ | ⟨hk, rfl⟩
  · exact .inl ⟨by omega, rfl⟩
  · exact .inr (.inl ⟨k, hk8, by omega, rfl⟩)
  · exact .inr (.inr (.inl ⟨by omega, rfl⟩))
  · exact .inr (.inr (.inr (.inl ⟨by omega, rfl⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨by omega, rfl⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨hg32, by omega, rfl⟩)))))
  · refine .inr (.inr (.inr (.inr (.inr (.inr ⟨?_, rfl⟩)))))
    split_ifs at hk ⊢ <;> omega

/-- The events before `m g` are those of the whole trace. -/
theorem Wit.get_of_lt {g j : Nat} (hg : g < 128) (hj : j < m g) :
    X.get (g, j) = fullAt A B D S g (P g) j := by
  have := hW.len g hg
  simp only [Execution.get]
  rw [hW.tr g hg, List.getElem?_append_left (by rw [List.length_take]; omega),
    List.getElem?_take, ite_eq_left hj, full_get]

/-! ### The events of each kind -/

/-- Ordinary source stores; independent bulk writes are classified separately. -/
theorem Wit.writes {g j pc : Nat} {a' : Acc} {bs : List Byte}
    (h : X.get (g, j) = some ⟨pc, .wr a' bs⟩) : g < 128 ∧ j < m g ∧
    ((g = 0 ∧ j = 1 ∧ a' = { loc := tslot S, size := 4 } ∧ bs = (b32 (P 0).col).toBytes) ∨
      (∃ k < 8, j = ldIdx g (P g) + 2 + k ∧ a' = stAcc D g k ∧
        bs = stBytes (word (P g).vals k))) := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  refine ⟨hg, hj, ?_⟩
  gemm_leaves
  · obtain ⟨rfl, rfl, hev⟩ := c; simp [tslotE] at hev
    exact .inl ⟨rfl, rfl, hev.2.1, hev.2.2⟩
  · obtain ⟨k, hk, rfl, hev⟩ := c; simp [stE] at hev
    exact .inr ⟨k, hk, rfl, hev.2.1, hev.2.2⟩


theorem Wit.reads {g j pc : Nat} {a' : Acc} {bs : List (Option Byte)}
    (h : X.get (g, j) = some ⟨pc, .rd a' bs⟩) : g < 128 ∧ j < m g ∧
    (j = hd g ∧ a' = { loc := tslot S, size := 4 } ∧ bs = (P g).rd) := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  refine ⟨hg, hj, ?_⟩
  gemm_leaves
  obtain ⟨rfl, hev⟩ := c; simp [rdE] at hev
  exact ⟨rfl, hev.2.1, hev.2.2⟩

theorem Wit.bar {g j pc i : Nat} (h : X.get (g, j) = some ⟨pc, .bar i⟩) : g < 128 ∧ j < m g ∧
    i = 0 ∧ (j + 1 = hd g ∨ j = ldIdx g (P g) + 11) := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  refine ⟨hg, hj, ?_⟩
  gemm_leaves
  · obtain ⟨hj', hev⟩ := c; simp [bar0E] at hev
    exact ⟨hev.2, .inl hj'⟩
  · obtain ⟨hj', hev⟩ := c; simp [bar1E] at hev
    exact ⟨hev.2, .inr hj'⟩

theorem Wit.bar_full {g j pc id : Nat} {count : Option Nat}
    (h : X.IsBarrier (g,j) id count pc) : count = none := by
  obtain ⟨hg,⟨hj,hc⟩ | ⟨-,pc',f,hev,-⟩⟩ := hW.cases h
  swap; · simp at hev
  gemm_leaves
  · obtain ⟨_,hev⟩ := c
    simp only [bar0E,Event.mk.injEq,Kind.bar.injEq] at hev
    exact hev.2.2.1
  · obtain ⟨_,hev⟩ := c
    simp only [bar1E,Event.mk.injEq,Kind.bar.injEq] at hev
    exact hev.2.2.1

theorem Wit.mma {g j pc d : Nat} {s : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (h : X.get (g, j) = some ⟨pc, .tc (.mma d s accum mask)⟩) : g < 128 ∧ j < m g ∧
    g = 0 ∧ j = hd 0 + 2 + (P 0).n0 ∧ d = (P 0).c ∧ s = mmaSpec S ∧ accum = false ∧
      mask = mmaMask := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  refine ⟨hg, hj, ?_⟩
  gemm_leaves
  obtain ⟨rfl, rfl, hev⟩ := c; simp [mmaE] at hev
  obtain ⟨-, h1, h2, h3, h4⟩ := hev
  exact ⟨rfl, rfl, h1, h2, h3, h4⟩

/-- The kernel's only MMA. -/
theorem Wit.mmaIssue {e : EvId} {d : Nat} {s : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} (h : X.MmaIssue e d s accum mask) :
    e = (0, hd 0 + 2 + (P 0).n0) ∧ d = (P 0).c ∧ s = mmaSpec S ∧ accum = false ∧
      mask = mmaMask := by
  obtain ⟨pc, hp⟩ := h
  obtain ⟨g, j⟩ := e
  obtain ⟨-, -, rfl, rfl, h1, h2, h3, h4⟩ := hW.mma hp
  exact ⟨rfl, h1, h2, h3, h4⟩

theorem Wit.commit {g j pc : Nat} {s : TcCommit.Spec}
    (h : X.get (g, j) = some ⟨pc, .tc (.commit s)⟩) :
    g < 128 ∧ j < m g ∧ g = 0 ∧ j = hd 0 + 3 + (P 0).n0 ∧ s = commitSpec S := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  refine ⟨hg, hj, ?_⟩
  gemm_leaves
  obtain ⟨rfl, rfl, hev⟩ := c; simp [commitE] at hev
  exact ⟨rfl, rfl, hev.2⟩

theorem Wit.wait {g j pc q : Nat} {m' : Loc} {ok acquire : Bool} {scope : MbarScope}
    (h : X.get (g, j) = some ⟨pc, .wait m' q ok acquire scope⟩) : g < 128 ∧ j < m g ∧ q = 0 ∧
    ((g = 0 ∧ hd 0 < j ∧ j ≤ hd 0 + 1 + (P 0).n0 ∧ m' = bar0 S ∧
        (ok = true ↔ j = hd 0 + 1 + (P 0).n0)) ∨
      (tl g (P g) ≤ j ∧ j ≤ tl g (P g) + (P g).n1 ∧ m' = bar1 S ∧
        (ok = true ↔ j = tl g (P g) + (P g).n1))) := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  refine ⟨hg, hj, ?_⟩
  gemm_leaves
  · obtain ⟨rfl, h1, h2, hev⟩ := c; simp [wait0E] at hev
    obtain ⟨-, h3, h4, h5⟩ := hev
    exact ⟨h4, .inl ⟨rfl, h1, by omega, h3, by simp [h5]; omega⟩⟩
  · obtain ⟨rfl, rfl, hev⟩ := c; simp [wait0E] at hev
    obtain ⟨-, h3, h4, h5⟩ := hev
    exact ⟨h4, .inl ⟨rfl, by omega, le_rfl, h3, by simp [h5]⟩⟩
  · obtain ⟨h1, h2, hev⟩ := c; simp [wait1E] at hev
    obtain ⟨-, h3, h4, h5⟩ := hev
    exact ⟨h4, .inr ⟨h1, by omega, h3, by simp [h5]; omega⟩⟩
  · obtain ⟨rfl, hev⟩ := c; simp [wait1E] at hev
    obtain ⟨-, h3, h4, h5⟩ := hev
    exact ⟨h4, .inr ⟨le_add_right le_rfl, le_rfl, h3, by simp [h5]⟩⟩

/-- Every poll is at one of the kernel's two `mbarrier.try_wait`s. -/
theorem Wit.wait_pc {g j pc q : Nat} {m' : Loc} {ok acquire : Bool} {scope : MbarScope}
    (h : X.get (g, j) = some ⟨pc, .wait m' q ok acquire scope⟩) :
    pc = Flow.mbarWait_0 ∨ pc = Flow.mbarWait_1 := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  gemm_leaves
  · obtain ⟨-, -, -, hev⟩ := c; exact .inl (Event.mk.inj hev).1
  · obtain ⟨-, -, hev⟩ := c; exact .inl (Event.mk.inj hev).1
  · obtain ⟨-, -, hev⟩ := c; exact .inr (Event.mk.inj hev).1
  · obtain ⟨-, hev⟩ := c; exact .inr (Event.mk.inj hev).1

theorem Wit.tld {g j pc ta : Nat} {vs : List Value}
    (h : X.get (g, j) = some ⟨pc, .tc (.ld ta vs .s32x32b)⟩) : g < 128 ∧ j < m g ∧
    j = ldIdx g (P g) ∧ ta = taddr g (P g).c ∧ vs = (P g).vals := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  refine ⟨hg, hj, ?_⟩
  gemm_leaves
  obtain ⟨rfl, hev⟩ := c; simp [ldE] at hev
  exact ⟨rfl, hev.2.1, hev.2.2⟩

/-- Every Tensor Memory load of this kernel has the `.32x32b` shape. -/
theorem Wit.tld_shape {g j pc ta : Nat} {vs : List Value} {sh : TcShape}
    (h : X.get (g, j) = some ⟨pc, .tc (.ld ta vs sh)⟩) : sh = .s32x32b := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  gemm_leaves
  obtain ⟨rfl, hev⟩ := c; simp [ldE] at hev
  exact hev.2.2.2

theorem Wit.talloc {g j pc n : Nat} {dst : Loc}
    (h : X.get (g, j) = some ⟨pc, .tc (.resource .one (some dst) (.alloc n))⟩) : g < 128 ∧ j < m g ∧
    g / 32 = 0 ∧ j = 0 ∧ dst = tslot S ∧ n = 32 := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  refine ⟨hg, hj, ?_⟩
  gemm_leaves
  obtain ⟨h1, rfl, hev⟩ := c; simp [allocE] at hev
  exact ⟨h1, rfl, hev.2.1, hev.2.2⟩

theorem Wit.tdealloc {g j pc ta n : Nat}
    (h : X.get (g, j) = some ⟨pc, .tc (.resource .one none (.dealloc ta n))⟩) :
    g < 128 ∧ j < m g ∧ g / 32 = 0 ∧ j = ldIdx g (P g) + 13 ∧ ta = (P g).c ∧ n = 32 := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  refine ⟨hg, hj, ?_⟩
  gemm_leaves
  obtain ⟨h1, rfl, hev⟩ := c; simp [deallocE] at hev
  exact ⟨h1, rfl, hev.2.1, hev.2.2⟩

/-- This kernel's only allocation-management events are its group-1 alloc and dealloc. -/
theorem Wit.resource {g j pc : Nat} {grp : CtaGroup} {dst : Option Loc} {a : Tmem.Request}
    (h : X.get (g, j) = some ⟨pc, .tc (.resource grp dst a)⟩) :
    (∃ d n, grp = .one ∧ dst = some d ∧ a = .alloc n) ∨
      (∃ ta n, grp = .one ∧ dst = none ∧ a = .dealloc ta n) := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  gemm_leaves
  all_goals first
    | (obtain ⟨-, rfl, hev⟩ := c; simp only [allocE, Event.mk.injEq,
         Kind.tc.injEq, TcKind.resource.injEq] at hev
       obtain ⟨-, rfl, rfl, rfl⟩ := hev
       exact .inl ⟨_, _, rfl, rfl, rfl⟩)
    | (obtain ⟨-, rfl, hev⟩ := c; simp only [deallocE, Event.mk.injEq,
         Kind.tc.injEq, TcKind.resource.injEq] at hev
       obtain ⟨-, rfl, rfl, rfl⟩ := hev
       exact .inr ⟨_, _, rfl, rfl, rfl⟩)

theorem Wit.fenceAfter {g j pc : Nat} (h : X.get (g, j) = some ⟨pc, .tc .fenceAfter⟩) :
    g < 128 ∧ j < m g ∧ (j = tl g (P g) + (P g).n1 + 1 ∨ j = ldIdx g (P g) + 12) := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  refine ⟨hg, hj, ?_⟩
  gemm_leaves
  · exact .inl c.1
  · exact .inr c.1

theorem Wit.fenceBefore {g j pc : Nat} (h : X.get (g, j) = some ⟨pc, .tc .fenceBefore⟩) :
    g < 128 ∧ j < m g ∧ j = ldIdx g (P g) + 10 := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  refine ⟨hg, hj, ?_⟩
  gemm_leaves
  exact c.1

theorem Wit.waitLd {g j pc : Nat} (h : X.get (g, j) = some ⟨pc, .tc .waitLd⟩) :
    g < 128 ∧ j < m g ∧ j = ldIdx g (P g) + 1 := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  refine ⟨hg, hj, ?_⟩
  gemm_leaves
  exact c.1

/-- This kernel issues no Tensor Memory stores. -/
theorem Wit.no_tst {g j pc a : Nat} {vs : List Value} {sh : TcShape}
    (h : X.get (g, j) = some ⟨pc, .tc (.st a vs sh)⟩) : False := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  gemm_leaves

/-- The kernel's MMA reads A from shared memory. -/
theorem Wit.shared_operands {i : EvId} {d : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (h : X.MmaIssue i d s acc mask) : s.aTmem = none := by
  obtain ⟨g, j⟩ := i
  obtain ⟨pc, h⟩ := h
  obtain ⟨-, -, -, -, -, rfl, -, -⟩ := hW.mma h
  rfl

/-- This kernel issues no Tensor Memory copies. -/
theorem Wit.no_cp {g j pc : Nat} {c : TcCopy.Spec}
    (h : X.get (g, j) = some ⟨pc, .tc (.cp c)⟩) : False := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  gemm_leaves

theorem Wit.no_waitSt {g j pc : Nat} (h : X.get (g, j) = some ⟨pc, .tc .waitSt⟩) : False := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  gemm_leaves

theorem Wit.no_inval {g j pc : Nat} {m' : Loc} (h : X.get (g, j) = some ⟨pc, .mbInval m'⟩) :
    False := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  gemm_leaves

theorem Wit.mbInit {g j pc n : Nat} {m' : Loc} (h : X.get (g, j) = some ⟨pc, .mbInit m' n⟩) :
    g < 128 ∧ j < m g ∧ g = 0 ∧ n = 1 ∧ ((j = 2 ∧ m' = bar0 S) ∨ (j = 3 ∧ m' = bar1 S)) := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  refine ⟨hg, hj, ?_⟩
  gemm_leaves
  · obtain ⟨rfl, rfl, hev⟩ := c; simp [init0E] at hev
    exact ⟨rfl, hev.2.2, .inl ⟨rfl, hev.2.1⟩⟩
  · obtain ⟨rfl, rfl, hev⟩ := c; simp [init1E] at hev
    exact ⟨rfl, hev.2.2, .inr ⟨rfl, hev.2.1⟩⟩

theorem Wit.arrive {g j pc tx count : Nat} {m' : Loc} {release : Bool} {scope : MbarScope}
    (h : X.get (g, j) = some ⟨pc, .arrive m' tx count release scope⟩) :
    g < 128 ∧ j < m g ∧ g = 0 ∧ j = 5 ∧ m' = bar0 S ∧ tx = 4352 ∧ count = 1 := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  refine ⟨hg, hj, ?_⟩
  gemm_leaves
  obtain ⟨rfl, rfl, hev⟩ := c; simp [arriveE] at hev
  exact ⟨rfl, rfl, hev.2.1, hev.2.2.1, hev.2.2.2.1⟩

/-- The linear copies: thread 0's copies of `A` (event 6) and `B` (event 7). -/
theorem Wit.bulk {g j pc : Nat} {s : AsyncCopy.Spec} (h : X.get (g, j) = some ⟨pc, .copy s⟩) :
    g < 128 ∧ j < m g ∧ g = 0 ∧ ((j = 6 ∧ s = specA A S) ∨ (j = 7 ∧ s = specB B S)) := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  refine ⟨hg, hj, ?_⟩
  gemm_leaves
  · obtain ⟨rfl, rfl, hev⟩ := c; simp only [bulkAE, Event.mk.injEq, Kind.copy.injEq] at hev
    exact ⟨rfl, .inl ⟨rfl, hev.2⟩⟩
  · obtain ⟨rfl, rfl, hev⟩ := c; simp only [bulkBE, Event.mk.injEq, Kind.copy.injEq] at hev
    exact ⟨rfl, .inr ⟨rfl, hev.2⟩⟩

/-- Every linear copy completes through `bar0`, writes its destination whole from memory, and has
a source of its destination's size. -/
theorem Wit.copy_spec {i : EvId} {s : AsyncCopy.Spec} (h : X.Copy i s) :
    s.completion = .mbarrier (bar0 S) ∧ s.writes = .whole ∧ s.data = none ∧
      s.src.size = s.dst.size ∧ s.generic = false := by
  obtain ⟨pc, h⟩ := h
  obtain ⟨g, j⟩ := i
  obtain ⟨-, -, -, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := hW.bulk h <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Every linear copy writes its destination whole from a memory source of its size. -/
theorem Wit.copy_form (i : EvId) : ∀ s, AsyncCopy.issuedBy X i = some s →
    s.data = none ∧ s.writes = .whole ∧ s.src.size = s.dst.size := fun _ hs => by
  obtain ⟨-, hw, hd, hsz, -⟩ := hW.copy_spec (AsyncCopy.issuedBy_some.mp hs)
  exact ⟨hd, hw, hsz⟩

theorem Wit.fenceProxy {g j pc : Nat} {k : ProxyFence} {s : Option MbarScope}
    (h : X.get (g, j) = some ⟨pc, .fenceProxy k s⟩) :
    g < 128 ∧ j < m g ∧ g = 0 ∧ j = 4 ∧ k = .async (some (.shared .cta)) ∧ s = none := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  refine ⟨hg, hj, ?_⟩
  gemm_leaves
  obtain ⟨h0, h4, hev⟩ := c
  simp only [fenceE, Event.mk.injEq, Kind.fenceProxy.injEq] at hev
  exact ⟨h0, h4, hev.2.1, hev.2.2⟩

/-- The kernel issues no atomic read-modify-write. -/
theorem Wit.no_rmw {g j pc : Nat} {a' : Acc} {o : List (Option Byte)} {n : Option (List Byte)}
    (h : X.get (g, j) = some ⟨pc, .rmw a' o n⟩) : False := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  gemm_leaves

/-- The kernel has no thread fence. -/
theorem Wit.no_threadFence {g j pc : Nat} {sem : FenceSem} {sc : MbarScope}
    (h : X.get (g, j) = some ⟨pc, .fence sem sc⟩) : False := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  gemm_leaves

/-- The kernel issues no `cp.async.mbarrier.arrive`. -/
theorem Wit.no_asyncArrive {g j pc : Nat} {m' : Loc} {noinc : Bool}
    (h : X.get (g, j) = some ⟨pc, .asyncArrive m' noinc⟩) : False := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  gemm_leaves

/-- The kernel issues no `cp.async.bulk.prefetch`. -/
theorem Wit.no_bulkPrefetch {g j pc : Nat} {a' : Acc}
    (h : X.get (g, j) = some ⟨pc, .bulkPrefetch a'⟩) : False := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  gemm_leaves

/-- The kernel issues no Tensor Core shift. -/
theorem Wit.no_shift {g j pc : Nat} {s : TcShift.Spec}
    (h : X.get (g, j) = some ⟨pc, .tc (.shift s)⟩) : False := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  gemm_leaves

theorem Wit.exit {g j pc : Nat} (h : X.get (g, j) = some ⟨pc, .exit⟩) :
    g < 128 ∧ j < m g ∧ j = ldIdx g (P g) + (if g / 32 = 0 then 14 else 13) := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  swap; · simp at hev
  refine ⟨hg, hj, ?_⟩
  gemm_leaves
  exact c.1


/-! ### Barrier instances and warp-collective instances -/

theorem Wit.take {g j : Nat} (hg : g < 128) (hj : j ≤ m g) :
    (X.tr g).take j = (fullE A B D S g (P g)).take j := by
  have := hW.len g hg
  rw [hW.tr g hg, List.take_append_of_le_length (by rw [List.length_take]; omega),
    List.take_take, Nat.min_eq_left hj]

theorem Wit.barK {g j k : Nat} (h : X.BarK (g, j) k) : g < 128 ∧ j < m g ∧
    ((j + 1 = hd g ∧ k = 0) ∨ (j = ldIdx g (P g) + 11 ∧ k = 1)) := by
  obtain ⟨⟨i, pc, hb⟩, hk⟩ := h
  obtain ⟨hg, hj, -, hpos⟩ := hW.bar hb
  refine ⟨hg, hj, ?_⟩
  simp only at hk
  rw [hW.take hg hj.le] at hk
  rcases hpos with hpos | hpos
  · refine .inl ⟨hpos, ?_⟩
    have hh := headE_length (A := A) (B := B) (S := S) (g := g) (col := (P g).col)
    rw [← hk, fullE_eq, show j = (headE A B S g (P g).col).length by omega, List.take_left,
      headE_bar]
  · refine .inr ⟨hpos, ?_⟩
    have h12 := post_take12 (D := D) (g := g) (c := (P g).c) (vals := (P g).vals)
    have e : (postE D g (P g).c (P g).vals ++ [exitE]).take 10 =
        wldE :: (storesE D g (P g).vals 8 ++ [fbE]) := by
      rw [show 10 = min 10 12 from rfl, ← List.take_take, h12]
      simp [List.take_append, storesE_length]
    rw [← hk, hpos, show ldIdx g (P g) + 11 = ldIdx g (P g) + 1 + 10 by omega, take_post, e]
    simp only [List.countP_append, List.countP_cons, preLd_bar,
      storesE_count Execution.isBar (fun j => by simp [stE, Execution.isBar])]
    simp [Execution.isBar, ldE, wldE, fbE]

omit hW in
/-- The warp-collective `tcgen05` events. -/
theorem tc_coll {ev : Event} (h : isTcColl ev = true) :
    (∃ pc grp dst a, ev = ⟨pc, .tc (.resource grp dst a)⟩) ∨
      (∃ pc ta vs sh, ev = ⟨pc, .tc (.ld ta vs sh)⟩) ∨ (∃ pc, ev = ⟨pc, .tc .waitLd⟩) ∨
      (∃ pc ta vs sh, ev = ⟨pc, .tc (.st ta vs sh)⟩) ∨ (∃ pc, ev = ⟨pc, .tc .waitSt⟩) := by
  obtain ⟨pc, kd⟩ := ev
  cases kd <;> simp [isTcColl] at h
  rename_i tk
  cases tk <;> simp at h <;> simp

theorem Wit.tcK {g j k : Nat} (h : X.TcK (g, j) k) : g < 128 ∧ j < m g ∧
    ((g / 32 = 0 ∧ j = 0 ∧ k = 0) ∨ (j = ldIdx g (P g) ∧ k = if g / 32 = 0 then 1 else 0) ∨
      (j = ldIdx g (P g) + 1 ∧ k = if g / 32 = 0 then 2 else 1) ∨
      (g / 32 = 0 ∧ j = ldIdx g (P g) + 13 ∧ k = 3)) := by
  obtain ⟨⟨ev, hget, hc⟩, hk⟩ := h
  simp only at hk
  have hpre := preLd_tc (A := A) (B := B) (S := S) (g := g) (P g)
  rcases tc_coll hc with ⟨pc, grp, dst, act, rfl⟩ | ⟨pc, ta, vs, sh, rfl⟩ | ⟨pc, rfl⟩ |
      ⟨pc, ta, vs, sh, rfl⟩ | ⟨pc, rfl⟩
  · rcases hW.resource hget with ⟨d, n, rfl, rfl, rfl⟩ | ⟨ta, n, rfl, rfl, rfl⟩
    · obtain ⟨hg, hj, h32, rfl, -⟩ := hW.talloc hget
      exact ⟨hg, hj, .inl ⟨h32, rfl, by simp at hk; exact hk.symm⟩⟩
    obtain ⟨hg, hj, h32, hpos, -⟩ := hW.tdealloc hget
    refine ⟨hg, hj, .inr (.inr (.inr ⟨h32, hpos, ?_⟩))⟩
    rw [hW.take hg hj.le, hpos, show ldIdx g (P g) + 13 = ldIdx g (P g) + 1 + 12 by omega,
      take_post, post_take12] at hk
    simp only [List.countP_append, List.countP_cons, hpre, ite_eq_left h32,
      storesE_count isTcColl (fun j => by simp [stE, isTcColl])] at hk
    simp [isTcColl, ldE, wldE, fbE, bar1E, fa2E] at hk
    omega
  · obtain rfl := hW.tld_shape hget
    obtain ⟨hg, hj, hpos, -⟩ := hW.tld hget
    refine ⟨hg, hj, .inr (.inl ⟨hpos, ?_⟩)⟩
    rw [hW.take hg hj.le, hpos, fullE_preLd, List.take_append_of_le_length (by rw [preLd_length]),
      List.take_of_length_le (by rw [preLd_length]), hpre] at hk
    exact hk.symm
  · obtain ⟨hg, hj, hpos⟩ := hW.waitLd hget
    refine ⟨hg, hj, .inr (.inr (.inl ⟨hpos, ?_⟩))⟩
    rw [hW.take hg hj.le, hpos, show ldIdx g (P g) + 1 = ldIdx g (P g) + 1 + 0 from rfl,
      take_post] at hk
    simp only [List.countP_append, List.countP_cons, hpre, List.take_zero, List.countP_nil] at hk
    by_cases h32 : g / 32 = 0 <;> simp [h32, isTcColl, ldE] at hk ⊢ <;> omega
  · exact (hW.no_tst hget).elim
  · exact (hW.no_waitSt hget).elim
omit hW in
theorem po_baseCausality {g i j : Nat} (hij : i < j) (hj : j < (X.tr g).length)
    (hna : (X.get (g, i)).bind Event.acc = none) : baseCausality L X (g, i) (g, j) :=
  .single (.inl (po_of_source_not_access rfl hij hj hna))

/-- Every memory access, with its footprint. -/
theorem Wit.access {g j : Nat} {a' : Acc} {w : Bool} (h : X.Access (g, j) a' w) :
    g < 128 ∧ j < m g ∧
    ((a' = { loc := tslot S, size := 4 } ∧ ((w = false ∧ j = hd g) ∨ (w = true ∧ g = 0 ∧ j = 1))) ∨
      (∃ k < 8, a' = stAcc D g k ∧ j = ldIdx g (P g) + 2 + k ∧ w = true)) := by
  rcases h with ⟨bs, ⟨pc, hr⟩, rfl⟩ | ⟨bs, ⟨pc, hw⟩, rfl⟩ | ⟨o, n, pc, hm⟩
  rotate_left 2
  · exact (hW.no_rmw hm).elim
  · obtain ⟨hg, hj, rfl, rfl, -⟩ := hW.reads hr
    exact ⟨hg, hj, .inl ⟨rfl, .inl ⟨rfl, rfl⟩⟩⟩
  · obtain ⟨hg, hj, hc⟩ := hW.writes hw
    refine ⟨hg, hj, ?_⟩
    rcases hc with ⟨rfl, rfl, rfl, -⟩ | ⟨k, hk, rfl, rfl, -⟩
    · exact .inl ⟨rfl, .inr ⟨rfl, rfl, rfl⟩⟩
    · exact .inr ⟨k, hk, rfl, rfl, rfl⟩

theorem Wit.no_nc {e : EvId} {a' : Acc} {bs : List (Option Byte)} : ¬ X.NcReads e a' bs := by
  rintro ⟨pc, h⟩
  obtain ⟨g, j⟩ := e
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  · gemm_leaves
  · simp at hev

theorem Wit.no_ub (hu : ∀ g < 128, u g = []) : ¬ HasUb X := by
  rintro ⟨⟨g, j⟩, pc, f, h⟩
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f', -, hu'⟩⟩ := hW.cases h
  · gemm_leaves
  · rw [hu g hg] at hu'; simp at hu'
theorem Wit.no_tensor {e : EvId} {addr : Nat} {spec : TensorCopy.Spec} :
    ¬ X.TensorIssue e addr spec := by
  rintro ⟨pc,h⟩
  obtain ⟨g,j⟩ := e
  obtain ⟨_,⟨_,hc⟩ | ⟨_,pc',f,hev,_⟩⟩ := hW.cases h
  · gemm_leaves
  · simp at hev

theorem Wit.no_tensorStore {e : EvId} {addr : Nat} {spec : TensorStore.Spec} :
    ¬ X.TensorStoreIssue e addr spec := by
  rintro ⟨pc,h⟩
  obtain ⟨g,j⟩ := e
  obtain ⟨_,⟨_,hc⟩ | ⟨_,pc',f,hev,_⟩⟩ := hW.cases h
  · gemm_leaves
  · simp at hev

theorem Wit.no_tensorPrefetch {e : EvId} {addr : Nat} {spec : TensorPrefetch.Spec} :
    ¬ X.TensorPrefetchIssue e addr spec := by
  rintro ⟨pc,h⟩
  obtain ⟨g,j⟩ := e
  obtain ⟨_,⟨_,hc⟩ | ⟨_,pc',f,hev,_⟩⟩ := hW.cases h
  · gemm_leaves
  · simp at hev

theorem Wit.no_clc {e : EvId} {spec : Clc.Spec} {targets : List Nat} :
    ¬ X.ClcIssue e spec targets := by
  rintro ⟨pc,h⟩
  obtain ⟨g,j⟩ := e
  obtain ⟨_,⟨_,hc⟩ | ⟨_,pc',f,hev,_⟩⟩ := hW.cases h
  · gemm_leaves
  · simp at hev

theorem Wit.no_shfl {g j pc : Nat} {md : ShflMode} {v r : Value} {b' c' : Nat} {ok : Bool}
    (h : X.get (g, j) = some ⟨pc, .shfl md v b' c' r ok⟩) : False := by
  obtain ⟨hg, ⟨hj, hc⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.cases h
  · gemm_leaves
  · simp at hev


/-- Every event is of the Tensor Core/mbarrier/bulk class. -/
theorem Wit.tcBulk : X.TcBulk := by
  rintro ⟨g, j⟩ pc kind h
  obtain ⟨_, ⟨_, hc⟩ | ⟨_, pc', f, hev, _⟩⟩ := hW.cases h
  · rcases hc with (c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c |
      c | c | c | c | c) <;>
    first
      | (obtain ⟨_, _, _, hev⟩ := c; cases hev; rfl)
      | (obtain ⟨_, _, hev⟩ := c; cases hev; rfl)
      | (obtain ⟨_, hev⟩ := c; cases hev; rfl)
  · cases hev; rfl

omit hW in
/-- A thread that exited performed its whole trace. -/
theorem trace_full {mem0 : Mem0} (hX : Consistent L kernel [] mem0 X)
    (hW : Wit A B D L.sharedBase X P m u)
    {g j pc : Nat} (h : X.get (g, j) = some ⟨pc, .exit⟩) :
    g < 128 ∧ m g = (fullE A B D L.sharedBase g (P g)).length ∧
      X.tr g = fullE A B D L.sharedBase g (P g) := by
  obtain ⟨hg, hj, hpos⟩ := hW.exit h
  have hl := hW.len g hg
  have hend := end_last hX h (.inr rfl)
  have hlen := hW.length g hg
  rw [fullE_length] at hl ⊢
  have hm : m g = ldIdx g (P g) + if g / 32 = 0 then 15 else 14 := by
    split_ifs at hpos hl ⊢ <;> omega
  have hu : u g = [] := List.eq_nil_of_length_eq_zero (by omega)
  refine ⟨hg, hm, ?_⟩
  rw [hW.tr g hg, hu, List.append_nil, List.take_of_length_le]
  rw [fullE_length, hm]


/-- Every mbarrier operand is `bar0` or `bar1`. -/
theorem Wit.uses_mbar {e : EvId} {mb : Loc} (hu : X.UsesMbar e mb) :
    mb = bar0 S ∨ mb = bar1 S := by
  obtain ⟨g, j⟩ := e
  rcases hu with ⟨tx, count, release, scope, pc, hp⟩ | ⟨s, hc, hm⟩ | ⟨noinc, pc, hp⟩ |
    ⟨s, rank, ⟨pc, hp⟩, ht⟩ | ⟨pc, q, ok, acquire, scope, hp⟩ | ⟨pc, hp⟩ |
    ⟨_, _, hi, _⟩ | ⟨_, _, _, hi, _⟩ | ⟨c, pc, hp⟩
  · exact .inl (hW.arrive hp).2.2.2.2.1
  · rw [(hW.copy_spec hc).1] at hm
    exact .inl (AsyncCopy.Completion.mbarrier.inj hm).symm
  · exact (hW.no_asyncArrive hp).elim
  · obtain ⟨-, -, -, -, rfl⟩ := hW.commit hp
    exact .inr (TcCommit.target_unicast_inv rfl ht).2
  · rcases (hW.wait hp).2.2.2 with ⟨-, -, -, h, -⟩ | ⟨-, -, h, -⟩
    · exact .inl h
    · exact .inr h
  · exact (hW.no_inval hp).elim
  · exact (hW.no_tensor hi).elim
  · exact (hW.no_clc hi).elim
  · rcases (hW.mbInit hp).2.2.2.2 with ⟨-, h⟩ | ⟨-, h⟩
    · exact .inl h
    · exact .inr h

/-- Both source instructions issue copies; their effects need not have occurred yet. -/
theorem Wit.bulkA (h : 6 < m 0) : X.Copy (0, 6) (specA A S) :=
  ⟨Flow.bulkCopy_0, by rw [hW.get_of_lt (by decide) h, fullAt_head _ (by decide)]; rfl⟩

theorem Wit.bulkB (h : 7 < m 0) : X.Copy (0, 7) (specB B S) :=
  ⟨Flow.bulkCopy_1, by rw [hW.get_of_lt (by decide) h, fullAt_head _ (by decide)]; rfl⟩

end

end


end PTX.Kernels.TcGemm.Proof
