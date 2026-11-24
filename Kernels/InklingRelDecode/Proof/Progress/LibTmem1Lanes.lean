-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.PgTmem
public import Lemmas.Tmem.PairProtocol

@[expose] public section

/-!
# The lanes of a warp make one Tensor Memory operation (`cta_group::1`; promotion candidate)

`Lemmas/Tmem/PairProtocol.lean` proves, for the operations of one warp of each CTA of a two-CTA
cluster (`cta_group::2`, `TmemWarpOps`), that the lanes of a warp make their `n`-th operation as
one collective instance (`tcCount_eq`, `lanes_same_event`). Its proofs use the group only through
the operation's shape `TmemShape`. This file states them for a single CTA's operations
(`Tmem1Ops`, group one), with the same arguments, plus `tc_le_of_ops`: a lane that has made at most
`n` operations has made at most as many warp-collective `tcgen05` events as the lane's `n`-th
operation is preceded by.

Promote to `Lemmas/Tmem/PairProtocol.lean` with `TmemWarpOps` generalized over the group.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem1
open PTX Tmem.Pair

noncomputable section

variable {L : Launch} {K : Kernel} {mem0 : Mem0} {X : Execution} {w : Nat}

/-- The shape of a thread's `n`-th operation (`cta_group::1`). -/
theorem tmemOp_shape1 (ht : Tmem1Ops L X w) {h n j : Nat} (hh : h < L.threads)
    (hop : TmemOp X h n j) : h % L.block / 32 = w ∧
      ∃ pc dst act, X.get (h, j) = some ⟨pc, .tc (.resource .one dst act)⟩ ∧ TmemShape n act := by
  obtain ⟨⟨pc, grp, dst, act, he⟩, rfl⟩ := hop
  obtain ⟨h0, rfl, hs⟩ := ht.event hh he
  exact ⟨h0, pc, dst, act, he, hs⟩

/-- An event of a lane at the collective count of another lane's `n`-th operation is its own
`n`-th operation. -/
theorem tcK_lane1 (ht : Tmem1Ops L X w) (htc : ¬ AlignedMismatch L K X) {h1 h2 n j1 j2 j' : Nat}
    (hw : SameWarp L h1 h2) (hop1 : TmemOp X h1 n j1) (hop2 : TmemOp X h2 n j2)
    (hk : X.TcK (h2, j') (tcCount X h1 j1)) : j' = j2 := by
  obtain ⟨⟨ev, hget, hcoll⟩, hcnt⟩ := hk
  obtain ⟨pc', kf⟩ := ev
  cases kf <;> simp only [isTcColl, Bool.false_eq_true] at hcoll
  rename_i kf
  obtain ⟨-, pc, dst, act, hget1, hs1⟩ := tmemOp_shape1 ht hw.1.1 hop1
  have hst : tcStatic (.resource .one dst act) = tcStatic kf := by
    by_contra hne
    apply htc
    refine ⟨.tc, .inl ((AlignedClass.divergent_tc_iff L).mpr ⟨(h1, j1), (h2, j'), _, _, _, _, _, hw,
      tcK_of_op hop1, ⟨⟨_, hget, ?_⟩, hcnt⟩, hget1, hget, .inr hne⟩)⟩
    cases kf <;> simp_all [isTcColl]
  obtain ⟨grp', dst', act', rfl⟩ : ∃ grp' dst' act', kf = .resource grp' dst' act' := by
    cases kf <;> simp_all [tcStatic]
  simp only [tcStatic, TcKind.resource.injEq] at hst
  obtain ⟨-, -, rfl⟩ := hst
  have hs' := (ht.event hw.1.2.1 hget).2.2
  have hord := (actIdx_of_shape hs1).symm.trans (actIdx_of_shape hs')
  exact tmemOp_unique ⟨⟨_, _, _, _, hget⟩, hord.symm⟩ hop2

/-- **The lanes of a warp make their `n`-th operation as one collective instance.** -/
theorem tcCount_eq1 (ht : Tmem1Ops L X w) (htc : ¬ AlignedMismatch L K X) {h1 h2 n j1 j2 : Nat}
    (hw : SameWarp L h1 h2) (hop1 : TmemOp X h1 n j1) (hop2 : TmemOp X h2 n j2) :
    tcCount X h1 j1 = tcCount X h2 j2 := by
  have key : ∀ {a b ja jb : Nat}, SameWarp L a b → TmemOp X a n ja → TmemOp X b n jb →
      ¬ tcCount X a ja < tcCount X b jb := by
    intro a b ja jb hab hopa hopb hlt
    have hle : tcCount X b jb ≤ (X.tr b).countP isTcColl := (List.take_sublist _ _).countP_le
    obtain ⟨j', ev, hev, hp, hc⟩ := MbarRing.Slot.exists_nth_countP isTcColl (xs := X.tr b)
      (c := tcCount X a ja) (by omega)
    have hj := tcK_lane1 ht htc hab hopa hopb ⟨⟨ev, hev, hp⟩, hc⟩
    subst hj
    simp only [tcCount] at hc hlt
    omega
  have h21 : SameWarp L h2 h1 := ⟨⟨hw.1.2.1, hw.1.1, hw.1.2.2.symm⟩, hw.2.symm⟩
  have := key hw hop1 hop2
  have := key h21 hop2 hop1
  omega

/-- **The lanes of a warp make their `n`-th operation with one event.** -/
theorem lanes_same_event1 (ht : Tmem1Ops L X w) (htc : ¬ AlignedMismatch L K X)
    {h1 h2 n j1 j2 : Nat} (hw : SameWarp L h1 h2) (hop1 : TmemOp X h1 n j1)
    (hop2 : TmemOp X h2 n j2) : X.get (h1, j1) = X.get (h2, j2) := by
  have hk := tcCount_eq1 ht htc hw hop1 hop2
  obtain ⟨-, pc, dst, act, hget1, -⟩ := tmemOp_shape1 ht hw.1.1 hop1
  obtain ⟨-, pc', dst', act', hget2, -⟩ := tmemOp_shape1 ht hw.1.2.1 hop2
  have hst :
      pc = pc' ∧ tcStatic (.resource .one dst act) = tcStatic (.resource .one dst' act') := by
    by_contra hne
    apply htc
    refine ⟨.tc, .inl ((AlignedClass.divergent_tc_iff L).mpr ⟨(h1, j1), (h2, j2), _, _, _, _, _, hw,
      tcK_of_op hop1, by rw [hk]; exact tcK_of_op hop2, hget1, hget2, ?_⟩)⟩
    by_cases hp : pc = pc'
    · exact .inr fun h => hne ⟨hp, h⟩
    · exact .inl hp
  obtain ⟨rfl, hst⟩ := hst
  simp only [tcStatic] at hst
  rw [hget1, hget2, hst]

/-- **A lane that has made at most `n` operations has made at most `k` warp-collective `tcgen05`
events**, where `k` is the collective count of another lane's `n`-th operation: otherwise its
`k`-th event is aligned with that operation (same kind, same request), so it is its own `n`-th
operation. -/
theorem tc_le_of_ops (ht : Tmem1Ops L X w) (htc : ¬ AlignedMismatch L K X) {g h n j : Nat}
    (hw : SameWarp L g h) (hop : TmemOp X g n j) (hle : tmemOps (X.tr h) ≤ n) :
    (X.tr h).countP isTcColl ≤ tcCount X g j := by
  by_contra hlt
  obtain ⟨j', ev, hev, hp, hc⟩ := MbarRing.Slot.exists_nth_countP isTcColl (xs := X.tr h)
    (c := tcCount X g j) (by omega)
  obtain ⟨-, pc, dst, act, hget1, hs1⟩ := tmemOp_shape1 ht hw.1.1 hop
  obtain ⟨pc', kf⟩ := ev
  cases kf <;> simp only [isTcColl, Bool.false_eq_true] at hp
  rename_i kf
  have hevg : X.get (h, j') = some ⟨pc', .tc kf⟩ := hev
  have hst : tcStatic (.resource .one dst act) = tcStatic kf := by
    by_contra hne
    apply htc
    refine ⟨.tc, .inl ((AlignedClass.divergent_tc_iff L).mpr ⟨(g, j), (h, j'), _, _, _, _, _, hw,
      tcK_of_op hop, ⟨⟨_, hevg, ?_⟩, hc⟩, hget1, hevg, .inr hne⟩)⟩
    cases kf <;> simp_all [isTcColl]
  obtain ⟨grp', dst', act', rfl⟩ : ∃ grp' dst' act', kf = .resource grp' dst' act' := by
    cases kf <;> simp_all [tcStatic]
  simp only [tcStatic, TcKind.resource.injEq] at hst
  obtain ⟨-, -, rfl⟩ := hst
  have hs' := (ht.event hw.1.2.1 hevg).2.2
  have hord := (actIdx_of_shape hs1).symm.trans (actIdx_of_shape hs')
  have hmem : TmemOp X h n j' := ⟨⟨_, _, _, _, hevg⟩, hord.symm⟩
  have hj' : j' < (X.tr h).length := (List.getElem?_eq_some_iff.mp hev).1
  have h3 := tmemOps_lt_of_lt hmem hj'
  rw [List.take_length] at h3
  omega

end

end PTX.Kernels.InklingRelDecode.Proof.Tmem1
