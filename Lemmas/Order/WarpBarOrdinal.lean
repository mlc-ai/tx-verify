-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.WaitOrderEnables
public import Lemmas.Flow.NthEv
public import Lemmas.Flow.ElectLead
public import Lemmas.Step.WarpLanes
public import Lemmas.Tcgen05.TcExtend

@[expose] public section

/-! # The warp barriers of two lanes, by their ordinals

A proof tool for DEP-WARP-BARRIER. Two lanes `g`, `h` of one warp each of whose `bar.warp.sync`
names the other's lane in its member mask take part in the same rendezvous in the same order:

* every warp barrier of `h` has a partner of `g` in its instance (`WarpBar.partner`): a warp
  barrier has returned, so the event of each lane of its mask is a need that is filled (`KindNeeds`,
  DEP-ORDER);
* partners come in program order (`WarpBar.mono`): two crossed partner pairs make a cycle of the
  dependency order, each return preceding the thread's later events (`Resumes`, a blocking
  return) and each participant's arrival preceding the other's return (a `Witness`), which
  `DependencyOk.acyclic` excludes;
* so partners have the same ordinal among their thread's warp barriers (`WarpBar.ordinal_eq`,
  counted by `warpBars`).

`WarpBar.sync` turns a partner pair into causality (`WarpBarSync`): what a lane did before its
warp barrier happens before what the other lane does after its own. -/

namespace PTX
noncomputable section

/-- A `bar.warp.sync` event. -/
def Execution.isWarpBar : Event → Bool
  | ⟨_, .warpBar ..⟩ => true
  | _ => false

/-- The warp barriers of thread `g` before its event `i`. -/
def warpBars (X : Execution) (g i : Nat) : Nat := ((X.tr g).take i).countP Execution.isWarpBar

namespace WarpBar

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- Two warp barriers of one instance (`WarpBarEdge` without the warp). -/
def Partner (X : Execution) (y x : EvId) : Prop :=
  ∃ m inst, X.WarpBar y m inst ∧ X.WarpBar x m inst

theorem Partner.symm {y x : EvId} (h : Partner X y x) : Partner X x y := by
  obtain ⟨m, inst, h1, h2⟩ := h
  exact ⟨m, inst, h2, h1⟩

theorem lt_len {e : EvId} {m inst : Nat} (h : X.WarpBar e m inst) : e.2 < (X.tr e.1).length := by
  obtain ⟨pc, hp⟩ := h
  exact len_of_get hp

/-- The count of warp barriers grows by one over a warp barrier. -/
theorem warpBars_succ {g i m inst : Nat} (h : X.WarpBar (g, i) m inst) :
    warpBars X g (i + 1) = warpBars X g i + 1 := by
  obtain ⟨pc, hp⟩ := h
  have hp' : (X.tr g)[i]? = some ⟨pc, .warpBar m inst⟩ := hp
  simp only [warpBars]
  rw [List.take_add_one, hp', Option.toList_some, List.countP_append]
  simp [Execution.isWarpBar]

/-- A smaller count of warp barriers comes first. -/
theorem lt_of_warpBars_lt {g i j : Nat} (h : warpBars X g i < warpBars X g j) : i < j := by
  by_contra hle
  have := Flow.countP_take_mono Execution.isWarpBar (X.tr g) (Nat.le_of_not_lt hle)
  simp only [warpBars] at h
  omega

/-- A warp barrier has returned, so its needs are filled (DEP-ORDER). -/
theorem ready (hX : Consistent L K A mem0 X) {e : EvId} {m inst : Nat}
    (he : X.WarpBar e m inst) : Ready L X e := by
  obtain ⟨pc, hp⟩ := he
  exact hX.dependency.ready _ (by simp [Returned, hp, Kind.resume])

/-- The need of lane `l` of a warp barrier whose mask names `l`: the event of that lane of the same
instance. -/
theorem need_mem {e : EvId} {m inst l : Nat} (he : X.WarpBar e m inst) (hl : electMember m l) :
    Need.node (fun x => ∃ j, x = .thread (warpLane L e.1 l, j) ∧
      X.WarpBar (warpLane L e.1 l, j) m inst) ∈ Needs L X e := by
  obtain ⟨pc, hp⟩ := he
  simp only [Needs, hp, KindNeeds, List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨l, ⟨hl.1, by simpa using hl.2⟩, rfl⟩

/-- **A warp barrier of `h` has a partner of `g`** when its mask names `g`'s lane. -/
theorem partner (hX : Consistent L K A mem0 X) {g h y m inst : Nat} (hs : SameWarp L h g)
    (hy : X.WarpBar (h, y) m inst) (hm : electMember m (laneOf L g)) :
    ∃ x, Partner X (h, y) (g, x) := by
  obtain ⟨-, -, x, rfl, hx⟩ := ready hX hy _ (need_mem hy hm)
  rw [Step.warpLane_of_sameWarp hs] at hx
  exact ⟨x, m, inst, hy, hx⟩

/-- The arrival of a participant precedes the return of another: it fills a need of it. -/
theorem depStep (hX : Consistent L K A mem0 X) {y x : EvId} (hs : SameWarp L y.1 x.1)
    (h : Partner X y x) : DepStep L K X (.thread y, false) (.thread x, true) := by
  obtain ⟨m, inst, hy, hx⟩ := h
  have hl := need_mem (L := L) hx (hX.warpBar.1 _ _ _ hy).2
  rw [Step.warpLane_of_sameWarp (sameWarp_symm hs)] at hl
  obtain ⟨pc, hp⟩ := hy
  exact DepStep.of_witness L (Witness.of_need L hl ⟨_, hp⟩ ⟨y.2, rfl, pc, hp⟩)

/-- A warp barrier's return precedes the thread's later instructions. -/
theorem resumes {g i j m inst : Nat} (he : X.WarpBar (g, i) m inst) (hij : i < j)
    (hj : j < (X.tr g).length) :
    DepStep L K X (.thread (g, i), true) (.thread (g, j), false) := by
  obtain ⟨pc, hp⟩ := he
  exact DepStep.of_resumes L (Resumes.of_blocking (b := true) hp rfl ⟨rfl, hij, hj⟩)

/-- **Partners come in program order.** -/
theorem mono (hX : Consistent L K A mem0 X) {g h y y' x x' : Nat} (hs : SameWarp L h g)
    (hp : Partner X (h, y) (g, x)) (hp' : Partner X (h, y') (g, x')) (hyy : y < y') :
    x < x' := by
  by_contra hle
  obtain ⟨m, inst, hy, hx⟩ := hp
  obtain ⟨m', inst', hy', hx'⟩ := hp'
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hle) with hlt | rfl
  · have hc : Relation.TransGen (DepStep L K X) (.thread (h, y), true) (.thread (h, y), true) :=
      .tail (.tail (.tail (.single (resumes hy hyy (lt_len hy')))
        (depStep hX hs ⟨m', inst', hy', hx'⟩)) (resumes hx' hlt (lt_len hx)))
        (depStep hX (sameWarp_symm hs) ⟨m, inst, hx, hy⟩)
    exact DepStepAcyclic.of_dependency hX.dependency _ hc
  · obtain ⟨pc, hpx⟩ := hx
    obtain ⟨pc', hpx'⟩ := hx'
    rw [hpx] at hpx'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.warpBar.injEq] at hpx'
    obtain ⟨-, -, rfl⟩ := hpx'
    have he := (hX.warpBar.2 _ _ _ _ _ hy hy' (Flow.sameWarp_self (hX.warpBar.1 _ _ _ hy).1)).2 rfl
    simp only [Prod.mk.injEq] at he
    omega

/-- The lower bound of the ordinals: a partner of a warp barrier of `h` has at least as many
earlier warp barriers. -/
theorem le_ordinal (hX : Consistent L K A mem0 X) {g h : Nat} (hs : SameWarp L h g)
    (hm : ∀ j m inst, X.WarpBar (h, j) m inst → electMember m (laneOf L g)) :
    ∀ n y x, Partner X (h, y) (g, x) → warpBars X h y = n → n ≤ warpBars X g x := by
  intro n
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro y x hp hn
    obtain ⟨y', hy'y, ev, hev, hq, hcnt⟩ := Flow.exists_nth Execution.isWarpBar (X.tr h)
      (n := n) (k := y) (by simp only [warpBars] at hn; omega)
    obtain ⟨pc, m, inst, rfl⟩ : ∃ pc m inst, ev = ⟨pc, .warpBar m inst⟩ := by
      obtain ⟨pc, kind⟩ := ev
      cases kind <;> simp_all [Execution.isWarpBar]
    have hwb : X.WarpBar (h, y') m inst := ⟨pc, hev⟩
    obtain ⟨x', hp'⟩ := partner hX hs hwb (hm _ _ _ hwb)
    have hle := ih y' x' hp' hcnt
    have hxx := mono hX hs hp' hp hy'y
    obtain ⟨m', inst', -, hx'⟩ := hp'
    have h1 := warpBars_succ hx'
    have h2 := Flow.countP_take_mono Execution.isWarpBar (X.tr g) (show x' + 1 ≤ x by omega)
    simp only [warpBars] at h1 h2 hle ⊢
    omega

/-- **Partners have the same ordinal** among their threads' warp barriers, when the masks of
both lanes' warp barriers name the other lane. -/
theorem ordinal_eq (hX : Consistent L K A mem0 X) {g h y x : Nat} (hs : SameWarp L h g)
    (hmh : ∀ j m inst, X.WarpBar (h, j) m inst → electMember m (laneOf L g))
    (hmg : ∀ j m inst, X.WarpBar (g, j) m inst → electMember m (laneOf L h))
    (hp : Partner X (h, y) (g, x)) : warpBars X h y = warpBars X g x :=
  Nat.le_antisymm (le_ordinal hX hs hmh _ y x hp rfl)
    (le_ordinal hX (sameWarp_symm hs) hmg _ x y hp.symm rfl)

/-- **A partner pair is causality** from before one lane's warp barrier to after the other's. -/
theorem sync {g h y x w k : Nat} (hs : SameWarp L h g) (hp : Partner X (h, y) (g, x))
    (hwy : w < y) (hxk : x < k) (hk : k < (X.tr g).length) : baseCausality L X (h, w) (g, k) := by
  obtain ⟨m, inst, hy, hx⟩ := hp
  exact .single (.inr (.inr (.inr (.inr (.inl ⟨y, x, ⟨hs, m, inst, hy, hx⟩, hwy, hxk, hk⟩)))))

end WarpBar

end
end PTX
