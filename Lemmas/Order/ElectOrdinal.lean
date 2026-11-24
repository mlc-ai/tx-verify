-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.WaitOrderEnables
public import Lemmas.Flow.NthEv
public import Lemmas.Flow.ElectLead
public import Lemmas.Step.WarpLanes
public import Lemmas.Tcgen05.TcExtend

@[expose] public section

/-! # Elections of one instance, by ordinal

A proof tool for a path of the dependency order from one lane of a warp to another through an
election (`elect.sync`, a rendezvous of its instance: DEP-WARP-ELECT, DEP-ORDER).

* **An election precedes what follows another lane's election of its instance**
  (`elect_depStep`): the event `e` fills a need of the return of `f`, which precedes each later
  event of `f`'s thread.
* **`ElectOrdinal`**: two elections of one instance in one warp are each lane's election of one
  ordinal (the lanes' elections before them are equally many). Instance labels are matching
  witnesses, not ordinals (DEP-WARP-ELECT), so it is proved from the order of the rendezvous, as
  `WarpBar.ordinal_eq` is for `bar.warp.sync`:
  * every election of `h` whose mask names the lane of `g` has a partner of `g` in its instance
    (`ElectOrd.partner`): an election has returned, so the election of each lane of its mask is a
    need that is filled (`KindNeeds`, DEP-ORDER);
  * partners come in program order (`ElectOrd.mono`): two crossed partner pairs make a cycle of
    the dependency order, each return preceding the thread's later events (`Resumes`, a blocking
    return) and each participant's arrival preceding the other's return (a `Witness`), which
    `DependencyOk.acyclic` excludes;
  * so partners have the same ordinal when the masks of both lanes' elections name the other
    lane (`ElectOrd.ordinal_eq`).

  The mask premise is needed: a lane may elect alone (a mask naming only itself) before an
  election of both lanes. `electOrdinal` proves `ElectOrdinal` when the elections of one warp
  name each other's lanes (`ElectMutual`), which holds when every election uses the full mask
  (`ElectMutual.of_full`). -/

namespace PTX

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- An election event. -/
def isElectEv (ev : Event) : Bool :=
  match ev.kind with
  | .elect .. => true
  | _ => false

/-- **The elections of one instance in one warp have one ordinal.** -/
def ElectOrdinal (L : Launch) (X : Execution) : Prop :=
  ∀ {e f : EvId} {pc pc' mask mask' inst l l' : Nat}, SameWarp L e.1 f.1 →
    X.Elect e pc mask inst l → X.Elect f pc' mask' inst l' →
    ((X.tr e.1).take e.2).countP isElectEv = ((X.tr f.1).take f.2).countP isElectEv

/-- The member mask of each election names the lane of each thread of its warp that elects. -/
def ElectMutual (L : Launch) (X : Execution) : Prop :=
  ∀ {e f : EvId} {pc pc' mask mask' inst inst' l l' : Nat}, SameWarp L e.1 f.1 →
    X.Elect e pc mask inst l → X.Elect f pc' mask' inst' l' → electMember mask (laneOf L f.1)

/-- Elections with the full mask name each other's lanes. -/
theorem ElectMutual.of_full
    (h : ∀ {e : EvId} {pc mask inst l : Nat}, X.Elect e pc mask inst l → mask = 4294967295) :
    ElectMutual L X := by
  intro e f pc pc' mask mask' inst inst' l l' _ he _
  rw [h he]
  have hl : laneOf L f.1 < 32 := Nat.mod_lt _ (by decide)
  revert hl
  generalize laneOf L f.1 = lane
  revert lane
  decide

/-- An election has returned, so its needs are filled (DEP-ORDER). -/
theorem elect_ready (hX : Consistent L K A mem0 X) {e : EvId} {pc mask inst l : Nat}
    (he : X.Elect e pc mask inst l) : Ready L X e := by
  have hp : X.get e = some ⟨pc, .elect mask inst l⟩ := he
  exact hX.dependency.ready _ (by simp [Returned, hp, Kind.resume])

/-- The need of lane `j` of an election whose mask names `j`: the election of that lane of the
same instance. -/
theorem elect_need_mem {e : EvId} {pc mask inst l j : Nat} (he : X.Elect e pc mask inst l)
    (hj : electMember mask j) :
    Need.node (fun x => ∃ k pc leader, x = .thread (warpLane L e.1 j, k) ∧
      X.get (warpLane L e.1 j, k) = some ⟨pc, .elect mask inst leader⟩) ∈ Needs L X e := by
  have hp : X.get e = some ⟨pc, .elect mask inst l⟩ := he
  simp only [Needs, hp, KindNeeds, List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨j, ⟨hj.1, by simpa using hj.2⟩, rfl⟩

/-- **An election precedes each later event of another lane's election of its instance.** -/
theorem elect_depStep (hX : Consistent L K A mem0 X) {e f : EvId}
    {pc pc' mask mask' inst l l' k : Nat} (hw : SameWarp L e.1 f.1)
    (he : X.Elect e pc mask inst l) (hf : X.Elect f pc' mask' inst l')
    (hfk : f.2 < k) (hk : k < (X.tr f.1).length) :
    Relation.TransGen (DepStep L K X) (.thread e, false) (.thread (f.1, k), false) := by
  obtain ⟨-, rfl, -⟩ := hX.elect.2.1 _ _ _ _ _ _ _ _ _ he hf hw
  have hn := elect_need_mem (L := L) hf (hX.elect.1 _ _ _ _ _ he).2.1
  rw [Step.warpLane_of_sameWarp (sameWarp_symm hw)] at hn
  have hp : X.get f = some ⟨pc', .elect mask inst l'⟩ := hf
  exact (Relation.TransGen.single (DepStep.of_witness L
    (Witness.of_need L hn (x := .thread e) ⟨_, he⟩ ⟨e.2, pc, l, rfl, he⟩))).tail
    (DepStep.of_resumes L (Resumes.of_blocking (b := true) hp rfl ⟨rfl, hfk, hk⟩))

/-- The elections of thread `g` before its event `i`. -/
def elections (X : Execution) (g i : Nat) : Nat := ((X.tr g).take i).countP isElectEv

namespace ElectOrd

/-- Two elections of one instance. -/
def Partner (X : Execution) (y x : EvId) : Prop :=
  ∃ pc pc' mask mask' inst l l', X.Elect y pc mask inst l ∧ X.Elect x pc' mask' inst l'

theorem Partner.symm {y x : EvId} (h : Partner X y x) : Partner X x y := by
  obtain ⟨pc, pc', mask, mask', inst, l, l', h1, h2⟩ := h
  exact ⟨pc', pc, mask', mask, inst, l', l, h2, h1⟩

theorem lt_len {e : EvId} {pc mask inst l : Nat} (h : X.Elect e pc mask inst l) :
    e.2 < (X.tr e.1).length :=
  len_of_get h

/-- The count of elections grows by one over an election. -/
theorem elections_succ {g i pc mask inst l : Nat} (h : X.Elect (g, i) pc mask inst l) :
    elections X g (i + 1) = elections X g i + 1 := by
  have hp : (X.tr g)[i]? = some ⟨pc, .elect mask inst l⟩ := h
  simp only [elections]
  rw [List.take_add_one, hp, Option.toList_some, List.countP_append]
  simp [isElectEv]

/-- **An election of `h` has a partner of `g`** when its mask names `g`'s lane. -/
theorem partner (hX : Consistent L K A mem0 X) {g h y pc mask inst l : Nat}
    (hs : SameWarp L h g) (hy : X.Elect (h, y) pc mask inst l)
    (hm : electMember mask (laneOf L g)) : ∃ x, Partner X (h, y) (g, x) := by
  obtain ⟨-, -, x, pc', l', rfl, hx⟩ := elect_ready hX hy _ (elect_need_mem hy hm)
  rw [Step.warpLane_of_sameWarp hs] at hx
  exact ⟨x, pc, pc', mask, mask, inst, l, l', hy, hx⟩

/-- The arrival of a participant precedes the return of another: it fills a need of it. -/
theorem depStep (hX : Consistent L K A mem0 X) {y x : EvId} (hs : SameWarp L y.1 x.1)
    (h : Partner X y x) : DepStep L K X (.thread y, false) (.thread x, true) := by
  obtain ⟨pc, pc', mask, mask', inst, l, l', hy, hx⟩ := h
  obtain ⟨-, rfl, -⟩ := hX.elect.2.1 _ _ _ _ _ _ _ _ _ hy hx hs
  have hn := elect_need_mem (L := L) hx (hX.elect.1 _ _ _ _ _ hy).2.1
  rw [Step.warpLane_of_sameWarp (sameWarp_symm hs)] at hn
  exact DepStep.of_witness L (Witness.of_need L hn (x := .thread y) ⟨_, hy⟩ ⟨y.2, pc, l, rfl, hy⟩)

/-- An election's return precedes the thread's later instructions. -/
theorem resumes {g i j pc mask inst l : Nat} (he : X.Elect (g, i) pc mask inst l) (hij : i < j)
    (hj : j < (X.tr g).length) :
    DepStep L K X (.thread (g, i), true) (.thread (g, j), false) :=
  DepStep.of_resumes L (Resumes.of_blocking (b := true) he rfl ⟨rfl, hij, hj⟩)

/-- **Partners come in program order.** -/
theorem mono (hX : Consistent L K A mem0 X) {g h y y' x x' : Nat} (hs : SameWarp L h g)
    (hp : Partner X (h, y) (g, x)) (hp' : Partner X (h, y') (g, x')) (hyy : y < y') :
    x < x' := by
  by_contra hle
  obtain ⟨pc, pc', mask, mask', inst, l, l', hy, hx⟩ := hp
  obtain ⟨qc, qc', nask, nask', inst', k, k', hy', hx'⟩ := hp'
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hle) with hlt | rfl
  · have hc : Relation.TransGen (DepStep L K X) (.thread (h, y), true) (.thread (h, y), true) :=
      .tail (.tail (.tail (.single (resumes hy hyy (lt_len hy')))
        (depStep hX hs ⟨qc, qc', nask, nask', inst', k, k', hy', hx'⟩))
        (resumes hx' hlt (lt_len hx)))
        (depStep hX (sameWarp_symm hs) ⟨pc', pc, mask', mask, inst, l', l, hx, hy⟩)
    exact DepStepAcyclic.of_dependency hX.dependency _ hc
  · unfold Execution.Elect at hx hx'
    rw [hx] at hx'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.elect.injEq] at hx'
    obtain ⟨-, -, rfl, -⟩ := hx'
    have hg := (hX.elect.1 _ _ _ _ _ hy).1
    have he := (hX.elect.2.1 _ _ _ _ _ _ _ _ _ hy hy' (Flow.sameWarp_self hg)).2.2.2 rfl
    simp only [Prod.mk.injEq] at he
    omega

/-- The lower bound of the ordinals: a partner of an election of `h` has at least as many
earlier elections. -/
theorem le_ordinal (hX : Consistent L K A mem0 X) {g h : Nat} (hs : SameWarp L h g)
    (hm : ∀ j pc mask inst l, X.Elect (h, j) pc mask inst l → electMember mask (laneOf L g)) :
    ∀ n y x, Partner X (h, y) (g, x) → elections X h y = n → n ≤ elections X g x := by
  intro n
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro y x hp hn
    obtain ⟨y', hy'y, ev, hev, hq, hcnt⟩ := Flow.exists_nth isElectEv (X.tr h)
      (n := n) (k := y) (by simp only [elections] at hn; omega)
    obtain ⟨pc, mask, inst, l, rfl⟩ : ∃ pc mask inst l, ev = ⟨pc, .elect mask inst l⟩ := by
      obtain ⟨pc, kind⟩ := ev
      cases kind <;> simp_all [isElectEv]
    have hel : X.Elect (h, y') pc mask inst l := hev
    obtain ⟨x', hp'⟩ := partner hX hs hel (hm _ _ _ _ _ hel)
    have hle := ih y' x' hp' hcnt
    have hxx := mono hX hs hp' hp hy'y
    obtain ⟨_, qc', _, nask', _, _, k', _, hx'⟩ := hp'
    have h1 := elections_succ hx'
    have h2 := Flow.countP_take_mono isElectEv (X.tr g) (show x' + 1 ≤ x by omega)
    simp only [elections] at h1 h2 hle ⊢
    omega

/-- **Partners have the same ordinal** among their threads' elections, when the masks of both
lanes' elections name the other lane. -/
theorem ordinal_eq (hX : Consistent L K A mem0 X) {g h y x : Nat} (hs : SameWarp L h g)
    (hmh : ∀ j pc mask inst l, X.Elect (h, j) pc mask inst l → electMember mask (laneOf L g))
    (hmg : ∀ j pc mask inst l, X.Elect (g, j) pc mask inst l → electMember mask (laneOf L h))
    (hp : Partner X (h, y) (g, x)) : elections X h y = elections X g x :=
  Nat.le_antisymm (le_ordinal hX hs hmh _ y x hp rfl)
    (le_ordinal hX (sameWarp_symm hs) hmg _ x y hp.symm rfl)

end ElectOrd

/-- **The elections of one instance in one warp have one ordinal** when the elections of one
warp name each other's lanes. -/
theorem electOrdinal (hX : Consistent L K A mem0 X) (hm : ElectMutual L X) :
    ElectOrdinal L X := by
  intro e f pc pc' mask mask' inst l l' hs he hf
  obtain ⟨h, y⟩ := e
  obtain ⟨g, x⟩ := f
  show elections X h y = elections X g x
  exact ElectOrd.ordinal_eq hX hs (fun j _ _ _ _ hj => hm (e := (h, j)) (f := (g, x)) hs hj hf)
    (fun j _ _ _ _ hj => hm (e := (g, j)) (f := (h, y)) (sameWarp_symm hs) hj he)
    ⟨pc, pc', mask, mask', inst, l, l', he, hf⟩

end
end PTX
