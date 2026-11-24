-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.WaitOrderEnables
public import Lemmas.Order.WaitOrderObject
public import Lemmas.Async.AsyncOrigins
public import Lemmas.Protocol.PollPhase
public import Lemmas.Order.CausalObjectWaitCount
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! # Round attribution for one slot of an mbarrier ring

A proof tool. One slot of a ring has one full object `F` and one empty object `E a` per
producer `a`. Uses of the slot are numbered `0, 1, …`. Producer `a`, for its use `s`, arrives on
`F` (`aF a s`); before it, for every `1 ≤ n ≤ s`, its successful poll of `E a` for use `n`
(`wE a n`) guards the arrival (`Resumes`). Consumer `b`, for its use `t`, issues a commit
(`cm b t`) whose asynchronous notification of `E a` is `note b a t`; its successful polls of `F`
for the uses `j ≤ t` (`wF b j`) guard the commit.

Each object is read only through its own history, and no phase number is assumed:
* `SF` are the counted arrivals of `F`, as pairs (producer, use), with their phases `phF`;
  `SE a` the counted notifications of `E a`, as pairs (consumer, use), with phases `phE a`.
* The successful poll `wF b j` observes some completed phase `oF b j` of `F`, and with it every
  counted arrival of that phase (`obsF`); that phase holds `np` counted arrivals (`fullF`).
  Earlier polls of the same consumer are present and observed earlier phases (`ltF`). The same
  for `wE a n`, `n ≥ 1`, on `E a` (`oE`, `obsE`, `fullE`, `ltE`; `nc` notifications).
  All of these are facts of one checked history: `Consistent.observed_of_phase` gives
  `MbarObserved` from the phases, and with it the poll's `Witness`,
  `MBarrier.CheckedLog.card_unit_arrivals_phase` the size of a completed phase, and
  `MBarrier.CheckedLog.selected_observed_lt` (one poller with alternating parity) the increase
  of the observed phases. No budget on the phase at a poll is assumed, and no rule that a phase
  is observed before the next phase's arrivals is used (OBJ-MBAR-STATE reports that as a fault).

Attribution, from the acyclicity of the dependency order (`DepStep`) alone. The poll for use `j`
observes exactly the arrivals of use `j`, one per producer (`content_full`, `observes_full`), and
the producer's poll for use `n + 1` exactly the notifications of use `n`, one per consumer
(`content_empty`, `observes_empty`); an asynchronous update of a producer's operation observed by
the consumer's poll for use `j` comes from a use at most `j` (`tx_le`).

The proof is a well-founded induction along the dependency order (`reach`): for every counted
arrival of use `s` and every `j < s`, consumer `b`'s poll for use `j` precedes it (`ReachF`), and
for every counted notification of use `t` and every `1 ≤ n ≤ t`, producer `a`'s poll for use `n`
precedes it (`ReachE`). For the arrival, the notifications observed by `a`'s polls `1, …, s`
precede it, so by induction they are of uses below their poll (a later use would close a
dependency cycle),
which with the counts and the increase of the observed phases makes the phase observed by
`wE a (j + 1)` exactly the notifications of use `j` (`content`); the one of consumer `b` closes
the path `wF b j → cm b j → note → wE a (j + 1) → aF a s`. The notification is symmetric,
through `wE a n → aF a n → wF b n → cm b t`. An induction on the use index alone does not
close: the attribution of `F` at use `j` needs that of `E a` at use `j`, which needs that of `F`
at use `j + 1`.

Order and phase numbers, from `DependencyOk.acyclic` (DEP-ORDER, object `F` or `E a`). The same
paths order each object's history (`not_before_of_reach`): a counted arrival of use `s` is not
before any consumer's poll for a use `j < s` in `F`'s history (`not_before_full`), and a counted
notification of use `t` is not before producer `a`'s poll for a use `1 ≤ n ≤ t` in `E a`'s history
(`not_before_empty`). So the arrival units before the poll for use `j` are at most `np · (j + 1)`,
which is the budget of `selected_poll_phase_of_units`: the poll for use `j` found phase `j + 1`
(`full_poll_phase`), and the producer's poll for use `n` found phase `n` (`empty_poll_phase`). -/

namespace PTX.MbarRing.Round

open AsyncCopy

/-- Counting on one object: when the phases `o 0 < o 1 < … < o J` each hold `|κ|` items and
the items of phase `o j` have uses at most `j`, phase `o j` holds exactly the items `(k, j)`. -/
theorem content {κ : Type} [Fintype κ] [DecidableEq κ] (S : Finset (κ × Nat))
    (ph : κ × Nat → Nat) (o : Nat → Nat) (J : Nat)
    (hlt : ∀ j j', j < j' → j' ≤ J → o j < o j')
    (hfull : ∀ j ≤ J, (S.filter (fun x => ph x = o j)).card = Fintype.card κ)
    (hle : ∀ j ≤ J, ∀ x ∈ S, ph x = o j → x.2 ≤ j) :
    ∀ j ≤ J, (∀ x ∈ S, ph x = o j → x.2 = j) ∧ ∀ k, (k, j) ∈ S ∧ ph (k, j) = o j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have h1 : ∀ x ∈ S, ph x = o j → x.2 = j := by
      intro x hx hp
      have hle' := hle j hj x hx hp
      by_contra hne
      have hlt' : x.2 < j := by omega
      obtain ⟨-, h2⟩ := ih x.2 hlt' (by omega)
      have := (h2 x.1).2
      rw [Prod.mk.eta, hp] at this
      have := hlt x.2 j hlt' hj
      omega
    refine ⟨h1, fun k => ?_⟩
    have hsub : S.filter (fun x => ph x = o j) ⊆ Finset.univ ×ˢ {j} := by
      intro x hx
      obtain ⟨hxS, hxp⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mpr (h1 x hxS hxp)⟩
    have heq : S.filter (fun x => ph x = o j) = Finset.univ ×ˢ {j} :=
      Finset.eq_of_subset_of_card_le hsub (by simp [hfull j hj])
    have hmem : (k, j) ∈ S.filter (fun x => ph x = o j) :=
      heq ▸ Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_singleton_self _⟩
    exact Finset.mem_filter.mp hmem

/-- Each mbarrier history of a consistent execution is checked. -/
theorem _root_.PTX.Execution.objects_checked {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} (X : Execution) (hX : Consistent L K A mem0 X) (m : Loc) :
    MBarrier.CheckedLog (X.objects m) :=
  (hX.tma.2.2.1 m).1

/-- A successful poll recorded in an object history is a successful wait event of a thread on
that object. -/
theorem _root_.PTX.Consistent.wait_of_record {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X) {m : Loc} {j : Nat}
    {w : MBarrier.Record Ref} (hj : (X.objects m)[j]? = some w)
    (hw : w.reply.waited = some true) :
    ∃ k pc parity acq ws, w.id = .thread k ∧ X.get k = some ⟨pc, .wait m parity true acq ws⟩ := by
  have hch := X.objects_checked hX m
  have hmem := List.mem_of_getElem? hj
  cases hid : w.id with
  | async i q =>
    obtain ⟨_, p, _, ha, _⟩ := hch.okPoll hj hw
    have hc := async_counter hX.tma.2.2.1 hmem hid
    rw [ha] at hc
    exact hc.elim
  | thread k =>
    obtain ⟨g, i⟩ := k
    have hs := (hX.object_thread_waited_iff hmem hid (hch.waited_no_fault hj hw)).mp hw
    cases he : X.get (g, i) with
    | none => simp [he] at hs
    | some ev =>
      obtain ⟨pc, kind⟩ := ev
      cases kind <;> simp [he, sourceWaitSuccess] at hs
      rename_i target parity ok acq sc
      obtain ⟨rfl, rfl⟩ : ok = true ∧ target = m := by cases ok <;> simp_all
      exact ⟨(g, i), pc, parity, acq, sc, rfl, he⟩

/-- Glue from one object's history to `MbarObserved`: a successful poll that observes phase `q`
observed every fault-free counter update recorded in phase `q`. -/
theorem _root_.PTX.Consistent.observed_of_phase {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X) {m : Loc} {i j q : Nat}
    {d w : MBarrier.Record Ref} (hni : MBarrier.NoInval (X.objects m))
    (hi : (X.objects m)[i]? = some d) (hdf : d.fault = none)
    (hcu : CounterUpdate d.action) (hj : (X.objects m)[j]? = some w)
    (hw : w.reply.waited = some true) (hp : MBarrier.phaseAt (X.objects m) i = some q)
    (ho : MBarrier.observedAt (X.objects m) j = some q) : MbarObserved X d.id w.id := by
  have hch := X.objects_checked hX m
  obtain ⟨k, pc, parity, acq, ws, hk, hget⟩ := hX.wait_of_record hj hw
  have hu := MbarRing.Slot.updateBeforeWait_of_phase hch hni hi hdf hj
    (hch.waited_no_fault hj hw) hw hp ho
  rw [hk] at hu ⊢
  refine ⟨object_record_present hX.tma (List.mem_of_getElem? hi), k, m, acq, ws, rfl,
    ⟨⟨pc, parity, hget⟩, hu⟩, fun r hr hid => ?_⟩
  obtain ⟨k', hk'⟩ := List.mem_iff_getElem?.mp hr
  have := ObjectInit.checked_record_index_eq hch hk' hi hid
  subst this
  rw [hk'] at hi
  cases hi
  exact hcu

/-- The dependency order alone has no cycle (DEP-ORDER, with the order of any one object). -/
theorem _root_.PTX.Consistent.depAcyclic {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X) :
    ∀ n, ¬ Relation.TransGen (DepStep L K X) n n := fun n h =>
  hX.dependency.acyclic (.cluster 0) trivial n (Relation.TransGen.mono (fun _ _ => Or.inl) _ _ h)

section
variable {L : Launch} {K : Kernel} {A : List Assumption} {X : Execution}

/-- One slot of a ring with `np` producers and `nc` consumers. -/
structure Slot (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) (np nc : Nat) where
  wE : Fin np → Nat → EvId
  aF : Fin np → Nat → EvId
  wF : Fin nc → Nat → EvId
  cm : Fin nc → Nat → EvId
  note : Fin nc → Fin np → Nat → Ref
  SF : Finset (Fin np × Nat)
  phF : Fin np × Nat → Nat
  SE : Fin np → Finset (Fin nc × Nat)
  phE : Fin np → Fin nc × Nat → Nat
  /-- The completed phase of `F` observed by consumer `b`'s poll for use `j`. -/
  oF : Fin nc → Nat → Nat
  /-- The completed phase of `E a` observed by producer `a`'s poll for use `n ≥ 1`. -/
  oE : Fin np → Nat → Nat
  /-- Thread layer: a producer's polls for the uses `1, …, s` guard its arrival of use `s`. -/
  guardP : ∀ x ∈ SF, ∀ n, 1 ≤ n → n ≤ x.2 → Resumes K X (wE x.1 n) (aF x.1 x.2)
  /-- Thread layer: a consumer's polls for the uses `0, …, t` guard its commit of use `t`. -/
  guardM : ∀ a, ∀ y ∈ SE a, ∀ j ≤ y.2, Resumes K X (wF y.1 j) (cm y.1 y.2)
  /-- A commit's issue precedes its notification in the dependency order. -/
  issue : ∀ a, ∀ y ∈ SE a, DepStep L K X (.thread (cm y.1 y.2), false) (note y.1 a y.2, false)
  /-- Object `F`: the poll observes every counted arrival of the phase it observes. -/
  obsF : ∀ b j, X.RefPresent (.thread (wF b j)) → ∀ x ∈ SF, phF x = oF b j →
    Witness L X (.thread (aF x.1 x.2)) (wF b j)
  /-- Object `E a`: the poll observes every counted notification of the phase it observes. -/
  obsE : ∀ a n, 1 ≤ n → X.RefPresent (.thread (wE a n)) → ∀ y ∈ SE a, phE a y = oE a n →
    Witness L X (note y.1 a y.2) (wE a n)
  /-- Object `F`: an observed phase holds `np` counted arrivals. -/
  fullF : ∀ b j, X.RefPresent (.thread (wF b j)) → (SF.filter (fun x => phF x = oF b j)).card = np
  /-- Object `E a`: an observed phase holds `nc` counted notifications. -/
  fullE : ∀ a n, 1 ≤ n → X.RefPresent (.thread (wE a n)) →
    ((SE a).filter (fun y => phE a y = oE a n)).card = nc
  /-- Object `F`: a consumer's earlier poll is present and observed an earlier phase. -/
  ltF : ∀ b j j', j < j' → X.RefPresent (.thread (wF b j')) →
    X.RefPresent (.thread (wF b j)) ∧ oF b j < oF b j'
  /-- Object `E a`: the producer's earlier poll is present and observed an earlier phase. -/
  ltE : ∀ a n n', 1 ≤ n → n < n' → X.RefPresent (.thread (wE a n')) →
    X.RefPresent (.thread (wE a n)) ∧ oE a n < oE a n'

namespace Slot
variable {np nc : Nat} (R : Slot L K A X np nc)

theorem present_of_guard {w f : EvId} (h : Resumes K X w f) : X.RefPresent (.thread w) :=
  present_of_len (by obtain ⟨⟨h1, h2, h3⟩, -⟩ := h; rw [h1]; omega)

/-- Every consumer's poll for a use below `s` precedes producer `x.1`'s arrival of use `s`. -/
def ReachF (x : Fin np × Nat) : Prop :=
  ∀ b j, j < x.2 →
    Relation.TransGen (DepStep L K X) (.thread (R.wF b j), true) (.thread (R.aF x.1 x.2), false)

/-- Producer `a`'s polls for the uses `1, …, t` precede consumer `y.1`'s notification of use `t`. -/
def ReachE (a : Fin np) (y : Fin nc × Nat) : Prop :=
  ∀ n, 1 ≤ n → n ≤ y.2 →
    Relation.TransGen (DepStep L K X) (.thread (R.wE a n), true) (R.note y.1 a y.2, false)

/-- The phases observed by producer `a`'s polls `1, …, s` hold the notifications of the uses
`0, …, s - 1`, when the notifications they observe are of uses below the poll. -/
theorem content_empty_of {a : Fin np} {s : Nat}
    (hpres : ∀ n, 1 ≤ n → n ≤ s → X.RefPresent (.thread (R.wE a n)))
    (hle : ∀ n, 1 ≤ n → n ≤ s → ∀ y ∈ R.SE a, R.phE a y = R.oE a n → y.2 + 1 ≤ n) :
    ∀ m, m + 1 ≤ s → (∀ y ∈ R.SE a, R.phE a y = R.oE a (m + 1) → y.2 = m) ∧
      ∀ b, (b, m) ∈ R.SE a ∧ R.phE a (b, m) = R.oE a (m + 1) := by
  cases s with
  | zero => intro m hm; omega
  | succ s =>
    have h := content (R.SE a) (R.phE a) (fun m => R.oE a (m + 1)) s
      (fun j j' hjj hj' => (R.ltE a (j + 1) (j' + 1) (by omega) (by omega)
        (hpres (j' + 1) (by omega) (by omega))).2)
      (fun j hj => by
        simpa using R.fullE a (j + 1) (by omega) (hpres (j + 1) (by omega) (by omega)))
      (fun j hj y hy hp => by have := hle (j + 1) (by omega) (by omega) y hy hp; omega)
    exact fun m hm => h m (by omega)

/-- The phases observed by consumer `b`'s polls `0, …, t` hold the arrivals of the uses
`0, …, t`, when the arrivals they observe are of uses at most the poll's. -/
theorem content_full_of {b : Fin nc} {t : Nat} (hpres : X.RefPresent (.thread (R.wF b t)))
    (hle : ∀ j ≤ t, ∀ x ∈ R.SF, R.phF x = R.oF b j → x.2 ≤ j) :
    ∀ j ≤ t, (∀ x ∈ R.SF, R.phF x = R.oF b j → x.2 = j) ∧
      ∀ a, (a, j) ∈ R.SF ∧ R.phF (a, j) = R.oF b j := by
  have hp : ∀ j ≤ t, X.RefPresent (.thread (R.wF b j)) := fun j hj => by
    rcases Nat.lt_or_eq_of_le hj with h | rfl
    · exact (R.ltF b j t h hpres).1
    · exact hpres
  exact content R.SF R.phF (R.oF b) t
    (fun j j' hjj hj' => (R.ltF b j j' hjj (hp j' hj')).2)
    (fun j hj => by simpa using R.fullF b j (hp j hj)) hle

/-- The dependency paths, by well-founded induction along the dependency order. -/
theorem reach (hacyc : ∀ n, ¬ Relation.TransGen (DepStep L K X) n n) :
    (∀ x ∈ R.SF, R.ReachF x) ∧ ∀ a, ∀ y ∈ R.SE a, R.ReachE a y := by
  classical
  let nodeF : Fin np × Nat → Ref × Bool := fun x => (.thread (R.aF x.1 x.2), false)
  let nodeE : Fin np → Fin nc × Nat → Ref × Bool := fun a y => (R.note y.1 a y.2, false)
  let nodes : Finset (Ref × Bool) :=
    R.SF.image nodeF ∪ Finset.univ.biUnion (fun a => (R.SE a).image (nodeE a))
  let P : Ref × Bool → Prop := fun n =>
    (∀ x ∈ R.SF, n = nodeF x → R.ReachF x) ∧ ∀ a, ∀ y ∈ R.SE a, n = nodeE a y → R.ReachE a y
  have hmemF : ∀ x ∈ R.SF, nodeF x ∈ nodes := fun x hx =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)
  have hmemE : ∀ a, ∀ y ∈ R.SE a, nodeE a y ∈ nodes := fun a y hy =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _,
      Finset.mem_image_of_mem _ hy⟩)
  have hall := induction_of_acyclic hacyc nodes P (fun node _ ih => by
    refine ⟨fun x hx hn => ?_, fun a y hy hn => ?_⟩
    · -- the arrival `x = (a, s)`
      subst hn
      have hpres : ∀ n, 1 ≤ n → n ≤ x.2 → X.RefPresent (.thread (R.wE x.1 n)) :=
        fun n h1 h2 => present_of_guard (R.guardP x hx n h1 h2)
      have hle : ∀ n, 1 ≤ n → n ≤ x.2 → ∀ y ∈ R.SE x.1, R.phE x.1 y = R.oE x.1 n →
          y.2 + 1 ≤ n := by
        intro n h1 h2 y hy hp
        by_contra hgt
        have hobs := R.obsE x.1 n h1 (hpres n h1 h2) y hy hp
        have hpath : Relation.TransGen (DepStep L K X) (nodeE x.1 y) (nodeF x) :=
          .tail (.single (DepStep.of_witness L hobs)) (DepStep.of_resumes L (R.guardP x hx n h1 h2))
        have hr := (ih _ (hmemE x.1 y hy) hpath).2 x.1 y hy rfl n h1 (by omega)
        exact hacyc _ (hr.tail (DepStep.of_witness L hobs))
      intro b j hj
      obtain ⟨hyS, hyp⟩ := (R.content_empty_of hpres hle j (by omega)).2 b
      exact .tail (.tail (.tail (.single (DepStep.of_resumes L (R.guardM x.1 (b, j) hyS j le_rfl)))
        (R.issue x.1 (b, j) hyS))
        (DepStep.of_witness L (R.obsE x.1 (j + 1) (by omega) (hpres (j + 1) (by omega) (by omega))
          (b, j) hyS hyp)))
        (DepStep.of_resumes L (R.guardP x hx (j + 1) (by omega) (by omega)))
    · -- the notification `y = (b, t)` of `E a`
      subst hn
      have hpres : X.RefPresent (.thread (R.wF y.1 y.2)) :=
        present_of_guard (R.guardM a y hy y.2 le_rfl)
      have hle : ∀ j ≤ y.2, ∀ x ∈ R.SF, R.phF x = R.oF y.1 j → x.2 ≤ j := by
        intro j hj x hx hp
        by_contra hgt
        have hobs := R.obsF y.1 j (present_of_guard (R.guardM a y hy j hj)) x hx hp
        have hpath : Relation.TransGen (DepStep L K X) (nodeF x) (nodeE a y) :=
          .tail (.tail (.single (DepStep.of_witness L hobs))
            (DepStep.of_resumes L (R.guardM a y hy j hj))) (R.issue a y hy)
        have hr := (ih _ (hmemF x hx) hpath).1 x hx rfl y.1 j (by omega)
        exact hacyc _ (hr.tail (DepStep.of_witness L hobs))
      intro n h1 h2
      obtain ⟨hxS, hxp⟩ := (R.content_full_of hpres hle n h2).2 a
      exact .tail (.tail (.tail (.single (DepStep.of_resumes L (R.guardP (a, n) hxS n h1 le_rfl)))
        (DepStep.of_witness L
          (R.obsF y.1 n (present_of_guard (R.guardM a y hy n h2)) (a, n) hxS hxp)))
        (DepStep.of_resumes L (R.guardM a y hy n h2))) (R.issue a y hy))
  exact ⟨fun x hx => (hall _ (hmemF x hx)).1 x hx rfl,
    fun a y hy => (hall _ (hmemE a y hy)).2 a y hy rfl⟩

/-- Object `F`: the poll for use `j` observes a phase holding exactly the counted arrivals of
use `j`, one of each producer. -/
theorem content_full (hacyc : ∀ n, ¬ Relation.TransGen (DepStep L K X) n n) {b : Fin nc} {j : Nat}
    (hw : X.RefPresent (.thread (R.wF b j))) :
    (∀ x ∈ R.SF, R.phF x = R.oF b j → x.2 = j) ∧ ∀ a, (a, j) ∈ R.SF ∧ R.phF (a, j) = R.oF b j := by
  have hr := (R.reach hacyc).1
  refine R.content_full_of hw (fun j' hj' x hx hp => ?_) j le_rfl
  by_contra hgt
  have hpres : X.RefPresent (.thread (R.wF b j')) := by
    rcases Nat.lt_or_eq_of_le hj' with h | rfl
    · exact (R.ltF b j' j h hw).1
    · exact hw
  exact hacyc _ ((hr x hx b j' (by omega)).tail (DepStep.of_witness L (R.obsF b j' hpres x hx hp)))

/-- Object `E a`: the poll for use `n + 1` observes a phase holding exactly the counted
notifications of use `n`, one of each consumer. -/
theorem content_empty (hacyc : ∀ n, ¬ Relation.TransGen (DepStep L K X) n n) {a : Fin np} {n : Nat}
    (hw : X.RefPresent (.thread (R.wE a (n + 1)))) :
    (∀ y ∈ R.SE a, R.phE a y = R.oE a (n + 1) → y.2 = n) ∧
      ∀ b, (b, n) ∈ R.SE a ∧ R.phE a (b, n) = R.oE a (n + 1) := by
  have hr := (R.reach hacyc).2 a
  have hpres : ∀ k, 1 ≤ k → k ≤ n + 1 → X.RefPresent (.thread (R.wE a k)) := fun k h1 h2 => by
    rcases Nat.lt_or_eq_of_le h2 with h | rfl
    · exact (R.ltE a k (n + 1) h1 h hw).1
    · exact hw
  refine R.content_empty_of hpres (fun k h1 h2 y hy hp => ?_) n le_rfl
  by_contra hgt
  exact hacyc _ ((hr y hy k h1 (by omega)).tail
    (DepStep.of_witness L (R.obsE a k h1 (hpres k h1 h2) y hy hp)))

/-- The consumer's poll for use `j` observed producer `a`'s counted arrival of use `j`. -/
theorem observes_full (hacyc : ∀ n, ¬ Relation.TransGen (DepStep L K X) n n) {b : Fin nc} {j : Nat}
    (hw : X.RefPresent (.thread (R.wF b j))) (a : Fin np) :
    (a, j) ∈ R.SF ∧ Witness L X (.thread (R.aF a j)) (R.wF b j) := by
  obtain ⟨hS, hp⟩ := (R.content_full hacyc hw).2 a
  exact ⟨hS, R.obsF b j hw (a, j) hS hp⟩

/-- The producer's poll for use `n + 1` observed consumer `b`'s counted notification of use
`n`. -/
theorem observes_empty (hacyc : ∀ n, ¬ Relation.TransGen (DepStep L K X) n n) {a : Fin np} {n : Nat}
    (hw : X.RefPresent (.thread (R.wE a (n + 1)))) (b : Fin nc) :
    (b, n) ∈ R.SE a ∧ Witness L X (R.note b a n) (R.wE a (n + 1)) := by
  obtain ⟨hS, hp⟩ := (R.content_empty hacyc hw).2 b
  exact ⟨hS, R.obsE a (n + 1) (by omega) hw (b, n) hS hp⟩

/-- Transaction side: an asynchronous update (a copy's complete-tx, say) that the consumer's
poll for use `j` observes, and that an operation of producer `a` guarded by `a`'s polls for the
uses `1, …, t` precede, comes from a use `t ≤ j`, when consumer `b`'s commit of use `j`
notified `E a`. -/
theorem tx_le (hacyc : ∀ n, ¬ Relation.TransGen (DepStep L K X) n n) {a : Fin np}
    {b : Fin nc} {j t : Nat} {op : EvId} {tx : Ref}
    (hguard : ∀ n, 1 ≤ n → n ≤ t → Resumes K X (R.wE a n) op)
    (hpath : Relation.TransGen (DepStep L K X) (.thread op, false) (tx, false))
    (hobs : Witness L X tx (R.wF b j)) (hy : (b, j) ∈ R.SE a) : t ≤ j := by
  by_contra hgt
  have hgM := R.guardM a (b, j) hy j (Nat.le_refl _)
  have hgT := hguard (j + 1) (by omega) (by omega)
  have hoE := (R.observes_empty hacyc (present_of_guard hgT) b).2
  exact hacyc (.thread (R.wF b j), true)
    ((((Relation.TransGen.single (DepStep.of_resumes L hgM)).tail (R.issue a (b, j) hy)).tail
      (DepStep.of_witness L hoE)).tail (DepStep.of_resumes L hgT) |>.trans
        (hpath.tail (DepStep.of_witness L hobs)))

/-- DEP-ORDER: what a record's operation precedes in the dependency order is not before it in
any mbarrier's history. -/
theorem not_before_of_reach {mem0 : Mem0} (hX : Consistent L K A mem0 X) {m : Loc} {u w : Ref}
    (hp : Relation.TransGen (DepStep L K X) (w, true) (u, false)) :
    ¬ MBarrier.Before (X.objects m) u w := by
  intro hbef
  obtain ⟨i, -, r, -, hi, hri, -⟩ := id hbef
  have hpu : X.RefPresent u := hri ▸ object_record_present hX.tma (List.mem_of_getElem? hi)
  exact hX.dependency.acyclic (.mbar m) trivial _
    ((Relation.TransGen.mono (fun _ _ => Or.inl) _ _ (hp.tail (DepStep.node hpu))).tail
      (.inr ⟨rfl, rfl, hbef⟩))

/-- DEP-ORDER on `F`: a counted arrival of use `s` is not before, in any object's
history, a consumer's poll for a use `j < s`. -/
theorem not_before_full {mem0 : Mem0} (hX : Consistent L K A mem0 X) {m : Loc}
    {x : Fin np × Nat} (hx : x ∈ R.SF) {b : Fin nc} {j : Nat} (hj : j < x.2) :
    ¬ MBarrier.Before (X.objects m) (.thread (R.aF x.1 x.2)) (.thread (R.wF b j)) :=
  not_before_of_reach hX ((R.reach hX.depAcyclic).1 x hx b j hj)

/-- DEP-ORDER on `E a`: a counted notification of use `t` is not before, in any
object's history, producer `a`'s poll for a use `1 ≤ n ≤ t`. -/
theorem not_before_empty {mem0 : Mem0} (hX : Consistent L K A mem0 X) {m : Loc}
    {a : Fin np} {y : Fin nc × Nat} (hy : y ∈ R.SE a) {n : Nat} (h1 : 1 ≤ n) (hn : n ≤ y.2) :
    ¬ MBarrier.Before (X.objects m) (R.note y.1 a y.2) (.thread (R.wE a n)) :=
  not_before_of_reach hX ((R.reach hX.depAcyclic).2 a y hy n h1 hn)

/-! ### Fault freedom of the two objects

The arrivals below need not be counted: a faulting arrival is not in `SF` (or `SE a`), but the
thread layer still guards it. -/

end Slot

/-- Counting by uses: pairs of uses below `Q` that miss one such pair are fewer than
`|κ| · Q`. -/
theorem card_lt_of_uses {κ : Type} [Fintype κ] [DecidableEq κ] (T : Finset (κ × Nat)) {Q : Nat}
    (hT : ∀ x ∈ T, x.2 < Q) {z : κ × Nat} (hz : z.2 < Q) (hzT : z ∉ T) :
    T.card < Fintype.card κ * Q := by
  have hzU : z ∈ Finset.univ ×ˢ Finset.range Q :=
    Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr hz⟩
  have hsub : T ⊆ (Finset.univ ×ˢ Finset.range Q).erase z := fun x hx =>
    Finset.mem_erase.mpr ⟨fun h => hzT (h ▸ hx),
      Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr (hT x hx)⟩⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hzU, Finset.card_product] at h
  have hpos : 0 < Fintype.card κ * Q := Nat.mul_pos (Fintype.card_pos_iff.mpr ⟨z.1⟩) (by omega)
  simp at h
  omega

/-- Counting by uses: pairs of uses below `Q` are at most `|κ| · Q`. -/
theorem card_le_of_uses {κ : Type} [Fintype κ] [DecidableEq κ] (T : Finset (κ × Nat)) {Q : Nat}
    (hT : ∀ x ∈ T, x.2 < Q) : T.card ≤ Fintype.card κ * Q := by
  have hsub : T ⊆ Finset.univ ×ˢ Finset.range Q := fun x hx =>
    Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr (hT x hx)⟩
  simpa using Finset.card_le_card hsub

/-- One history's arrival units before a position, counted by the (participant, use) pairs of
the non-faulting arrivals before it. -/
theorem units_le_of_uses {κ : Type} [DecidableEq κ] {log : List (MBarrier.Record Ref)}
    (h : MBarrier.CheckedLog log) (upd : κ × Nat → Ref) (T : Finset (κ × Nat)) {i : Nat}
    (hunit : ∀ (k : Nat) (r : MBarrier.Record Ref) (c tx : Nat), log[k]? = some r →
      r.fault = none → r.action = .arrive c tx → c = 1)
    (hT : ∀ k < i, ∀ (r : MBarrier.Record Ref) (c tx : Nat), log[k]? = some r → r.fault = none →
      r.action = .arrive c tx → ∃ x ∈ T, r.id = upd x) :
    MBarrier.unitsBefore log i ≤ T.card := by
  classical
  refine (h.unitsBefore_le_card (T.image upd) hunit (fun k hk r c tx hr hf ha => ?_)).trans
    Finset.card_image_le
  obtain ⟨x, hx, hid⟩ := hT k hk r c tx hr hf ha
  exact Finset.mem_image.mpr ⟨x, hx, hid.symm⟩

/-- A selected successful poll whose earlier arrivals are of uses below `q`, with selected count
`q - 1 + δ`, found phase `q`. -/
theorem poll_phase {κ : Type} [Fintype κ] [DecidableEq κ] {log : List (MBarrier.Record Ref)}
    (h : MBarrier.CheckedLog log) (hni : MBarrier.NoInval log) (upd : κ × Nat → Ref)
    (S : Finset (κ × Nat)) (sel : Ref → Bool) {δ : Nat} (hδ : δ ≤ 1)
        (halt : MBarrier.SelectedAlternates sel log δ)
    (hcount : ∀ (k : Nat) (r : MBarrier.Record Ref) (c tx : Nat), log[k]? = some r →
      r.fault = none → r.action = .arrive c tx → c = 1 ∧ ∃ x ∈ S, r.id = upd x)
    (hexp : ∀ k st, MBarrier.stateBefore log k = some st → st.expected = Fintype.card κ)
    (hne : Nonempty κ) {k q : Nat} {w : MBarrier.Record Ref} (hq : 1 ≤ q)
    (hk : log[k]? = some w) (hww : w.reply.waited = some true) (hsel : sel w.id = true)
    (hcnt : MBarrier.selectedBefore sel log k = q - 1 + δ)
    (hearly : ∀ k' < k, ∀ (r : MBarrier.Record Ref) x, log[k']? = some r → r.fault = none →
      x ∈ S → r.id = upd x → x.2 < q) :
    ∃ st, MBarrier.stateBefore log k = some st ∧ st.phase = q := by
  classical
  obtain ⟨st, hst, hph⟩ := h.selected_poll_phase_of_units hni sel hδ halt hk hsel hww
    (fun st hst => by
      rw [hexp k st hst, hcnt]
      have hu := units_le_of_uses h upd (S.filter (fun x => x.2 < q))
        (fun k r c tx hr hf ha => (hcount k r c tx hr hf ha).1)
        (fun k' hk' r c tx hr hf ha => by
          obtain ⟨-, x, hx, hid⟩ := hcount k' r c tx hr hf ha
          exact ⟨x, Finset.mem_filter.mpr ⟨hx, hearly k' hk' r x hr hf hx hid⟩, hid⟩)
      have hc := card_le_of_uses (S.filter (fun x => x.2 < q)) (Q := q)
        (fun x hx => (Finset.mem_filter.mp hx).2)
      have hpos : 0 < Fintype.card κ := Fintype.card_pos
      have : Fintype.card κ * q < Fintype.card κ * (q - 1 + δ + 2 - δ) :=
        Nat.mul_lt_mul_of_pos_left (by omega) hpos
      omega)
  exact ⟨st, hst, by rw [hcnt] at hph; omega⟩

namespace Slot
variable {np nc : Nat} (R : Slot L K A X np nc)

/-- Exact phase at `F`: consumer `b`'s successful poll for use `j`, with `j + δ` earlier
selected successes of an alternating poller, found phase `j + 1`, so it observed phase `j`.
From `F`'s checked history: the counted arrivals are the unit arrivals of `SF`, and the
expected count is `np`. -/
theorem full_poll_phase {mem0 : Mem0} (hX : Consistent L K A mem0 X) (hnp : 0 < np) {m : Loc}
    (hni : MBarrier.NoInval (X.objects m))
    (sel : Ref → Bool) {δ : Nat} (hδ : δ ≤ 1)
    (halt : MBarrier.SelectedAlternates sel (X.objects m) δ)
    (hcount : ∀ (k : Nat) (r : MBarrier.Record Ref) (c tx : Nat), (X.objects m)[k]? = some r →
      r.fault = none → r.action = .arrive c tx →
      c = 1 ∧ ∃ x ∈ R.SF, r.id = .thread (R.aF x.1 x.2))
    (hexp : ∀ k st, MBarrier.stateBefore (X.objects m) k = some st → st.expected = np)
    {b : Fin nc} {j k : Nat} {w : MBarrier.Record Ref} (hk : (X.objects m)[k]? = some w)
    (hwid : w.id = .thread (R.wF b j)) (hww : w.reply.waited = some true)
    (hsel : sel w.id = true) (hcnt : MBarrier.selectedBefore sel (X.objects m) k = j + δ) :
    ∃ st, MBarrier.stateBefore (X.objects m) k = some st ∧ st.phase = j + 1 :=
  poll_phase (X.objects_checked hX m) hni (fun x : Fin np × Nat => Ref.thread
    (R.aF x.1 x.2)) R.SF sel
    hδ halt hcount (by simpa using hexp) ⟨⟨0, hnp⟩⟩ (by omega) hk hww hsel (by rw [hcnt]; omega)
    (fun k' hk' r' x hr' _ hx hid' => by
      by_contra hge
      exact R.not_before_full hX hx (b := b) (j := j) (by omega)
        ⟨k', k, r', w, hr', hid', hk, hwid, hk'⟩)

/-- Exact phase at `E a`: producer `a`'s successful poll for use `n ≥ 1`, with `n - 1 + δ`
earlier selected successes of an alternating poller, found phase `n`, so it observed phase
`n - 1`. From `E a`'s checked history: the counted arrivals are the unit notifications of
`SE a`, and the expected count is `nc`. -/
theorem empty_poll_phase {mem0 : Mem0} (hX : Consistent L K A mem0 X) (hnc : 0 < nc) {m : Loc}
    (hni : MBarrier.NoInval (X.objects m))
    {a : Fin np} (sel : Ref → Bool) {δ : Nat} (hδ : δ ≤ 1)
    (halt : MBarrier.SelectedAlternates sel (X.objects m) δ)
    (hcount : ∀ (k : Nat) (r : MBarrier.Record Ref) (c tx : Nat), (X.objects m)[k]? = some r →
      r.fault = none → r.action = .arrive c tx → c = 1 ∧ ∃ y ∈ R.SE a, r.id = R.note y.1 a y.2)
    (hexp : ∀ k st, MBarrier.stateBefore (X.objects m) k = some st → st.expected = nc)
    {n k : Nat} {w : MBarrier.Record Ref} (hn : 1 ≤ n) (hk : (X.objects m)[k]? = some w)
    (hwid : w.id = .thread (R.wE a n)) (hww : w.reply.waited = some true)
    (hsel : sel w.id = true) (hcnt : MBarrier.selectedBefore sel (X.objects m) k = n - 1 + δ) :
    ∃ st, MBarrier.stateBefore (X.objects m) k = some st ∧ st.phase = n :=
  poll_phase (X.objects_checked hX m) hni (fun y : Fin nc × Nat => R.note y.1 a y.2) (R.SE a) sel
    hδ halt hcount (by simpa using hexp) ⟨⟨0, hnc⟩⟩ hn hk hww hsel hcnt
    (fun k' hk' r' y hr' _ hy hid' => by
      by_contra hge
      exact R.not_before_empty hX hy (n := n) hn (by omega)
        ⟨k', k, r', w, hr', hid', hk, hwid, hk'⟩)

end Slot
end

end PTX.MbarRing.Round
