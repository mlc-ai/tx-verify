-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ElectActor

@[expose] public section

/-! # Lanes that lead every election, or none

A proof tool. When every lane of a warp continues after an `elect.sync` (the elected lane
issues some operations, the others skip them), a thread's issue counts depend on which lane the
elections return. They are stated in two cases over the thread's trace: `ElectLead L g es`,
every election in `es` returned this thread's lane, and `ElectNonLead L g es`, none did. Both
hold of every prefix and change only at an election event (`electLead_snoc_elect`,
`electLead_snoc_of_ne`), so a run invariant carries conjuncts `ElectLead L g es → …` and
`ElectNonLead L g es → …`.

Which case holds is a fact about the execution: elections of one warp with one mask return one
leader (`ElectOk.deterministic`). A thread all of whose elections use one mask is `ElectLead`
or `ElectNonLead` (`electLead_or_nonLead`); a thread of the warp that elected at least once is
`ElectLead` exactly when its lane is the leader every other thread of the warp saw
(`electLead_iff`), so one thread of the warp leads (`electLead_unique`, `exists_leader`). -/

namespace PTX.Flow
open PTX

noncomputable section

/-- Every election in `es` returned the lane of thread `g`. -/
def ElectLead (L : Launch) (g : Nat) (es : List Event) : Prop :=
  ∀ e ∈ es, ∀ mask inst ld, e.kind = .elect mask inst ld → ld = laneOf L g

/-- No election in `es` returned the lane of thread `g`. -/
def ElectNonLead (L : Launch) (g : Nat) (es : List Event) : Prop :=
  ∀ e ∈ es, ∀ mask inst ld, e.kind = .elect mask inst ld → ld ≠ laneOf L g

/-- Every election in `es` uses the member mask `m`. -/
def ElectMask (m : Nat) (es : List Event) : Prop :=
  ∀ e ∈ es, ∀ mask inst ld, e.kind = .elect mask inst ld → mask = m

/-- Some election in `es` returned lane `ld`. -/
def Elected (es : List Event) (ld : Nat) : Prop :=
  ∃ e ∈ es, ∃ mask inst, e.kind = .elect mask inst ld

variable {L : Launch} {g : Nat}

/-! ### Along a trace -/

@[simp] theorem electLead_nil : ElectLead L g [] := fun _ h => absurd h List.not_mem_nil
@[simp] theorem electNonLead_nil : ElectNonLead L g [] := fun _ h => absurd h List.not_mem_nil

theorem electLead_append {a b : List Event} :
    ElectLead L g (a ++ b) ↔ ElectLead L g a ∧ ElectLead L g b := by
  simp only [ElectLead, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (.inl he), fun e he => h e (.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

theorem electNonLead_append {a b : List Event} :
    ElectNonLead L g (a ++ b) ↔ ElectNonLead L g a ∧ ElectNonLead L g b := by
  simp only [ElectNonLead, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (.inl he), fun e he => h e (.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

theorem ElectLead.of_sublist {a b : List Event} (h : ElectLead L g b) (hs : a.Sublist b) :
    ElectLead L g a :=
  fun e he => h e (hs.subset he)

theorem ElectNonLead.of_sublist {a b : List Event} (h : ElectNonLead L g b) (hs : a.Sublist b) :
    ElectNonLead L g a :=
  fun e he => h e (hs.subset he)

theorem ElectLead.take {es : List Event} (h : ElectLead L g es) (k : Nat) :
    ElectLead L g (es.take k) :=
  h.of_sublist (List.take_sublist k es)

theorem ElectNonLead.take {es : List Event} (h : ElectNonLead L g es) (k : Nat) :
    ElectNonLead L g (es.take k) :=
  h.of_sublist (List.take_sublist k es)

theorem ElectLead.of_snoc {es : List Event} {e : Event} (h : ElectLead L g (es ++ [e])) :
    ElectLead L g es :=
  (electLead_append.mp h).1

theorem ElectNonLead.of_snoc {es : List Event} {e : Event} (h : ElectNonLead L g (es ++ [e])) :
    ElectNonLead L g es :=
  (electNonLead_append.mp h).1

/-- An event that is no election changes neither case. -/
theorem electLead_snoc_of_ne {es : List Event} {e : Event}
    (he : ∀ mask inst ld, e.kind ≠ .elect mask inst ld) :
    ElectLead L g (es ++ [e]) ↔ ElectLead L g es :=
  ⟨ElectLead.of_snoc, fun h => electLead_append.mpr ⟨h, fun e' he' mask inst ld hk => by
    rw [List.mem_singleton.mp he'] at hk; exact absurd hk (he mask inst ld)⟩⟩

theorem electNonLead_snoc_of_ne {es : List Event} {e : Event}
    (he : ∀ mask inst ld, e.kind ≠ .elect mask inst ld) :
    ElectNonLead L g (es ++ [e]) ↔ ElectNonLead L g es :=
  ⟨ElectNonLead.of_snoc, fun h => electNonLead_append.mpr ⟨h, fun e' he' mask inst ld hk => by
    rw [List.mem_singleton.mp he'] at hk; exact absurd hk (he mask inst ld)⟩⟩

/-- An election keeps `ElectLead` exactly when it returns this lane. -/
theorem electLead_snoc_elect {es : List Event} {e : Event} {mask inst ld : Nat}
    (he : e.kind = .elect mask inst ld) :
    ElectLead L g (es ++ [e]) ↔ ElectLead L g es ∧ ld = laneOf L g := by
  rw [electLead_append]
  refine and_congr_right fun _ => ⟨fun h => h e (List.mem_singleton_self e) mask inst ld he,
    fun h e' he' mask' inst' ld' hk => ?_⟩
  rw [List.mem_singleton.mp he', he] at hk
  cases hk
  exact h

/-- An election keeps `ElectNonLead` exactly when it returns another lane. -/
theorem electNonLead_snoc_elect {es : List Event} {e : Event} {mask inst ld : Nat}
    (he : e.kind = .elect mask inst ld) :
    ElectNonLead L g (es ++ [e]) ↔ ElectNonLead L g es ∧ ld ≠ laneOf L g := by
  rw [electNonLead_append]
  refine and_congr_right fun _ => ⟨fun h => h e (List.mem_singleton_self e) mask inst ld he,
    fun h e' he' mask' inst' ld' hk => ?_⟩
  rw [List.mem_singleton.mp he', he] at hk
  cases hk
  exact h

/-- A trace with an election is not in both cases. -/
theorem not_electLead_and_nonLead {es : List Event} {ld : Nat} (he : Elected es ld)
    (h1 : ElectLead L g es) (h2 : ElectNonLead L g es) : False := by
  obtain ⟨e, hm, mask, inst, hk⟩ := he
  exact h2 e hm mask inst ld hk (h1 e hm mask inst ld hk)

/-- A trace without an election is in both cases. -/
theorem electLead_of_not_elected {es : List Event} (h : ∀ ld, ¬ Elected es ld) :
    ElectLead L g es ∧ ElectNonLead L g es :=
  ⟨fun e hm mask inst ld hk => absurd ⟨e, hm, mask, inst, hk⟩ (h ld),
    fun e hm mask inst ld hk => absurd ⟨e, hm, mask, inst, hk⟩ (h ld)⟩

/-! ### In an execution -/

variable {X : Execution}

/-- An election in a thread's trace is an election event of the execution. -/
theorem elect_of_mem {e : Event} {mask inst ld : Nat} (hm : e ∈ X.tr g)
    (hk : e.kind = .elect mask inst ld) : ∃ j, X.Elect (g, j) e.pc mask inst ld := by
  obtain ⟨j, hj, he⟩ := List.getElem_of_mem hm
  refine ⟨j, ?_⟩
  show (X.tr g)[j]? = some ⟨e.pc, .elect mask inst ld⟩
  rw [List.getElem?_eq_getElem hj, he, ← hk]

theorem sameWarp_self {h : Nat} (hh : h < L.threads) : SameWarp L h h := ⟨⟨hh, hh, rfl⟩, rfl⟩

/-- Two elections of one warp with one mask, in the traces of `g` and `h`, return one
leader. -/
theorem leader_eq (hok : ElectOk L X) {h m ld ld' : Nat} (hw : g = h ∨ SameWarp L g h)
    (hmg : ElectMask m (X.tr g)) (hmh : ElectMask m (X.tr h)) (he : Elected (X.tr g) ld)
    (hf : Elected (X.tr h) ld') : ld = ld' := by
  obtain ⟨e, hme, mask, inst, hke⟩ := he
  obtain ⟨f, hmf, mask', inst', hkf⟩ := hf
  obtain ⟨j, hj⟩ := elect_of_mem hme hke
  obtain ⟨j', hj'⟩ := elect_of_mem hmf hkf
  have h1 := hmg e hme mask inst ld hke
  have h2 := hmh f hmf mask' inst' ld' hkf
  subst h1 h2
  have hw' : SameWarp L g h := hw.elim (fun h' => h' ▸ sameWarp_self (hok.1 _ _ _ _ _ hj).1) id
  exact hok.deterministic hj hj' hw'

/-- **The two cases.** A thread all of whose elections use one mask either led every election
in its trace or none. -/
theorem electLead_or_nonLead (hok : ElectOk L X) {m : Nat} (hm : ElectMask m (X.tr g)) :
    ElectLead L g (X.tr g) ∨ ElectNonLead L g (X.tr g) := by
  by_cases h : Elected (X.tr g) (laneOf L g)
  · refine .inl fun e he mask inst ld hk => ?_
    exact leader_eq hok (.inl rfl) hm hm ⟨e, he, mask, inst, hk⟩ h
  · exact .inr fun e he mask inst ld hk hl => h (hl ▸ ⟨e, he, mask, inst, hk⟩)

/-- **Which case.** Let some thread `g` of the warp have seen leader `ld`. A thread `h` of the
warp that elected with the same mask leads exactly when its lane is `ld`. -/
theorem electLead_iff (hok : ElectOk L X) {h m ld ld' : Nat} (hw : SameWarp L g h)
    (hmg : ElectMask m (X.tr g)) (hmh : ElectMask m (X.tr h)) (he : Elected (X.tr g) ld)
    (hf : Elected (X.tr h) ld') : ElectLead L h (X.tr h) ↔ laneOf L h = ld := by
  have hl := leader_eq hok (.inr hw) hmg hmh he hf
  subst hl
  constructor
  · intro hd
    obtain ⟨f, hmf, mask, inst, hk⟩ := hf
    exact (hd f hmf mask inst _ hk).symm
  · intro hlane e hme mask inst ld hk
    rw [hlane]
    exact leader_eq hok (.inl rfl) hmh hmh ⟨e, hme, mask, inst, hk⟩ hf

theorem electNonLead_iff (hok : ElectOk L X) {h m ld ld' : Nat} (hw : SameWarp L g h)
    (hmg : ElectMask m (X.tr g)) (hmh : ElectMask m (X.tr h)) (he : Elected (X.tr g) ld)
    (hf : Elected (X.tr h) ld') : ElectNonLead L h (X.tr h) ↔ laneOf L h ≠ ld := by
  rw [Ne, ← electLead_iff hok hw hmg hmh he hf]
  refine ⟨fun h1 h2 => not_electLead_and_nonLead hf h2 h1, fun h1 => ?_⟩
  exact (electLead_or_nonLead hok hmh).resolve_left h1

/-- **One leader.** Two threads of a warp that elected with one mask and led their elections
are one thread. -/
theorem electLead_unique (hok : ElectOk L X) {h m ld ld' : Nat} (hw : SameWarp L g h)
    (hmg : ElectMask m (X.tr g)) (hmh : ElectMask m (X.tr h)) (he : Elected (X.tr g) ld)
    (hf : Elected (X.tr h) ld') (hg : ElectLead L g (X.tr g)) (hh : ElectLead L h (X.tr h)) :
    g = h := by
  have hlg : laneOf L g = ld := by
    obtain ⟨e, hme, mask, inst, hk⟩ := he
    exact (hg e hme mask inst ld hk).symm
  have hlh := (electLead_iff hok hw hmg hmh he hf).mp hh
  exact sameWarp_eq_of_lane_eq hw (hlg.trans hlh.symm)

/-- **A leader exists.** The leader `ld` a thread saw is a lane of its warp, and — every lane of
the warp being a launched thread (`hlane`) — the lane of a launched thread. The lanes of the mask
that did not elect are a need of the instance (`KindNeeds`, DEP-ORDER), not part of `ElectOk`, so
this says nothing about their traces. -/
theorem exists_leader (hok : ElectOk L X) {ld : Nat} (he : Elected (X.tr g) ld)
    (hlane : ∀ l, l < 32 → ∃ h, SameWarp L g h ∧ laneOf L h = l) :
    ∃ h, h < L.threads ∧ SameWarp L g h ∧ laneOf L h = ld := by
  obtain ⟨e, hme, mask, inst, hk⟩ := he
  obtain ⟨j, hj⟩ := elect_of_mem hme hk
  have hld : ld < 32 := (hok.1 _ _ _ _ _ hj).2.2.1
  obtain ⟨h, hw, hl⟩ := hlane ld hld
  exact ⟨h, hw.1.2.1, hw, hl⟩

end

end PTX.Flow
