-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Dependency
public import Lemmas.Tmem.AllocResult

@[expose] public section

namespace PTX.Tmem.Pair

/-! # Return dependency of a nonleader allocation participant -/

variable {L : Launch} {X Y : Execution} {i store : EvId} {dst : Loc}

theorem sameWarp_leader_eq {g h : Nat} (hw : SameWarp L g h)
    (hg : laneOf L g = 0) (hh : laneOf L h = 0) : g = h := by
  obtain ⟨⟨_, _, hc⟩, hw⟩ := hw
  have hlocal := Nat.div_add_mod (g % L.block) 32
  unfold laneOf at hg hh
  rw [hw, hg, ← hh, Nat.div_add_mod] at hlocal
  have hfull := Nat.div_add_mod g L.block
  rw [hc, ← hlocal, Nat.div_add_mod] at hfull
  exact hfull.symm

@[simp] theorem allocResultNeeds_leader {request : Tmem.Request} (hl : laneOf L i.1 = 0) :
    allocResultNeeds L X i request = [] := by
  cases request <;> simp [allocResultNeeds, hl]

@[simp] theorem allocResultNeeds_dealloc (base count : Nat) :
    allocResultNeeds L X i (.dealloc base count) = [] := rfl

@[simp] theorem allocResultNeeds_relinquish :
    allocResultNeeds L X i .relinquish = [] := rfl

theorem allocResultNeeds_nonleader {count : Nat} (hl : laneOf L i.1 ≠ 0) :
    allocResultNeeds L X i (.alloc count) = [.node (AllocResultFill L X i)] := by
  simp [allocResultNeeds, hl]

/-- A matching result write is a present fill for the nonleader's return. -/
theorem AllocResult.fills (h : AllocResult L X store i dst) {count : Nat}
    (hl : laneOf L i.1 ≠ 0) :
    ∃ fills, Need.node fills ∈ allocResultNeeds L X i (.alloc count) ∧
      X.RefPresent (.thread store) ∧ fills (.thread store) := by
  obtain ⟨_, site, hstore⟩ := h.writes
  exact ⟨AllocResultFill L X i, by rw [allocResultNeeds_nonleader hl]; simp,
    ⟨⟨site, .wr { loc := dst, size := 4 } _⟩, hstore⟩, ⟨dst, h⟩⟩

/-- A result fill establishes the presence of the result store. -/
theorem AllocResultFill.present {x : AsyncCopy.Ref} (h : AllocResultFill L X i x) :
    X.RefPresent x := by
  cases x with
  | thread store =>
    obtain ⟨dst, hr⟩ := h
    obtain ⟨bytes, site, he⟩ := hr.writes
    exact ⟨⟨site, .wr { loc := dst, size := 4 } bytes⟩, he⟩
  | async => exact h.elim

/-- Execution extension preserves result fills. -/
theorem AllocResultFill.mono {x : AsyncCopy.Ref} (h : AllocResultFill L X i x)
    (hle : X.le Y) : AllocResultFill L Y i x := by
  cases x with
  | thread store =>
    obtain ⟨dst, hr⟩ := h
    exact ⟨dst, hr.mono hle⟩
  | async => exact h.elim

/-- An extension creates no new result fill between a store and participant already present. -/
theorem AllocResultFill.of_prefix {x : AsyncCopy.Ref} (h : AllocResultFill L Y i x)
    (hle : X.le Y) (hx : X.RefPresent x) (hi : X.RefPresent (.thread i)) :
    AllocResultFill L X i x := by
  cases x with
  | thread store =>
    obtain ⟨dst, hr⟩ := h
    obtain ⟨_, hstore⟩ := hx
    obtain ⟨_, hparticipates⟩ := hi
    exact ⟨dst, hr.of_prefix hle (PTX.len_of_get hstore) (PTX.len_of_get hparticipates)⟩
  | async => exact h.elim

/-- A thread append preserves an old result fill, regardless of asynchronous records. -/
theorem AllocResultFill.mono_trace {x : AsyncCopy.Ref} (h : AllocResultFill L X i x)
    (htr : ∀ g, X.tr g <+: Y.tr g) : AllocResultFill L Y i x := by
  cases x with
  | thread store =>
    obtain ⟨dst, hr⟩ := h
    exact ⟨dst, hr.mono_trace htr⟩
  | async => exact h.elim

/-- A result fill between old nodes is already witnessed by the old trace. -/
theorem AllocResultFill.of_tracePrefix {x : AsyncCopy.Ref} (h : AllocResultFill L Y i x)
    (htr : ∀ g, X.tr g <+: Y.tr g) (hx : X.RefPresent x)
    (hi : i.2 < (X.tr i.1).length) : AllocResultFill L X i x := by
  cases x with
  | thread store =>
    obtain ⟨dst, hr⟩ := h
    obtain ⟨_, he⟩ := hx
    exact ⟨dst, hr.of_tracePrefix htr (PTX.len_of_get he) hi⟩
  | async => exact h.elim

/-- Once the return need is included, an old load cannot gain a handoff from
a newly appended result store. For the leader's own load, the store is already
earlier in the leader's trace. -/
theorem AllocResultBefore.store_present_of_load_prefix {l : Loc} {store load : EvId}
    (h : AllocResultBefore L Y l store load) (hle : X.le Y)
    (hload : load.2 < (X.tr load.1).length)
    (hready : ∀ i, Returned X i → Ready L X i)
    (hneed : ∀ i site group dst count,
      X.get i = some ⟨site, .tc (.resource group (some dst) (.alloc count))⟩ →
      laneOf L i.1 ≠ 0 → Need.node (AllocResultFill L X i) ∈ Needs L X i) :
    store.2 < (X.tr store.1).length := by
  obtain ⟨j, dst, a, bytes, hr, hj, _, ⟨site, hread⟩, _⟩ := h
  have hresultY := hr
  obtain ⟨hwarp, hleader, _, _, k, leaderSite, group, count, _, _, hk, _, hpart, hkl, hkj,
    hwrite⟩ := hr
  by_cases hlane : laneOf L load.1 = 0
  · have ht : store.1 = load.1 := sameWarp_leader_eq hwarp hleader hlane
    have hindex : store.2 ≤ load.2 := by
      have hsame : k = j := by
        rw [ht] at hkl
        exact hkl.unique hkj
      omega
    have hne : store.2 ≠ load.2 := by
      intro he
      have hs : store = load := Prod.ext ht he
      rw [hs, hread] at hwrite
      cases hwrite
    rw [ht]
    omega
  · let participant : EvId := (load.1, j)
    have hjold : j < (X.tr load.1).length := hj.trans hload
    have hget : X.get participant = some (X.tr load.1)[j] := List.getElem?_eq_getElem hjold
    have hget' := Execution.le_get hle hget
    rw [hpart] at hget'
    have hp : X.get participant =
        some ⟨leaderSite, .tc (.resource group (some dst) (.alloc count))⟩ := by
      rw [hget, Option.some.inj hget'.symm]
    have hreturned : Returned X participant := by
      simp only [Returned, hp, Kind.resume, TcKind.resume, participant]
      omega
    obtain ⟨source, hsource, hfill⟩ := hready participant hreturned _
      (hneed participant leaderSite group dst count hp hlane)
    cases source with
    | async => exact hfill.elim
    | thread source =>
      obtain ⟨dst', hresult⟩ := hfill
      have he : source = store := (hresult.mono hle).unique hresultY
      subst source
      obtain ⟨_, he⟩ := hsource
      exact PTX.len_of_get he

/-- With the result return need registered, a nonleader readback depends on the
actual result store through the return of its own allocation event. -/
theorem AllocResultBefore.dep_path {K : Kernel} {l : Loc} {store load : EvId}
    (h : AllocResultBefore L X l store load) (hlane : laneOf L load.1 ≠ 0)
    (hneed : ∀ i site group dst count,
      X.get i = some ⟨site, .tc (.resource group (some dst) (.alloc count))⟩ →
      laneOf L i.1 ≠ 0 → Need.node (AllocResultFill L X i) ∈ Needs L X i) :
    Relation.TransGen (DepStep L K X) (.thread store, false) (.thread load, false) := by
  obtain ⟨j, dst, _, _, ha, hj, _, ⟨_, hget⟩, _⟩ := h
  have hfill : AllocResultFill L X (load.1, j) (.thread store) := ⟨dst, ha⟩
  obtain ⟨_, _, _, _, _, site, group, count, _, _, _, _, hpart, _, _, _⟩ := ha
  have hnode := hneed (load.1, j) site group dst count hpart hlane
  have hbefore : TraceBefore X (load.1, j) load := ⟨rfl, hj, PTX.len_of_get hget⟩
  exact .tail (.single (DepStep.of_witness L (Witness.of_need L hnode hfill.present hfill)))
    (DepStep.of_resumes L (Resumes.of_blocking hpart rfl hbefore))

end PTX.Tmem.Pair
