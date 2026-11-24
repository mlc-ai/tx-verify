-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.AllocResultDependency

@[expose] public section

/-! # A performed allocation-management event is ready when its operation is

A proof tool for the progress step at a Tensor Memory allocation-management event. The record that
performed the event's warp request holds the 32 lane events of one warp-collective instance
(`WarpRequest.Valid`), so the warp needs of the event (`tcNeeds`) are filled; the peer lanes of a
complete `cta_group::2` operation are the lane events of the other request of its pairing, and the
lanes of an earlier release are the lane events of its record. A nonleader allocation also needs
the local result store. These witnesses give `ReturnReady.ready` (DEP-ORDER). -/

namespace PTX.Tmem.Pair

open PTX

noncomputable section

variable {L : Launch} {X : Execution}

/-- The lane events of a valid warp request are present. -/
theorem WarpRequest.Valid.present {group : CtaGroup} {w : WarpRequest}
    (hv : w.Valid L X group) (lane : Fin 32) : X.RefPresent (.thread (w.event L lane)) :=
  ⟨_, hv.2.2.1 lane⟩

/-- A performed and covered resource event is ready when its allocation result has been published
for any participating nonleader. -/
theorem ReturnReady.ready (hX : HistoriesOk L X) {i : EvId} {pc : Nat} {group : CtaGroup}
    {dst : Option Loc} {request : Request}
    (he : X.get i = some ⟨pc, .tc (.resource group dst request)⟩) (hr : ReturnReady L X i)
    (publish : ∀ count, request = .alloc count → laneOf L i.1 ≠ 0 →
      ∃ store dst, AllocResult L X store i dst) :
    Ready L X i := by
  obtain ⟨⟨cta, r, hr0, lane0, hlane0⟩, hcov⟩ := hr
  have hv : r.Valid L X := (hX.1 cta).1 r hr0
  obtain ⟨-, -, hw⟩ := hv
  obtain ⟨hcta, hwarp, hget, k, hk⟩ := hw
  have hgroup : r.group = group := by
    have := hget lane0
    rw [hlane0, he] at this
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at this
    exact this.2.1.symm
  intro n hn
  simp only [Needs, he, KindNeeds, resourceNeeds, List.mem_append, List.mem_cons] at hn
  rcases hn with (htc | rfl | hrest) | hresult
  · -- a lane of the warp: the record's event of that lane
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp htc
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hh
    rw [List.mem_range] at hl
    have hl32 : l < 32 := by unfold warpSize at hl; omega
    have hi : i = r.own.event L lane0 := hlane0.symm
    have hlane : warpLane L i.1 l = (r.own.event L ⟨l, hl32⟩).1 := by
      rw [hi]
      unfold warpLane laneOf WarpRequest.event
      have h0 := lane0.isLt
      have hb : (r.own.warp + 1) * 32 ≤ L.block := hwarp
      simp only
      have hmod : (r.own.cta * L.block + r.own.warp * 32 + lane0.val) % L.block =
          r.own.warp * 32 + lane0.val := by
        rw [Nat.add_assoc, Nat.mul_comm, Nat.mul_add_mod]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      omega
    refine ⟨.thread (r.own.event L ⟨l, hl32⟩), WarpRequest.Valid.present
      ⟨hcta, hwarp, hget, k, hk⟩ _, (r.own.event L ⟨l, hl32⟩).2, ?_, ?_⟩
    · rw [hlane]
    · rw [hlane]
      have h1 := hk ⟨l, hl32⟩
      have h0 := hk lane0
      rw [hlane0] at h0
      exact ⟨h1.1, h1.2.trans h0.2.symm⟩
  · exact ⟨cta, r, hr0, lane0, hlane0⟩
  · unfold needsIf at hrest
    split at hrest
    · rename_i hm
      have hc := hcov hm
      simp only [List.mem_cons, List.mem_append] at hrest
      rcases hrest with (rfl | hpeer) | hreuse
      · exact hc
      · cases group with
        | one => simp at hpeer
        | two =>
          obtain ⟨l, -, rfl⟩ := List.mem_map.mp hpeer
          obtain ⟨ws, hws, w, hw, hpw⟩ := hc
          rcases hws with ⟨cta', r', hr', hg', rfl⟩ | ⟨q, hq, rfl⟩
          · exfalso
            obtain ⟨-, -, hw'⟩ := (hX.1 cta').1 r' hr'
            obtain ⟨lane', hl'⟩ := hpw
            rw [List.mem_singleton] at hw
            subst hw
            have := hw'.2.2.1 lane'
            rw [hl', he, hg'] at this
            simp at this
          · obtain ⟨hpv, -, -⟩ := hX.2.1 q hq
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
            rcases hw with rfl | rfl
            · exact ⟨_, hpv.2.2.1.present l, q, hq, .inl ⟨hpw, rfl⟩⟩
            · exact ⟨_, hpv.2.1.present l, q, hq, .inr ⟨hpw, rfl⟩⟩
      · cases request with
        | alloc n =>
          obtain ⟨j, hjr, hj⟩ := List.mem_flatMap.mp hreuse
          split at hj
          · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hj
            obtain ⟨d, hd⟩ : ∃ d, (X.tmemHistory (i.1 / L.block))[j]? = some d :=
              ⟨_, List.getElem?_eq_getElem (List.mem_range.mp hjr)⟩
            have hdv : d.Valid L X := (hX.1 _).1 d (List.mem_of_getElem? hd)
            exact ⟨_, hdv.2.2.present l, d, hd, rfl⟩
          · simp at hj
        | dealloc b m => simp at hreuse
        | relinquish => simp at hreuse
    · simp at hrest
  · cases request <;> simp only [allocResultNeeds] at hresult
    case alloc count =>
      split at hresult
      · cases hresult
      · rename_i hn
        obtain rfl := List.mem_singleton.mp hresult
        obtain ⟨store, dst, hstore⟩ := publish count rfl hn
        have hf : AllocResultFill L X i (.thread store) := ⟨dst, hstore⟩
        exact ⟨_, hf.present, hf⟩
    all_goals cases hresult

end

end PTX.Tmem.Pair
