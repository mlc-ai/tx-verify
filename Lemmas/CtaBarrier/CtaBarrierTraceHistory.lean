-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.CtaBarrier.CtaBarrierHistory
public import Mathlib.Data.List.Basic

@[expose] public section

namespace PTX.CtaBarrier
variable {α : Type}

/-- Successful arrivals leave the bank's exited-thread set unchanged. -/
theorem arrive_exited {block id warp : Nat} {count : Option Nat} {s t : State}
    (h : arrive block s id warp count = .ok t) : t.exited = s.exited := by
  by_cases hid : id < 16
  · by_cases hw : warp < warps block ∧ warpLive block s.exited warp
    · cases hn : target block count with
      | error err => simp [arrive,hid,hw,hn,bind,Except.bind] at h
      | ok n =>
        by_cases ha : warp ∈ (s.slots id).arrived
        · simp [arrive,hid,hw,hn,ha,bind,Except.bind,pure,Except.pure,throw] at h
        · cases he : (s.slots id).expected with
          | none =>
            simp [arrive,hid,hw,hn,ha,he,bind,Except.bind,pure,Except.pure] at h
            cases h; rfl
          | some k =>
            by_cases hk : k = n
            · simp [arrive,hid,hw,hn,ha,he,hk,bind,Except.bind,pure,Except.pure] at h
              cases h; rfl
            · simp [arrive,hid,hw,hn,ha,he,hk,bind,Except.bind,pure,Except.pure,
                throw] at h
    · simp [arrive,hid,hw,bind,Except.bind,pure,Except.pure,throw] at h
  · simp [arrive,hid,bind,Except.bind,pure,Except.pure,throw] at h

theorem arrive_live {block id warp : Nat} {count : Option Nat} {s t : State}
    (h : arrive block s id warp count = .ok t) :
    warp < warps block ∧ warpLive block s.exited warp := by
  by_cases hw : warp < warps block ∧ warpLive block s.exited warp
  · exact hw
  · by_cases hid : id < 16
    · simp [arrive,hid,hw,bind,Except.bind,pure,Except.pure,throw] at h
    · simp [arrive,hid,bind,Except.bind,pure,Except.pure,throw] at h

/-- Resource histories can add exited threads but cannot revive them. -/
theorem perform_exited_mono {block : Nat} {s t : State} {r : Record α}
    (h : r.perform block s = .ok t) : s.exited ⊆ t.exited := by
  cases r with
  | exit g e =>
    by_cases hg : g < block ∧ g ∉ s.exited
    · simp [Record.perform,exitThread,hg,pure,Except.pure] at h
      cases h
      exact Finset.subset_insert _ _
    · simp [Record.perform,exitThread,hg,bind,Except.bind,pure,Except.pure,throw] at h
  | arrival id w count lanes =>
    simp only [Record.perform] at h
    split_ifs at h
    rw [arrive_exited h]

theorem run_exited_mono {block : Nat} {s t : State} {h : List (Record α)}
    (hr : run block s h = .ok t) : s.exited ⊆ t.exited := by
  induction h generalizing s with
  | nil => cases hr; exact Finset.Subset.refl _
  | cons r rs ih =>
    cases hp : r.perform block s with
    | error err => simp [run,hp,Except.bind] at hr
    | ok u =>
      have ht : run block u rs = .ok t := by simpa only [run,hp,Except.bind] using hr
      exact (perform_exited_mono hp).trans (ih ht)

/-- A successful history supplies both states around each recorded operation. -/
theorem run_at_record {block i : Nat} {h : List (Record α)} {r : Record α} {last : State}
    (hr : run block {} h = .ok last) (hi : h[i]? = some r) :
    ∃ s t, At block h i s ∧ r.perform block s = .ok t := by
  have hlt := (List.getElem?_eq_some_iff.mp hi).1
  have hd : h = h.take i ++ r :: h.drop (i+1) := by
    rw [← (List.getElem?_eq_some_iff.mp hi).2,← List.drop_eq_getElem_cons hlt]
    exact (List.take_append_drop i h).symm
  have hr' := hr
  rw [hd] at hr'
  obtain ⟨s,hs⟩ := run_prefix hr'
  rw [run_append,hs] at hr'
  cases ht : r.perform block s with
  | error err => simp [run,ht,Except.bind] at hr'
  | ok t => exact ⟨s,t,hs,ht⟩

/-- A live lane in a later prefix was live in every earlier prefix. -/
theorem exited_prefix {block i j : Nat} {h : List (Record α)} {s t : State}
    (hij : i ≤ j) (hi : At block h i s) (hj : At block h j t) :
    s.exited ⊆ t.exited := by
  have hd : h.take j = h.take i ++ (h.take j).drop i := by
    calc
      h.take j = (h.take j).take i ++ (h.take j).drop i := (List.take_append_drop i _).symm
      _ = h.take i ++ (h.take j).drop i := by rw [List.take_take,Nat.min_eq_left hij]
  unfold At at hi hj
  rw [hd,run_append,hi] at hj
  exact run_exited_mono hj

/-- Arrival records contain every lane which is still live in that warp. -/
theorem perform_arrival_lanes {block id warp : Nat} {count : Option Nat}
    {lanes : List (Nat × α)} {s t : State}
    (h : Record.perform block s (.arrival id warp count lanes) = .ok t) :
    (lanes.map Prod.fst).Nodup ∧
      (∀ p ∈ lanes, p.1 < block ∧ p.1 / 32 = warp ∧ p.1 ∉ s.exited) ∧
      (∀ g < block, g / 32 = warp → g ∉ s.exited → g ∈ lanes.map Prod.fst) := by
  simp only [Record.perform] at h
  split_ifs at h with hl
  refine ⟨hl.1,hl.2.1,?_⟩
  intro g hg hgw hn
  have hge : warp * 32 + g % 32 = g := by omega
  have hh := hl.2.2 (g % 32) (Finset.mem_range.mpr (Nat.mod_lt _ (by decide)))
    (by simpa only [hge] using hg)
    (by simpa only [hge] using hn)
  simpa only [hge] using hh

theorem perform_ref_exists {block : Nat} {r : Record α} {s t : State}
    (hp : r.perform block s = .ok t) : ∃ e, e ∈ r.refs := by
  cases r with
  | exit g e => exact ⟨e,by simp [Record.refs]⟩
  | arrival id w count lanes =>
    have hl := perform_arrival_lanes hp
    have ha : arrive block s id w count = .ok t := by
      simp only [Record.perform] at hp
      split_ifs at hp
      exact hp
    obtain ⟨_,lane,hln,hg,hn⟩ := arrive_live ha
    have hln32 := Finset.mem_range.mp hln
    have hm := hl.2.2 (w*32+lane) hg (by omega) hn
    obtain ⟨p,hpl,_⟩ := List.mem_map.mp hm
    exact ⟨p.2,List.mem_map.mpr ⟨p,hpl,rfl⟩⟩

/-- Distinct records in a checked history order their references in its flattened
list. This index is a proof rank for resource dependencies, not a global event time. -/
theorem refs_index_lt [DecidableEq α] {h : List (Record α)}
    (hnd : (h.flatMap Record.refs).Nodup) {i j : Nat} {r q : Record α} {e f : α}
    (hr : h[i]? = some r) (hq : h[j]? = some q) (hij : i < j)
    (he : e ∈ r.refs) (hf : f ∈ q.refs) :
    (h.flatMap Record.refs).idxOf e < (h.flatMap Record.refs).idxOf f := by
  have hil := (List.getElem?_eq_some_iff.mp hr).1
  have hjl := (List.getElem?_eq_some_iff.mp hq).1
  have hd : h = h.take j ++ q :: h.drop (j+1) := by
    rw [← (List.getElem?_eq_some_iff.mp hq).2,← List.drop_eq_getElem_cons hjl]
    exact (List.take_append_drop j h).symm
  have hm : r ∈ h.take j := by
    apply List.mem_iff_getElem.mpr
    refine ⟨i,?_,?_⟩
    · simp only [List.length_take]; omega
    · simpa only [List.getElem_take] using (List.getElem?_eq_some_iff.mp hr).2
  have hepre := List.mem_flatMap.mpr ⟨r,hm,he⟩
  have hn := hnd
  rw [hd,List.flatMap_append,List.flatMap_cons] at hn
  have hfpre : f ∉ (h.take j).flatMap Record.refs := by
    intro hp
    exact (List.nodup_append.mp hn).2.2 f hp f (List.mem_append.mpr (.inl hf)) rfl
  rw [hd,List.flatMap_append,List.idxOf_append_of_mem hepre,List.idxOf_append_of_notMem hfpre]
  have hl := List.idxOf_lt_length_iff.mpr hepre
  omega

end PTX.CtaBarrier
