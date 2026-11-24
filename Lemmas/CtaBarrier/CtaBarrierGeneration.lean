-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.CtaBarrier.CtaBarrierRoundCompletion
public import Lemmas.CtaBarrier.CtaBarrierTraceHistory
public import Lemmas.CtaBarrier.CtaBarrierRounds

@[expose] public section

section
namespace PTX.CtaBarrier
variable {α : Type} {block warp : Nat} {event : Nat → α}

theorem mem_fullLanes {p : Nat × α} :
    p ∈ fullLanes block warp event ↔
      p.1 < block ∧ p.1 / 32 = warp ∧ p.2 = event p.1 := by
  constructor
  · intro hp
    obtain ⟨lane,hlane,rfl⟩ := List.mem_map.mp hp
    obtain ⟨hr,hbound⟩ := List.mem_filter.mp hlane
    have hn := List.mem_range.mp hr
    exact ⟨of_decide_eq_true hbound,by omega,rfl⟩
  · rintro ⟨hp,hw,he⟩
    have heq : warp*32+p.1%32 = p.1 := by omega
    apply List.mem_map.mpr
    refine ⟨p.1%32,List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),?_⟩,?_⟩
    · simpa only [heq,decide_eq_true_eq] using hp
    · exact Prod.ext heq (by simpa only [heq] using he.symm)

theorem mem_fullLanes_refs {id : Nat} {e : α} :
    e ∈ (Record.arrival id warp none (fullLanes block warp event)).refs ↔
      ∃ g, g < block ∧ g/32 = warp ∧ e = event g := by
  simp only [Record.refs,List.mem_map,mem_fullLanes]
  constructor
  · rintro ⟨p,⟨hg,hw,he⟩,hpe⟩
    exact ⟨p.1,hg,hw,hpe.symm.trans he⟩
  · rintro ⟨g,hg,hw,rfl⟩
    exact ⟨(g,event g),⟨hg,hw,rfl⟩,rfl⟩

theorem fullLanes_refs_nodup {id : Nat} (hinj : Function.Injective event) :
    (Record.arrival id warp none (fullLanes block warp event)).refs.Nodup := by
  simp only [Record.refs,fullLanes,List.map_map,Function.comp_def]
  apply (List.nodup_range.filter _).map
  intro a b hab
  exact Nat.add_left_cancel (hinj hab)

theorem fullLanes_suffix_nodup {id : Nat} {ws : List Nat} (hws : ws.Nodup)
    (hinj : Function.Injective event) :
    ((ws.map (fun w => Record.arrival id w none (fullLanes block w event))).flatMap
      Record.refs).Nodup := by
  simp only [List.flatMap_map]
  apply List.nodup_flatMap.mpr
  constructor
  · intro w _; exact fullLanes_refs_nodup hinj
  · apply hws.pairwise_of_forall_ne
    intro w hw v hv hne
    apply List.disjoint_left.mpr
    intro e he hf
    obtain ⟨g,_,hg,he⟩ := mem_fullLanes_refs.mp he
    obtain ⟨g',_,hg',hf⟩ := mem_fullLanes_refs.mp hf
    have hh := hinj (he.symm.trans hf)
    subst g'
    exact hne (hg.symm.trans hg')

end PTX.CtaBarrier
end

section
namespace PTX.CtaBarrier
variable {α : Type}

/-- Expose an arbitrary counted or uncounted named arrival's resource update. -/
theorem arrive_shape {block id warp : Nat} {count : Option Nat} {s t : State}
    (h : arrive block s id warp count = .ok t) :
    ∃ n, target block count = .ok n ∧ t.exited = s.exited ∧
      ∀ j, t.slots j = if j = id then settle block s.exited
        {s.slots id with expected := some n, arrived := insert warp (s.slots id).arrived}
        else s.slots j := by
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
            cases h
            exact ⟨n,rfl,rfl,fun _ => rfl⟩
          | some k =>
            by_cases hk : k = n
            · simp [arrive,hid,hw,hn,ha,he,hk,bind,Except.bind,pure,Except.pure] at h
              cases h
              exact ⟨n,rfl,rfl,fun _ => rfl⟩
            · simp [arrive,hid,hw,hn,ha,he,hk,bind,Except.bind,pure,Except.pure,
                throw] at h
    · simp [arrive,hid,hw,bind,Except.bind,pure,Except.pure,throw] at h
  · simp [arrive,hid,bind,Except.bind,pure,Except.pure,throw] at h

/-- No actual resource update reverses any named generation counter. -/
theorem perform_generation_mono {block : Nat} {s t : State} {r : Record α}
    (h : r.perform block s = .ok t) (id : Nat) :
    (s.slots id).generation ≤ (t.slots id).generation := by
  cases r with
  | exit g e =>
    by_cases hg : g < block ∧ g ∉ s.exited
    · simp [Record.perform,exitThread,hg,pure,Except.pure] at h
      cases h
      change (s.slots id).generation ≤ (settle block (insert g s.exited) (s.slots id)).generation
      have hh := settle_generation block (insert g s.exited) (s.slots id)
      omega
    · simp [Record.perform,exitThread,hg,bind,Except.bind,pure,Except.pure,throw] at h
  | arrival slot warp count lanes =>
    simp only [Record.perform] at h
    split_ifs at h
    obtain ⟨n,_,_,hslots⟩ := arrive_shape h
    rw [hslots]
    split_ifs with heq
    · subst slot
      have hh := settle_generation block s.exited
        {s.slots id with expected := some n,arrived := insert warp (s.slots id).arrived}
      dsimp only at hh
      exact hh.elim (fun hh => by rw [hh]) (fun hh => by rw [hh]; omega)
    · exact le_refl _

theorem run_generation_mono {block : Nat} {s t : State} {h : List (Record α)}
    (hr : run block s h = .ok t) (id : Nat) :
    (s.slots id).generation ≤ (t.slots id).generation := by
  induction h generalizing s with
  | nil => cases hr; exact le_refl _
  | cons r rs ih =>
    cases hp : r.perform block s with
    | error err => simp only [run,hp,Except.bind] at hr; cases hr
    | ok u =>
      have ht : run block u rs = .ok t := by simpa only [run,hp,Except.bind] using hr
      exact (perform_generation_mono hp id).trans (ih ht)

theorem at_generation_mono {block i : Nat} {h : List (Record α)} {s t : State}
    (hs : At block h i s) (ht : run block {} h = .ok t) (id : Nat) :
    (s.slots id).generation ≤ (t.slots id).generation := by
  have hd : h = h.take i ++ h.drop i := (List.take_append_drop i h).symm
  rw [hd,run_append,hs] at ht
  exact run_generation_mono ht id

/-- A release has advanced the named generation in every checked later state. -/
theorem released_generation_lt {block id phase : Nat} {h : List (Record α)} {t : State}
    (ht : run block {} h = .ok t) (hd : Released block h id phase) :
    phase < (t.slots id).generation := by
  obtain ⟨i,r,s,u,hi,hs,hr,hgen,hgen'⟩ := hd
  have hlt := (List.getElem?_eq_some_iff.mp hi).1
  have ha : At block h (i+1) u := by
    unfold At
    rw [List.take_succ_eq_append_getElem hlt,(List.getElem?_eq_some_iff.mp hi).2,run_append,hs]
    simp only [run,hr,Except.bind]
  have hh := at_generation_mono ha ht id
  rw [hgen'] at hh
  omega

/-- Appended arrivals either retain an old recorded identity or belong to a
generation at least as late as the prefix's terminal actual resource state. -/
theorem GenerationOf.append_cases {block id phase : Nat} {xs ys : List (Record α)}
    {e : α} {last : State} (hx : run block {} xs = .ok last)
    (hg : GenerationOf block (xs++ys) e id phase) :
    GenerationOf block xs e id phase ∨ (last.slots id).generation ≤ phase := by
  obtain ⟨i,s,warp,count,lanes,g,hi,hs,he,hphase,t,ht⟩ := hg
  by_cases hidx : i < xs.length
  · left
    refine ⟨i,s,warp,count,lanes,g,?_,?_,he,hphase,t,ht⟩
    · rwa [List.getElem?_append_left hidx] at hi
    · unfold At at hs ⊢
      rwa [List.take_append_of_le_length hidx.le] at hs
  · right
    have hlen : xs.length ≤ i := by omega
    unfold At at hs
    have hieq : i = xs.length+(i-xs.length) := by omega
    rw [hieq,List.take_length_add_append,run_append,hx] at hs
    have hh := run_generation_mono hs id
    rwa [hphase] at hh

/-- Appending records cannot introduce a completion of an already past phase.
The update either belongs to the original history or its generation is at least
the resource generation at the end of that history. -/
theorem CompletesAt.append_cases {block i id phase : Nat} {xs ys : List (Record α)}
    {last : State} (hx : run block {} xs = .ok last)
    (hc : CompletesAt block (xs++ys) i id phase) :
    CompletesAt block xs i id phase ∨ (last.slots id).generation ≤ phase := by
  obtain ⟨r,s,t,hi,hs,hr,hphase,hnext⟩ := hc
  by_cases hidx : i < xs.length
  · left
    refine ⟨r,s,t,?_,?_,hr,hphase,hnext⟩
    · rwa [List.getElem?_append_left hidx] at hi
    · unfold At at hs ⊢
      rwa [List.take_append_of_le_length hidx.le] at hs
  · right
    have hieq : i = xs.length+(i-xs.length) := by omega
    unfold At at hs
    rw [hieq,List.take_length_add_append,run_append,hx] at hs
    have hh := run_generation_mono hs id
    rwa [hphase] at hh

end PTX.CtaBarrier
end
