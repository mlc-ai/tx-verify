-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.CtaBarrier.CtaBarrierIdentity
public import Lemmas.CtaBarrier.CtaBarrierHistory
public import Lemmas.Order.DependencyWitness
public import Lemmas.Order.OrderBaseCausality
public import Lemmas.Execution.NoBarArrive

@[expose] public section

/-! # When a pending CTA barrier arrival cannot fault

The members and the open count of a named resource come from recorded arrivals of its current
generation (`slotFrom_run`). In a consistent execution a warp whose lanes wait, unrecorded, at
a barrier has no recorded arrival in the open generation of that ID: each lane's earlier
arrivals were passed, so their generations were released (the release need of `KindNeeds`,
`ctaBarDone_of_returned`). Hence a pending
arrival is never a `duplicateArrival`, and it is a `countMismatch` only if two arrivals of one
CTA at one ID carry different counts (`not_ctaBarFault`). -/

namespace PTX.CtaBarrier
variable {α : Type}

/-- The slot's members and open count are witnessed by successful recorded arrivals of the
slot's current generation. -/
def SlotFrom (block : Nat) (h : List (Record α)) (s : State) : Prop :=
  ∀ id,
    (∀ w ∈ (s.slots id).arrived, ∃ i u cnt lanes t,
      h[i]? = some (.arrival id w cnt lanes) ∧ At block h i u ∧
      (u.slots id).generation = (s.slots id).generation ∧
      Record.perform block u (.arrival id w cnt lanes) = .ok t) ∧
    (∀ k, (s.slots id).expected = some k → ∃ i u w cnt lanes t,
      h[i]? = some (.arrival id w cnt lanes) ∧ At block h i u ∧
      (u.slots id).generation = (s.slots id).generation ∧ target block cnt = .ok k ∧
      Record.perform block u (.arrival id w cnt lanes) = .ok t)

theorem at_append_left {block i : Nat} {h ys : List (Record α)} {u : State}
    (hi : i ≤ h.length) (ha : At block h i u) : At block (h ++ ys) i u := by
  unfold At at ha ⊢
  rwa [List.take_append_of_le_length hi]

theorem getElem?_append_left' {h ys : List (Record α)} {i : Nat} {r : Record α}
    (hi : h[i]? = some r) : (h ++ ys)[i]? = some r := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1, hi]

/-- Old witnesses stay witnesses of an unchanged slot. -/
theorem slotFrom_keep {block : Nat} {h : List (Record α)} {s : State} {r : Record α}
    (hs : SlotFrom block h s) (id : Nat) (sl : Slot) (hsl : sl = s.slots id) :
    (∀ w ∈ sl.arrived, ∃ i u cnt lanes t,
      (h ++ [r])[i]? = some (.arrival id w cnt lanes) ∧ At block (h ++ [r]) i u ∧
      (u.slots id).generation = sl.generation ∧
      Record.perform block u (.arrival id w cnt lanes) = .ok t) ∧
    (∀ k, sl.expected = some k → ∃ i u w cnt lanes t,
      (h ++ [r])[i]? = some (.arrival id w cnt lanes) ∧ At block (h ++ [r]) i u ∧
      (u.slots id).generation = sl.generation ∧ target block cnt = .ok k ∧
      Record.perform block u (.arrival id w cnt lanes) = .ok t) := by
  subst hsl
  refine ⟨fun w hw => ?_, fun k hk => ?_⟩
  · obtain ⟨i, u, cnt, lanes, t, hi, ha, hg, hp⟩ := (hs id).1 w hw
    exact ⟨i, u, cnt, lanes, t, getElem?_append_left' hi,
      at_append_left (List.getElem?_eq_some_iff.mp hi).1.le ha, hg, hp⟩
  · obtain ⟨i, u, w, cnt, lanes, t, hi, ha, hg, hc, hp⟩ := (hs id).2 k hk
    exact ⟨i, u, w, cnt, lanes, t, getElem?_append_left' hi,
      at_append_left (List.getElem?_eq_some_iff.mp hi).1.le ha, hg, hc, hp⟩

/-- A settled slot is either unchanged or a fresh generation with no members. -/
theorem settle_cases (block : Nat) (exited : Finset Nat) (sl : Slot) :
    settle block exited sl = sl ∨
      ((settle block exited sl).arrived = ∅ ∧ (settle block exited sl).expected = none) := by
  unfold settle
  split
  · exact .inr ⟨rfl, rfl⟩
  · exact .inl rfl

theorem slotFrom_snoc {block : Nat} {h : List (Record α)} {s t : State} {r : Record α}
    (hrun : run block {} h = .ok s) (hs : SlotFrom block h s) (hr : r.perform block s = .ok t) :
    SlotFrom block (h ++ [r]) t := by
  have hlast : At block (h ++ [r]) h.length s := by
    unfold At
    rw [List.take_append_of_le_length le_rfl, List.take_length]
    exact hrun
  have hnew : (h ++ [r])[h.length]? = some r := by simp
  intro id
  cases r with
  | exit g e =>
    have hslot : t.slots id = settle block (insert g s.exited) (s.slots id) := by
      by_cases hg : g < block ∧ g ∉ s.exited
      · simp [Record.perform, exitThread, hg, pure, Except.pure] at hr
        rw [← hr]
      · simp [Record.perform, exitThread, hg, bind, Except.bind, throw, throwThe,
          MonadExceptOf.throw] at hr
    rcases settle_cases block (insert g s.exited) (s.slots id) with heq | ⟨ha, hx⟩
    · exact slotFrom_keep hs id _ (hslot.trans heq)
    · refine ⟨fun w hw => ?_, fun k hk => ?_⟩
      · rw [hslot, ha] at hw; exact absurd hw (Finset.notMem_empty w)
      · rw [hslot, hx] at hk; cases hk
  | arrival id' w' cnt lanes =>
    have hr' := hr
    simp only [Record.perform] at hr'
    split_ifs at hr' with hlanes
    obtain ⟨n, hn, hex, hslots⟩ := arrive_shape hr'
    by_cases hid : id = id'
    · subst hid
      have hsl := hslots id
      rw [ite_eq_left rfl] at hsl
      set old := s.slots id with hold
      rcases settle_cases block s.exited
          { old with expected := some n, arrived := insert w' old.arrived } with heq | ⟨ha, hx⟩
      · rw [heq] at hsl
        have hgen : (t.slots id).generation = old.generation := by rw [hsl]
        refine ⟨fun w hw => ?_, fun k hk => ?_⟩
        · rw [hsl] at hw
          simp only [Finset.mem_insert] at hw
          rcases hw with rfl | hw
          · exact ⟨h.length, s, cnt, lanes, t, hnew, hlast, by rw [hgen], hr⟩
          · obtain ⟨i, u, c', l', t', hi, ha, hg, hp⟩ := (hs id).1 w hw
            exact ⟨i, u, c', l', t', getElem?_append_left' hi,
              at_append_left (List.getElem?_eq_some_iff.mp hi).1.le ha, by rw [hgen, hg], hp⟩
        · rw [hsl] at hk
          simp only [Option.some.injEq] at hk
          subst hk
          exact ⟨h.length, s, w', cnt, lanes, t, hnew, hlast, by rw [hgen], hn, hr⟩
      · refine ⟨fun w hw => ?_, fun k hk => ?_⟩
        · rw [hsl, ha] at hw; exact absurd hw (Finset.notMem_empty w)
        · rw [hsl, hx] at hk; cases hk
    · have hsl := hslots id
      rw [ite_eq_right hid] at hsl
      exact slotFrom_keep hs id _ hsl

theorem slotFrom_run {block : Nat} {h : List (Record α)} {s : State}
    (hrun : run block {} h = .ok s) : SlotFrom block h s := by
  induction h using List.reverseRecOn generalizing s with
  | nil =>
    simp only [run] at hrun
    cases hrun
    intro id
    exact ⟨fun w hw => absurd hw (Finset.notMem_empty w), fun k hk => by cases hk⟩
  | append_singleton h r ih =>
    rw [run_append] at hrun
    cases hh : run block {} h with
    | error e => rw [hh] at hrun; cases hrun
    | ok u =>
      rw [hh] at hrun
      simp only [Except.bind, run] at hrun
      cases hp : r.perform block u with
      | error e => rw [hp] at hrun; cases hrun
      | ok t =>
        rw [hp] at hrun
        cases hrun
        exact slotFrom_snoc hh (ih hh) hp

theorem at_exited_mono {block i : Nat} {h : List (Record α)} {u t : State}
    (ha : At block h i u) (ht : run block {} h = .ok t) : u.exited ⊆ t.exited := by
  unfold At at ha
  have hh : h = h.take i ++ h.drop i := (List.take_append_drop i h).symm
  rw [hh, run_append, ha] at ht
  exact run_exited_mono ht

/-- A successful arrival names a live warp. -/
theorem arrive_ok_live {block id w : Nat} {cnt : Option Nat} {s t : State}
    (h : arrive block s id w cnt = .ok t) : warpLive block s.exited w := by
  by_contra hn
  unfold arrive at h
  by_cases hid : id < 16
  · simp [hid, hn, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · simp [hid, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-- The error of a failing arrival at a live warp with valid operands. -/
theorem arrive_error_cases {block id w : Nat} {cnt : Option Nat} {s : State} {err : Error}
    (h : arrive block s id w cnt = .error err) (hf : err.isFault = true) :
    warpLive block s.exited w ∧ ∃ n, target block cnt = .ok n ∧
      (w ∈ (s.slots id).arrived ∨ ∃ k, (s.slots id).expected = some k ∧ k ≠ n) := by
  unfold arrive at h
  by_cases hid : id < 16
  · by_cases hw : w < warps block ∧ warpLive block s.exited w
    · cases hn : target block cnt with
      | error e =>
        simp [hid, hw, hn, bind, Except.bind] at h
        subst h
        have hbad : e = .badCount := by
          unfold target at hn
          split at hn
          · cases hn
          · cases hn
          · split_ifs at hn
            cases hn
            rfl
        subst hbad
        simp [Error.isFault] at hf
      | ok n =>
        refine ⟨hw.2, n, rfl, ?_⟩
        by_cases ha : w ∈ (s.slots id).arrived
        · exact .inl ha
        · cases he : (s.slots id).expected with
          | none =>
            simp [hid, hw, hn, ha, he, bind, Except.bind, pure, Except.pure] at h
          | some k =>
            by_cases hk : k = n
            · simp [hid, hw, hn, ha, he, hk, bind, Except.bind, pure, Except.pure] at h
            · exact .inr ⟨k, rfl, hk⟩
    · simp [hid, hw, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
      subst h; simp [Error.isFault] at hf
  · simp [hid, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    subst h; simp [Error.isFault] at hf

/-- A successful arrival record contains every live lane of its warp. -/
theorem perform_arrival_lane {block id w : Nat} {cnt : Option Nat} {lanes : List (Nat × α)}
    {u t : State} (hp : Record.perform block u (.arrival id w cnt lanes) = .ok t)
    {g : Nat} (hg : g < block) (hw : g / 32 = w) (hx : g ∉ u.exited) :
    g ∈ lanes.map Prod.fst := by
  simp only [Record.perform] at hp
  split_ifs at hp with hl
  have hlane : g % 32 ∈ Finset.range 32 := Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
  have := hl.2.2 (g % 32) hlane
  have hgeq : w * 32 + g % 32 = g := by rw [← hw]; omega
  rw [hgeq] at this
  exact this hg hx

end PTX.CtaBarrier

namespace PTX
noncomputable section
open CtaBarrier

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- A recorded arrival lane carries its generation. -/
theorem generationOf_of_record {h : List (CtaBarrier.Record EvId)} {i id w : Nat}
    {cnt : Option Nat} {lanes : List (Nat × EvId)} {u t : CtaBarrier.State}
    (hi : h[i]? = some (.arrival id w cnt lanes)) (ha : CtaBarrier.At L.block h i u)
    (hp : CtaBarrier.Record.perform L.block u (.arrival id w cnt lanes) = .ok t)
    {g : Nat} {e : EvId} (he : (g, e) ∈ lanes) :
    CtaBarrier.GenerationOf L.block h e id (u.slots id).generation :=
  ⟨i, u, w, cnt, lanes, g, hi, ha, he, rfl, t, hp⟩

/-- An unrecorded barrier event has no later event of its thread. -/
theorem barrier_unrecorded_last (hX : Consistent L K A mem0 X) {e : EvId} {id : Nat}
    {cnt : Option Nat} {pc : Nat} (hb : X.IsBarrier e id cnt pc)
    (hn : e ∉ (X.barriers (e.1 / L.block)).flatMap CtaBarrier.Record.refs) :
    ¬ e.2 + 1 < (X.tr e.1).length := by
  intro hlt
  obtain ⟨key, hk, -⟩ := ctaBarDone_of_returned hX hb hlt
  obtain ⟨i, s, warp, count, lanes, g, hi, -, hm, -⟩ := hk.2.2
  exact hn (List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? hi,
    List.mem_map.mpr ⟨(g, e), hm, rfl⟩⟩)

theorem lane_div {c g : Nat} (hg : g < L.block) : (c * L.block + g) / L.block = c := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hg, Nat.zero_add]

/-- A live lane of a successfully recorded arrival. -/
theorem record_live_lane {u t : CtaBarrier.State} {id w : Nat} {cnt : Option Nat}
    {lanes : List (Nat × EvId)}
    (hp : CtaBarrier.Record.perform L.block u (.arrival id w cnt lanes) = .ok t) :
    ∃ g e, (g, e) ∈ lanes := by
  have hp' := hp
  simp only [CtaBarrier.Record.perform] at hp'
  split_ifs at hp' with hl
  obtain ⟨lane, hlr, hgb, hgx⟩ := CtaBarrier.arrive_ok_live hp'
  obtain ⟨⟨g, e⟩, hm, -⟩ := List.mem_map.mp (hl.2.2 lane hlr hgb hgx)
  exact ⟨g, e, hm⟩

/-- **A pending CTA barrier arrival is not a resource fault**, when all arrivals of one CTA at
one ID carry one count. -/
theorem not_ctaBarFault [hK : Fact K.NoBarArrive] (hX : Consistent L K A mem0 X)
    (hcount : ∀ e f id cnt cnt' pc pc', e.1 / L.block = f.1 / L.block →
      X.IsBarrier e id cnt pc → X.IsBarrier f id cnt' pc' → cnt = cnt') :
    ¬ CtaBarFault L X := by
  rintro ⟨c, hc, s, hrun, id, warp, count, lanes, err, hsrc, hfree, hp, hfault⟩
  have hhist := hX.ctaBar
  obtain ⟨hnd, hsrcs, -⟩ := hhist.2 c hc
  have hslot := (CtaBarrier.slotFrom_run hrun) id
  simp only [CtaBarrier.Record.perform] at hp
  split_ifs at hp with hl
  · obtain ⟨hlive, n, hn, hcase⟩ := CtaBarrier.arrive_error_cases hp hfault
    obtain ⟨lane, hlr, hgb, hgx⟩ := hlive
    have hlt := Finset.mem_range.mp hlr
    obtain ⟨⟨g, e⟩, hm, hge⟩ := List.mem_map.mp (hl.2.2 lane hlr hgb hgx)
    simp only at hge
    subst hge
    obtain ⟨-, he1, pc, hb⟩ := hsrc _ hm
    simp only at he1 hb
    replace hb := hX.isBarrier_of_arrival hK.out hb
    have hdiv : e.1 / L.block = c := by rw [he1]; exact lane_div hgb
    rcases hcase with hdup | ⟨k, hk, hkn⟩
    · -- a recorded arrival of the warp in the open generation shares this lane
      have hlast : ¬ e.2 + 1 < (X.tr e.1).length :=
        barrier_unrecorded_last hX hb (by rw [hdiv]; exact hfree _ hm)
      obtain ⟨i, u, cnt', lanes', t, hi, ha, hgen, hp'⟩ := hslot.1 warp hdup
      have hxu : warp * 32 + lane ∉ u.exited :=
        fun hx => hgx (CtaBarrier.at_exited_mono ha hrun hx)
      obtain ⟨⟨_, e'⟩, hm', hge'⟩ := List.mem_map.mp
        (CtaBarrier.perform_arrival_lane hp' hgb (by omega) hxu)
      simp only at hge'
      subst hge'
      obtain ⟨-, he1', pc', hb'⟩ := hsrcs _ (List.mem_of_getElem? hi) (_, e') hm'
      simp only at he1' hb'
      replace hb' := hX.isBarrier_of_arrival hK.out hb'
      have hrec' : e' ∈ (X.barriers c).flatMap CtaBarrier.Record.refs :=
        List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? hi, List.mem_map.mpr ⟨(_, e'), hm', rfl⟩⟩
      have hne : e ≠ e' := fun h => hfree _ hm (h ▸ hrec')
      have hsame : e.1 = e'.1 := he1.trans he1'.symm
      have hel := len_of_get hb
      have hel' := len_of_get hb'
      have hlt' : e'.2 < e.2 := by
        by_contra hge
        have hne2 : e.2 ≠ e'.2 := fun h2 => hne (Prod.ext hsame h2)
        rw [← hsame] at hel'
        exact hlast (by omega)
      have hpass : e'.2 + 1 < (X.tr e'.1).length := by rw [← hsame]; omega
      obtain ⟨key, hk, hdone⟩ := ctaBarDone_of_returned hX hb' hpass
      have hdiv' : e'.1 / L.block = c := by rw [← hsame]; exact hdiv
      have hgo := generationOf_of_record (L := L) hi ha hp' hm'
      have hgk := hk.2.2
      rw [hdiv'] at hgk
      obtain ⟨hid, hph⟩ := CtaBarrier.GenerationOf.unique hnd hgk hgo
      unfold CtaBarDone at hdone
      rw [hdiv', hid, hph, hgen] at hdone
      have := CtaBarrier.released_generation_lt hrun hdone
      omega
    · -- the open count comes from a recorded arrival with another count
      obtain ⟨i, u, w2, cnt2, lanes2, t, hi, ha, hgen, htg, hp2⟩ := hslot.2 k hk
      obtain ⟨g2, e2, hm2⟩ := record_live_lane (L := L) hp2
      obtain ⟨hg2, he2, pc2, hb2⟩ := hsrcs _ (List.mem_of_getElem? hi) (g2, e2) hm2
      replace hb2 := hX.isBarrier_of_arrival hK.out hb2
      have hdiv2 : e2.1 / L.block = c := by rw [he2]; exact lane_div hg2
      have heq := hcount e e2 id count cnt2 pc pc2 (hdiv.trans hdiv2.symm) hb hb2
      subst heq
      rw [hn] at htg
      exact hkn (Except.ok.inj htg).symm
  · cases hp
    simp [CtaBarrier.Error.isFault] at hfault

end
end PTX
