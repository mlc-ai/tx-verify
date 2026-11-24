-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmaTracking
public import Lemmas.Flow.Final

@[expose] public section

/-! # Event footprints of the index coordinate handoff -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.IndexCoordinateTrace

open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

section
variable {g : Nat}

private theorem fired_site {d : Machine.ThreadD} {e : Event} {o : Option TState} {ins : Instr}
    (hFired : (Machine.machine P L g).Fired (some d) e o)
    (hCode : kernel.code[(Machine.code P L g).pc d]? = some ins) :
    ∃ t, (Machine.code P L g).AtD d t ∧ (Machine.code P L g).inv d ∧
      Fires ((Machine.code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o := by
  obtain ⟨t, ht, hf⟩ := hFired
  change (Machine.code P L g).AtD d t ∧ (Machine.code P L g).inv d at ht
  change Fires t.pc (match kernel.code[(Machine.code P L g).pc d]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  rw [hCode, ht.1.1] at hf
  exact ⟨t, ht.1, ht.2, hf⟩

/-- The read's scalar footprint selects one coordinate word in the current slot. -/
theorem read_word {d : Wg1Tma.D} {e : Event} {o : Option TState} {k : Fin 16} {j : Fin 4}
    (hpre : Pre P L mem0) (hsite : d.site = .coord k j)
    (hFired : (Machine.machine P L g).Fired (some (.tma d)) e o) :
    ∃ a bs, e.kind = .rd a bs ∧ a.size = 4 ∧
      a.loc = ⟨.shared, ctaOf L g,
        L.sharedBase + Wg1Tma.coordBase (d.block % 4) + 4 * Wg1Tma.coordPos k.val j.val⟩ := by
  have hCode : kernel.code[(Machine.code P L g).pc (.tma d)]? =
      some ⟨none, .mem (Wg1Tma.coordLoad k)⟩ := by
    change kernel.code[d.site.pc]? = _
    rw [hsite]
    exact Wg1Tma.coordLoad_code k j
  obtain ⟨t, ht, hInv, h⟩ := fired_site hFired hCode
  change (Wg1Tma.code P L g).AtD d t at ht
  change Wg1Tma.Inv P L g d at hInv
  obtain ⟨bs, he, _⟩ := Wg1Tma.fires_coord hpre hsite ht hInv h
  have hPhase := hInv.phase_eq (by simp [hsite]) (by simp [hsite])
  rw [hPhase] at he
  refine ⟨_, bs, congrArg Event.kind he, rfl, ?_⟩
  simp only [Wg1Tma.coordPos]
  congr 1
  omega

/-- Each coordinate store produces exactly the four bytes of its lane's coordinate word. -/
theorem written_word {d : Wg1Index.D} {e : Event} {o : Option TState} {extra high : Bool} {a : Acc}
    {bs : List Byte} (hpre : Pre P L mem0) (hsite : d.site = .coord extra high)
    (hFired : (Machine.machine P L g).Fired (some (.index d)) e o) (he : e.kind = .wr a bs) :
    bs = (b32 (Wg1Index.coordValue P L g d.block (laneOf L g)
        (if high then 1 else 0))).toBytes ∧
      a.size = 4 ∧ a.loc = ⟨.shared, ctaOf L g,
        L.sharedBase + Wg1Tma.coordBase (d.block % 4) + 8 * laneOf L g +
          4 * (if high then 1 else 0)⟩ := by
  have prove {a' : Acc}
      (hk : e.kind = .wr a' (b32 (Wg1Index.coordValue P L g d.block
        (laneOf L g) d.site.sub)).toBytes)
      (hl : a'.loc = ⟨.shared, ctaOf L g, L.sharedBase +
        Wg1Index.coordOff L g d.phase + 4 * d.site.sub⟩)
      (hz : a'.size = 4) (hi : Wg1Index.Inv P L g d) :
      bs = (b32 (Wg1Index.coordValue P L g d.block (laneOf L g)
          (if high then 1 else 0))).toBytes ∧
        a.size = 4 ∧ a.loc = ⟨.shared, ctaOf L g,
          L.sharedBase + Wg1Tma.coordBase (d.block % 4) + 8 * laneOf L g +
            4 * (if high then 1 else 0)⟩ := by
    have ha := Kind.wr.inj (he.symm.trans hk)
    obtain ⟨rfl, hbs⟩ := ha
    have hPhase := hi.phase_block (by simp [hsite])
    have hSub : d.site.sub = (if high then 1 else 0) := by rw [hsite]; cases high <;> rfl
    rw [hSub] at hbs hl
    refine ⟨hbs, hz, ?_⟩
    rw [hl, hPhase]
    unfold Wg1Index.coordOff Wg1Tma.coordBase
    congr 1
    omega
  cases extra
  · have hpc : d.site.pc = 2471 := by rw [hsite]; rfl
    have hCode := (congrArg (fun pc => kernel.code[pc]?) hpc).trans Flow.code_2471
    obtain ⟨t, ht, hInv, hf⟩ := fired_site hFired hCode
    cases o with
    | none =>
      rcases fires_none_ends hf with ⟨f, h⟩ | h <;> rw [he] at h <;> cases h
    | some u =>
      obtain ⟨_, h, hl, hz, _⟩ := Wg1Index.fires_coord_main hpre hsite hInv ht (by
        rw [hsite]
        exact Flow.code_2471) hf
      exact prove h hl hz hInv
  · have hpc : d.site.pc = 2560 := by rw [hsite]; rfl
    have hCode := (congrArg (fun pc => kernel.code[pc]?) hpc).trans Flow.code_2560
    obtain ⟨t, ht, hInv, hf⟩ := fired_site hFired hCode
    cases o with
    | none =>
      rcases fires_none_ends hf with ⟨f, h⟩ | h <;> rw [he] at h <;> cases h
    | some u =>
      obtain ⟨_, h, hl, hz, _⟩ := Wg1Index.fires_coord_extra hpre hsite hInv ht (by
        rw [hsite]
        exact Flow.code_2560) hf
      exact prove h hl hz hInv

/-- The scalar validity write occupies its lane's byte of the current slot. -/
theorem written_validity {d : Wg1Index.D} {e : Event} {o : Option TState} {extra : Bool} {a : Acc}
    {bs : List Byte} (hpre : Pre P L mem0) (hsite : d.site = .valid extra)
    (hFired : (Machine.machine P L g).Fired (some (.index d)) e o) (he : e.kind = .wr a bs) :
    a.size = 1 ∧ a.loc = ⟨.shared, ctaOf L g,
      L.sharedBase + 221696 + 8 * (d.block % 4) + laneOf L g / 4⟩ := by
  have prove {a' : Acc} {bs' : List Byte} (hk : e.kind = .wr a' bs')
      (hl : a'.loc = ⟨.shared, ctaOf L g, L.sharedBase + Wg1Index.validOff L g d.phase⟩)
      (hz : a'.size = 1) (hi : Wg1Index.Inv P L g d) :
      a.size = 1 ∧ a.loc = ⟨.shared, ctaOf L g,
        L.sharedBase + 221696 + 8 * (d.block % 4) + laneOf L g / 4⟩ := by
    obtain ⟨rfl, -⟩ := Kind.wr.inj (he.symm.trans hk)
    refine And.intro hz ?_
    rw [hl, hi.phase_block (by simp [hsite])]
    simp [Wg1Index.validOff, Nat.add_assoc]
  cases extra
  · have hpc : d.site.pc = 2474 := by rw [hsite]; rfl
    have hc := (congrArg (fun pc => kernel.code[pc]?) hpc).trans Flow.code_2474
    obtain ⟨t, ht, hi, hf⟩ := fired_site hFired hc
    cases o with
    | none =>
      rcases fires_none_ends hf with ⟨f, h⟩ | h <;> rw [he] at h <;> cases h
    | some u =>
      obtain ⟨_, hk, hl, hz, _⟩ := Wg1Index.fires_valid_main hpre hsite hi ht
        (by rw [hpc]; exact Flow.code_2474) hf
      exact prove hk hl hz hi
  · have hpc : d.site.pc = 2563 := by rw [hsite]; rfl
    have hc := (congrArg (fun pc => kernel.code[pc]?) hpc).trans Flow.code_2563
    obtain ⟨t, ht, hi, hf⟩ := fired_site hFired hc
    cases o with
    | none =>
      rcases fires_none_ends hf with ⟨f, h⟩ | h <;> rw [he] at h <;> cases h
    | some u =>
      obtain ⟨_, hk, hl, hz, _⟩ := Wg1Index.fires_valid_extra hpre hsite hi ht
        (by rw [hpc]; exact Flow.code_2563) hf
      exact prove hk hl hz hi

private def tailSite : Wg1Index.Site → Bool
  | .coord _ true | .valid _ | .ready _ => true
  | _ => false

private def previous (L : Launch) (g : Nat) (d prev : Wg1Index.D) (e : Event) : Prop :=
  prev.block = d.block ∧ (∃ a bs, e.kind = .wr a bs) ∧
    match d.site with
    | .coord extra true => prev.site = .coord extra false
    | .valid extra => prev.site = .coord extra true
    | .ready extra => (prev.site = .coord extra true ∧ laneOf L g % 4 ≠ 0) ∨
        prev.site = .valid extra
    | _ => True

set_option maxHeartbeats 2200000 in
private theorem role_previous {d prev : Wg1Index.D} {e : Event}
    (hn : Wg1Index.next P L g prev e = some (some d)) (hd : tailSite d.site = true) :
    previous L g d prev e := by
  cases hp : prev.site <;> cases he : e.kind <;>
    simp only [Wg1Index.next, Wg1Index.nextSite, hp, he, Option.some.injEq,
      reduceCtorEq] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    simp only [previous, Wg1Index.afterPairFirst, Wg1Index.afterReady] at *
    try split_ifs at hd
    all_goals simp_all [tailSite]

set_option maxHeartbeats 1000000 in
private theorem machine_previous {p : Machine.ThreadD} {d : Wg1Index.D} {e : Event}
    (hn : Machine.next P L g p e = some (some (.index d))) (hd : tailSite d.site = true) :
    ∃ prev : Wg1Index.D, p = .index prev ∧ previous L g d prev e := by
  cases p
  case prologue p =>
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals try cases hn
    all_goals rename_i w _ _
    all_goals fin_cases w <;> cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
    unfold Wg1Index.init Wg1Index.firstSite at hd
    split_ifs at hd <;> cases hd
  case index p =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i q hq
      cases hn
      exact ⟨p, rfl, role_previous hq hd⟩
    · split at hn <;> cases hn
    · cases hn
  all_goals
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn
end

private theorem trace_previous {g i : Nat} {d : Wg1Index.D}
    (hlen : i ≤ (X.tr g).length)
    (hs : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (hd : tailSite d.site = true) :
    ∃ j e prev, i = j + 1 ∧ X.get (g, j) = some e ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.index prev)) ∧
      previous L g d prev e := by
  cases i with
  | zero =>
    rw [Frame.stateAt_zero] at hs
    cases hs
  | succ j =>
    have hj : j < (X.tr g).length := by omega
    have he : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hj
    have hz := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hs] at hz
    cases hp : Frame.stateAt (Machine.code P L) X g j with
    | none => rw [hp] at hz; cases hz
    | some p =>
      cases p with
      | none => rw [hp] at hz; cases hz
      | some p =>
        rw [hp] at hz
        change some (some (.index d)) = Machine.next P L g p (X.tr g)[j] at hz
        obtain ⟨p, rfl, h⟩ := machine_previous hz.symm hd
        exact ⟨j, _, p, rfl, he, hp, h⟩

/-- A publishing lane has already written both coordinate words of that block.
The optional validity store can occur between the words and their publication. -/
theorem writes_before_publish {g i : Nat} {d : Wg1Index.D} {extra high : Bool}
    (hlen : i ≤ (X.tr g).length)
    (hs : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (hd : d.site = .ready extra) :
    ∃ j e w a bs, j < i ∧ X.get (g, j) = some e ∧ e.kind = .wr a bs ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.index w)) ∧
      w.block = d.block ∧ w.site = .coord extra high := by
  obtain ⟨p, e, prev, hp, he, hs', h⟩ := trace_previous hlen hs (by simp [hd, tailSite])
  simp only [previous, hd] at h
  obtain ⟨hb, hwrite, hsite⟩ := h
  have before {q : Nat} {hi : Wg1Index.D} {f : Event} (hlt : q < i)
      (hf : X.get (g, q) = some f) (hs : Frame.stateAt (Machine.code P L) X g q =
        some (some (.index hi))) (hBlock : hi.block = d.block) (hHigh : hi.site = .coord extra true)
      (hwr : ∃ a bs, f.kind = .wr a bs) :
      ∃ j e w a bs, j < i ∧ X.get (g, j) = some e ∧ e.kind = .wr a bs ∧
        Frame.stateAt (Machine.code P L) X g j = some (some (.index w)) ∧
        w.block = d.block ∧ w.site = .coord extra high := by
    cases high
    · obtain ⟨j, e, w, hj, he, hw, hz⟩ :=
        trace_previous (PTX.len_of_get hf).le hs (by simp [hHigh, tailSite])
      change w.block = hi.block ∧ (∃ a bs, e.kind = .wr a bs) ∧ _ at hz
      obtain ⟨hb, ⟨a, bs, hwr⟩, hd⟩ := hz
      rw [hHigh] at hd
      exact ⟨j, e, w, a, bs, by omega, he, hwr, hw, hb.trans hBlock, hd⟩
    · obtain ⟨a, bs, hwr⟩ := hwr
      exact ⟨q, f, hi, a, bs, hlt, hf, hwr, hs, hBlock, hHigh⟩
  rcases hsite with hcoord | hvalid
  · exact before (by omega) he hs' hb hcoord.1 hwrite
  · obtain ⟨q, f, hi, hq, hf, hh, h⟩ :=
      trace_previous (PTX.len_of_get he).le hs' (by simp [hvalid, tailSite])
    simp only [previous, hvalid] at h
    exact before (by omega) hf hh (h.1.trans hb) h.2.2 h.2.1

/-- Each quad's leader wrote the validity byte immediately before publishing that block. -/
theorem valid_before_publish {g i : Nat} {d : Wg1Index.D} {extra : Bool}
    (hlen : i ≤ (X.tr g).length)
    (hs : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (hd : d.site = .ready extra) (hLane : laneOf L g % 4 = 0) :
    ∃ j e w a bs, j < i ∧ X.get (g, j) = some e ∧ e.kind = .wr a bs ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.index w)) ∧
      w.block = d.block ∧ w.site = .valid extra := by
  obtain ⟨p, e, prev, hp, he, hs', h⟩ := trace_previous hlen hs (by simp [hd, tailSite])
  simp only [previous, hd] at h
  obtain ⟨hb, ⟨a, bs, hwrite⟩, hsite | hsite⟩ := h
  · exact (hsite.2 hLane).elim
  · exact ⟨p, e, prev, a, bs, by omega, he, hwrite, hs', hb, hsite⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.IndexCoordinateTrace
