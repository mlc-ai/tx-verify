-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Span
public import Lemmas.Flow.StepsQFPt
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Pieces
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Site
public import Lemmas.Flow.StepsQFW

@[expose] public section

/-! # A site whose event continues: the combinator of the softmax's strict steps

`adv_soft` is `Code.advanceFP` for the value machine: the span starts at the control facts of the
next pc (those of the site's own table that stay live) with the data facts of the state. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

variable {e : Control.Entry} {L : Launch} {g : Nat}

/-- The span of a site: control facts of the pc after it and the data facts, to the next site. -/
abbrev SoftSpan (e : Control.Entry) (L : Launch) (g : Nat) (d dn : Data.D) : Prop :=
  SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) (d.c.site.pc + 1)
    (Data.dF L d ++ factsFrom (Control.ctlLive (d.c.site.pc + 1)) (Control.valueOf e L g d.c))
    dn.c.site.pc (Data.dF L dn ++
      factsFrom (Control.ctlLive dn.c.site.pc) (Control.valueOf e L g dn.c))

/-- **A site whose event continues** by the span `seg`. -/
theorem adv_soft {d dn : Data.D} {p : Nat} (hp : d.c.site.pc = p) {gd : Option (Nat × Bool)}
    {op : Op} {Wf : Event → Prop}
    (hc : kernel.code[p]? = some ⟨gd, op⟩)
    (ha : ∀ {t u ev}, t.pc = p → Fires p (eventTmpl Assumptions.all L g t op) ev (some u) →
      u = PTX.next t)
    (hn : ∀ ev, Data.succ e L g d ev = some (some dn))
    (hi : Control.Inv e (g % L.block) d.c → Control.Inv e (g % L.block) dn.c)
    (hq : afterF lateQt p [] = true)
    (hin : ∀ r ∈ Control.ctlLive (p + 1), r ∈ Control.ctlLive p)
    (seg : SoftSpan e L g d dn) (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      Wf d ev := by
  subst hp
  refine Code.StepForQP.ofInv fun hinv => Code.advanceFPt (C := Data.code e L g) (d := d)
    (dn := dn) hc ha hn rfl rfl rfl rfl (hi hinv) hq ?_ ev
  refine (SegQ.fromFacts (F' := Data.dF L d ++ factsFrom (Control.ctlLive (d.c.site.pc + 1))
    (Control.valueOf e L g d.c)) ?_ seg).comp (SegQ.weaken fun _ hR =>
    holds_of_forall fun p hp => ?_)
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact List.mem_append_right _ h
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
      exact List.mem_append_left _ (mem_factsFrom (hin r hr))
  · rcases List.mem_append.mp hp with h | h
    · exact holds_mem hR (List.mem_append_right _ h)
    · exact holds_mem hR (List.mem_append_left _ h)

theorem SegQ.chain {Q : TState → Prop} {a b c : Nat} {F G : List (Nat × Value)}
    (h1 : SegQ kernel Assumptions.all L g Q a F b G)
    (h2 : SegQ kernel Assumptions.all L g Q b G c G) :
    SegQ kernel Assumptions.all L g Q a F c G := h1.comp h2

/-- **A poll** that writes the predicate `r` and goes to `dst ok`: the span after it starts at the
facts of the poll with the predicate. -/
theorem wait_soft {d : Data.D} {dst : Bool → Data.D} {p r base : Nat} {off : Int} {par : Opnd}
    {acq : Bool} {sc : MbarScope} {Wf : Event → Prop} (hp : d.c.site.pc = p)
    (hc : kernel.code[p]? = some ⟨none, .mbarWait r base off par acq sc⟩)
    (hoff : r ∉ (factsFrom (Control.ctlLive p) (Control.valueOf e L g d.c)).map Prod.fst ∧
      r ∉ (Data.dF L d).map Prod.fst)
    (hn : ∀ m q ok s, Data.succ e L g d ⟨p, .wait m q ok acq s⟩ = some (some (dst ok)))
    (hi : ∀ ok, Control.Inv e (g % L.block) d.c → Control.Inv e (g % L.block) (dst ok).c)
    (hq : afterF lateQt p [(r, .old .pred)] = true)
    (seg : ∀ ok, SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) (p + 1)
      ((r, .pred ok) :: (Data.dF L d ++ factsFrom (Control.ctlLive p) (Control.valueOf e L g d.c)))
      (dst ok).c.site.pc (Data.dF L (dst ok) ++
        factsFrom (Control.ctlLive (dst ok).c.site.pc) (Control.valueOf e L g (dst ok).c)))
    (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      Wf d ev := by
  subst hp
  refine Code.StepForQP.ofInv fun hinv => Code.waitFP (C := Data.code e L g) (d := d) (dst := dst)
    hc ?_ hn rfl rfl (fun _ => rfl) (fun _ => rfl) (fun ok => ?_) hq (fun ok => ?_) ev
  · simp only [Control.facts, List.map_append, List.mem_append, not_or]
    exact ⟨hoff.1, hoff.2⟩
  · exact hi ok hinv
  · refine (SegQ.fromFacts (F' := (r, .pred ok) :: (Data.dF L d ++ factsFrom
      (Control.ctlLive d.c.site.pc) (Control.valueOf e L g d.c))) ?_ (seg ok)).comp
      (SegQ.weaken fun _ hR => holds_of_forall fun q hq => ?_)
    · intro q hq
      simp only [Control.facts, List.mem_cons, List.mem_append] at hq ⊢
      tauto
    · simp only [Control.facts, List.mem_append] at hq
      rcases hq with h | h
      · exact holds_mem hR (List.mem_append_right _ h)
      · exact holds_mem hR (List.mem_append_left _ h)

/-- A span cut at `m`: the facts at the cut are the end's facts restricted to the registers
live at `m` (the values are those of the end state). -/
theorem SegQ.cut {Q : TState → Prop} {a m b : Nat} {F D : List (Nat × Value)} {V : Nat → Value}
    (h1 : SegQ kernel Assumptions.all L g Q a F m (D ++ factsFrom (Control.ctlLive m) V))
    (h2 : SegQ kernel Assumptions.all L g Q m (D ++ factsFrom (Control.ctlLive m) V) b
      (D ++ factsFrom (Control.ctlLive b) V)) :
    SegQ kernel Assumptions.all L g Q a F b (D ++ factsFrom (Control.ctlLive b) V) :=
  h1.comp h2

/-- The registers neither the table nor the data facts of a state name. -/
theorem facts_ne {d : Data.D} {r : Nat} (hc : r ∉ Control.ctlLive d.c.site.pc)
    (hd : r ∉ Data.dKeys d.c.site) : ∀ p ∈ (Data.code e L g).facts d, p.1 ≠ r := by
  intro p hp hr
  rcases List.mem_append.mp hp with h | h
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    exact hc (hr ▸ hq)
  · exact hd (hr ▸ (Data.dFS_keys L d.c.site d.v ▸ List.mem_map_of_mem h))

/-- The facts of a state at the next pc, when only the site changes: no span. -/
theorem seg_adj {Q : TState → Prop} {a : Nat} {d dn : Data.D}
    (hD : ∀ q ∈ Data.dF L dn, q ∈ Data.dF L d)
    (hv : Control.valueOf e L g dn.c = Control.valueOf e L g d.c)
    (hk : ∀ r ∈ Control.ctlLive dn.c.site.pc, r ∈ Control.ctlLive d.c.site.pc) :
    SegQ kernel Assumptions.all L g Q a ((Data.code e L g).facts d) a
      ((Data.code e L g).facts dn) := by
  refine SegQ.weaken fun _ hR => holds_of_forall fun q hq => holds_mem hR ?_
  rcases List.mem_append.mp hq with h | h
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    refine List.mem_append_left _ (List.mem_map.mpr ⟨r, hk r hr, ?_⟩)
    exact congrArg (Prod.mk r) (congrFun hv r).symm
  · exact List.mem_append_right _ (hD q h)

/-- The facts of a span's end are among those of its start (same values). -/
theorem sub_facts {D D' : List (Nat × Value)} {ks ks' : List Nat} {V : Nat → Value}
    (hD : ∀ p ∈ D', p ∈ D) (hk : ∀ r ∈ ks', r ∈ ks) :
    ∀ p ∈ D' ++ factsFrom ks' V, p ∈ D ++ factsFrom ks V := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact List.mem_append_left _ (hD p h)
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    exact List.mem_append_right _ (mem_factsFrom (hk r hr))

/-- The facts of a span written only outside `wr`. -/
theorem facts_nmem {wr : List Nat} {d : Data.D} {ks : List Nat} {V : Nat → Value}
    (hd : ∀ k ∈ Data.dKeys d.c.site, k ∉ wr) (hk : ∀ k ∈ ks, k ∉ wr) :
    ∀ p ∈ Data.dF L d ++ factsFrom ks V, p.1 ∉ wr := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hd _ (by rw [← Data.dFS_keys L d.c.site d.v]; exact List.mem_map_of_mem h)
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    exact hk r hr

open Lean in
set_option hygiene false in
/-- A window of the lane over the facts of its end, with its single and half pieces. -/
macro "win " n:ident : tactic => do
  let w := (n.getId.toString.drop 3).toString
  let ns := Name.mkStr `PTX.Kernels.InklingRelDecode.Gen s!"TypedLate{((w.drop 1).take 2).toString}"
  let ho := mkIdent (Name.mkStr ns (w ++ "_ho_ok"))
  `(tactic|
    (refine $n (A := Assumptions.all) (R := LateR' L g) (fp3_of (by decide +kernel))
      (facts_nmem (by (try dsimp only); decide +kernel) (by (try dsimp only); decide +kernel))
      (sub_facts (fun _ h => h) (by (try dsimp only); decide +kernel))
      (by intro pc h; exact single_late (by revert pc; decide +kernel))
      (by first
        | (intro pc h; exact nomatch h)
        | (intro pc h; exact half_late (by revert pc; decide +kernel) ($ho pc h)))))

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
