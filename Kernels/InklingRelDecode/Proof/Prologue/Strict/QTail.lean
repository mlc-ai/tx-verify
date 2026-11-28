-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.QStqStep
public import Lemmas.Flow.IssueNextBar

@[expose] public section

/-! # The strict steps of the end of the prologue: the fence, the two stores, the barrier -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

theorem tail_check : (∀ τ ∈ Data.tags .st8, τ ∈ Data.tags .fnc1) ∧
    (ctlLive 570).isSublist (ctlLive 569) = true ∧
    (∀ τ ∈ Data.tags (.st9 0), τ ∈ Data.tags .st8) ∧ (ctlLive 571).isSublist (ctlLive 570) = true ∧
    (∀ τ ∈ Data.tags .exit, τ ∈ Data.tags .bar18) ∧ (ctlLive 574).isSublist (ctlLive 573) = true ∧
    (∀ τ ∈ Data.tags (.st9 1), τ ∈ Data.tags (.st9 0)) ∧ (∀ τ ∈ Data.tags .bar18, τ ∈ Data.tags
        (.st9 1)) := by
  decide +kernel

/-- No step: a site whose facts are among those of the site before. -/
theorem site_sub (c : Control.D) (v : Data.Vals) (s s' : Site) (a : Nat)
    (ht : ∀ τ ∈ Data.tags s', τ ∈ Data.tags s)
    (hl : (ctlLive s'.pc).isSublist (ctlLive s.pc) = true) :
    SegQ kernel Assumptions.all L g (QT proQt) a (dFacts Q L g w (dq c v s)) a
      (dFacts Q L g w (dq c v s')) := by
  refine SegQ.sub fun q hq' => ?_
  rcases List.mem_append.mp hq' with h | h
  · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp h
    rw [tag_val_site (Q := Q) (L := L) (g := g) c v s' s τ]
    exact List.mem_append_left _ (List.mem_map_of_mem
      (f := fun τ => (τ.reg, τ.val Q L g (dq c v s))) (ht τ hτ))
  · exact List.mem_append_right _ (mem_facts_sub hl h)


/-- **The proxy fence of the stores** strictly steps to the scalar store. -/
theorem step_fnc1 (d : Data.D) (hs : d.c.site = .fnc1) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a, b, c, won, bcast⟩, vs⟩ := d
  cases hs
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨hI, hpay⟩ := hinv
  obtain ⟨ht, hl, -⟩ := tail_check
  let c0 : Control.D := ⟨.fnc1, a, b, c, won, bcast⟩
  have hi : (Data.code Q L g w).inv ⟨⟨.st8, a, b, c, won, bcast⟩, vs⟩ :=
    ⟨trivial, payload_next (Q := Q) (L := L) (g := g) (d := c0) (e := ⟨0, .exit⟩)
      (t := ⟨.st8, a, b, c, won, bcast⟩) rfl hpay (fun j h => by cases h)⟩
  refine Code.advanceQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
    (d := ⟨c0, vs⟩) (dn := ⟨⟨.st8, a, b, c, won, bcast⟩, vs⟩) Flow.code_569
    (fun h => fires_next (by trivial) h) (fun e => rfl) rfl rfl rfl rfl hi (fun _ _ => typed_nil')
    (by decide +kernel : Code.afterWrites proQt 569 [] [] = true) (dFacts_seg (pre := [])
        (site_sub c0 vs .fnc1 .st8 570 ht hl)) e ins hat
    ⟨hI, hpay⟩ hc hq hw hf


/-- **The scalar store** strictly steps to the first element of the last store. -/
theorem step_st8 (d : Data.D) (hs : d.c.site = .st8) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a, b, c, won, bcast⟩, vs⟩ := d
  cases hs
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨hI, hpay⟩ := hinv
  obtain ⟨-, -, ht, hl, -⟩ := tail_check
  let c0 : Control.D := ⟨.st8, a, b, c, won, bcast⟩
  have hi : (Data.code Q L g w).inv ⟨⟨.st9 0, a, b, c, won, bcast⟩, vs⟩ :=
    ⟨trivial, payload_next (Q := Q) (L := L) (g := g) (d := c0) (e := ⟨0, .exit⟩)
      (t := ⟨.st9 0, a, b, c, won, bcast⟩) rfl hpay (fun j h => by cases h)⟩
  refine Code.scalarStoreQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
    (d := ⟨c0, vs⟩) (dn := ⟨⟨.st9 0, a, b, c, won, bcast⟩, vs⟩) Flow.code_570 rfl rfl
    (fun e => rfl) rfl rfl rfl rfl hi (fun _ _ => typed_nil')
    (by decide +kernel : Code.afterWrites proQt 570 [] [] = true)
    (dFacts_seg (pre := []) (site_sub c0 vs .st8 (.st9 0) 571 ht hl)) e ins hat ⟨hI, hpay⟩ hc hq
    hw hf

theorem st9_end (c : Control.D) (v : Data.Vals) :
    SegQ kernel Assumptions.all L g (QT proQt) 572 (dFacts Q L g w (dq c v (.st9 1))) 573
      (dFacts Q L g w (dq c v .bar18)) := by
  simp only [dq]
  pro_seg


/-- **An element of the last store** strictly steps to the next element or the barrier. -/
theorem step_st9 (d : Data.D) (j : Fin 2) (hs : d.c.site = .st9 j) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a, b, c, won, bcast⟩, vs⟩ := d
  cases hs
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨hI, hpay⟩ := hinv
  obtain ⟨-, -, -, -, -, -, ht1, ht2⟩ := tail_check
  have hl1 : (ctlLive 571).isSublist (ctlLive 571) = true := by decide +kernel
  fin_cases j
  · let c0 : Control.D := ⟨.st9 0, a, b, c, won, bcast⟩
    have hi : (Data.code Q L g w).inv ⟨⟨.st9 1, a, b, c, won, bcast⟩, vs⟩ :=
      ⟨trivial, payload_next (Q := Q) (L := L) (g := g) (d := c0) (e := ⟨0, .exit⟩)
        (t := ⟨.st9 1, a, b, c, won, bcast⟩) rfl hpay (fun j h => by cases h)⟩
    refine Code.vstQW (C := Data.code Q L g w) (qt := proQt) (ex := [])
      (d := ⟨c0, vs⟩) (dn := ⟨⟨.st9 1, a, b, c, won, bcast⟩, vs⟩) Flow.code_571 rfl
      (fun e => rfl) rfl (fun _ => ⟨rfl, rfl, rfl, fun R h => holds_of_forall fun p hp =>
        holds_mem h ?hp, hi⟩) (fun _ _ => typed_nil')
      (by decide +kernel : Code.afterWrites proQt 571 [] [] = true) (fun h => by simp [Data.code,
          c0, Site.sub] at h)
      e ins hat ⟨hI, hpay⟩ hc hq hw hf
    exact hp
  · let c0 : Control.D := ⟨.st9 1, a, b, c, won, bcast⟩
    have hi : (Data.code Q L g w).inv ⟨⟨.bar18, a, b, c, won, bcast⟩, vs⟩ :=
      ⟨trivial, payload_next (Q := Q) (L := L) (g := g) (d := c0) (e := ⟨0, .exit⟩)
        (t := ⟨.bar18, a, b, c, won, bcast⟩) rfl hpay (fun j h => by cases h)⟩
    refine Code.vstQW (C := Data.code Q L g w) (qt := proQt) (ex := [])
      (d := ⟨c0, vs⟩) (dn := ⟨⟨.bar18, a, b, c, won, bcast⟩, vs⟩) Flow.code_571 rfl
      (fun e => rfl) rfl (fun h => by simp [Data.code, c0, Site.sub] at h) (fun _ _ => typed_nil')
      (by decide +kernel : Code.afterWrites proQt 571 [] [] = true)
      (fun _ => ⟨rfl, rfl, hi, dFacts_seg (pre := []) (st9_end c0 vs)⟩) e ins hat
      ⟨hI, hpay⟩ hc hq hw hf


/-- **The last barrier** strictly steps to the exit. -/
theorem step_bar18 (d : Data.D) (hs : d.c.site = .bar18) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a, b, c, won, bcast⟩, vs⟩ := d
  cases hs
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨hI, hpay⟩ := hinv
  obtain ⟨-, -, -, -, ht, hl, -⟩ := tail_check
  let c0 : Control.D := ⟨.bar18, a, b, c, won, bcast⟩
  have hi : (Data.code Q L g w).inv ⟨⟨.exit, a, b, c, won, bcast⟩, vs⟩ :=
    ⟨trivial, payload_next (Q := Q) (L := L) (g := g) (d := c0) (e := ⟨0, .exit⟩)
      (t := ⟨.exit, a, b, c, won, bcast⟩) rfl hpay (fun j h => by cases h)⟩
  refine Code.advanceQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
    (d := ⟨c0, vs⟩) (dn := ⟨⟨.exit, a, b, c, won, bcast⟩, vs⟩) Flow.code_573
    (fun h => fires_barSync_next h) (fun e => rfl) rfl rfl rfl rfl hi (fun _ _ => typed_nil')
    (by decide +kernel : Code.afterWrites proQt 573 [] [] = true)
    (dFacts_seg (pre := []) (site_sub c0 vs .bar18 .exit 574 ht hl)) e ins hat ⟨hI, hpay⟩ hc hq hw
        hf

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
