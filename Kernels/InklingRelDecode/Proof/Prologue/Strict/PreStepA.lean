-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.PreSpan
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.QTail
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Ld
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Arrive
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Barrier
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.BlockRead
public import Lemmas.Flow.IssueNext
public import Lemmas.Flow.IssueNextBar
public import Lemmas.Flow.StepsQGuard
import Kernels.InklingRelDecode.Flow.Code.Part003
import Kernels.InklingRelDecode.Flow.Code.Part004

@[expose] public section

/-! # The strict steps of the barriers, the arrival and the block-table loads -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

/-- The value machine's successor when the control successor is `c'` and the words stay. -/
theorem data_next {d : Data.D} {c' : Control.D}
    (hc : ∀ e, Control.next Q L g d.c e = some (some c'))
    (hr : ∀ e, Data.record d e = d.v) :
    ∀ e, (Data.code Q L g w).next d e = some (some ⟨c', d.v⟩) := fun e => by
  change (Control.next Q L g d.c e).map _ = _
  rw [hc e]
  simp [hr e]

/-- A payload survives a change of site past the request loads. -/
theorem pay_site {c : Control.D} {s : Site} (h : Control.Payload c) (h1 : 130 ≤ c.site.pc) :
    Control.Payload {c with site := s} :=
  ⟨fun _ => h.1 (by omega), fun _ => h.2 h1⟩

theorem pre_tags_sub : (∀ b : Fin 3, (∀ τ ∈ Data.tags (.arr b), τ ∈ Data.tags (.pb b 0)) ∧
    (ctlLive (Site.arr b).pc).isSublist (ctlLive (Site.pb b 0).pc) = true) := by decide +kernel


theorem pre_pc : (∀ (b : Fin 3) j, 130 ≤ (Site.pb b j).pc) ∧ (∀ b : Fin 3, 130 ≤ (Site.arr b).pc) ∧
    (∀ (b : Fin 3) h, 130 ≤ (Site.lb b h).pc) := by decide +kernel

theorem arr_next (c : Control.D) (b : Fin 3) (hs : c.site = .arr b) (e : Event) :
    Control.next Q L g c e = some (some {c with site := .lb b 0}) := by
  obtain ⟨s, f, l, q, n, bc⟩ := c
  cases hs
  rfl

/-- **The arrival** strictly steps to the block-table load. -/
theorem step_arr (d : Data.D) (b : Fin 3) (hs : d.c.site = .arr b) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a, y, p, won, bcast⟩, vs⟩ := d
  cases hs
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨hI, hpay⟩ := hinv
  let c : Control.D := ⟨.arr b, a, y, p, won, bcast⟩
  refine Code.advanceGQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
    (d := ⟨c, vs⟩) (dn := dq c vs (.lb b 0)) (arr_fetch b) (fun h => fires_next (by trivial) h)
    (data_next (d := ⟨c, vs⟩) (fun e => arr_next c b rfl e) (fun _ => rfl)) rfl rfl rfl rfl
    ⟨trivial, pay_site hpay (pre_pc.2.1 b)⟩ (fun _ _ => typed_nil')
    ((by decide +kernel : ∀ b : Fin 3, Code.afterWrites proQt (Site.arr b).pc [] [] = true) b)
    ?_ e ins hat ⟨hI, hpay⟩ hc hq hw hf
  exact dFacts_seg (pre := []) (pa b c vs _ _ rfl rfl)

theorem lb_tag : ∀ (b : Fin 3) (h : Fin 2),
    (proQt ((Site.lb b h).pc + 1)).lookup (lbDst b h) = some (.bits 32) := by decide +kernel

theorem lb_keep : ∀ (b : Fin 3) (h : Fin 2), ∀ p ∈ proQt ((Site.lb b h).pc + 1), p.1 ≠ lbDst b h →
    (proQt (Site.lb b h).pc).lookup p.1 = some p.2 ∨ ([] : Env).lookup p.1 = some p.2 := by
  decide +kernel

theorem lb_fresh : ∀ (b : Fin 3) (h : Fin 2),
    lbDst b h ∉ (Data.tags (.lb b h)).map Data.Tag.reg := by decide +kernel

/-- **A block-table load** strictly steps to the barrier after it. -/
theorem step_lb (d : Data.D) (b : Fin 3) (h : Fin 2) (hs : d.c.site = .lb b h) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a, y, p, won, bcast⟩, vs⟩ := d
  cases hs
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨hI, hpay⟩ := hinv
  let c : Control.D := ⟨.lb b h, a, y, p, won, bcast⟩
  refine Code.ldWQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
    (P := fun v => ∃ x, v = b32 x) (r := lbDst b h) (d := ⟨c, vs⟩)
    (f := fun v => ⟨{c with site := lbBar b h}, payUp vs b h v⟩) (lb_fetch b h) rfl rfl rfl rfl
    ?_ ?_ rfl rfl ?_ (fun _ _ => typed_nil') ?_ ?_ ?_ e ins hat ⟨hI, hpay⟩ hc hq hw hf
  · exact fun e hWf hpc x bs hk => by
      obtain ⟨p, hp⟩ := hWf.2.1 b h hpc x bs hk
      exact ⟨_, hp, p, rfl⟩
  · intro x bs v hr hP
    obtain ⟨z, rfl⟩ := hP
    fin_cases h <;> simp [c, Data.code, Data.succ, Control.next, Data.record, hr,
      Except.toOption, Data.loadVal, payUp, lbBar]
  · exact fresh_reg (d := ⟨c, vs⟩) (lb_checked b h).1 (lb_fresh b h)
  · intro v ⟨z, hz⟩ tg hl
    rw [lb_tag b h] at hl
    cases hl
    exact ⟨_, by rw [hz]; rfl⟩
  · exact ld_hq (n := (Site.lb b h).pc) (r := lbDst b h) (lb_keep b h)
  · intro v ⟨z, hz⟩
    subst hz
    exact ⟨rfl, rfl, ⟨trivial, pay_site hpay (pre_pc.2.2 b h)⟩,
      dFacts_seg (pre := [(lbDst b h, b32 z)]) (lbA b h c vs z _ _ rfl rfl)⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
