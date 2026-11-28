-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.ElectSpan
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.EarlyFacts
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Step
public import Lemmas.Flow.SegQSkip
public import Lemmas.Flow.StepsQElect
public import Lemmas.Flow.StepsQGuard
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Init

@[expose] public section

/-! # The strict steps of the elections and the initializations -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

theorem init_key (i : Fin 12) : 26 + i.val ∈ ctlLive (Site.init i).pc := by
  obtain ⟨h, -⟩ := init_checked i; exact h

theorem init_sub (i : Fin 12) : (afterInit i).sub = 0 := by
  obtain ⟨-, h, -⟩ := init_checked i; exact h

theorem init_pc_eq (i : Fin 12) : (Site.init i).pc + 1 = (afterInit i).pc := by
  obtain ⟨-, -, h, -⟩ := init_checked i; exact h

theorem init_live (i : Fin 12) :
    (ctlLive (afterInit i).pc).isSublist (ctlLive (Site.init i).pc) = true := by
  obtain ⟨-, -, -, h⟩ := init_checked i; exact h

theorem el_votes (i : Fin 12) : (ctlLive (Site.el i).pc).all (fun k => !voteReg k) = true := by
  obtain ⟨h, -⟩ := el_checked i; exact h

theorem el_leader_free (i : Fin 12) : elLeader i ∉ ctlLive (Site.el i).pc := by
  obtain ⟨-, h, -⟩ := el_checked i; exact h

theorem el_pred_free (i : Fin 12) : 41 + i.val ∉ ctlLive (Site.el i).pc := by
  obtain ⟨-, -, h, -⟩ := el_checked i; exact h

theorem el_ne (i : Fin 12) : elLeader i ≠ 41 + i.val := by
  obtain ⟨-, -, -, h⟩ := el_checked i; exact h

theorem afterInit_early (i : Fin 12) : Data.early (afterInit i) = true := by
  unfold afterInit; split <;> rfl

theorem afterInit_inv (c : Control.D) (i : Fin 12) :
    Control.Inv (g % L.block) { c with site := afterInit i } := by
  unfold afterInit; split <;> trivial

theorem init_hn {Q : Params} (i : Fin 12) (c : Control.D) (hs : c.site = .init i) (ev : Event) :
    Control.next Q L g c ev = some (some { c with site := afterInit i }) := by
  obtain ⟨s, f, l, q, e, bc⟩ := c
  cases hs
  rfl

theorem init_next (d : Data.D) (i : Fin 12) (hs : d.c.site = .init i) (e : Event) :
    (Data.code Q L g w).next d e = some (some ⟨{ d.c with site := afterInit i }, d.v⟩) := by
  obtain ⟨⟨s, a, b, c, won, bcast⟩, vs⟩ := d
  cases hs
  rfl

/-- The machine's facts at an election do not read its result. -/
theorem code_facts_el (c : Control.D) (i : Fin 12) (hs : c.site = .el i) (v : Data.Vals)
    (b : Bool) : (Data.code Q L g w).facts ⟨c, v⟩ =
      (Data.code Q L g w).facts ⟨{c with elected := b}, v⟩ := by
  obtain ⟨s, f, l, q, e, bc⟩ := c
  cases hs
  exact code_facts_early rfl (plain_early rfl) (elect_facts _ _ b (el_votes i))

/-- The site after the election `i` whose result is `win`. -/
def elNext (L : Launch) (g : Nat) (i : Fin 12) (win : Bool) : Site :=
  if decide (g % L.block < 32) && win then .init i else afterInit i

theorem el_hn {Q : Params} (i : Fin 12) (c : Control.D) (hs : c.site = .el i) (mk inst ld) :
    Control.next Q L g c ⟨(Site.el i).pc, .elect mk inst ld⟩ = some (some
      { c with site := elNext L g i (laneOf L g == ld), elected := laneOf L g == ld }) := by
  obtain ⟨s, f, l, q, e, bc⟩ := c
  cases hs
  rfl

theorem el_inv (c : Control.D) (i : Fin 12) (win : Bool) :
    Control.Inv (g % L.block) { c with site := elNext L g i win, elected := win } := by
  unfold elNext
  split
  · rename_i h
    simpa [Control.Inv] using h
  · unfold afterInit; split <;> trivial

theorem el_pc_lt (i : Fin 12) : 41 < (Site.el i).pc := by fin_cases i <;> decide

/-- The skipped initialization: the guard of its election is false. -/
theorem init_skip (i : Fin 12) (a y p : Nat) (bcast : Value) (v : Data.Vals) (win : Bool)
    (h : (decide (g % L.block < 32) && win) = false) :
    SegQ kernel Assumptions.all L g (QT proQt) (Site.init i).pc
      (dFacts Q L g w (dS (.init i) a y p win bcast v)) (afterInit i).pc
      (dFacts Q L g w (dS (afterInit i) a y p win bcast v)) := by
  have e : (Site.init i).pc + 1 = (afterInit i).pc := (init_pc_eq i)
  rw [← e]
  refine SegQ.skipG (pick := false) (neg := false) (p := 26 + i.val) (init_fetch i) ?_ rfl ?_
    ((by decide +kernel : ∀ i : Fin 12, tagsIn (proQt ((Site.init i).pc + 1))
      (proQt (Site.init i).pc) = true) i)
  · intro R hR
    have key : 26 + i.val ∈ ctlLive (Site.init i).pc := (init_key i)
    have := holds_mem hR (List.mem_append_right _ (mem_factsFrom (val := valueOf Q L g w
      (dS (.init i) a y p win bcast v).c) key))
    have val : valueOf Q L g w (dS (.init i) a y p win bcast v).c (26 + i.val) =
        .pred (decide (g % L.block < 32) && win) := by fin_cases i <;> rfl
    rw [val, h] at this
    exact this
  · exact fun R hR => holds_dFacts_mono (w := w) (pc := (Site.init i).pc)
      (pc' := (afterInit i).pc) (dF_early (d := dS (.init i) a y p win bcast v)
        (d' := dS (afterInit i) a y p win bcast v) rfl (afterInit_early i)) rfl
      (init_live i) hR

/-- **The election of an initialization** strictly steps to the initialization or past it. -/
theorem step_el (d : Data.D) (i : Fin 12) (hs : d.c.site = .el i) (hk : Ok Q L g d) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a0, b0, c0, won, bcast⟩, vs⟩ := d
  cases hs
  have ha : a0 = b32 (Q.qStart (reqOf L g)) :=
    hk.1.first ((by decide : 34 < 41).trans (el_pc_lt i))
  have hb : b0 = b32 (Q.qStart (reqOf L g + 1)) :=
    hk.1.last ((by decide : 37 < 41).trans (el_pc_lt i))
  have hc : c0 = b32 (Q.seqK (reqOf L g)) := hk.1.seq (el_pc_lt i)
  subst ha hb hc
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨hI, hpay⟩ := hinv
  let A := Q.qStart (reqOf L g)
  let Y := Q.qStart (reqOf L g + 1)
  let P := Q.seqK (reqOf L g)
  let c := (dS (.el i) A Y P won bcast vs).c
  have hn : ∀ mk inst ld, (Data.code Q L g w).next (dS (.el i) A Y P won bcast vs)
      ⟨(Site.el i).pc, .elect mk inst ld⟩ = some (some (dS (elNext L g i (laneOf L g == ld))
        A Y P (laneOf L g == ld) bcast vs)) := fun _ _ _ => rfl
  refine Code.electQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
    (d := dS (.el i) A Y P won bcast vs)
    (dst := fun ld => dS (elNext L g i (laneOf L g == ld)) A Y P (laneOf L g == ld) bcast vs)
    (r := elLeader i) (p := 41 + i.val) (el_fetch i) ?_ ?_ (el_ne i) hn
    rfl rfl ?_ (fun _ => rfl) ?_ (fun _ _ => typed_nil') ?_ ?_ e ins hat ⟨hI, hpay⟩ hc hq hw hf
  · exact fresh_keys (el_leader_free i)
      ((by decide +kernel : ∀ i : Fin 12, elLeader i ∉ (Data.tags (.el i)).map Data.Tag.reg) i)
  · exact fresh_keys (el_pred_free i)
      ((by decide +kernel : ∀ i : Fin 12, 41 + i.val ∉ (Data.tags (.el i)).map Data.Tag.reg) i)
  · intro ld
    change (elNext L g i (laneOf L g == ld)).sub = 0
    unfold elNext
    split
    · rfl
    · exact (init_sub i)
  · intro ld
    exact ⟨el_inv (L := L) (g := g) c i _, payload_next (el_hn (Q := Q) (L := L) (g := g) i c rfl
      0 0 ld) hpay (fun j h => by cases h)⟩
  · exact (by decide +kernel : ∀ i : Fin 12, Code.afterWrites proQt (Site.el i).pc
      [(elLeader i, .bits 32), (41 + i.val, .pred)] [] = true) i
  · intro ld
    rw [code_facts_el _ i rfl vs (laneOf L g == ld)]
    by_cases h : (decide (g % L.block < 32) && (laneOf L g == ld)) = true
    · have e : elNext L g i (laneOf L g == ld) = .init i := by simp [elNext, h]
      rw [e]
      exact dFacts_seg (pre := [(41 + i.val, .pred (laneOf L g == ld)),
        (elLeader i, .bits 32 (BitVec.ofNat 64 ld))])
        ((elA i A Y P ld bcast vs _).comp (elB i A Y P bcast vs _))
    · have e : elNext L g i (laneOf L g == ld) = afterInit i := by simp [elNext, h]
      rw [e]
      exact dFacts_seg (pre := [(41 + i.val, .pred (laneOf L g == ld)),
        (elLeader i, .bits 32 (BitVec.ofNat 64 ld))])
        (((elA i A Y P ld bcast vs _).comp (elB i A Y P bcast vs _)).comp
          (init_skip i A Y P bcast vs _ (by simpa using h)))

/-- **The initialization** of a barrier strictly steps to the next election. -/
theorem step_init (d : Data.D) (i : Fin 12) (hs : d.c.site = .init i) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a, b, c, won, bcast⟩, vs⟩ := d
  cases hs
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨hI, hpay⟩ := hinv
  let c0 : Control.D := ⟨.init i, a, b, c, won, bcast⟩
  have hi : (Data.code Q L g w).inv ⟨⟨afterInit i, a, b, c, won, bcast⟩, vs⟩ :=
    ⟨afterInit_inv c0 i, payload_next (init_hn (Q := Q) (L := L) (g := g) i c0 rfl ⟨0, .exit⟩)
      hpay (fun j h => by cases h)⟩
  have hwr : Code.afterWrites proQt (Site.init i).pc [] [] = true :=
    (by decide +kernel : ∀ i : Fin 12, Code.afterWrites proQt (Site.init i).pc [] [] = true) i
  refine Code.advanceGQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
    (d := ⟨c0, vs⟩) (dn := ⟨⟨afterInit i, a, b, c, won, bcast⟩, vs⟩) (init_fetch i)
    (fun h => fires_next (by trivial) h) (fun e => init_next _ i rfl e) rfl rfl
    (init_sub i) rfl hi (fun _ _ => typed_nil') hwr
    (SegQ.cast_start (init_pc_eq i) (SegQ.weaken fun R hR => holds_code_mono (w := w)
      (d := ⟨c0, vs⟩) (d' := ⟨⟨afterInit i, a, b, c, won, bcast⟩, vs⟩)
      (dF_early rfl (afterInit_early i)) rfl (init_live i) hR))
    e ins hat ⟨hI, hpay⟩ hc hq hw hf

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
