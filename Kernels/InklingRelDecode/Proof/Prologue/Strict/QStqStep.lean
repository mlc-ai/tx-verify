-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.QStqNext
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.QLdStep
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Store
public import Lemmas.Flow.StepsQVst

@[expose] public section

/-! # The strict steps of the query stores and of the end of the prologue -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

theorem stq_mid : ∀ (i : Fin 8) (j : Fin 4) (h : j.val + 1 < 4),
    (∀ τ ∈ Data.tags (.stq i ⟨j.val + 1, h⟩), τ ∈ Data.tags (.stq i j)) ∧
    Control.afterStore i j = .stq i ⟨j.val + 1, h⟩ ∧
    Code.afterWrites proQt (Site.stq i j).pc [] [] = true := by decide +kernel

theorem stq_wr : ∀ (i : Fin 8) (j : Fin 4),
    Code.afterWrites proQt (Site.stq i j).pc [] [] = true := by decide +kernel

theorem stq_last : ∀ i : Fin 7, Control.afterStore (f8 i) 3 = .stq (f8s i) 0 := by decide +kernel

theorem stq_tail : (∀ τ ∈ Data.tags .fnc1, τ ∈ Data.tags (.stq 7 3)) ∧
    (ctlLive 569).isSublist (ctlLive 568) = true ∧ Control.afterStore 7 3 = .fnc1 := by
  decide +kernel


theorem stq_next_eq (c : Control.D) (v : Data.Vals) (i : Fin 8) (j : Fin 4) (hs : c.site = .stq i j)
    (e : Event) : (Data.code Q L g w).next ⟨c, v⟩ e =
      some (some ⟨{c with site := Control.afterStore i j}, v⟩) := by
  obtain ⟨_, a, b, c0, won, bcast⟩ := c
  cases hs
  rfl

theorem stq_ctl_eq {i : Fin 8} {j : Fin 4} (c : Control.D) (e : Event) (hs : c.site = .stq i j) :
    Control.next Q L g c e = some (some {c with site := Control.afterStore i j}) := by
  obtain ⟨_, a, b, c0, won, bcast⟩ := c
  cases hs
  rfl

/-- **An element of a query store** strictly steps to the next element or the next store. -/
theorem step_stq (d : Data.D) (i : Fin 8) (j : Fin 4) (hs : d.c.site = .stq i j)
    (hk : Ok Q L g d) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a, b, c0, won, bcast⟩, vs⟩ := d
  cases hs
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨hI, hpay⟩ := hinv
  let c : Control.D := ⟨.stq i j, a, b, c0, won, bcast⟩
  have hv : ∀ k, (vs.q k).bytes = 2 := hk.qBytes
  have pay : Payload {c with site := Control.afterStore i j} :=
    payload_next (Q := Q) (L := L) (g := g) (d := c) (e := ⟨0, .exit⟩)
      (stq_ctl_eq (Q := Q) (L := L) (g := g) c ⟨0, .exit⟩ rfl) hpay (fun k h => by cases h)
  by_cases hm : j.val + 1 < 4
  · obtain ⟨ht, hnext, hwr⟩ := stq_mid i j hm
    rw [hnext] at pay
    refine Code.vstQW (C := Data.code Q L g w) (qt := proQt) (ex := [])
      (d := ⟨c, vs⟩) (dn := ⟨{c with site := .stq i ⟨j.val + 1, hm⟩}, vs⟩)
      (Control.fetchQueryStore i) rfl (fun e => by rw [stq_next_eq c vs i j rfl, hnext]) rfl
      (fun _ => ⟨rfl, rfl, rfl, fun R h => holds_of_forall fun p hp => holds_mem h ?_,
        ⟨trivial, pay⟩⟩) (fun _ _ => typed_nil') (stq_wr i j) (fun h => absurd hm h) e ins hat
      ⟨hI, hpay⟩ hc hq hw hf
    rcases List.mem_append.mp hp with h | h
    · exact List.mem_append_left _ h
    · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp h
      rw [tag_val_site (Q := Q) (L := L) (g := g) c vs (.stq i ⟨j.val + 1, hm⟩) (.stq i j) τ]
      exact List.mem_append_right _ (List.mem_map_of_mem
        (f := fun τ => (τ.reg, τ.val Q L g (dq c vs (.stq i j)))) (ht τ hτ))
  · have hj : j = 3 := Fin.ext (by omega)
    subst hj
    by_cases hi : i.val < 7
    · obtain ⟨i', rfl⟩ : ∃ i' : Fin 7, i = f8 i' := ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
      rw [stq_last i'] at pay
      have key := stq_next (Q := Q) (L := L) (g := g) (w := w) c vs hv i'
      have e1 : 527 + 6 * i'.val = 526 + 6 * i'.val + 1 := by omega
      have e2 : 532 + 6 * i'.val = 526 + 6 * (f8s i').val := by
        have : (f8s i').val = i'.val + 1 := rfl
        omega
      rw [e1, e2] at key
      refine Code.vstQW (C := Data.code Q L g w) (qt := proQt) (ex := [])
        (d := ⟨c, vs⟩) (dn := ⟨{c with site := .stq (f8s i') 0}, vs⟩)
        (Control.fetchQueryStore _) rfl (fun e => by rw [stq_next_eq c vs _ _ rfl, stq_last i'])
        rfl (fun h => absurd h (by simp [Data.code, srcs, c, Site.sub])) (fun _ _ => typed_nil')
        (stq_wr _ 3) (fun _ => ⟨rfl, rfl, ⟨trivial, pay⟩, dFacts_seg (pre := []) key⟩) e ins
        hat ⟨hI, hpay⟩ hc hq hw hf
    · have hi7 : i = 7 := Fin.ext (by omega)
      subst hi7
      obtain ⟨ht, hl, hf1⟩ := stq_tail
      rw [hf1] at pay
      have fn : SegQ kernel Assumptions.all L g (QT proQt) 569 (dFacts Q L g w ⟨c, vs⟩) 569
          (dFacts Q L g w ⟨{c with site := .fnc1}, vs⟩) := by
        refine SegQ.sub fun q hq' => ?_
        rcases List.mem_append.mp hq' with h | h
        · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp h
          rw [tag_val_site (Q := Q) (L := L) (g := g) c vs .fnc1 (.stq 7 3) τ]
          exact List.mem_append_left _ (List.mem_map_of_mem
            (f := fun τ => (τ.reg, τ.val Q L g (dq c vs (.stq 7 3)))) (ht τ hτ))
        · exact List.mem_append_right _ (mem_facts_sub hl h)
      refine Code.vstQW (C := Data.code Q L g w) (qt := proQt) (ex := [])
        (d := ⟨c, vs⟩) (dn := ⟨{c with site := .fnc1}, vs⟩)
        (Control.fetchQueryStore _) rfl (fun e => by rw [stq_next_eq c vs _ _ rfl, hf1])
        rfl (fun h => absurd h (by simp [Data.code, srcs, c, Site.sub])) (fun _ _ => typed_nil')
        (stq_wr _ 3) (fun _ => ⟨rfl, rfl, ⟨trivial, pay⟩, dFacts_seg (pre := []) fn⟩) e ins hat
        ⟨hI, hpay⟩ hc hq hw hf

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
