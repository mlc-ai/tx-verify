-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.PreStepA
public import Lemmas.Flow.StepsQShflOne
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Shuffle

@[expose] public section

/-! # The strict steps of the block barriers and of the shuffle -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

/-- The arrival of a lane that is not the group's first is skipped. -/
theorem arr_skip (b : Fin 3) (c : Control.D) (v : Data.Vals) (h : g % L.block % 128 ≠ 0) :
    SegQ kernel Assumptions.all L g (QT proQt) (Site.arr b).pc (dFacts Q L g w (dq c v (.arr b)))
      ((Site.arr b).pc + 1) (dFacts Q L g w (dq c v (.arr b))) := by
  refine SegQ.skipG (pick := false) (neg := false) (p := 177) (arr_fetch b) ?_ rfl
    (fun R hR => hR) ((by decide +kernel : ∀ b : Fin 3, tagsIn (proQt ((Site.arr b).pc + 1))
      (proQt (Site.arr b).pc) = true) b)
  intro R hR
  have := holds_mem hR (List.mem_append_right _ (mem_factsFrom (val := valueOf Q L g w
    (dq c v (.arr b)).c) (arr_guard b)))
  have val : valueOf Q L g w (dq c v (.arr b)).c 177 =
      .pred (decide (g % L.block % 128 = 0)) := rfl
  rw [val, decide_eq_false h] at this
  exact this

theorem pb0_next (c : Control.D) (b : Fin 3) (hs : c.site = .pb b 0) (e : Event) :
    Control.next Q L g c e = some (some {c with site :=
      (if g % L.block % 128 = 0 then Site.arr b else Site.lb b 0)}) := by
  obtain ⟨s, f, l, q, n, bc⟩ := c
  cases hs
  simp [Control.next]

theorem pb0_lt : ∀ b : Fin 3, 130 ≤ (Site.pb b 0).pc := by decide +kernel

/-- **The first barrier of a preload block** strictly steps to the arrival or the table load. -/
theorem step_pb0 (d : Data.D) (b : Fin 3) (hs : d.c.site = .pb b 0) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a, y, p, won, bcast⟩, vs⟩ := d
  cases hs
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨hI, hpay⟩ := hinv
  let c : Control.D := ⟨.pb b 0, a, y, p, won, bcast⟩
  have wr := (by decide +kernel : ∀ b : Fin 3, Code.afterWrites proQt (Site.pb b 0).pc [] [] =
    true) b
  have hn := pb0_next (Q := Q) (L := L) (g := g) c b rfl
  by_cases lead : g % L.block % 128 = 0
  · simp only [lead, ↓reduceIte] at hn
    refine Code.advanceQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
      (d := ⟨c, vs⟩) (dn := dq c vs (.arr b)) (pb0_fetch b) (fun h => fires_barSyncN_next h)
      (data_next (d := ⟨c, vs⟩) hn (fun _ => rfl)) rfl rfl rfl rfl
      ⟨lead, pay_site hpay (pb0_lt b)⟩ (fun _ _ => typed_nil') wr ?_ e ins hat ⟨hI, hpay⟩ hc hq hw
      hf
    exact dFacts_seg (pre := []) (SegQ.cast_start (pb0_adj b).1 (site_subAt c vs _ _ _ _
      (pre_tags_sub b).1 (pb0_adj b).2))
  · simp only [lead, ↓reduceIte] at hn
    refine Code.advanceQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
      (d := ⟨c, vs⟩) (dn := dq c vs (.lb b 0)) (pb0_fetch b) (fun h => fires_barSyncN_next h)
      (data_next (d := ⟨c, vs⟩) hn (fun _ => rfl)) rfl rfl rfl rfl
      ⟨trivial, pay_site hpay (pb0_lt b)⟩ (fun _ _ => typed_nil') wr ?_ e ins hat ⟨hI, hpay⟩ hc hq
      hw hf
    refine dFacts_seg (pre := []) (SegQ.comp (b := (Site.arr b).pc) (G := dFacts Q L g w
      (dq c vs (.arr b))) (SegQ.cast_start (pb0_adj b).1 (site_subAt c vs _ _ _ _
      (pre_tags_sub b).1 (pb0_adj b).2)) (SegQ.comp (b := (Site.arr b).pc + 1)
      (G := dFacts Q L g w (dq c vs (.arr b))) (arr_skip b c vs lead) (pa b c vs _ _ rfl rfl)))

theorem pbt_tags : ∀ (b : Fin 3) (j : Fin 4),
    ∀ τ ∈ Data.tags (pbTail b j), τ ∈ Data.tags (pbBar b j) := by decide +kernel

theorem pbt_lt : ∀ (b : Fin 3) (j : Fin 4), 130 ≤ (pbBar b j).pc := by decide +kernel

theorem pbt_next (c : Control.D) (b : Fin 3) (j : Fin 4) (hs : c.site = pbBar b j) (e : Event) :
    Control.next Q L g c e = some (some {c with site := pbTail b j}) := by
  obtain ⟨s, f, l, q, n, bc⟩ := c
  cases hs
  fin_cases j <;> rfl

theorem pbt_inv (c : Control.D) (b : Fin 3) (j : Fin 4) :
    Control.Inv (g % L.block) {c with site := pbTail b j} := by
  fin_cases j <;> trivial

theorem pbt_sub (b : Fin 3) (j : Fin 4) : (pbTail b j).sub = 0 := by fin_cases j <;> rfl

/-- **The other barriers of a preload block** strictly step to the shuffle or the elections. -/
theorem step_pbT (d : Data.D) (b : Fin 3) (j : Fin 4) (hs : d.c.site = pbBar b j) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a, y, p, won, bcast⟩, vs⟩ := d
  cases hs
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨hI, hpay⟩ := hinv
  let c : Control.D := ⟨pbBar b j, a, y, p, won, bcast⟩
  have wr := (by decide +kernel : ∀ (b : Fin 3) (j : Fin 4),
    Code.afterWrites proQt (pbBar b j).pc [] [] = true) b j
  refine Code.advanceQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
    (d := ⟨c, vs⟩) (dn := dq c vs (pbTail b j)) (pbt_fetch b j)
    (fun h => fires_barSyncN_next h)
    (data_next (d := ⟨c, vs⟩) (pbt_next c b j rfl) (fun _ => by
      obtain ⟨b', j'⟩ := (⟨b, j⟩ : Fin 3 × Fin 4); fin_cases b <;> fin_cases j <;> rfl))
    rfl rfl (pbt_sub b j) rfl
    ⟨pbt_inv c b j, pay_site hpay (pbt_lt b j)⟩ (fun _ _ => typed_nil') wr ?_ e ins hat
    ⟨hI, hpay⟩ hc hq hw hf
  exact dFacts_seg (pre := []) (SegQ.cast_start (pbt_frames b j).1 (site_subAt c vs _ _ _ _
    (pbt_tags b j) (pbt_frames b j).2))

theorem psh_pel : ∀ b : Fin 3, (Site.psh b).pc + 1 = (Site.pel b 0).pc := by decide +kernel

theorem psh_free : ∀ b : Fin 3, pshDest b ∉ ctlLive (Site.psh b).pc ∧
    pshDest b ∉ (Data.tags (.psh b)).map Data.Tag.reg := by decide +kernel

theorem psh_tags : ∀ b : Fin 3, (∀ τ ∈ Data.tags (.pel b 0), τ ∈ Data.tags (.psh b)) ∧
    ∀ τ ∈ Data.tags (.pel b 0), ∀ b' h, τ ≠ .col b' h := by decide +kernel

/-- The broadcast does not change the facts that name the word it fills. -/
theorem psh_sub (c : Control.D) (vs : Data.Vals) (b : Fin 3) (y : BitVec 64) :
    ∀ q ∈ (Data.code Q L g w).facts ⟨{c with site := .pel b 0, broadcast := .bits 32 y}, vs⟩,
      q ∈ (pshDest b, Value.bits 32 y) ::
        (Data.code Q L g w).facts ⟨{c with site := .psh b}, vs⟩ := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    rcases of_decide_eq_true (List.all_eq_true.mp (psh_frames b) r hr) with rfl | ⟨fixed, old⟩
    · have val : valueOf Q L g w {c with site := .pel b 0, broadcast := .bits 32 y} (pshDest b) =
          .bits 32 y := by fin_cases b <;> rfl
      show (pshDest b, valueOf Q L g w {c with site := .pel b 0, broadcast := .bits 32 y}
        (pshDest b)) ∈ _
      rw [val]
      exact List.mem_cons_self
    · refine List.mem_cons_of_mem _ (List.mem_append_left _ ?_)
      rw [valueOf_plain fixed]
      have := mem_factsFrom (val := valueOf Q L g w {c with site := .psh b}) old
      rwa [valueOf_plain fixed] at this
  · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp h
    refine List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr
      ⟨τ, (psh_tags b).1 τ hτ, ?_⟩))
    have := (psh_tags b).2 τ hτ
    cases τ <;> first | rfl | exact absurd rfl (this _ _)

theorem psh_next (c : Control.D) (b : Fin 3) (hs : c.site = .psh b) (m a b' c' recv ok) :
    Control.next Q L g c ⟨(Site.psh b).pc, .shfl m a b' c' recv ok⟩ =
      some (some {c with site := .pel b 0, broadcast := recv}) := by
  obtain ⟨s, f, l, q, n, bc⟩ := c
  cases hs
  rfl

/-- **The broadcast of the page word** strictly steps to the first election of the block. -/
theorem step_psh (d : Data.D) (b : Fin 3) (hs : d.c.site = .psh b) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a, y, p, won, bcast⟩, vs⟩ := d
  cases hs
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨hI, hpay⟩ := hinv
  let c : Control.D := ⟨.psh b, a, y, p, won, bcast⟩
  have hl : 130 ≤ (Site.psh b).pc := (by decide +kernel : ∀ b : Fin 3, 130 ≤ (Site.psh b).pc) b
  refine Code.shflOneQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
    (d := ⟨c, vs⟩) (dn := fun r => ⟨{c with site := .pel b 0, broadcast := r}, vs⟩)
    (r := pshDest b) (psh_fetch b) ?_ ?_ ?_ rfl rfl (fun _ => rfl) (fun _ => rfl)
    (fun y => ⟨trivial, pay_site hpay hl⟩) (fun _ _ => typed_nil')
    ((by decide +kernel : ∀ b : Fin 3, Code.afterWrites proQt (Site.psh b).pc
      [(pshDest b, .bits 32)] [] = true) b) ?_ e ins hat ⟨hI, hpay⟩ hc hq hw hf
  · intro q hq he
    have hm : q.1 ∈ ((Data.code Q L g w).facts ⟨c, vs⟩).map Prod.fst := List.mem_map_of_mem hq
    exact fresh_keys (d := ⟨c, vs⟩) (psh_free b).1 (psh_free b).2 (he ▸ hm)
  · intro e' hWf hpc m av bv cv recv ok hk
    obtain ⟨-, -, -, h⟩ := hWf
    exact h b hpc m av bv cv recv ok hk
  · intro m av bv cv recv ok
    show (Control.next Q L g c ⟨(Site.psh b).pc, .shfl m av bv cv recv ok⟩).map _ = _
    rw [psh_next c b rfl]
    rfl
  · intro y
    exact SegQ.cast_start (psh_pel b) (SegQ.sub (psh_sub c vs b y))

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
