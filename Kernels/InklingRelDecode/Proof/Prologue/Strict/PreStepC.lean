-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.PreTail
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.PreSpanE
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.CopyElection
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.QueryRoute
import Kernels.InklingRelDecode.Flow.Code.Part003
import Kernels.InklingRelDecode.Flow.Code.Part004

@[expose] public section

/-! # The strict steps of the tensor copies and of their elections -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

theorem ptc_fetch (b : Fin 3) (j : Fin 4) : ∃ op, kernel.code[(Site.ptc b j).pc]? =
    some ⟨some (copyGuard b j, false), op⟩ ∧ AdvancesOp op := by
  fin_cases b <;> fin_cases j
  · exact ⟨_, Flow.code_211, trivial⟩
  · exact ⟨_, Flow.code_217, trivial⟩
  · exact ⟨_, Flow.code_226, trivial⟩
  · exact ⟨_, Flow.code_231, trivial⟩
  · exact ⟨_, Flow.code_253, trivial⟩
  · exact ⟨_, Flow.code_259, trivial⟩
  · exact ⟨_, Flow.code_268, trivial⟩
  · exact ⟨_, Flow.code_273, trivial⟩
  · exact ⟨_, Flow.code_295, trivial⟩
  · exact ⟨_, Flow.code_301, trivial⟩
  · exact ⟨_, Flow.code_310, trivial⟩
  · exact ⟨_, Flow.code_315, trivial⟩
/-- The site after the copy `j` of block `b`. -/
noncomputable abbrev acSite (Q : Params) (L : Launch) (g : Nat) (c : Control.D) (b : Fin 3)
    (j : Fin 4) : Site := afterCopy c (g % L.block) (preloadN Q L g c) b j

theorem ptc_next (c : Control.D) (b : Fin 3) (j : Fin 4) (hs : c.site = .ptc b j) (e : Event) :
    Control.next Q L g c e = some (some {c with site := acSite Q L g c b j}) := by
  obtain ⟨s, f, l, q, n, bc⟩ := c
  cases hs
  rfl

/-- The site after a copy is a site of the loop or a query site: it has no element and holds. -/
theorem ac_ok (c : Control.D) (b : Fin 3) (j : Fin 4) :
    (acSite Q L g c b j).sub = 0 ∧
      Control.Inv (g % L.block) {c with site := acSite Q L g c b j} := by
  obtain ⟨-, qinv, qsub⟩ := query_route (Q := Q) (L := L) (g := g) (w := b32 0) (d := c) 0
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj with rfl | rfl | rfl | rfl
  · exact ⟨rfl, trivial⟩
  · exact ⟨rfl, trivial⟩
  · exact ⟨rfl, trivial⟩
  simp only [acSite, afterCopy]
  split_ifs <;> first | exact ⟨qsub, qinv⟩ | exact ⟨rfl, trivial⟩

theorem ptc_lt : ∀ (b : Fin 3) (j : Fin 4), 130 ≤ (Site.ptc b j).pc := by decide +kernel

/-- **A tensor copy** strictly steps to the site after the copy. -/
theorem step_ptc {m} (hp : Pre Q L m) (hw0 : w = b32 0) (d : Data.D) (b : Fin 3) (j : Fin 4)
    (hs : d.c.site = .ptc b j) (hk : Ok Q L g d) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a, y, p, won, bcast⟩, vs⟩ := d
  cases hs
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨hI, hpay⟩ := hinv
  let c : Control.D := ⟨.ptc b j, a, y, p, won, bcast⟩
  obtain ⟨op, hfetch, hadv⟩ := ptc_fetch b j
  obtain ⟨hsub, hinv'⟩ := ac_ok (Q := Q) (L := L) (g := g) c b j
  refine Code.advanceGQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
    (d := ⟨c, vs⟩) (dn := dq c vs (acSite Q L g c b j)) hfetch
    (fun h => fires_next hadv h) (data_next (d := ⟨c, vs⟩) (ptc_next c b j rfl) (fun _ => rfl))
    (by fin_cases j <;> rfl) rfl hsub rfl ⟨hinv', pay_site hpay (ptc_lt b j)⟩
    (fun _ _ => typed_nil') ((by decide +kernel : ∀ (b : Fin 3) (j : Fin 4),
      Code.afterWrites proQt (Site.ptc b j).pc [] [] = true) b j) ?_ e ins hat ⟨hI, hpay⟩ hc hq
    hw hf
  exact dFacts_seg (pre := []) (ptc_res hp hw0 hk.qBytes c b j _ rfl)

/-- The site after the election of a copy whose result is `win`. -/
noncomputable def pelNext (Q : Params) (L : Launch) (g : Nat) (c : Control.D) (b : Fin 3)
    (j : Fin 4) (win : Bool) : Site :=
  if decide (g % L.block % 128 < 64) && win then .ptc b j else acSite Q L g c b j

/-- The state after the election of a copy won by lane `ld`. -/
noncomputable def pelDst (Q : Params) (L : Launch) (g : Nat) (c : Control.D) (vs : Data.Vals)
    (b : Fin 3) (j : Fin 4) (ld : Nat) : Data.D :=
  ⟨{c with site := pelNext Q L g c b j (laneOf L g == ld), elected := laneOf L g == ld}, vs⟩

theorem pel_hn (c : Control.D) (b : Fin 3) (j : Fin 4) (hs : c.site = .pel b j) (mk inst ld) :
    Control.next Q L g c ⟨(Site.pel b j).pc, .elect mk inst ld⟩ = some (some {c with
      site := pelNext Q L g c b j (laneOf L g == ld), elected := laneOf L g == ld}) := by
  obtain ⟨s, f, l, q, n, bc⟩ := c
  cases hs
  rfl

/-- The machine's facts at a copy election do not read its result. -/
theorem code_facts_pel (c : Control.D) (b : Fin 3) (j : Fin 4) (hs : c.site = .pel b j)
    (v : Data.Vals) (win : Bool) : (Data.code Q L g w).facts ⟨c, v⟩ =
      (Data.code Q L g w).facts ⟨{c with elected := win}, v⟩ := by
  obtain ⟨s, f, l, q, e, bc⟩ := c
  cases hs
  change facts Q L g w _ _ ++ _ = facts Q L g w _ _ ++ _
  congr 1
  exact elect_facts _ _ win (pel_checked b j).1

theorem pel_inv (c : Control.D) (b : Fin 3) (j : Fin 4) (win : Bool) :
    Control.Inv (g % L.block) {c with site := pelNext Q L g c b j win, elected := win} ∧
    (pelNext Q L g c b j win).sub = 0 := by
  unfold pelNext
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨by simpa [Control.Inv] using h, rfl⟩
  · obtain ⟨h1, h2⟩ := ac_ok (Q := Q) (L := L) (g := g) {c with elected := win} b j
    exact ⟨h2, h1⟩

theorem pel_free : ∀ (b : Fin 3) (j : Fin 4),
    pelLeader b j ∉ (Data.tags (.pel b j)).map Data.Tag.reg ∧
    copyVote b j ∉ (Data.tags (.pel b j)).map Data.Tag.reg := by decide +kernel

theorem pel_lt : ∀ (b : Fin 3) (j : Fin 4), 130 ≤ (Site.pel b j).pc := by decide +kernel

/-- The skipped copy: the guard of its election is false. -/
theorem ptc_skip (b : Fin 3) (j : Fin 4) (c : Control.D) (v : Data.Vals) (win : Bool)
    (h : (decide (g % L.block % 128 < 64) && win) = false) :
    SegQ kernel Assumptions.all L g (QT proQt) (Site.ptc b j).pc
      (dFacts Q L g w (dq {c with elected := win} v (.ptc b j))) ((Site.ptc b j).pc + 1)
      (dFacts Q L g w (dq {c with elected := win} v (.ptc b j))) := by
  obtain ⟨op, hc⟩ := ptc_guarded b j
  refine SegQ.skipG (pick := false) (neg := false) (p := copyGuard b j) hc ?_ rfl (fun R hR => hR)
    ((by decide +kernel : ∀ (b : Fin 3) (j : Fin 4),
      tagsIn (proQt ((Site.ptc b j).pc + 1)) (proQt (Site.ptc b j).pc) = true) b j)
  intro R hR
  have := holds_mem hR (List.mem_append_right _ (mem_factsFrom (val := valueOf Q L g w
    (dq {c with elected := win} v (.ptc b j)).c) (pel_checked b j).2.2))
  have val : valueOf Q L g w (dq {c with elected := win} v (.ptc b j)).c (copyGuard b j) =
      .pred (decide (g % L.block % 128 < 64) && win) := by fin_cases b <;> fin_cases j <;> rfl
  rw [val, h] at this
  exact this

/-- **The election of a copy** strictly steps to the copy or past it. -/
theorem step_pel {m} (hp : Pre Q L m) (hw0 : w = b32 0) (d : Data.D) (b : Fin 3) (j : Fin 4)
    (hs : d.c.site = .pel b j) (hk : Ok Q L g d) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a, y, p, won, bcast⟩, vs⟩ := d
  cases hs
  have hv := hk.qBytes
  obtain ⟨-, ⟨x, hx⟩, -, -⟩ := hk
  cases hx
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨hI, hpay⟩ := hinv
  let c : Control.D := ⟨.pel b j, a, y, p, won, .bits 32 x⟩
  obtain ⟨-, ⟨-, -, hne⟩, -⟩ := pel_checked b j
  refine Code.electQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
    (d := ⟨c, vs⟩) (dst := pelDst Q L g c vs b j) (r := pelLeader b j) (p := copyVote b j)
    (pel_fetch b j)
    ?_ ?_ hne ?_ rfl rfl (fun ld => (pel_inv c b j _).2) (fun _ => rfl) ?_ (fun _ _ => typed_nil')
    ((by decide +kernel : ∀ (b : Fin 3) (j : Fin 4), Code.afterWrites proQt (Site.pel b j).pc
      [(pelLeader b j, .bits 32), (copyVote b j, .pred)] [] = true) b j) ?_ e ins hat
    ⟨hI, hpay⟩ hc hq hw hf
  · exact fresh_keys (d := ⟨c, vs⟩) (pel_checked b j).2.1.1 (pel_free b j).1
  · exact fresh_keys (d := ⟨c, vs⟩) (pel_checked b j).2.1.2.1 (pel_free b j).2
  · intro mk inst ld
    show (Control.next Q L g c ⟨(Site.pel b j).pc, .elect mk inst ld⟩).map _ = _
    rw [pel_hn c b j rfl]
    rfl
  · intro ld
    exact ⟨(pel_inv c b j _).1, payload_next (pel_hn (Q := Q) (L := L) (g := g) c b j rfl 0 0 ld)
      hpay (fun j h => by cases h)⟩
  · intro ld
    rw [code_facts_pel c b j rfl vs (laneOf L g == ld)]
    refine dFacts_seg (pre := [(copyVote b j, .pred (laneOf L g == ld)),
      (pelLeader b j, .bits 32 (BitVec.ofNat 64 ld))]) ?_
    unfold pelDst
    by_cases h : (decide (g % L.block % 128 < 64) && (laneOf L g == ld)) = true
    · have e : pelNext Q L g c b j (laneOf L g == ld) = .ptc b j := by simp [pelNext, h]
      rw [e]
      exact pelA b j c x vs ld _ _ _ rfl rfl
    · have e : pelNext Q L g c b j (laneOf L g == ld) = acSite Q L g c b j := by
        simp [pelNext, h]
      rw [e]
      exact (pelA b j c x vs ld _ _ _ rfl rfl).comp ((ptc_skip b j c vs _ (by simpa using h)).comp
        (ptc_res hp hw0 hv {c with elected := laneOf L g == ld} b j _ rfl))

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
