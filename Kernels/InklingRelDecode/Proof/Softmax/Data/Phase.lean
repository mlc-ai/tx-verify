-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Update
public import Lemmas.Flow.PhaseTable
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The facts of the update crossing by position

On the way from the round to the barrier of pc 999 the thread runs through code the control
machine decides by branches (the first round's skip, the skipped rescale, the end of the O
rescale). The facts are given by position: the round's before pc 949, the new running maximum
from pc 950 to pc 999. The control machine says where the thread stops. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

set_option maxRecDepth 100000
noncomputable section
variable {L : Launch} {g : Nat}

/-- After the update (pcs 950 to 999) the running maximum is the new one. -/
def updPost (pc : Nat) : Bool := decide (950 ≤ pc ∧ pc ≤ 999)

def updKeys (pc : Nat) : List Nat :=
  if updPost pc then [498, 1914] else [498, 1914, 1522, 168, 507]

def updSpec (pc : Nat) : Bool := decide (pc = 949)

/-- The values before the update. -/
def updV1 (L : Launch) (m mx : Value) : Nat → Value := Lib.alphaVal (scaleW L) m mx

/-- The values after the update. -/
def updV2 (L : Launch) (m mx : Value) (r : Nat) : Value :=
  if r = 1914 then Lib.mNext (scaleW L) m mx else Lib.alphaVal (scaleW L) m mx r

/-- The update item as a run of one step. -/
theorem upd_segd (c m mx : Value) :
    SegD kernel Assumptions.all L g 1 949
      (factsFrom [1914, 1522, 168, 498] (Lib.alphaVal c m mx)) 950
      (factsFrom [1914, 1522, 168, 498] (xFinal (Lib.alphaVal c m mx) [.base Lib.updItem]))
      (xCond (Lib.alphaVal c m mx) [.base Lib.updItem]) := by
  have := SegD.xouts (K := kernel) (A := Assumptions.all) (L := L) (g := g)
    (items := [.base Lib.updItem]) (liveS := [1914, 1522, 168, 498])
    (liveT := [1914, 1522, 168, 498])
    (V := Lib.alphaVal c m mx) (Lib.upd_at (L := L) (g := g)).code (by decide +kernel)
    (by
      have pred : isPred (Lib.alphaVal c m mx 168) = true := by
        simp [Lib.alphaVal, Lib.alphaRest, xFinal, XItem.upd, XItem.vals, OItem.vals, isPred,
          Function.update]
      simp [xReq, XItem.req, OItem.req, Lib.updItem, pred, isRegOrF32])
    (by decide +kernel) (Lib.upd_at (L := L) (g := g)).rules (by decide +kernel)
  exact this

theorem upd_val (c m mx : Value) (r : Nat) (hr : r = 498 ∨ r = 1914) :
    xFinal (Lib.alphaVal c m mx) [.base Lib.updItem] r =
      if r = 1914 then Lib.mNext c m mx else Lib.alphaVal c m mx r := by
  rcases hr with rfl | rfl
  · rw [Lib.xFinal_other (by decide)]; simp
  · simp only [ite_true]; rfl

/-- **The update step**: the table's facts of pc 949 give those of pc 950. -/
theorem upd_spec {ivs : List (Nat × Nat)} (hiv : inIvs ivs 950 = true) (m mx : Value) :
    ∀ pc, updSpec pc = true → inIvs ivs pc = true → ∀ t t1 : TState, t.pc = pc →
      TabAt updKeys updPost (updV1 L m mx) (updV2 L m mx) t →
      Tau kernel Assumptions.all L g t t1 →
      ((inIvs ivs t1.pc || evAtB kernel t1.pc) = true ∧
        TabAt updKeys updPost (updV1 L m mx) (updV2 L m mx) t1) ∨
        Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) t1 := by
  intro pc hsp _ t t1 hpc hT ht1
  simp only [updSpec, decide_eq_true_eq] at hsp
  subst hsp
  obtain ⟨hsub, hacc, hH⟩ := hT
  have hfault : t.fault = none := by
    unfold Tau out at ht1
    cases hf : t.fault with
    | none => rfl
    | some f => rw [hf] at ht1; cases ht1
  have hpost : updPost 949 = false := by decide
  have hF : Holds t.regs (factsFrom [1914, 1522, 168, 498] (Lib.alphaVal (scaleW L) m mx)) := by
    rw [hpc] at hH
    simp only [phi, hpost, Bool.false_eq_true, ↓reduceIte, updKeys] at hH
    exact holds_factsFrom_mono hH (by decide)
  have seg := upd_segd (L := L) (g := g) (scaleW L) m mx t ⟨hpc, hsub, hacc, hfault, hF⟩
  by_cases hC : xCond (Lib.alphaVal (scaleW L) m mx) [.base Lib.updItem]
  · obtain ⟨u, hr, hu⟩ := seg.1 hC
    have hTau : Tau kernel Assumptions.all L g t u :=
      tauStep_iff.mp (by simpa [run] using hr)
    rw [tau_det ht1 hTau]
    refine .inl ⟨?_, hu.2.1, hu.2.2.1, ?_⟩
    · rw [hu.1]; simp [hiv]
    · refine holds_of_pointwise fun r hr' => ?_
      have hpu : updPost u.pc = true := by rw [hu.1]; decide
      simp only [updKeys, hpu, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr'
      obtain ⟨-, -, -, -, hur⟩ := id hu
      have hm := holds_mem hur (mem_factsFrom (val := xFinal (Lib.alphaVal (scaleW L) m mx)
        [.base Lib.updItem]) (show r ∈ [1914, 1522, 168, 498] by simp; omega))
      simp only [updV2, hpu, ↓reduceIte]
      rw [← upd_val _ _ _ r (by omega)]
      exact hm
  · exact .inr (dead_step (seg.2 hC) ht1)

/-- The table's facts at a position that the machine's data facts follow from. -/
theorem phi_round {s : Site} (hs : s = .waitO ∨ s = .ldO) (v : Vals) {R : Nat → Option Value}
    (h : Holds R (phi updKeys updPost (updV1 L v.m v.mx) (updV2 L v.m v.mx) s.pc)) :
    Holds R (dFS L s v) := by
  rcases hs with rfl | rfl
  all_goals
    refine holds_of_mem fun r x hm => holds_mem h ?_
    simp [dFS, inRound, alphaFacts, phi, updKeys, updPost, updV1, factsFrom, Site.pc,
      Flow.mbarWait_1, Flow.tmemLoad_1, alphaVal_c, alphaVal_m, alphaVal_mx] at hm ⊢
    exact hm

theorem phi_bar20 (m mx : Value) (v : Vals) (hv : v.m = Lib.mNext (scaleW L) m mx)
    {R : Nat → Option Value}
    (h : Holds R (phi updKeys updPost (updV1 L m mx) (updV2 L m mx) 999)) :
    Holds R (dFS L .bar20 v) := by
  refine holds_of_mem fun r x hm => holds_mem h ?_
  simp [dFS, inRound, phi, updKeys, updPost, updV2, factsFrom, alphaVal_c, hv] at hm ⊢
  exact hm

/-- **The data step after the event**: the facts by position at the stop the control machine
names (`F`, the facts of the stop's site). -/
theorem goal_tab {ivs : List (Nat × Nat)} {keys : Nat → List Nat} {post spec : Nat → Bool}
    {V1 V2 : Nat → Value} {F : List (Nat × Value)} {u : TState} {q : Nat}
    (hscan : tabScan kernel ivs keys post spec = true)
    (hS : ∀ pc, inIvs ivs pc = true → spec pc = false → Assumption.SegFreePc Assumptions.all pc)
    (hspec : ∀ pc, spec pc = true → inIvs ivs pc = true → ∀ t t1 : TState, t.pc = pc →
      TabAt keys post V1 V2 t →
      Tau kernel Assumptions.all L g t t1 →
      ((inIvs ivs t1.pc || evAtB kernel t1.pc) = true ∧ TabAt keys post V1 V2 t1) ∨
        Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) t1)
    (hu : (inIvs ivs u.pc || evAtB kernel u.pc) = true) (hT : TabAt keys post V1 V2 u)
    (hstops : (∀ t'', Relation.ReflTransGen (Tau kernel Assumptions.all L g) u t'' →
      Stops kernel Assumptions.all L g t'' → t''.pc = q) ∨
      Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) u)
    (hconv : ∀ R, Holds R (phi keys post V1 V2 q) → Holds R F) :
    (∀ t', Relation.ReflTransGen (Tau kernel Assumptions.all L g) u t' →
      Stops kernel Assumptions.all L g t' → Holds t'.regs F) ∨
      Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) u := by
  by_cases hD : Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) u
  · exact .inr hD
  refine .inl fun t' hr hs => ?_
  rcases hstops with hst | hd
  · rcases rtg_table (g := g) Lib.rulesFrame hscan hS hspec hu hT hr with
      ⟨-, -, -, hh⟩ | hd
    · rw [hst t' hr hs] at hh
      exact hconv _ hh
    · exact absurd hd hD
  · exact absurd hd hD

/-- The round's data facts are the table's before the update. -/
theorem dFS_phi {s : Site} (hs : inRound s = true) (v : Vals) {pc : Nat} (hpc : updPost pc = false)
    {R : Nat → Option Value} (h : Holds R (dFS L s v)) :
    Holds R (phi updKeys updPost (updV1 L v.m v.mx) (updV2 L v.m v.mx) pc) := by
  replace h : Holds R ([(498, scaleW L), (1914, v.m)] ++ alphaFacts L v) :=
    holds_of_mem fun r x hm => holds_mem h (round_sub hs v _ hm)
  refine holds_of_pointwise fun r hr => ?_
  simp only [updKeys, hpc, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  simp only [hpc, Bool.false_eq_true, ↓reduceIte, updV1]
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [alphaVal_c]; exact holds_mem h (by simp)
  · rw [alphaVal_m]; exact holds_mem h (by simp)
  · rw [alphaVal_mx]; exact holds_mem h (by simp [alphaFacts])
  · exact holds_mem h (by simp [alphaFacts])
  · exact holds_mem h (by simp [alphaFacts])

/-- The state after an event that keeps the registers of the table. -/
theorem tab_of {t u : TState} {s : Site} (hs : inRound s = true) (v : Vals)
    (hreg : Holds t.regs (dFS L s v)) (hsub : u.sub = 0) (hacc : u.acc = []) {pc : Nat}
    (hpc : u.pc = pc) (hpost : updPost pc = false)
    (hkept : ∀ r ∈ [498, 1914, 1522, 168, 507], u.regs r = t.regs r) :
    TabAt updKeys updPost (updV1 L v.m v.mx) (updV2 L v.m v.mx) u := by
  refine ⟨hsub, hacc, ?_⟩
  rw [hpc]
  have h2 := dFS_phi hs v hpost hreg
  refine holds_of_mem fun r y hm => ?_
  obtain ⟨r', hr', he⟩ := List.mem_map.mp hm
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, -⟩ := he
  simp only [updKeys, hpost, Bool.false_eq_true, ↓reduceIte] at hr'
  rw [hkept r' hr']
  exact holds_mem h2 hm

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
