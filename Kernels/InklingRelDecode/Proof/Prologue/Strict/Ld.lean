-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Stable
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Step

@[expose] public section

/-! # The strict steps of the three request loads -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

/-- The register the load writes is a control register: the invariant tags nothing at `n`. -/
theorem ld_hv {n r : Nat} (h : (proQt n).lookup r = none) {P : Value → Prop} :
    ∀ v, P v → ∀ tg, (proQt n).lookup r = some tg → tg.ok (some v) := fun _ _ tg h' => by
  rw [h] at h'; cases h'

/-- The tags at `n + 1` are those of `n`. -/
theorem ld_hq {n r : Nat} (h : ∀ p ∈ proQt (n + 1), p.1 ≠ r →
    (proQt n).lookup p.1 = some p.2 ∨ ([] : Env).lookup p.1 = some p.2) :
    ∀ p ∈ proQt (n + 1), p.1 ≠ r →
      (proQt n).lookup p.1 = some p.2 ∨ ([] : Env).lookup p.1 = some p.2 := h

/-- The successor of a request load: the rebuilt word goes into the state. -/
macro "ld_hn" : tactic => `(tactic| (intro x bs v h hP; subst hP; simp [Data.code, Data.succ,
  Control.next, Data.record, h, Except.toOption]))

/-- No fact of the state names the register the load writes. -/
macro "ld_fr" pc:num r:num s:term : tactic => `(tactic| exact fresh_reg
  (by change $r ∉ ctlLive $pc; decide +kernel)
  (by change $r ∉ (Data.tags $s).map Data.Tag.reg; decide +kernel))

theorem ld0_span (x : BitVec 64) (won : Bool) (bcast : Value) (v : Data.Vals) :
    let d : Data.D := ⟨⟨.ld 0, .bits 32 x, b32 0, b32 0, won, bcast⟩, v⟩
    let dn : Data.D := ⟨⟨.ld 1, .bits 32 x, b32 0, b32 0, won, bcast⟩, v⟩
    SegQ kernel Assumptions.all L g (QT proQt) 35 ([(610, .bits 32 x)] ++ dFacts Q L g w d) 37
      (dFacts Q L g w dn) := by
  intro d dn
  simp only [d, dn]
  pro_facts
  segq_ctlv proQt, (plainRules_pro (a := 27) (b := 574) le_rfl),
    (plainSegs_pro (a := 27) (b := 574) le_rfl), Lib.rulesFrame using pro_vals

theorem step_ld0 (d : Data.D) (hs : d.c.site = .ld 0) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a, b, c, won, bcast⟩, vs⟩ := d
  cases hs
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨⟨rfl, rfl, rfl⟩, hpay⟩ := hinv
  refine Code.ldWQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
    (P := fun v => v = b32 (requestWord Q (reqOf L g) 0)) (r := 610)
    (d := ⟨⟨.ld 0, b32 0, b32 0, b32 0, won, bcast⟩, vs⟩)
    (f := fun v => ⟨⟨.ld 1, v, b32 0, b32 0, won, bcast⟩, vs⟩) Flow.code_34 rfl rfl rfl rfl
    ?_ ?_ rfl rfl ?_ (fun _ _ => typed_nil') ?_ ?_ ?_ e ins hat ⟨⟨rfl, rfl, rfl⟩, hpay⟩ hc hq hw hf
  · exact fun e hWf hpc x bs hk => ⟨_, hWf.1 0 hpc x bs hk, rfl⟩
  · ld_hn
  · ld_fr 34 610 (.ld 0)
  · exact ld_hv (n := 35) (r := 610) (by decide +kernel)
  · exact ld_hq (n := 34) (r := 610) (by decide +kernel)
  · intro v hv
    subst hv
    refine ⟨rfl, rfl, ⟨⟨rfl, rfl⟩, ⟨fun h => absurd h (by change ¬41 ≤ 37; decide),
        fun h => absurd h (by change ¬130 ≤ 37; decide)⟩⟩, ?_⟩
    rw [code_facts_ld0 (w := w) _ rfl vs (.bits 32 (BitVec.ofNat 64 (requestWord Q (reqOf L g) 0)))]
    exact dFacts_seg (pre := [(610, _)]) (ld0_span _ won bcast vs)

theorem ld1_span (a y : BitVec 64) (won : Bool) (bcast : Value) (v : Data.Vals) :
    let d : Data.D := ⟨⟨.ld 1, .bits 32 a, .bits 32 y, b32 0, won, bcast⟩, v⟩
    let dn : Data.D := ⟨⟨.ld 2, .bits 32 a, .bits 32 y, b32 0, won, bcast⟩, v⟩
    SegQ kernel Assumptions.all L g (QT proQt) 38 ([(611, .bits 32 y)] ++ dFacts Q L g w d) 41
      (dFacts Q L g w dn) := by
  intro d dn
  simp only [d, dn]
  pro_facts
  segq_ctlv proQt, (plainRules_pro (a := 27) (b := 574) le_rfl),
    (plainSegs_pro (a := 27) (b := 574) le_rfl), Lib.rulesFrame using pro_vals

theorem step_ld1 (d : Data.D) (hs : d.c.site = .ld 1) (hk : Ok Q L g d) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a, b, c, won, bcast⟩, vs⟩ := d
  cases hs
  have ha : a = b32 (Q.qStart (reqOf L g)) := hk.1.first (by change 34 < 37; decide)
  subst ha
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨⟨rfl, rfl⟩, hpay⟩ := hinv
  refine Code.ldWQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
    (P := fun v => v = b32 (requestWord Q (reqOf L g) 1)) (r := 611)
    (d := ⟨⟨.ld 1, b32 (Q.qStart (reqOf L g)), b32 0, b32 0, won, bcast⟩, vs⟩)
    (f := fun v => ⟨⟨.ld 2, b32 (Q.qStart (reqOf L g)), v, b32 0, won, bcast⟩, vs⟩)
    Flow.code_37 rfl rfl rfl rfl ?_ ?_ rfl rfl ?_ (fun _ _ => typed_nil') ?_ ?_ ?_ e ins hat
    ⟨⟨rfl, rfl⟩, hpay⟩ hc hq hw hf
  · exact fun e hWf hpc x bs hk => ⟨_, hWf.1 1 hpc x bs hk, rfl⟩
  · ld_hn
  · ld_fr 37 611 (.ld 1)
  · exact ld_hv (n := 38) (r := 611) (by decide +kernel)
  · exact ld_hq (n := 37) (r := 611) (by decide +kernel)
  · intro v hv
    subst hv
    refine ⟨rfl, rfl, ⟨rfl, ⟨fun _ => rfl, fun h => absurd h (by change ¬130 ≤ 41; decide)⟩⟩, ?_⟩
    rw [code_facts_ld1 (w := w) _ rfl vs (.bits 32 (BitVec.ofNat 64 (requestWord Q (reqOf L g) 1)))]
    exact dFacts_seg (pre := [(611, _)]) (ld1_span _ _ won bcast vs)

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
