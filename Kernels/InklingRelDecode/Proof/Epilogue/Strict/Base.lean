-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Control.Machine
public import Kernels.InklingRelDecode.Proof.Lib.FloatPlain3
public import Kernels.InklingRelDecode.Proof.Lib.RulesFrame
public import Kernels.InklingRelDecode.Gen.TypedLateQt
public import Lemmas.Flow.SegQFLane
public import Lemmas.Flow.SegQFSkip

@[expose] public section

/-! # The strict steps of the epilogue's control machine: the shared parts

The lane's invariant is `QTF lateQt` and its fact about a state after an event `TauAll R` for a
predicate `R` of the lane (the assembly takes the one of the data lanes). A span between two sites
is a chain of lane windows, branches and exact pieces of the control registers. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

/-- The pcs `[a, b)` are the epilogue's pcs away from the three single-instruction readings. -/
def epiOk (a b : Nat) : Bool :=
  (List.range' a (b - a)).all fun pc =>
    2563 ≤ pc && pc < 2853 && !Assumptions.emuSites.contains pc

theorem fp3_epi {L : Launch} {g a b : Nat} (h : epiOk a b = true) :
    FloatPlain3 Assumptions.all L g a b := by
  refine Lib.floatPlain3 fun pc h1 h2 => ?_
  have := (List.all_eq_true.mp h) pc (List.mem_range'_1.mpr ⟨h1, by omega⟩)
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
  obtain ⟨⟨h3, h4⟩, h5⟩ := this
  exact ⟨h5, by omega, by omega, by omega⟩

set_option hygiene false in
/-- The closing tactic of the exact pieces of a stretch of the epilogue. -/
macro "epi_ctl " a:num ", " b:num " using " vals:tacticSeq : tactic => `(tactic|
  lane_ctl lateQt, (fp3_epi (L := L) (g := g) (a := $a) (b := $b) (by decide +kernel)),
    Lib.rulesFrame using $vals)


section
open Control

variable {e : Entry} {L : Launch} {g : Nat} {R : TState → Prop} {Wf : Event → Prop}

/-- The facts of a pc are among those of an earlier one that holds all their registers. -/
theorem fsub {v : Value} {p q : Nat} (h : ∀ r ∈ ctlLive q, r ∈ ctlLive p) :
    ∀ a ∈ facts e L g v q, a ∈ facts e L g v p := by
  intro a ha
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
  exact mem_factsFrom (h r hr)

/-- The segment between two consecutive pcs keeps the facts of the registers that go on. -/
theorem seg_step {s' : Site} {v : Value} {p : Nat} {Q : TState → Prop}
    (hp' : s'.pc = p + 1) (hs : ∀ r ∈ ctlLive (p + 1), r ∈ ctlLive p) :
    SegQ kernel Assumptions.all L g Q (p + 1) (facts e L g v p) s'.pc (facts e L g v s'.pc) := by
  rw [hp']
  exact SegQ.weaken fun _ hR => holds_of_forall fun a ha =>
    holds_mem hR (fsub (v := v) (p := p) hs a ha)

/-- **A site whose event continues** by the segment `hseg` of the lane. -/
theorem adv_gen {s s' : Site} {v : Value} {p : Nat} {gd : Option (Nat × Bool)} {op : Op}
    (hp : s.pc = p) (hc : kernel.code[p]? = some ⟨gd, op⟩)
    (ha : ∀ {t u ev}, Fires p (eventTmpl Assumptions.all L g t op) ev (some u) → u = PTX.next t)
    (hn : ∀ ev, Control.next e L g ⟨s, v⟩ ev = some (some ⟨s', v⟩))
    (hi : Inv e (g % L.block) ⟨s, v⟩ → Inv e (g % L.block) ⟨s', v⟩)
    (hq : afterF lateQt p [] = true)
    (hseg : SegQ kernel Assumptions.all L g
      (fun t => QTF lateQt t ∧ TauAll kernel Assumptions.all L g R t) (p + 1) (facts e L g v p)
      s'.pc (facts e L g v s'.pc)) (ev : Event) :
    (code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g R) Wf ⟨s, v⟩ ev := by
  subst hp
  exact Code.StepForQP.ofInv fun hinv => Code.advanceFP (C := code e L g) hc ha hn rfl rfl rfl rfl
    (hi hinv) hq hseg ev

/-- **A site whose event continues at the next pc** with the facts of its registers. -/
theorem adv_site {s s' : Site} {v : Value} {p : Nat} {gd : Option (Nat × Bool)} {op : Op}
    (hp : s.pc = p) (hp' : s'.pc = p + 1) (hc : kernel.code[p]? = some ⟨gd, op⟩)
    (ha : ∀ {t u ev}, Fires p (eventTmpl Assumptions.all L g t op) ev (some u) → u = PTX.next t)
    (hn : ∀ ev, Control.next e L g ⟨s, v⟩ ev = some (some ⟨s', v⟩))
    (hi : Inv e (g % L.block) ⟨s, v⟩ → Inv e (g % L.block) ⟨s', v⟩)
    (hq : afterF lateQt p [] = true) (hs : ∀ r ∈ ctlLive (p + 1), r ∈ ctlLive p) (ev : Event) :
    (code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g R) Wf ⟨s, v⟩ ev := by
  exact adv_gen hp hc ha hn hi hq (seg_step hp' hs) ev

end

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
