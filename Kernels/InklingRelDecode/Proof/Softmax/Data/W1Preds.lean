-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.MaskConst

@[expose] public section

/-! # The predicates and the bit words the first window's exact path needs

The two predicates of the lane's half (registers 1 and 2) are predicates for every thread of the
CTA (they read the thread index only), and the entry's register 484 is a 32-bit word. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

def isPredB : Value → Bool
  | .pred _ => true
  | _ => false

theorem pred_ctl : ∀ t < 256, isPredB (Gen.en_v591 (fun r => if r = 462 then b32 t else b32 0)) =
    true ∧ isPredB (Gen.en_v592 (fun r => if r = 462 then b32 t else b32 0)) = true := by
  decide +kernel

theorem isPredB_pred {v : Value} (h : isPredB v = true) : ∃ q, v = .pred q := by
  cases v <;> simp [isPredB] at h
  exact ⟨_, rfl⟩

theorem derV_12 (ht : g % L.block < 256) :
    (∃ q, derV e L g 1 = .pred q) ∧ ∃ q, derV e L g 2 = .pred q := by
  have h1 : derV e L g 1 = Gen.en_v591 (lookupD (G0 e L g)) := by
    simp [derV, G6, G5, G4, G3, G2, G1, lookupD, Gen.io_facts3, Gen.ie_facts1, Gen.ng_facts1,
      Gen.e8_facts1, Gen.dv_facts1, Gen.en_facts1, List.lookup]
  have h2 : derV e L g 2 = Gen.en_v592 (lookupD (G0 e L g)) := by
    simp [derV, G6, G5, G4, G3, G2, G1, lookupD, Gen.io_facts3, Gen.ie_facts1, Gen.ng_facts1,
      Gen.e8_facts1, Gen.dv_facts1, Gen.en_facts1, List.lookup]
  have h462 : lookupD (G0 e L g) 462 = b32 (g % L.block) := by simp [G0, lookupD]
  have c1 : Gen.en_v591 (lookupD (G0 e L g)) =
      Gen.en_v591 (fun r => if r = 462 then b32 (g % L.block) else b32 0) := by
    simp only [Gen.en_v591, Gen.en_v590, Gen.en_v589, h462, ↓reduceIte]
  have c2 : Gen.en_v592 (lookupD (G0 e L g)) =
      Gen.en_v592 (fun r => if r = 462 then b32 (g % L.block) else b32 0) := by
    simp only [Gen.en_v592, Gen.en_v588, Gen.en_v587, h462, ↓reduceIte]
  obtain ⟨p1, p2⟩ := pred_ctl _ ht
  rw [h1, h2, c1, c2]
  exact ⟨isPredB_pred p1, isPredB_pred p2⟩

theorem w1V_12 {d : D} (hs : d.c.site = .waitLd) :
    w1V e L g d 1 = derV e L g 1 ∧ w1V e L g d 2 = derV e L g 2 := by
  have go : ∀ r, r ∈ kW1 → r ∈ keysC → r ∉ ctlLive Site.waitLd.pc →
      r ≠ 498 → r ≠ 1914 → r ≠ 482 → r ≠ 484 → r ≠ 483 → r ≠ 199 →
      w1V e L g d r = derV e L g r := by
    intro r hr h' h hr1 hr2 hr3 hr4 hr5 hr6
    rw [w1V_eq hs hr]
    unfold lookupD baseF
    simp only [lookup_append_eq, Control.facts, hs, lookup_factsFrom]
    simp [dF, dFS, startF, pF, wF, wFS, hs, inRound, derF, lookup_factsFrom, h, h']
    simp only [List.lookup, beq_false_of_ne hr1, beq_false_of_ne hr2, beq_false_of_ne hr3,
      beq_false_of_ne hr4, beq_false_of_ne hr5, beq_false_of_ne hr6, Option.getD_none]
  exact ⟨go 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide),
    go 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)⟩

theorem w1V_484 {d : D} (hs : d.c.site = .waitLd) :
    ∃ w x, w1V e L g d 484 = .bits w x := by
  rw [w1V_eq hs (by decide +kernel)]
  unfold lookupD baseF
  simp only [lookup_append_eq, Control.facts, hs, lookup_factsFrom]
  have h : 484 ∉ ctlLive Site.waitLd.pc := by decide +kernel
  simp [dF, dFS, startF, hs, inRound, h, List.lookup]
end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
