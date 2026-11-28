-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsJump
public import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsScan
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Cross
public import Kernels.InklingRelDecode.Proof.Softmax.Data.TabGoal
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The bias words at the first stop

The table's facts hold at the first stop after a state of the path, or the thread is dead
(`words_goal`), and the facts of the stop's site follow from them (`conv_nxt0`, `conv_waitS`,
`conv_arrive`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

set_option maxRecDepth 100000
noncomputable section
variable {L : Launch} {g : Nat}

theorem wtab_emu (k : WK) :
    ((pcsOf (wIvs k)).all fun pc => !Assumptions.emuSites.contains pc) = true := by
  cases k <;> decide +kernel

/-- The table's facts hold at the first stop, or the thread is dead. -/
theorem words_goal {k : WK} {ws : Nat → Value}
    (hws : ∀ pc, 679 ≤ pc → pc < 807 → inIvs (wIvs k) pc = true → ∀ i, ws i = dflt)
    {u : TState} {q : Nat} {F : List (Nat × Value)}
    (hu : TabGood kernel (wIvs k) (wKeys k) wPost (wV1 ws) (wV2 ws) u)
    (hstops : (∀ t'', Relation.ReflTransGen (Tau kernel Assumptions.all L g) u t'' →
      Stops kernel Assumptions.all L g t'' → t''.pc = q) ∨
      Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) u)
    (hconv : ∀ R, Holds R (phi (wKeys k) wPost (wV1 ws) (wV2 ws) q) → Holds R F) :
    (∀ t', Relation.ReflTransGen (Tau kernel Assumptions.all L g) u t' →
      Stops kernel Assumptions.all L g t' → Holds t'.regs F) ∨
      Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) u := by
  exact goal_tabJ (wtab_scan k) (hseg_ivs (wtab_emu k)) (w_jump k ws hws) hu hstops hconv

theorem wk_pack (k : WK) {q : Nat} (hq : q = 1124 ∨ q = 1257) :
    ∀ m, m < 32 → 1916 + m ∈ wKeys k q := by
  rcases hq with rfl | rfl <;> cases k <;> decide +kernel

theorem wk_nxt (k : WK) : ∀ i, i < 64 → nxtReg i ∈ wKeys k 1257 := by
  cases k <;> decide +kernel

theorem wk_arr : ∀ i, i < 64 → nxtReg i ∈ wKeys .b 1013 := by decide +kernel

theorem phi_mem {keys : Nat → List Nat} {post : Nat → Bool} {V1 V2 : Nat → Value} {pc r : Nat}
    (h : r ∈ keys pc) : (r, (if post pc then V2 else V1) r) ∈ phi keys post V1 V2 pc :=
  mem_factsFrom h

/-- The packs of the table's words are among its facts at a loop's first sites. -/
theorem conv_packs {k : WK} {ws : Nat → Value} {R : Nat → Option Value} {q : Nat}
    (hq : q = 1124 ∨ q = 1257) (h : Holds R (phi (wKeys k) wPost (wV1 ws) (wV2 ws) q)) :
    Holds R (packF ws) := by
  refine holds_of_mem fun r x hm => ?_
  obtain ⟨m, hm', he⟩ := List.mem_map.mp hm
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hm32 := List.mem_range.mp hm'
  have hp : wPost q = true := by rcases hq with rfl | rfl <;> decide
  have := holds_mem h (phi_mem (post := wPost) (V1 := wV1 ws) (V2 := wV2 ws)
    (wk_pack k hq m hm32))
  simp only [hp, ↓reduceIte] at this
  rwa [wV2_of ws (by omega), wV1_pack ws hm32] at this

theorem conv_nxt0 {k : WK} {ws : Nat → Value} {R : Nat → Option Value} {v' : Vals}
    (hc : v'.cur = ws) (h : Holds R (phi (wKeys k) wPost (wV1 ws) (wV2 ws) (Site.nxt 0).pc)) :
    Holds R (wFS (.nxt 0) v') := by
  have : wFS (.nxt 0) v' = packF v'.cur := rfl
  rw [this, hc]
  exact conv_packs (Or.inl rfl) h

theorem conv_waitS {k : WK} {ws : Nat → Value} {R : Nat → Option Value} {v' : Vals}
    (hc : v'.cur = ws) (hl : v'.ld = fun _ => dflt)
    (h : Holds R (phi (wKeys k) wPost (wV1 ws) (wV2 ws) Site.waitS.pc)) :
    Holds R (wFS .waitS v') := by
  have e : wFS .waitS v' = packF v'.cur ++ wordF nxtReg v'.ld 64 := rfl
  rw [e, hc, hl]
  refine (holds_append _ _ _).mpr ⟨conv_packs (Or.inr rfl) h, ?_⟩
  refine holds_of_mem fun r x hm => ?_
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hm
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hi' := List.mem_range.mp hi
  have := holds_mem h (phi_mem (post := wPost) (V1 := wV1 ws) (V2 := wV2 ws) (wk_nxt k i hi'))
  simp only [show wPost Site.waitS.pc = true by decide, ↓reduceIte, wV2_nxt ws hi'] at this
  exact this

theorem conv_arrive {ws : Nat → Value} {R : Nat → Option Value} {v' : Vals} (hl : v'.ld = ws)
    (h : Holds R (phi (wKeys .b) wPost (wV1 ws) (wV2 ws) (Site.arrive).pc)) :
    Holds R (wFS .arrive v') := by
  have e : wFS .arrive v' = wordF nxtReg v'.ld 64 := rfl
  rw [e, hl]
  refine holds_of_mem fun r x hm => ?_
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hm
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hi' := List.mem_range.mp hi
  have := holds_mem h (phi_mem (post := wPost) (V1 := wV1 ws) (V2 := wV2 ws) (wk_arr i hi'))
  simp only [show wPost Site.arrive.pc = false by decide, Bool.false_eq_true, ↓reduceIte,
    wV1_nxt ws hi'] at this
  exact this

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
