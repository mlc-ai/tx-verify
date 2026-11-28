-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsGoal
public import Kernels.InklingRelDecode.Proof.Softmax.Data.DerivedSite
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The bias words after the barrier of the entry, the last preload and the loop's barriers

The four events that are followed by the moves of the bias words (`WordsTab`): the barrier of
pc 575 and the last preload (pc 806) by the preloads' defaults and packs, the barrier of pc 1012
and the arrival of pc 1013 by the packs of the loop's words. The first stop after them is a
preload, a loop site or the epilogue. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The facts of a loop site that follows the moves hold at its position of the table. -/
theorem conv_loop {k : WK} {ws : Nat → Value} {z : Site} {v' : Vals}
    (hz : z = .nxt 0 ∨ z = .waitS ∨ z = .epilogue) (hc : v'.cur = ws)
    (hl : v'.ld = fun _ => dflt) {R : Nat → Option Value}
    (h : Holds R (phi (wKeys k) wPost (wV1 ws) (wV2 ws) z.pc)) : Holds R (wFS z v') := by
  rcases hz with rfl | rfl | rfl
  · exact conv_nxt0 hc h
  · exact conv_waitS hc hl h
  · exact trivial

theorem w_bar0_conv {d : D} (hs : d.c.site = .bar0) (ev : Event) (S : Site)
    (hS : S = .pre 0 ∨ S = .nxt 0 ∨ S = .waitS ∨ S = .epilogue) {R : Nat → Option Value}
    (h : Holds R (phi (wKeys .a) wPost (wV1 fun _ => dflt) (wV2 fun _ => dflt) S.pc)) :
    Holds R (wF ⟨{d.c with site := S}, record L d ev S⟩) := by
  rcases hS with rfl | rfl | rfl | rfl
  · exact trivial
  all_goals
    refine conv_loop (k := .a) (by simp) ?_ ?_ h <;> simp [record, hs, loopB, dflt]

/-- **The bias words after the barrier of the entry.** -/
theorem w_bar0 {d : D} (hs : d.c.site = .bar0) : DataStep (codeS e L g) wF d := by
  refine @bar0_open e L g d hs _ fun t ev hat hpc hstops => ?_
  have h199 := (atS_const hat).1
  refine words_goal (k := .a) (ws := fun _ => dflt) (fun _ _ _ _ _ => rfl)
    (q := (afterBar0 e L g d).site.pc) ⟨?_, hat.2.1.trans rfl, hat.2.2.1.trans rfl, ?_⟩
    hstops (fun R h => ?_)
  · rw [hpc]; decide +kernel
  · rw [hpc]
    have hk : wKeys .a 576 = [199] := by decide +kernel
    have h : t.regs 199 = some dflt := holds_mem h199 (by simp [startF, dflt])
    show Holds t.regs _
    refine holds_of_pointwise fun r hr => ?_
    rw [hk] at hr
    obtain rfl := List.mem_singleton.mp hr
    simpa [wPost, wV1] using h
  · refine w_bar0_conv hs ev _ ?_ h
    by_cases hp : preEnabled e (g % L.block) = true
    · simp [hp]
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      rcases loopSite_mem e (g % L.block) d.c.i with h | h | h <;> simp [h]

/-- **The bias words after the last preload.** -/
theorem w_pre63 {d : D} (hs : d.c.site = .pre 63) : DataStep (codeS e L g) wF d := by
  refine @pre63_open e L g d hs _ fun t x bs v c' hat hv hc hpc => ?_
  subst hc
  intro hstops
  have hw := atS_wFat hat
  have h199 := (atS_const hat).1
  have hl : Lib.loadWord bs = v := by
    unfold Lib.loadWord
    rw [hv]
    rfl
  refine words_goal (k := .p) (ws := Function.update d.v.ld 63 v)
    (fun pc h1 h2 h3 => absurd h3 (by simp [inIvs, wIvs]; omega))
    (q := (loopSite e (g % L.block) d.c.i).pc) ⟨?_, rfl, rfl, ?_⟩ hstops (fun R h => ?_)
  · show (inIvs (wIvs .p) (t.pc + 1) || evAtB kernel (t.pc + 1)) = true
    rw [hpc]; decide +kernel
  · show Holds _ (phi (wKeys .p) wPost _ _ (t.pc + 1))
    rw [hpc]
    refine holds_of_pointwise fun r hr => ?_
    have hk : wKeys .p 807 = 199 :: (List.range 64).map preReg := by decide +kernel
    rw [hk] at hr
    have hacc : t.acc = [] := hat.2.2.1
    simp only [show wPost 807 = false by decide, Bool.false_eq_true, ↓reduceIte]
    rcases List.mem_cons.mp hr with rfl | hr
    · show (setRegs t [326] (t.acc ++ [v])).regs 199 = _
      rw [EventFrame.setRegs_regs_of_not_mem (by simp)]
      simpa [wV1] using holds_mem h199 (v := dflt) (by simp [startF, dflt])
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
      have hi' := List.mem_range.mp hi
      show (setRegs t [326] (t.acc ++ [v])).regs (263 + i) = some (wV1 _ (263 + i))
      rw [wV1_pre _ (by omega)]
      by_cases h63 : i = 63
      · subst h63
        simp [setRegs, setReg, hacc]
      · rw [EventFrame.setRegs_regs_of_not_mem (by simp; omega), Function.update_of_ne h63]
        refine holds_mem hw (v := d.v.ld i) ?_
        simp only [wF, hs, wFS, wordF, List.mem_map, List.mem_range]
        exact ⟨i, by omega, rfl⟩
  · have hm := loopSite_mem e (g % L.block) d.c.i
    have hb : loopB (loopSite e (g % L.block) d.c.i) := by
      rcases hm with h | h | h <;> simp [h, loopB]
    refine conv_loop hm ?_ ?_ h
    · simp [record, hs, hb, hl]
    · simp [record, hs, hb]

theorem w_b_conv {d : D} {ev : Event} {c' : Control.D}
    (hd : d.c.site = .bar21 ∨ d.c.site = .arrive)
    (hS : (c'.site = .arrive ∧ d.c.site = .bar21) ∨ c'.site = .nxt 0 ∨ c'.site = .waitS ∨
      c'.site = .epilogue) {R : Nat → Option Value}
    (h : Holds R (phi (wKeys .b) wPost (wV1 d.v.ld) (wV2 d.v.ld) c'.site.pc)) :
    Holds R (wF ⟨c', record L d ev c'.site⟩) := by
  rcases hS with ⟨h1, h2⟩ | h1 | h1 | h1
  · simp only [wF, h1]
    refine conv_arrive ?_ (by rwa [h1] at h)
    simp [record, h2]
  all_goals
    simp only [wF, h1] at h ⊢
    refine conv_loop (k := .b) (by simp) ?_ ?_ h <;> rcases hd with hd | hd <;>
      simp [record, hd]

theorem w_b_after {d d' : D} {t : TState}
    (hw : Holds t.regs (wordF nxtReg d.v.ld 64)) (hsub : t.sub = 0) (hacc : t.acc = [])
    (hpc : (PTX.next t).pc = 1013 ∨ (PTX.next t).pc = 1014)
    (hstops : (∀ t'', Relation.ReflTransGen (Tau kernel Assumptions.all L g) (PTX.next t) t'' →
      Stops kernel Assumptions.all L g t'' → t''.pc = d'.c.site.pc) ∨
      Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) (PTX.next t))
    (hconv : ∀ R, Holds R (phi (wKeys .b) wPost (wV1 d.v.ld) (wV2 d.v.ld) d'.c.site.pc) →
      Holds R (wF d')) :
    (∀ t', Relation.ReflTransGen (Tau kernel Assumptions.all L g) (PTX.next t) t' →
      Stops kernel Assumptions.all L g t' → Holds t'.regs (wF d')) ∨
      Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) (PTX.next t) := by
  refine words_goal (k := .b) (ws := d.v.ld)
    (fun pc h1 h2 h3 => absurd h3 (by simp [inIvs, wIvs]; omega)) ⟨?_, hsub, hacc, ?_⟩ hstops
    hconv
  · rcases hpc with h | h <;> rw [h] <;> decide +kernel
  · show Holds t.regs _
    have hk : wKeys .b (PTX.next t).pc = nwK := by
      rcases hpc with h | h <;> rw [h] <;> decide +kernel
    have hp : wPost (PTX.next t).pc = false := by rcases hpc with h | h <;> rw [h] <;> decide
    refine holds_of_pointwise fun r hr => ?_
    rw [hk] at hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    have hi' := List.mem_range.mp hi
    simp only [hp, Bool.false_eq_true, ↓reduceIte, wV1_nxt _ hi']
    refine holds_mem hw (v := d.v.ld i) ?_
    simp only [wordF, List.mem_map, List.mem_range]
    exact ⟨i, hi', rfl⟩

/-- **The packs of the loop's words after the barrier of pc 1012.** -/
theorem w_bar21 {d : D} (hs : d.c.site = .bar21) : DataStep (codeS e L g) wF d := by
  have pc : (codeS e L g).pc d = 1012 := by
    change d.c.site.pc = 1012
    rw [hs]
    rfl
  have pc0 : (code e L g).pc d = 1012 := pc
  intro t ev u d' ins hat hi hc' hf hn
  have hat0 := atS_code hat
  have hn' : (code e L g).next d ev = some (some d') := hn
  rw [pc] at hc' hf
  rw [Flow.code_bar_21] at hc'
  obtain rfl := Option.some.inj hc'
  obtain rfl := fires_barSyncN_next hf
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn'
  have hpc : (PTX.next t).pc = 1013 := by
    have h1 := hat.1
    simp only [PTX.next]
    omega
  have hw : Holds t.regs (wordF nxtReg d.v.ld 64) := by
    have h := atS_wFat hat
    simp only [wF, hs] at h
    exact h
  refine w_b_after hw (hat.2.1.trans rfl) (hat.2.2.1.trans rfl) (Or.inl hpc)
    (stops_pc hat0 hi (by rw [pc0]; exact Flow.code_bar_21) (by rw [pc0]; exact hf) hn')
    (fun R h => w_b_conv (Or.inl hs) ?_ h)
  by_cases h128 : g % L.block % 128 = 0
  · simp [Control.next, hs, h128] at hnc
    subst hnc
    exact .inl ⟨rfl, hs⟩
  · simp only [Control.next, hs, h128, ↓reduceIte, Option.some.injEq] at hnc
    subst hnc
    exact .inr (loopSite_mem e (g % L.block) (d.c.i + 1))

/-- **The packs of the loop's words after the arrival of pc 1013.** -/
theorem w_arrive {d : D} (hs : d.c.site = .arrive) : DataStep (codeS e L g) wF d := by
  have pc : (codeS e L g).pc d = 1013 := by
    change d.c.site.pc = 1013
    rw [hs]
    rfl
  have pc0 : (code e L g).pc d = 1013 := pc
  intro t ev u d' ins hat hi hc' hf hn
  have hat0 := atS_code hat
  have hn' : (code e L g).next d ev = some (some d') := hn
  rw [pc] at hc' hf
  rw [Flow.code_mbarArrive_3] at hc'
  obtain rfl := Option.some.inj hc'
  have hu : u = PTX.next t := fires_arrive_next hf
  subst hu
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn'
  have hpc : (PTX.next t).pc = 1014 := by
    have h1 := hat.1
    simp only [PTX.next]
    omega
  have hw : Holds t.regs (wordF nxtReg d.v.ld 64) := by
    have h := atS_wFat hat
    simp only [wF, hs] at h
    exact h
  refine w_b_after hw (hat.2.1.trans rfl) (hat.2.2.1.trans rfl) (Or.inr hpc)
    (stops_pc hat0 hi (by rw [pc0]; exact Flow.code_mbarArrive_3) (by rw [pc0]; exact hf) hn')
    (fun R h => w_b_conv (Or.inr hs) ?_ h)
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  exact .inr (loopSite_mem e (g % L.block) (d.c.i + 1))

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
