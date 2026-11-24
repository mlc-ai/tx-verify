-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0
import Lemmas.Flow.SegChain

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
-- A segment's generated value tactic may have no goals when all fields reduce by evaluation.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}

theorem last_block_compare {b n : Nat} (hb : b < n) (hn : n < 2 ^ 31) :
    compare .eq .b 32 (truncBits 32 (BitVec.ofNat 64 ((b + 1 + (2 ^ 32 - n)) % 2 ^ 32)))
      (truncBits 32 (BitVec.ofInt 64 0)) = decide (b + 1 = n) := by
  norm_signed

theorem phase2_succ (b : Nat) : (((b + 1) / 2) % 2 = 1) ↔ (b / 2 % 2 ≠ b % 2) := by
  have h : (b + 1) / 2 = b / 2 + b % 2 := by omega
  rw [h, Nat.add_mod]
  omega

theorem phase4_succ (b : Nat) :
    (((b + 1) / 4) % 2 = 1) ↔ (b / 4 % 2 ≠ (if b % 4 = 3 then 1 else 0)) := by
  split <;> omega


/-- The loop's zero test selects its epilogue exactly on the last block. -/
theorem run_1123_1124 (hpre : Pre P L mem0) (hbatch : eOf L g < P.b) (d : D)
    (hblock : d.block < blocksOf P L g) {t : TState}
    (h : At t 1123 (factsFrom ((Flow.live 1122).filter (fun r => tracked.contains r))
      (valueOf P L g d))) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u 1124
      ((113, .pred (decide (d.block + 1 = blocksOf P L g))) ::
        factsFrom ((Flow.live 1122).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
  have hlim : blocksOf P L g < 2 ^ 31 := by
    have hh := (blocksOf_word_bounds hpre hbatch).2
    omega
  seg_fp h using
    (simp only [Value.pred.injEq])
    (exact last_block_compare hblock hlim)

/-- The branch skips the ring updates on the final block. -/
theorem branch_after_block (d : D) (last : Bool) {t : TState}
    (h : At t 1124 ((113, .pred last) ::
      factsFrom ((Flow.live 1122).filter (fun r => tracked.contains r)) (valueOf P L g d))) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u (if last then 1143 else 1125)
      ((113, .pred last) ::
        factsFrom ((Flow.live 1122).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
  exact run_bra Flow.code_1124 last h h.2.2.2.2.1
    (Thread.asms_localRule_bra (by rw [h.1]; decide) (by rw [h.1]; decide))

/-- The two-slot generation advances when the previous slot was odd. -/
theorem run_1125_1130 (d : D) {t : TState}
    (h : At t 1125 (factsFrom ((Flow.live 1122).filter (fun r => tracked.contains r))
      (valueOf P L g d))) :
    ∃ u, run kernel asms L g 5 t = some u ∧ At u 1130
      ((1718, .bits 32 (truncBits 32 (~~~(truncBits 32 (BitVec.ofNat 64 (d.block % 2)))))) ::
        (114, .pred (decide ((d.block + 1) / 2 % 2 = 1))) ::
        factsFrom ((Flow.live 1130).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
  seg_fp h using
    (first | rfl | norm_signed [land255, phase2_succ])

private def nextBlock (d : D) : D :=
  { d with block := d.block + 1, site := .wg0Sync, sub := 0 }

private def loopValues (P : Params) (L : Launch) (g : Nat) (d : D)
    (advanced : List Nat) (r : Nat) : Value :=
  if advanced.contains r then valueOf P L g (nextBlock d) r else valueOf P L g d r

private def loopFacts (P : Params) (L : Launch) (g : Nat) (d : D)
    (advanced : List Nat) (pc : Nat) : List (Nat × Value) :=
  factsFrom ((Flow.live pc).filter tracked.contains) (loopValues P L g d advanced)

private theorem flip_slot_word {i : Nat} (hi : i < 2) :
    Value.bits 32 ((truncBits 32 (truncBits 32 (~~~(truncBits 32 (BitVec.ofNat 64 i))))) &&&
      truncBits 32 (BitVec.ofInt 64 1)) = b32 (1 - i) := by
  interval_cases i <;> rfl

/-- Install the next P-buffer slot and its generation. -/
private theorem run_1130_1132 (d : D) {t : TState}
    (h : At t 1130
      ((1718, .bits 32 (truncBits 32 (~~~(truncBits 32 (BitVec.ofNat 64 (d.block % 2)))))) ::
        (114, .pred (decide ((d.block + 1) / 2 % 2 = 1))) ::
        factsFrom ((Flow.live 1130).filter tracked.contains) (valueOf P L g d))) :
    ∃ u, run kernel asms L g 2 t = some u ∧
      At u 1132 (loopFacts P L g d [452, 2953] 1132) := by
  have hslot : (d.block + 1) % 2 = 1 - d.block % 2 := by omega
  have hflip := flip_slot_word (i := d.block % 2) (by omega)
  simp only [loopFacts]
  by_cases hp : (d.block + 1) / 2 % 2 = 1 <;>
    simp only [hp, decide_true, decide_false] at h <;> seg_fp h using
      all_goals first
        | (change _ = b32 ((d.block + 1) % 2); rw [hslot]; exact hflip)
        | (have hpar : (d.block + 1) / 2 % 2 = 1 ∨ (d.block + 1) / 2 % 2 = 0 := by omega
           change _ = Value.bits 16 (BitVec.ofNat 64 ((d.block + 1) / 2 % 2))
           simp_all only [or_false, false_or, Nat.one_ne_zero]; rfl)

/-- The index-ring slot's generation changes on a wrap from slot three. -/
private theorem run_1132_1133 (d : D) :
    Seg kernel asms L g 1 1132 (loopFacts P L g d [452, 2953] 1132) 1133
      ((115, .pred (decide (d.block % 4 = 3))) :: loopFacts P L g d [452, 2953] 1133) := by
  intro t h
  simp only [loopFacts] at h ⊢
  have hsmall : d.block % 4 < 4 := Nat.mod_lt _ (by decide)
  seg_fp h using
    norm_signed []

private theorem run_1133_1136 (d : D) :
    Seg kernel asms L g 3 1133
      ((115, .pred (decide (d.block % 4 = 3))) :: loopFacts P L g d [452, 2953] 1133)
      1136 ((116, .pred (decide ((d.block + 1) / 4 % 2 = 1))) ::
        loopFacts P L g d [452, 2953] 1136) := by
  intro t h
  simp only [loopFacts] at h ⊢
  by_cases hs : d.block % 4 = 3 <;> simp only [hs, decide_true, decide_false] at h <;>
    seg_fp h using norm_signed [land255, phase4_succ, hs]

/-- Commit the four-slot index generation and advance its slot modulo four. -/
private theorem run_1136_1143 (d : D) :
    Seg kernel asms L g 7 1136
      ((116, .pred (decide ((d.block + 1) / 4 % 2 = 1))) ::
        loopFacts P L g d [452, 2953] 1136)
      1143 (loopFacts P L g d [451, 452, 2952, 2953] 1143) := by
  intro t h
  simp only [loopFacts] at h ⊢
  have hs : d.block % 4 < 4 := Nat.mod_lt _ (by decide)
  by_cases hp : (d.block + 1) / 4 % 2 = 1 <;>
    simp only [hp, decide_true, decide_false] at h <;> seg_fp h using
      all_goals first
        | (change _ = b32 ((d.block + 1) % 4); norm_signed [])
        | (have hpar : (d.block + 1) / 4 % 2 = 1 ∨ (d.block + 1) / 4 % 2 = 0 := by omega
           change _ = Value.bits 16 (BitVec.ofNat 64 ((d.block + 1) / 4 % 2))
           simp_all only [or_false, false_or, Nat.one_ne_zero]; rfl)

private def ringRegs (again : Bool) : List Nat :=
  if again then [451, 452, 2952, 2953] else []

private def counterRegs (again : Bool) : List Nat := [2883, 2884] ++ ringRegs again

/-- Advance the block counters and test whether the row still has a block. -/
private theorem run_1143_1146 (d : D) (again : Bool)
    (hblock : d.block < blocksOf P L g) (hlim : blocksOf P L g < 2 ^ 31) :
    Seg kernel asms L g 3 1143 (loopFacts P L g d (ringRegs again) 1143) 1146
      ((117, .pred (decide (d.block + 1 < blocksOf P L g))) ::
        loopFacts P L g d (counterRegs again) 1146) := by
  intro t h
  cases again <;> simp only [loopFacts, counterRegs, ringRegs, Bool.false_eq_true,
    ite_false, ite_true, List.append_nil, List.cons_append, List.nil_append] at h ⊢ <;>
    seg_fp h using
      (try simp [loopValues, nextBlock])
      (try wg0_values)
      norm_signed []

/-- The second block test branches back to the common Wg0 barrier or opens the LSE path. -/
private theorem branch_to_next_site (d : D) (again : Bool) {t : TState}
    (h : At t 1146 ((117, .pred again) :: loopFacts P L g d (counterRegs again) 1146)) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u (if again then 253 else 1147)
      ((117, .pred again) :: loopFacts P L g d (counterRegs again) 1146) := by
  exact run_bra Flow.code_1146 again h h.2.2.2.2.1
    (Thread.asms_localRule_bra (by rw [h.1]; decide) (by rw [h.1]; decide))

/-- Recompute each warp's arm and the common barrier operands on the new block. -/
private theorem run_253_256 (d : D) (hw : warpOf L g < 4) :
    Seg kernel asms L g 3 253
      (loopFacts P L g d (counterRegs true) 1146)
      256 (facts P L g (nextBlock d)) := by
  intro t h
  simp only [loopFacts] at h
  change ∃ u, run kernel asms L g 3 t = some u ∧ At u 256
    (factsFrom ((Flow.live 256).filter tracked.contains) (valueOf P L g (nextBlock d)))
  seg_fp h using
    (first | rfl | (change _ = Value.pred (decide (2 ≤ warpOf L g)); norm_signed []))

/-- The rescale arm's last Tensor Memory fence directly enters the shared P fence. -/
theorem step_rescaleFenceB (d : D) (hd : d.site = .rescaleFenceB) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat hinv hc hf => by
    have hsite : d.site.pc = 1119 := by rw [hd]; rfl
    have hsub : d.sub = 0 := by
      have hs := hinv.subLt
      simpa [hd, Site.elems] using hs
    rw [hsite] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1119)
    change e = ⟨1119, .tc .fenceBefore⟩ ∧ some u = some (PTX.next t) at hf
    obtain ⟨he, hu⟩ := hf
    have hu' := Option.some.inj hu
    subst hu'
    let d' : D := {d with site := .soFence}
    have hn : next P L g d e = some (some d') := by simp [next, nextSite, hd, he, d']
    have hav := at_next_of hat hsite hsub
    have hkeep : ∀ r ∈ (Flow.live 1120).filter tracked.contains,
        r ∈ (Flow.live 1119).filter tracked.contains := by decide +kernel
    refine Or.inl (Or.inr ⟨d', PTX.next t, hn, .refl, ?_, ?_⟩)
    · refine ⟨hav.1, hav.2.1.trans hsub.symm, hav.2.2.1, hav.2.2.2.1, ?_⟩
      exact holds_factsFrom_mono hav.2.2.2.2 hkeep
    · have hi := inv_setSite hinv .soFence (by simp [Site.inEpilogue]) (by simp [Site.inRescale])
        (by rintro ⟨_, _, h⟩; cases h) (by simp) (by simp)
      simpa [code, d', hsub] using hi

/-- Detect an empty row before selecting the LSE operands. -/
private theorem run_1147_1148 (d : D) :
    Seg kernel asms L g 1 1147 (loopFacts P L g d (counterRegs false) 1146) 1148
      ((138, .pred (decide (d.peak = ⊥))) ::
        factsFrom ((Flow.live 1147).filter tracked.contains) (valueOf P L g d)) := by
  intro t h
  have hs : (Flow.live 1147).filter tracked.contains ⊆
      (Flow.live 1146).filter tracked.contains := by decide +kernel
  have hsame : ∀ r ∈ (Flow.live 1147).filter tracked.contains,
      (counterRegs false).contains r = false := by decide +kernel
  have hat := h.mono (holds_of_pointwise fun r hr => by
    have hval := holds_mem h.2.2.2.2 (mem_factsFrom (hs hr))
    simpa only [loopValues, hsame r hr, Bool.false_eq_true, ite_false] using hval)
  have hr : t.regs 2885 = some (peakVal d.peak) :=
    holds_mem hat.2.2.2.2 (mem_factsFrom (by decide +kernel))
  let op : Op := .float {
    op := .setp (.ord .eq) none, ty := ⟨.f32, 1⟩, ftz := true,
    dsts := [some 138], srcs := [.reg 2885, .f32imm 4286578688] }
  have hc : kernel.code[1147]? = some ⟨none, op⟩ := Flow.code_1147
  have he : execLocalA asms L g t op =
      .ok (PTX.next (setReg t 138 (.pred (decide (d.peak = ⊥))))) := by
    apply Assumption.execLocalA_idealReal
      (f := .setpInf .f32) rfl (by decide)
      (fun a ha l i state _ => asms_segment_free (L := l) (g := i) state a
        (List.mem_cons_of_mem _ ha))
    have hr' : Assumption.readERealOpnd t .f32 (.reg 2885) =
        Assumption.readEReal .f32 (peakVal d.peak) := by
      simp [Assumption.readERealOpnd, readReg, hr, pure, Except.pure]
    have hneg : Assumption.readERealOpnd t .f32 (.f32imm 4286578688) =
        some (.ok (⊥ : EReal)) := rfl
    have hneg' : Assumption.readEReal .f32 negInf = some (.ok (⊥ : EReal)) := rfl
    change Assumption.bindRead (Assumption.readERealOpnd t .f32 (.reg 2885)) (fun x =>
        Assumption.bindRead (Assumption.readERealOpnd t .f32 (.f32imm 4286578688)) fun y =>
          some (.ok (PTX.next (setReg t 138 (.pred (Assumption.erealCompare .eq x y)))))) = _
    rw [hr', hneg]
    cases d.peak with
    | bot =>
      simp [peakVal, hneg', Assumption.bindRead, Assumption.erealCompare]
    | coe x =>
      simp [peakVal, Assumption.readEReal, Assumption.bindRead,
        Assumption.erealCompare, pure, Except.pure, Ne.symm (EReal.bot_ne_coe x)]
  exact ⟨_, run_local hc rfl hat he, hat.set (not_mem_factsFrom (by decide +kernel))⟩

/-- Select the final LSE reference and half-sum and set the named-barrier operands. -/
private theorem run_1148_1154 (d : D) :
    Seg kernel asms L g 6 1148 ((138, .pred (decide (d.peak = ⊥))) ::
      factsFrom ((Flow.live 1147).filter tracked.contains) (valueOf P L g d))
      1154 (facts P L g {d with site := .lseBar}) := by
  intro t h
  have hpar : d.block / 2 % 2 < 2 := Nat.mod_lt _ (by decide)
  change ∃ u, run kernel asms L g 6 t = some u ∧ At u 1154
    (factsFrom ((Flow.live 1154).filter tracked.contains) (valueOf P L g {d with site := .lseBar}))
  let live := (Flow.live 1147).filter tracked.contains
  have ha : At t 1148 ((138, .pred (decide (d.peak = ⊥))) ::
      (2955, halfSumVal d) :: (2950, miVal d) :: factsFrom live (valueOf P L g d)) :=
    h.mono ⟨h.2.2.2.2.1,
      holds_mem h.2.2.2.2.2 (mem_factsFrom (r := 2955) (by decide +kernel)),
      holds_mem h.2.2.2.2.2 (mem_factsFrom (r := 2950) (by decide +kernel)),
      h.2.2.2.2.2⟩
  by_cases hp : d.peak = ⊥ <;> cases hm : d.miUpd <;> cases hs : d.sumUpd <;>
    simp [hp, hm, hs, halfSumVal, miVal] at ha <;> seg_fp ha using
      (first
        | rfl
        | (change _ = b32 (d.block / 2 % 2); interval_cases hpar' : d.block / 2 % 2 <;> rfl)
        | (wg0_values; simp [lseRefVal, miVal, halfSumVal, negInf, fl, b32, *]))

/-- After the softmax-ready arrival, advance the rings or enter the last block's LSE epilogue. -/
theorem step_soReady (hpre : Pre P L mem0) (hbatch : eOf L g < P.b)
    (d : D) (hd : d.site = .soReady) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat hinv hc hf => by
    obtain ⟨rel, scope, he, rfl⟩ := fires_soReady hpre hd hat hc hf
    have hsite : d.site.pc = 1122 := by rw [hd]; rfl
    have hsub : d.sub = 0 := by
      have hs := hinv.subLt
      simpa [hd, Site.elems] using hs
    have hlim : blocksOf P L g < 2 ^ 31 := by
      have hh := (blocksOf_word_bounds hpre hbatch).2
      omega
    obtain ⟨t₁, hr₁, ha₁⟩ := run_1123_1124 hpre hbatch d hinv.blockLt
      (at_next_of hat hsite hsub)
    by_cases hb : d.block + 1 < blocksOf P L g
    · have hnlast : d.block + 1 ≠ blocksOf P L g := by omega
      simp only [hnlast, decide_false] at ha₁
      obtain ⟨t₂, hr₂, ha₂⟩ := branch_after_block d false ha₁
      obtain ⟨t₃, hr₃, ha₃⟩ := run_1125_1130 d (ha₂.mono ha₂.2.2.2.2.2)
      obtain ⟨t₄, hr₄, ha₄⟩ := run_1130_1132 d ha₃
      obtain ⟨t₅, hr₅, ha₅⟩ := run_1132_1133 d t₄ ha₄
      obtain ⟨t₆, hr₆, ha₆⟩ := run_1133_1136 d t₅ ha₅
      obtain ⟨t₇, hr₇, ha₇⟩ := run_1136_1143 d t₆ ha₆
      obtain ⟨t₈, hr₈, ha₈⟩ := run_1143_1146 d true hinv.blockLt hlim t₇ ha₇
      simp only [hb, decide_true] at ha₈
      obtain ⟨t₉, hr₉, ha₉⟩ := branch_to_next_site d true ha₈
      obtain ⟨v, hr₁₀, hav⟩ := run_253_256 d hinv.warpLt t₉ (ha₉.mono ha₉.2.2.2.2.2)
      have hn : next P L g d e = some (some (nextBlock d)) := by
        simp [next, nextSite, nextBlock, hd, he, hb]
      refine Or.inl (Or.inr ⟨nextBlock d, v, hn, ?_, ?_, ?_⟩)
      · exact run_rtg (run_comp (run_comp (run_comp (run_comp
          (run_comp (run_comp (run_comp (run_comp (run_comp hr₁ hr₂) hr₃) hr₄) hr₅)
            hr₆) hr₇) hr₈) hr₉) hr₁₀)
      · exact hav
      · have hi := handoff_inv hinv hb
        exact inv_setSite hi .wg0Sync (by simp [Site.inEpilogue]) (by simp [Site.inRescale])
          (by rintro ⟨_, _, h⟩; cases h) (by simp) (by simp)
    · have hlast : d.block + 1 = blocksOf P L g := by
        have hh := hinv.blockLt
        omega
      simp only [hlast, decide_true] at ha₁
      obtain ⟨t₂, hr₂, ha₂⟩ := branch_after_block d true ha₁
      have hkeep : (Flow.live 1143).filter tracked.contains ⊆
          (Flow.live 1122).filter tracked.contains := by decide +kernel
      have ha₂' : At t₂ 1143 (loopFacts P L g d (ringRegs false) 1143) :=
        ha₂.mono (holds_factsFrom_mono ha₂.2.2.2.2.2 hkeep)
      obtain ⟨t₃, hr₃, ha₃⟩ := run_1143_1146 d false hinv.blockLt hlim t₂ ha₂'
      simp only [hb, decide_false] at ha₃
      obtain ⟨t₄, hr₄, ha₄⟩ := branch_to_next_site d false ha₃
      obtain ⟨t₅, hr₅, ha₅⟩ := run_1147_1148 d t₄ (ha₄.mono ha₄.2.2.2.2.2)
      obtain ⟨v, hr₆, hav⟩ := run_1148_1154 d t₅ ha₅
      let d' : D := {d with site := .lseBar}
      have hn : next P L g d e = some (some d') := by
        simp [next, nextSite, hd, he, hb, d']
      refine Or.inl (Or.inr ⟨d', v, hn, ?_, ?_, ?_⟩)
      · exact run_rtg (run_comp (run_comp (run_comp (run_comp (run_comp hr₁ hr₂) hr₃) hr₄) hr₅)
          hr₆)
      · exact ⟨hav.1, hav.2.1.trans hsub.symm, hav.2.2.1, hav.2.2.2.1, hav.2.2.2.2⟩
      · simpa [code, d', hsub] using epilogue_inv hinv hb

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
