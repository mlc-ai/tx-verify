-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.Compute
public import Kernels.InklingRelDecode.Proof.Lib.IntOps
public import Lemmas.Flow.DataArith
public import Lemmas.Flow.DataElect
public import Lemmas.Flow.DivStep
public import Kernels.InklingRelDecode.Proof.Lib.Havoc
import Kernels.InklingRelDecode.Flow.Code.Part003
import Kernels.InklingRelDecode.Flow.Code.Part004
import Lemmas.Flow.CtlStepsU
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The sites that compute a data fact: the column elections

After the copy election of a block's first half (`pel b 0`) the column of the half tile is built
from the broadcast bit (`and`, `shl`, `add`); after the second (`pel b 1`) it is 128 on. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.EventFrame Control

noncomputable section

/-- The facts of a state do not name a register outside its live set and its data facts. -/
theorem fresh_facts {Q L g w} {d : D} {r : Nat} (h1 : r ∉ ctlLive d.c.site.pc)
    (h2 : ∀ τ ∈ tags d.c.site, τ.reg ≠ r) : r ∉ ((code Q L g w).facts d).map Prod.fst := by
  intro hm
  simp only [List.map_append, List.mem_append] at hm
  rcases hm with hm | hm
  · apply h1
    change r ∈ (factsFrom (ctlLive d.c.site.pc) _).map Prod.fst at hm
    rwa [factsFrom_keys] at hm
  · obtain ⟨τ, hτ, e⟩ := List.mem_map.mp (by simpa [dF] using hm)
    exact h2 τ hτ e

theorem elect_fetch (b : Fin 3) (j : Fin 2) :
    ∃ r p, kernel.code[(Site.pel b ⟨j.val, by omega⟩).pc]? =
    some ⟨none, .warp ⟨.elect, none, [some r, some p], [], some (.imm (-1))⟩⟩ ∧
    r ∉ ctlLive (Site.pel b ⟨j.val, by omega⟩).pc ∧ p ∉ ctlLive (Site.pel b ⟨j.val, by omega⟩).pc ∧
    (∀ τ ∈ tags (.pel b ⟨j.val, by omega⟩), τ.reg ≠ r ∧ τ.reg ≠ p) := by
  fin_cases b <;> fin_cases j
  · exact ⟨694, 58, Flow.code_203, by decide +kernel⟩
  · exact ⟨698, 60, Flow.code_213, by decide +kernel⟩
  · exact ⟨715, 68, Flow.code_245, by decide +kernel⟩
  · exact ⟨720, 69, Flow.code_255, by decide +kernel⟩
  · exact ⟨737, 77, Flow.code_287, by decide +kernel⟩
  · exact ⟨742, 78, Flow.code_297, by decide +kernel⟩

/-- The copy election of half `j` of block `b`. -/
abbrev pelS (b : Fin 3) (j : Fin 2) : Site := .pel b ⟨j.val, by omega⟩

/-- **The data step of a copy election**, from the `Reach` after it, for each successor. -/
theorem pel_step_of {Q L g w} (d : D) (b : Fin 3) (j : Fin 2) (hs : d.c.site = pelS b j)
    (hR : ∀ d' : D, d'.c.site ∈ succs (pelS b j) → d'.c.broadcast = d.c.broadcast →
      d'.v = d.v → Reach kernel Assumptions.all L g ((pelS b j).pc + 1)
        ((checkedCode Q L g w).facts d.c ++ dF Q L g d) (dF Q L g d')) :
    DataStep (code Q L g w) (dF Q L g) d := by
  obtain ⟨r, p, hcode, hr, hp, htag⟩ := elect_fetch b j
  have hc : kernel.code[(code Q L g w).pc d]? =
      some ⟨none, .warp ⟨.elect, none, [some r, some p], [], some (.imm (-1))⟩⟩ := by
    show kernel.code[d.c.site.pc]? = _
    rw [hs]; exact hcode
  have hl : ∀ b' h', d.c.site ≠ .lb b' h' := fun b' h' e => by rw [hs] at e; cases e
  have hnb : ¬ Bare d.c.site := by
    rw [hs]; exact (by decide : ∀ b j, ¬ Bare (pelS b j)) b j
  intro t e u d' ins' hat hi' hc' hf hn
  exact DataStep.elect (r := r) (p := p) hc
    (fun _ mk inst ld d' t hn' hat' => by
      obtain ⟨hp0, hs0, ha0, hf0, hr0⟩ := hat'
      obtain ⟨c, hnc, rfl⟩ := succ_split hn'
      obtain ⟨hsite, hbc⟩ := next_succ Q L g hnb hnc
      have hbc' : c.broadcast = d.c.broadcast := hbc (fun b' e => by rw [hs] at e; cases e)
      refine hR _ (hs ▸ hsite) hbc' (record_keep hl (fun j e => by rw [hs] at e; cases e)) _
        ⟨?_, ?_, ?_, ?_, ?_⟩
      · show t.pc + 1 = _
        rw [hp0]; show d.c.site.pc + 1 = _; rw [hs]
      · exact hs0.trans (by show d.c.site.sub = 0; rw [hs]; rfl)
      · exact ha0.trans rfl
      · exact hf0
      · have hs' : d.c.site = Site.pel b ⟨j.val, by omega⟩ := hs
        refine holds_update_update hr0 (fresh_facts (by rw [hs']; exact hr) fun τ hτ => ?_)
          (fresh_facts (by rw [hs']; exact hp) fun τ hτ => ?_)
        · rw [hs'] at hτ; exact (htag τ hτ).1
        · rw [hs'] at hτ; exact (htag τ hτ).2) ins' hat hi' hc' hf hn

def srcReg (b : Fin 3) : Nat := [693, 714, 736].getD b 0
def andReg (b : Fin 3) : Nat := [695, 716, 738].getD b 0
def shlReg (b : Fin 3) : Nat := [697, 719, 741].getD b 0
def andPc (b : Fin 3) : Nat := [206, 247, 289].getD b 0
def shlPc (b : Fin 3) : Nat := [209, 251, 293].getD b 0

theorem col_fetch (b : Fin 3) :
    kernel.code[andPc b]? = some ⟨none, .int ⟨.and, .int .b 32, false, [some (andReg b)],
      [.reg (srcReg b), .imm 1]⟩⟩ ∧
    kernel.code[shlPc b]? = some ⟨none, .int ⟨.shl, .int .b 32, false, [some (shlReg b)],
      [.reg (andReg b), .imm 6]⟩⟩ ∧
    kernel.code[shlPc b + 1]? = some ⟨none, .int ⟨.add, .int .s 32, false,
      [some (Tag.col b 0).reg], [.reg (shlReg b), .reg 495]⟩⟩ := by
  fin_cases b
  · exact ⟨Flow.code_206, Flow.code_209, Flow.code_210⟩
  · exact ⟨Flow.code_247, Flow.code_251, Flow.code_252⟩
  · exact ⟨Flow.code_289, Flow.code_293, Flow.code_294⟩

theorem col_hooks : ∀ b : Fin 3,
    Havoc.check Lib.hooks [srcReg b, 495] ((pelS b 0).pc + 1) (andPc b)
      ((kernel.code.drop ((pelS b 0).pc + 1)).take (andPc b - ((pelS b 0).pc + 1))) = true ∧
    Havoc.check Lib.hooks [andReg b, 495] (andPc b + 1) (shlPc b)
      ((kernel.code.drop (andPc b + 1)).take (shlPc b - (andPc b + 1))) = true ∧
    Assumptions.emuSites.contains (andPc b) = false ∧
    Assumptions.emuSites.contains (shlPc b) = false ∧
    Assumptions.emuSites.contains (shlPc b + 1) = false := by decide +kernel

theorem pel_tags : ∀ (b : Fin 3) (j : Fin 2), ∀ s' ∈ succs (pelS b j), ∀ τ ∈ tags s',
    τ ∈ tags (pelS b j) ∨ τ = .col b j := by decide +kernel

theorem col_src : ∀ b : Fin 3, srcReg b ∈ ctlLive (pelS b 0).pc ∧ .ox ∈ tags (pelS b 0) ∧
    Tag.pc (.col b 0) = shlPc b + 1 ∧ andPc b + 1 ≤ shlPc b ∧ (pelS b 0).pc + 1 ≤ andPc b ∧
    shlPc b + 2 ≤ 574 := by decide +kernel

/-- **The column of the first half tile** from the broadcast bit. -/
theorem col0_seg {Q L g w} (d : D) (b : Fin 3) (hs : d.c.site = pelS b 0) :
    SegU kernel Assumptions.all L g ((pelS b 0).pc + 1)
      ((checkedCode Q L g w).facts d.c ++ dF Q L g d) (shlPc b + 2)
      [((Tag.col b 0).reg, Tag.val Q L g d (.col b 0))] := by
  obtain ⟨hf1, hf2, hf3⟩ := col_fetch b
  obtain ⟨hk1, hk2, he1, he2, he3⟩ := col_hooks b
  obtain ⟨hsrc, hox, hcol, hab, hpa, hbd⟩ := col_src b
  have hpc : d.c.site.pc = (pelS b 0).pc := by rw [hs]
  have hbcv : valueOf Q L g w d.c (srcReg b) = d.c.broadcast := by fin_cases b <;> rfl
  have hS0 : ∀ x ∈ [(srcReg b, d.c.broadcast), (495, Tag.val Q L g d .ox)],
      x ∈ (checkedCode Q L g w).facts d.c ++ dF Q L g d := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · refine List.mem_append_left _ ?_
      change _ ∈ factsFrom (ctlLive d.c.site.pc) (valueOf Q L g w d.c)
      rw [hpc, ← hbcv]
      exact mem_factsFrom hsrc
    · refine List.mem_append_right _ (List.mem_map.mpr ⟨.ox, by rw [hs]; exact hox, rfl⟩)
  set bc := d.c.broadcast with hbc
  generalize hox' : (Tag.val Q L g d .ox) = ox at *
  have hoxb : ox = .bits 32 (BitVec.ofNat 64 ((Q.headCols * (L.ctaidOf (g / L.block)).get .y) %
      2 ^ 32)) := by rw [← hox']; rfl
  let X : Value := .bits 32 (Lib.word bc &&& truncBits 32 (BitVec.ofInt 64 1))
  let S0 : List (Nat × Value) := [(srcReg b, bc), (495, ox)]
  have hlen : 2856 ≤ kernel.code.length := by decide +kernel
  have c1 : SegU kernel Assumptions.all L g ((pelS b 0).pc + 1) S0 (andPc b) S0 :=
    SegU.of_havoc Lib.rulesFrame Lib.hooks_ok hpa (le_trans (by omega) hlen) hk1 (fun _ h => h)
  have c2 := Lib.andStep (L := L) (g := g) (F := S0) (va := bc) (k := 1) hf1 he1
    (List.mem_cons_self ..) (G := (andReg b, X) :: S0) fun R hR => by
      exact holds_update_cons hR (by fin_cases b <;> simp [S0, srcReg, andReg])
  have hsub : ∀ x ∈ [(andReg b, X), (495, ox)], x ∈ (andReg b, X) :: S0 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp [S0]
  have c3 : SegU kernel Assumptions.all L g (andPc b + 1) ((andReg b, X) :: S0) (shlPc b)
      [(andReg b, X), (495, ox)] :=
    SegU.of_havoc Lib.rulesFrame Lib.hooks_ok (by omega) (le_trans (by omega) hlen) hk2 hsub
  let Y : Value := .bits 32 (truncBits 32 (Lib.word X <<< 6))
  have c4 := Lib.shlStep (L := L) (g := g) (F := [(andReg b, X), (495, ox)]) (va := X) (k := 6)
    (n := 6) hf2 he2 (List.mem_cons_self ..) (by decide) (by norm_num)
    (G := (shlReg b, Y) :: [(andReg b, X), (495, ox)]) fun R hR => by
      exact holds_update_cons hR (by fin_cases b <;> simp [andReg, shlReg])
  have c5 := Lib.addBitsStep (L := L) (g := g) (a := shlReg b) (b := 495)
    (F := (shlReg b, Y) :: [(andReg b, X), (495, ox)]) (x := truncBits 32 (Lib.word X <<< 6))
    (y := BitVec.ofNat 64 ((Q.headCols * (L.ctaidOf (g / L.block)).get .y) % 2 ^ 32)) hf3 he3
    (List.mem_cons_self ..) (by rw [hoxb]; simp)
    (G := ((Tag.col b 0).reg, Value.bits 32 (truncBits 32 (truncBits 32 (truncBits 32
      (Lib.word X <<< 6)) + truncBits 32 (BitVec.ofNat 64
        ((Q.headCols * (L.ctaidOf (g / L.block)).get .y) % 2 ^ 32))))) ::
      (shlReg b, Y) :: [(andReg b, X), (495, ox)]) fun R hR => by
      exact holds_update_cons hR (by fin_cases b <;> simp [andReg, shlReg, Tag.reg])
  have hval : Tag.val Q L g d (.col b 0) = Value.bits 32 (truncBits 32 (truncBits 32 (truncBits 32
      (Lib.word X <<< 6)) + truncBits 32 (BitVec.ofNat 64
        ((Q.headCols * (L.ctaidOf (g / L.block)).get .y) % 2 ^ 32)))) := by
    show colVal Q L g bc 0 = _
    unfold colVal u32 b32
    simp only [Lib.word, X, Value.regBits, Option.getD_some]
    rw [col_chain]
    simp
  refine SegU.mono_goal (SegU.weaken_start (((((c1.comp c2).comp c3).comp c4).comp c5))
    fun R hR => ?_) ?_
  · exact holds_of_mem fun r v hm => holds_mem hR (hS0 _ hm)
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    rw [hval]
    exact List.mem_cons_self ..

theorem col1_fetch (b : Fin 3) :
    kernel.code[Tag.pc (.col b 1)]? = some ⟨none, .int ⟨.add, .int .s 32, false,
      [some (Tag.col b 1).reg], [.reg (Tag.col b 0).reg, .imm 128]⟩⟩ := by
  fin_cases b
  · exact Flow.code_216
  · exact Flow.code_258
  · exact Flow.code_300

theorem col1_facts : ∀ b : Fin 3,
    Havoc.check Lib.hooks [(Tag.col b 0).reg] ((pelS b 1).pc + 1) (Tag.pc (.col b 1))
      ((kernel.code.drop ((pelS b 1).pc + 1)).take (Tag.pc (.col b 1) - ((pelS b 1).pc + 1))) =
      true ∧ Assumptions.emuSites.contains (Tag.pc (.col b 1)) = false ∧
    (pelS b 1).pc + 1 ≤ Tag.pc (.col b 1) ∧ Tag.pc (.col b 1) + 1 ≤ 574 ∧
    (Tag.col b 0) ∈ tags (pelS b 1) := by decide +kernel

/-- **The column of the second half tile**: 128 on from the first's. -/
theorem col1_seg {Q L g w} (d : D) (b : Fin 3) (hs : d.c.site = pelS b 1) :
    SegU kernel Assumptions.all L g ((pelS b 1).pc + 1)
      ((checkedCode Q L g w).facts d.c ++ dF Q L g d) (Tag.pc (.col b 1) + 1)
      [((Tag.col b 1).reg, Tag.val Q L g d (.col b 1))] := by
  obtain ⟨hk, he, hab, hbd, hcol⟩ := col1_facts b
  have hlen : 2856 ≤ kernel.code.length := by decide +kernel
  have hmem : ((Tag.col b 0).reg, Tag.val Q L g d (.col b 0)) ∈
      (checkedCode Q L g w).facts d.c ++ dF Q L g d :=
    List.mem_append_right _ (List.mem_map.mpr ⟨_, by rw [hs]; exact hcol, rfl⟩)
  have hv0 : Tag.val Q L g d (.col b 0) = .bits 32 (BitVec.ofNat 64 ((64 * ((Lib.word
      d.c.broadcast).toNat % 2) + 128 * (0 : Fin 2).val + Q.headCols *
      (L.ctaidOf (g / L.block)).get .y) % 2 ^ 32)) := rfl
  generalize Tag.val Q L g d (.col b 0) = x0 at hmem hv0
  have c1 : SegU kernel Assumptions.all L g ((pelS b 1).pc + 1) [((Tag.col b 0).reg, x0)]
      (Tag.pc (.col b 1)) [((Tag.col b 0).reg, x0)] :=
    SegU.of_havoc Lib.rulesFrame Lib.hooks_ok hab (le_trans (by omega) hlen) hk (fun _ h => h)
  rw [hv0] at c1
  have c2 := Lib.addImmStep (L := L) (g := g) (F := [((Tag.col b 0).reg, .bits 32
    (BitVec.ofNat 64 ((64 * ((Lib.word d.c.broadcast).toNat % 2) + 128 * (0 : Fin 2).val +
      Q.headCols * (L.ctaidOf (g / L.block)).get .y) % 2 ^ 32)))]) (k := 128) (col1_fetch b) he
    (List.mem_cons_self ..)
    (G := [((Tag.col b 1).reg, Tag.val Q L g d (.col b 1))])
    fun R _ => by
      refine ⟨?_, trivial⟩
      simp only [Function.update_self, Option.some.injEq]
      rw [add_imm128]
      show Value.bits 32 _ = colVal Q L g d.c.broadcast 1
      unfold colVal u32 b32
      congr 3
      simp
      omega
  refine SegU.weaken_start (c1.comp c2) fun R hR => ?_
  rw [hv0] at hmem
  exact ⟨holds_mem hR hmem, trivial⟩

theorem pel_nums : ∀ (b : Fin 3) (j : Fin 2), 27 ≤ (pelS b j).pc + 1 ∧
    (pelS b j).pc + 1 ≤ Tag.pc (.col b j) + 1 ∧ Tag.pc (.col b j) + 1 ≤ 574 := by decide +kernel

/-- **The first event after a copy election holds the successor's data facts**, from the segment
that builds the column. -/
theorem pel_reach {Q L g w} (d : D) (b : Fin 3) (j : Fin 2) (hs : d.c.site = pelS b j)
    (hseg : SegU kernel Assumptions.all L g ((pelS b j).pc + 1)
      ((checkedCode Q L g w).facts d.c ++ dF Q L g d) (Tag.pc (.col b j) + 1)
      [((Tag.col b j).reg, Tag.val Q L g d (.col b j))])
    (d' : D) (hsite : d'.c.site ∈ succs (pelS b j)) (hbc : d'.c.broadcast = d.c.broadcast)
    (hv : d'.v = d.v) : Reach kernel Assumptions.all L g ((pelS b j).pc + 1)
      ((checkedCode Q L g w).facts d.c ++ dF Q L g d) (dF Q L g d') := by
  obtain ⟨h27, hpq, hq⟩ := pel_nums b j
  refine Reach.carry_new (C := dF Q L g d)
    (N := [((Tag.col b j).reg, Tag.val Q L g d (.col b j))]) Lib.rulesFrame ?_ ?_
    (fun pc h1 h2 => seg_range (by omega) h2) hpq hq
    (fun R hR => ((holds_append _ _ _).mp hR).2) hseg (fun R hR => hR) ?_
  · have : (dF Q L g d).map Prod.fst = (tags d.c.site).map Tag.reg := by simp [dF]
    rw [this, hs]
    exact region_tags h27 fun τ hτ => by
      have := Nat.blt_eq.mp (List.all_eq_true.mp (tags_pc (pelS b j)) τ hτ)
      omega
  · exact region_tags (T := [.col b j]) (by omega) fun τ hτ => by
      simp only [List.mem_singleton] at hτ
      subst hτ
      have := (pel_nums b j).2.1
      omega
  · intro x hx
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp (by simpa only [dF] using hx)
    rcases pel_tags b j _ hsite τ hτ with h1 | rfl
    · left
      simp only [dF, List.mem_map]
      refine ⟨τ, by rw [hs]; exact h1, ?_⟩
      cases τ <;> first | (simp [Tag.val, hbc, hv]; done) |
        (have := old_noq (pelS b j); simp only [tags, qTags, List.append_nil] at h1
         exact absurd h1 (by first | exact this.1 _ | exact this.2 _ _))
    · right
      simp [Tag.val, hbc]

theorem col_end (b : Fin 3) : Tag.pc (.col b 0) = shlPc b + 1 := (col_src b).2.2.1

/-- **The data step of a copy election that computes a column.** -/
theorem pel_step {Q L g w} (d : D) (b : Fin 3) (j : Fin 2) (hs : d.c.site = pelS b j) :
    DataStep (code Q L g w) (dF Q L g) d := by
  refine pel_step_of d b j hs fun d' h1 h2 h3 => pel_reach d b j hs ?_ d' h1 h2 h3
  fin_cases j
  · rw [show (⟨0, by omega⟩ : Fin 2) = 0 from rfl, col_end]
    exact col0_seg d b hs
  · exact col1_seg d b hs

theorem compute_cases (s : Site) (hq : qside s = false) (hc : carrySite s ≠ true) :
    (∃ b h, s = .lb b h) ∨ (∃ b, s = pelS b 0) ∨ (∃ b, s = pelS b 1) ∨ s = .exit := by
  cases s with
  | lb b h' => exact .inl ⟨b, h', rfl⟩
  | exit => exact .inr (.inr (.inr rfl))
  | pel b j =>
    fin_cases j
    · exact .inr (.inl ⟨b, rfl⟩)
    · exact .inr (.inr (.inl ⟨b, rfl⟩))
    all_goals exact absurd (by simp [carrySite, compute, qside] at hq ⊢) hc
  | stq _ j | ptc _ j =>
    fin_cases j <;> exact absurd (by simp [carrySite, compute, qside] at hq ⊢) hc
  | _ => exact absurd (by simp [carrySite, compute, qside] at hq ⊢) hc

/-- **The data step of every state of the prologue.** -/
theorem data_step {Q L g w} (d : D) (hq : qside d.c.site = false) :
    DataStep (code Q L g w) (dF Q L g) d := by
  by_cases hc : carrySite d.c.site = true
  · exact carry_step d hc
  · rcases compute_cases _ hq hc with ⟨b, h, hs⟩ | ⟨b, hs⟩ | ⟨b, hs⟩ | hs
    · exact lb_step d b h hs
    · exact pel_step d b 0 hs
    · exact pel_step d b 1 hs
    · intro ins' hat hi' hc' hf hn
      obtain ⟨c, hnc, -⟩ := succ_split hn
      simp [Control.next, hs] at hnc

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
