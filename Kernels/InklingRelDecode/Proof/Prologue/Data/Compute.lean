-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.Carry
public import Kernels.InklingRelDecode.Proof.Lib.RawArith
public import Kernels.InklingRelDecode.Proof.Lib.MulStep
public import Lemmas.Flow.DataCompute
public import Lemmas.Flow.DataArith
import Kernels.InklingRelDecode.Flow.Code.Part003
import Kernels.InklingRelDecode.Flow.Code.Part004
import Lemmas.Flow.CtlStepsU
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The sites that compute a data fact: the block-table loads

The row of a loaded page is the word times the page stride plus the head's row offset, one
`mad.lo` after the load. A word without an integer reading ends the thread in that instruction
(`Lib.madStep`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.EventFrame Control

noncomputable section

def payReg (b : Fin 3) (h : Fin 2) : Nat := [681, 701, 723].getD b 0 + 6 * h.val
def madPc (b : Fin 3) (h : Fin 2) : Nat := (Site.lb b h).pc + (if b = 0 ∧ h = 0 then 2 else 1)
def endPc (b : Fin 3) (h : Fin 2) : Nat :=
  (Site.lb b h).pc + (if b = 0 ∧ h = 0 then 4 else 2)
def lbNext (b : Fin 3) (h : Fin 2) : Site := .pb b (if h = 0 then 1 else 3)

/-- The facts a block-table load adds. -/
def newTags (b : Fin 3) (h : Fin 2) : List Tag :=
  if b = 0 ∧ h = 0 then [.row 0 0, .oy, .ox] else [.row b h]

theorem lb_tags : ∀ b h, (∀ τ ∈ tags (lbNext b h), τ ∈ tags (.lb b h) ∨ τ ∈ newTags b h) ∧
    (∀ τ ∈ tags (.lb b h), ∀ b' h', τ ≠ .row b' h') := by decide +kernel

theorem lb_noq : (∀ b h k, Tag.qh k ∉ tags (.lb b h)) ∧ ∀ b h i k, Tag.qw i k ∉ tags (.lb b h) := by
  decide +kernel

def loadOp (b : Fin 3) (h : Fin 2) : MemAccess :=
  {kind := .load, space := some .global, sem := .weak, elem := .int .b 32,
   addr := ⟨.reg (2071 + 2 * b.val + h.val) 64, 0⟩, dsts := [some (payReg b h)]}

theorem load_fetch (b : Fin 3) (h : Fin 2) :
    kernel.code[(Site.lb b h).pc]? = some ⟨none, .mem (loadOp b h)⟩ := by
  fin_cases b <;> fin_cases h
  · exact Flow.code_197
  · exact Flow.code_220
  · exact Flow.code_241
  · exact Flow.code_262
  · exact Flow.code_283
  · exact Flow.code_304

theorem mad_fetch (b : Fin 3) (h : Fin 2) : kernel.code[madPc b h]? = some ⟨none, .int ⟨.mad .lo,
    .int .s 32, false, [some (Tag.row b h).reg], [.reg (payReg b h), .reg 529, .reg 494]⟩⟩ := by
  fin_cases b <;> fin_cases h
  · exact Flow.code_199
  · exact Flow.code_221
  · exact Flow.code_242
  · exact Flow.code_263
  · exact Flow.code_284
  · exact Flow.code_305

theorem word_u32 (n : Nat) : Lib.word (u32 n) = BitVec.ofNat 64 (n % 2 ^ 32) := by
  simp only [Lib.word, u32, b32, Value.regBits, Option.getD_some]
  exact trunc_ofNat n

theorem mad_row (Q : Params) (L : Launch) (g : Nat) (v : Value) :
    Value.bits 32 (truncBits 32 (Lib.word v * Lib.word (u32 Q.pageRows) +
      Lib.word (u32 (Q.headRows * (L.ctaidOf (g / L.block)).get .y)))) = rowVal Q L g v := by
  rw [word_u32, word_u32]
  unfold rowVal Lib.word u32 b32
  rw [mad_trunc]
  have h : ∀ x : Nat, x % 4294967296 % 18446744073709551616 = x % 4294967296 := fun x =>
    Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num))
  simp [truncBits, h]

/-- The block-table load puts the word in the successor's record and leaves the control. -/
theorem lb_next {Q L g} {d d' : D} {b h} {e : Event} {x bs v} (hs : d.c.site = .lb b h)
    (hn : succ Q L g d e = some (some d')) (hk : e.kind = .rd x bs) (hv : rebuild 3 bs = .ok v) :
    d'.c = {d.c with site := lbNext b h} ∧ d'.v.pay b h = v := by
  have : loadVal bs = v := by simp [loadVal, hv, Except.toOption]
  unfold succ at hn
  fin_cases h <;> simp only [Control.next, hs, Option.map_some, Option.some.injEq] at hn <;>
    subst hn <;> simp [record, hs, hk, this, lbNext]

theorem pay_fresh : ∀ b h, payReg b h ∉ ctlLive (Site.lb b h).pc ∧
    ∀ τ ∈ tags (.lb b h), τ.reg ≠ payReg b h := by decide +kernel

theorem new_pc : ∀ b h, endPc b h ≤ 574 ∧ ∀ τ ∈ newTags b h, τ.pc < endPc b h := by
  decide +kernel

/-- The facts of a state after its load wrote `v` into the block-table register. -/
theorem holds_loaded {Q L g w} {d : D} {t : TState} (b : Fin 3) (h : Fin 2) (v : Value)
    (hs : d.c.site = .lb b h) (hf : Holds t.regs ((code Q L g w).facts d)) :
    Holds (setReg t (payReg b h) v).regs
      ((checkedCode Q L g w).facts d.c ++ dF Q L g d ++ [(payReg b h, v)]) := by
  obtain ⟨hc, hd⟩ := pay_fresh b h
  have hfresh : payReg b h ∉ ((code Q L g w).facts d).map Prod.fst := by
    intro hm
    simp only [List.map_append, List.mem_append] at hm
    rcases hm with hm | hm
    · have : payReg b h ∈ ctlLive d.c.site.pc := by
        change payReg b h ∈ (factsFrom (ctlLive d.c.site.pc) _).map Prod.fst at hm
        rwa [factsFrom_keys] at hm
      rw [hs] at this
      exact hc this
    · obtain ⟨τ, hτ, e⟩ := List.mem_map.mp (by simpa [dF] using hm)
      rw [hs] at hτ
      exact hd τ hτ e
  refine holds_of_mem fun r v' hm => ?_
  simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hm
  rcases hm with hm | ⟨rfl, rfl⟩
  · have hm' : (r, v') ∈ (code Q L g w).facts d := by
      simp only [List.mem_append]; exact hm
    have hne : r ≠ payReg b h := fun e => hfresh (by
      subst e; exact List.mem_map_of_mem (f := Prod.fst) hm')
    simp only [setReg]
    rw [Function.update_of_ne hne]
    exact holds_mem hf hm'
  · exact Function.update_self ..

/-- The facts a block-table load adds, in the successor. -/
def newFacts (Q : Params) (L : Launch) (g : Nat) (d' : D) (b : Fin 3) (h : Fin 2) :=
  (newTags b h).map fun τ => (τ.reg, τ.val Q L g d')

/-- **The first event after a block-table load holds the successor's data facts**, from a segment
that computes the new ones. -/
theorem lb_reach_of {Q L g w} {d d' : D} {b h} {v : Value} (hs : d.c.site = .lb b h)
    (hQ : d'.c = {d.c with site := lbNext b h} ∧ d'.v.pay b h = v)
    {G0 : List (Nat × Value)}
    (hseg : SegU kernel Assumptions.all L g ((Site.lb b h).pc + 1)
      ((checkedCode Q L g w).facts d.c ++ dF Q L g d ++ [(payReg b h, v)]) (endPc b h) G0)
    (hGN : ∀ R, Holds R G0 → Holds R (newFacts Q L g d' b h)) :
    Reach kernel Assumptions.all L g ((Site.lb b h).pc + 1)
      ((checkedCode Q L g w).facts d.c ++ dF Q L g d ++ [(payReg b h, v)]) (dF Q L g d') := by
  have hr := (Site.lb b h).pc_range
  obtain ⟨hnew, hnpc⟩ := new_pc b h
  have hend : (Site.lb b h).pc + 1 ≤ endPc b h := by unfold endPc; split <;> omega
  refine Reach.carry_new (C := dF Q L g d) (N := newFacts Q L g d' b h) Lib.rulesFrame ?_ ?_
    (fun pc h1 h2 => seg_range (by omega) h2) hend hnew
    (fun R hR => ((holds_append _ _ _).mp ((holds_append _ _ _).mp hR).1).2) hseg hGN ?_
  · have : (dF Q L g d).map Prod.fst = (tags d.c.site).map Tag.reg := by simp [dF]
    rw [this, hs]
    exact region_tags (by omega) fun τ hτ => by
      have := Nat.blt_eq.mp (List.all_eq_true.mp (tags_pc (.lb b h)) τ hτ)
      omega
  · have : (newFacts Q L g d' b h).map Prod.fst = (newTags b h).map Tag.reg := by
      simp [newFacts]
    rw [this]
    exact region_tags (by omega) hnpc
  · intro x hx
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp (by simpa only [dF] using hx)
    have hc : d'.c.site = lbNext b h := by rw [hQ.1]
    rw [hc] at hτ
    rcases (lb_tags b h).1 τ hτ with h1 | h1
    · left
      simp only [dF, List.mem_map]
      refine ⟨τ, by rw [hs]; exact h1, ?_⟩
      cases τ with
      | row b' h' => exact absurd rfl ((lb_tags b h).2 _ h1 b' h')
      | col b' h' => simp [Tag.val, hQ.1]
      | qh k => exact absurd h1 (lb_noq.1 b h k)
      | qw i k => exact absurd h1 (lb_noq.2 b h i k)
      | _ => rfl
    · exact .inr (List.mem_map.mpr ⟨τ, h1, rfl⟩)

theorem row_fresh : ∀ b h, (Tag.row b h).reg ∉ ctlLive (Site.lb b h).pc ∧
    (∀ τ ∈ tags (.lb b h), τ.reg ≠ (Tag.row b h).reg) ∧ payReg b h ≠ (Tag.row b h).reg ∧
    (¬(b = 0 ∧ h = 0) → .stride ∈ tags (.lb b h) ∧ .oy ∈ tags (.lb b h)) := by decide +kernel

theorem no_emu : ∀ b h, Assumptions.emuSites.contains (madPc b h) = false := by decide +kernel

/-- The facts of the loaded state do not name a register that is none of theirs. -/
theorem fresh_loaded {Q L g w} {d : D} {b h v r} (hs : d.c.site = .lb b h)
    (h1 : r ∉ ctlLive (Site.lb b h).pc) (h2 : ∀ τ ∈ tags (.lb b h), τ.reg ≠ r)
    (h3 : payReg b h ≠ r) :
    r ∉ ((checkedCode Q L g w).facts d.c ++ dF Q L g d ++ [(payReg b h, v)]).map Prod.fst := by
  intro hm
  simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil,
    List.mem_singleton] at hm
  rcases hm with (hm | hm) | hm
  · apply h1
    have : r ∈ ctlLive d.c.site.pc := by
      change r ∈ (factsFrom (ctlLive d.c.site.pc) _).map Prod.fst at hm
      rwa [factsFrom_keys] at hm
    rwa [hs] at this
  · obtain ⟨τ, hτ, e⟩ := List.mem_map.mp (by simpa [dF] using hm)
    rw [hs] at hτ
    exact h2 τ hτ e
  · exact h3 hm.symm

/-- **The row of a loaded page**, computed by the `mad.lo` after the load. -/
theorem lb_row {Q L g w} {d d' : D} {b h} {v : Value} (hbh : ¬(b = 0 ∧ h = 0))
    (hs : d.c.site = .lb b h) (hQ : d'.c = {d.c with site := lbNext b h} ∧ d'.v.pay b h = v) :
    Reach kernel Assumptions.all L g ((Site.lb b h).pc + 1)
      ((checkedCode Q L g w).facts d.c ++ dF Q L g d ++ [(payReg b h, v)]) (dF Q L g d') := by
  obtain ⟨hf, -, hp, hm⟩ := row_fresh b h
  obtain ⟨hst, hoy⟩ := hm hbh
  have hmem : ∀ τ ∈ tags (.lb b h), (τ.reg, τ.val Q L g d) ∈
      (checkedCode Q L g w).facts d.c ++ dF Q L g d ++ [(payReg b h, v)] := fun τ hτ => by
    simp only [List.mem_append, dF, List.mem_map]
    exact .inl (.inr ⟨τ, by rw [hs]; exact hτ, rfl⟩)
  have hpc : madPc b h = (Site.lb b h).pc + 1 := by simp [madPc, hbh]
  have hq : endPc b h = madPc b h + 1 := by simp [endPc, madPc, hbh]
  have hseg := Lib.madStep (L := L) (g := g) (dst := (Tag.row b h).reg) (a := payReg b h)
    (b := 529) (c := 494)
    (va := v) (vb := Tag.stride.val Q L g d) (vc := Tag.oy.val Q L g d) (mad_fetch b h)
    (no_emu b h) (by simp) (hmem _ hst) (hmem _ hoy) (G := ((Tag.row b h).reg, rowVal Q L g v) ::
      ((checkedCode Q L g w).facts d.c ++ dF Q L g d ++ [(payReg b h, v)]))
    fun R hR => by
      rw [show Tag.val Q L g d .stride = u32 Q.pageRows from rfl,
        show Tag.val Q L g d .oy = u32 (Q.headRows * (L.ctaidOf (g / L.block)).get .y) from rfl,
        mad_row]
      exact holds_update_cons hR (fresh_loaded hs hf (fun τ hτ => (row_fresh b h).2.1 τ hτ) hp)
  refine lb_reach_of hs hQ (by rw [hq, ← hpc]; exact hseg) ?_
  · intro R hR
    simp only [newFacts, newTags, hbh, ite_false, List.map_cons, List.map_nil]
    exact ⟨by simpa [Tag.val, hQ.2] using hR.1, trivial⟩

theorem load_regs (b : Fin 3) (h : Fin 2) : (loadOp b h).regs = [payReg b h] := rfl

/-- **The data step of a block-table load**, from the `Reach` after it. -/
theorem lb_step_of {Q L g w} (d : D) (b : Fin 3) (h : Fin 2) (hs : d.c.site = .lb b h)
    (hR : ∀ (d' : D) (v : Value), d'.c = {d.c with site := lbNext b h} ∧ d'.v.pay b h = v →
      Reach kernel Assumptions.all L g ((Site.lb b h).pc + 1)
        ((checkedCode Q L g w).facts d.c ++ dF Q L g d ++ [(payReg b h, v)]) (dF Q L g d')) :
    DataStep (code Q L g w) (dF Q L g) d := by
  have hc : kernel.code[(code Q L g w).pc d]? = some ⟨none, .mem (loadOp b h)⟩ := by
    show kernel.code[d.c.site.pc]? = _
    rw [hs]; exact load_fetch b h
  intro t e u d' ins' hat hi' hc' hf hn
  exact DataStep.loadE (a := loadOp b h)
    (Q := fun (v : Value) (d' : D) => d'.c = {d.c with site := lbNext b h} ∧ d'.v.pay b h = v)
    hc rfl rfl rfl rfl (fun hm => absurd hm (by simp [loadOp, MemAccess.regs, hs]))
    (fun _ _ _ _ _ hn' hv => lb_next hs hn' rfl hv)
    (fun _ v d' t hQ hat' => by
      obtain ⟨hp0, -, hacc, hf0, hr0⟩ := hat'
      dsimp only
      rw [load_regs, hacc, List.nil_append]
      refine hR d' v hQ _ ⟨?_, rfl, rfl, ?_, ?_⟩
      · show t.pc + 1 = _
        rw [hp0]; show d.c.site.pc + 1 = _; rw [hs]
      · exact hf0
      · exact holds_loaded (w := w) b h v hs hr0) ins' hat hi' hc' hf hn

theorem fresh00 : ∀ r ∈ [494, 684, 495], r ∉ ctlLive 197 ∧
    (∀ τ ∈ tags (.lb 0 0), τ.reg ≠ r) ∧ payReg 0 0 ≠ r := by decide +kernel

theorem mem00 : 479 ∈ ctlLive 197 ∧ .rows ∈ tags (.lb 0 0) ∧ .cols ∈ tags (.lb 0 0) ∧
    .stride ∈ tags (.lb 0 0) := by decide +kernel

theorem mul_val (a b : Nat) : Value.bits 32 (truncBits 32 (Lib.word (u32 a) * Lib.word (u32 b))) =
    u32 (a * b) := by
  rw [word_u32, word_u32, mul_trunc]
  rfl

/-- **The first block-table load** also computes the head's row and column origins. -/
theorem lb_origin {Q L g w} {d d' : D} {v : Value} (hs : d.c.site = .lb 0 0)
    (hQ : d'.c = {d.c with site := lbNext 0 0} ∧ d'.v.pay 0 0 = v) :
    Reach kernel Assumptions.all L g ((Site.lb 0 0).pc + 1)
      ((checkedCode Q L g w).facts d.c ++ dF Q L g d ++ [(payReg 0 0, v)]) (dF Q L g d') := by
  obtain ⟨hy, hrows, hcols, hst⟩ := mem00
  have hmem : ∀ τ ∈ tags (.lb 0 0), (τ.reg, τ.val Q L g d) ∈
      (checkedCode Q L g w).facts d.c ++ dF Q L g d ++ [(payReg 0 0, v)] := fun τ hτ => by
    simp only [List.mem_append, dF, List.mem_map]
    exact .inl (.inr ⟨τ, by rw [hs]; exact hτ, rfl⟩)
  have hpc : d.c.site.pc = 197 := by rw [hs]; rfl
  have hy' : (479, u32 ((L.ctaidOf (g / L.block)).get .y)) ∈
      (checkedCode Q L g w).facts d.c ++ dF Q L g d ++ [(payReg 0 0, v)] := by
    simp only [List.mem_append]
    refine .inl (.inl ?_)
    change _ ∈ factsFrom (ctlLive d.c.site.pc) (valueOf Q L g w d.c)
    rw [hpc]
    exact mem_factsFrom hy
  have hfr : ∀ r ∈ [494, 684, 495], r ∉ ((checkedCode Q L g w).facts d.c ++ dF Q L g d ++
      [(payReg 0 0, v)]).map Prod.fst := fun r hr =>
    fresh_loaded hs (fun hm => (fresh00 r hr).1 hm) (fun τ hτ => (fresh00 r hr).2.1 τ hτ)
      (fresh00 r hr).2.2
  have e494 : Tag.val Q L g d .rows = u32 Q.headRows := rfl
  generalize hF0 : (checkedCode Q L g w).facts d.c ++ dF Q L g d ++ [(payReg 0 0, v)] = F0 at *
  have s1 := Lib.mulStep (L := L) (g := g) (dst := 494) (a := 530) (b := 479)
    (va := Tag.val Q L g d .rows) (vb := u32 ((L.ctaidOf (g / L.block)).get .y)) Flow.code_198
    (by decide +kernel) (hmem _ hrows) hy'
    (G := (494, u32 (Q.headRows * (L.ctaidOf (g / L.block)).get .y)) :: _)
    fun R hR => by
      rw [e494, mul_val]
      exact holds_update_cons hR (hfr 494 (by simp))
  have s2 := Lib.madStep (L := L) (g := g) (dst := 684) (a := 681) (b := 529) (c := 494)
    (F := (494, u32 (Q.headRows * (L.ctaidOf (g / L.block)).get .y)) :: F0) (va := v)
    (vb := Tag.val Q L g d .stride)
    (vc := u32 (Q.headRows * (L.ctaidOf (g / L.block)).get .y)) Flow.code_199
    (by decide +kernel) (by
      rw [← hF0]
      exact List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_singleton_self (payReg 0 0, v))))
    (List.mem_cons_of_mem _ (hmem _ hst)) (List.mem_cons_self ..)
    (G := (684, rowVal Q L g v) :: _)
    fun R hR => by
      rw [show Tag.val Q L g d .stride = u32 Q.pageRows from rfl, mad_row]
      refine holds_update_cons hR ?_
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨by decide, hfr 684 (by simp)⟩
  have s3 := Lib.mulStep (L := L) (g := g) (dst := 495) (a := 531) (b := 479)
    (F := (684, rowVal Q L g v) ::
      (494, u32 (Q.headRows * (L.ctaidOf (g / L.block)).get .y)) :: F0)
    (va := Tag.val Q L g d .cols) (vb := u32 ((L.ctaidOf (g / L.block)).get .y)) Flow.code_200
    (by decide +kernel) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hmem _ hcols)))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy'))
    (G := (495, u32 (Q.headCols * (L.ctaidOf (g / L.block)).get .y)) :: _)
    fun R hR => by
      rw [show Tag.val Q L g d .cols = u32 Q.headCols from rfl, mul_val]
      refine holds_update_cons hR ?_
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨by decide, by decide, hfr 495 (by simp)⟩
  subst hF0
  refine lb_reach_of (Q := Q) (L := L) (g := g) (w := w) hs hQ ((s1.comp s2).comp s3) ?_
  intro R hR
  obtain ⟨h495, h684, h494, -⟩ := hR
  simp only [newFacts, newTags, ite_true, and_self, List.map_cons, List.map_nil]
  exact ⟨by show R 684 = some (rowVal Q L g (d'.v.pay 0 0)); rw [hQ.2]; exact h684, h494, h495,
    trivial⟩

/-- **The data step of every block-table load.** -/
theorem lb_step {Q L g w} (d : D) (b : Fin 3) (h : Fin 2) (hs : d.c.site = .lb b h) :
    DataStep (code Q L g w) (dF Q L g) d := by
  refine lb_step_of d b h hs fun d' v hQ => ?_
  by_cases h00 : b = 0 ∧ h = 0
  · obtain ⟨rfl, rfl⟩ := h00
    exact lb_origin hs hQ
  · exact lb_row h00 hs hQ

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
