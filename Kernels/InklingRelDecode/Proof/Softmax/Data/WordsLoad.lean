-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsMid
public import Lemmas.Flow.DataLoadG
public import Lemmas.Flow.FrameTail

@[expose] public section

/-! # The bias words of the preloads and of the loop's loads

A load of one word adds its fact to those of the words before it: the successor's facts are the
state's and the new register's, and the code up to the next event writes none of them. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.EventFrame Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- Instruction `pc` is a guarded load of one register `r`. -/
def ldB (pc r : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨some (_, false), .mem a⟩ =>
    decide (a.kind = .load) && !a.nc && decide (a.ext = .same) && (a.regs == [r])
  | _ => false

theorem ldB_spec {pc r : Nat} (h : ldB pc r = true) : ∃ p a,
    kernel.code[pc]? = some ⟨some (p, false), .mem a⟩ ∧ a.kind = .load ∧ a.nc = false ∧
      a.ext = .same ∧ a.regs = [r] := by
  unfold ldB at h
  split at h
  · rename_i p a hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq] at h
    exact ⟨p, a, hc, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · cases h

/-- The facts of one more word. -/
theorem wordF_succ {reg : Nat → Nat} (hinj : ∀ a b, reg a = reg b → a = b) (ws : Nat → Value)
    (v : Value) (j : Nat) :
    (∀ x ∈ wordF reg (Function.update ws j v) (j + 1), x = (reg j, v) ∨ x ∈ wordF reg ws j) ∧
      ∀ x ∈ wordF reg ws j, x.1 ≠ reg j := by
  constructor
  · intro x hx
    simp only [wordF, List.mem_map, List.mem_range] at hx ⊢
    obtain ⟨k, hk, rfl⟩ := hx
    by_cases h : k = j
    · subst h; simp
    · exact .inr ⟨k, by omega, by simp [Function.update_of_ne h]⟩
  · intro x hx
    simp only [wordF, List.mem_map, List.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    intro h
    have := hinj _ _ h
    omega

/-- **The data step of a load of one bias word.** -/
theorem w_load {d : D} {pc r : Nat} {S : List Nat} (hpc : d.c.site.pc = pc)
    (hld : ldB pc r = true) (hSf : ∀ q ∈ S, Assumption.SegFreePc Assumptions.all q)
    (hp : (S.contains (pc + 1) || evAtB kernel (pc + 1)) = true)
    (hr : ∀ x ∈ wF d, x.1 ≠ r)
    (hn : ∀ x bs v d', rebuild 3 bs = .ok v →
      succ e L g d ⟨pc, .rd x bs⟩ = some (some d') →
      (∀ y ∈ wF d', y = (r, v) ∨ y ∈ wF d) ∧ frameSetG kernel S ((wF d').map Prod.fst) = true) :
    DataStep (codeS e L g) wF d := by
  obtain ⟨p, a, hc, hk, hnc, he, hreg⟩ := ldB_spec hld
  apply DataStep.loadG (a := a) (r := r) (gd := some (p, false))
    (by change kernel.code[d.c.site.pc]? = _; rw [hpc]; exact hc) hk hnc he hreg
    (fun _ => rfl) (fun _ => rfl)
  intro hi x bs v d' t hv hnext hat
  have hnext' : succ e L g d ⟨pc, .rd x bs⟩ = some (some d') := by
    change succ e L g d ⟨d.c.site.pc, .rd x bs⟩ = _ at hnext
    rwa [hpc] at hnext
  obtain ⟨hsub, hB⟩ := hn x bs v d' hv hnext'
  obtain ⟨hpt, hst, hat', hft, hrg⟩ := hat
  have hw := atS_wF hrg
  have hpc' : t.pc = pc := hpt.trans hpc
  refine reach_frameSetG (S := S) (F := wF d') (p := pc + 1) Lib.rulesFrame hB hSf hp
    (fun R h => h) _ ⟨by simp [hpc'], rfl, rfl, by simp [setReg, hft], ?_⟩
  refine holds_of_mem fun q w hm => ?_
  rcases hsub _ hm with h | h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp [setReg]
  · have hne := hr _ h
    simpa [setReg, Function.update_of_ne hne] using holds_mem hw h

theorem preReg_inj : ∀ a b, preReg a = preReg b → a = b := by
  intro a b h; simp only [preReg] at h; omega

theorem nxtReg_inj : ∀ a b, nxtReg a = nxtReg b → a = b := by
  intro a b h; simp only [nxtReg] at h; split_ifs at h <;> omega

/-- The positions the continuation of a preload (from the next default) runs through. -/
def preIvs0 : List (Nat × Nat) := [(681, 318), (1049, 208), (2560, 5)]

/-- ... and of a load of the loop, up to the wait. -/
def nxtIvs0 : List (Nat × Nat) := [(1125, 132)]

/-- The checks of an instruction of a continuation: a local one goes forward and writes only
the registers that `bad` allows at its position. -/
def fwdWr (bad : Nat → Nat → Bool) (ins : Instr) (pc : Nat) : Bool :=
  !ins.op.isLocal || (decide (pc < nextPc ins.op pc) && (writesRegs ins.op).all (bad pc))

/-- A preload's register is written only up to its load. -/
def preBad (pc r : Nat) : Bool := !(263 ≤ r && r < 327) || decide (pc ≤ 680 + 2 * (r - 263))

/-- A word of the loop is written only up to its load, and no pack is written. -/
def nxtBad (pc r : Nat) : Bool :=
  !(1916 ≤ r && r < 1948) && (r != 332 || decide (pc ≤ 1123)) &&
    (!(334 ≤ r && r < 397) || decide (pc ≤ 1123 + 2 * (r - 333)))

theorem pre_scan : scanOk kernel preIvs0 [] = true := by decide +kernel
theorem nxt_scan : scanOk kernel nxtIvs0 [] = true := by decide +kernel
theorem pre_fw : scanBy kernel preIvs0 (fwdWr preBad) = true := by decide +kernel
theorem nxt_fw : scanBy kernel nxtIvs0 (fwdWr nxtBad) = true := by decide +kernel
theorem pre_emu : ((pcsOf preIvs0).all fun pc => !Assumptions.emuSites.contains pc) = true := by
  decide +kernel
theorem nxt_emu : ((pcsOf nxtIvs0).all fun pc => !Assumptions.emuSites.contains pc) = true := by
  decide +kernel
theorem pre_ld : ∀ j : Fin 63, ldB (680 + 2 * j.val) (263 + j.val) = true := by decide +kernel
theorem nxt_ld : ∀ j : Fin 64, ldB (1124 + 2 * j.val) (nxtReg j.val) = true := by decide +kernel

theorem fw_of {ivs : List (Nat × Nat)} {bad : Nat → Nat → Bool}
    (h : scanBy kernel ivs (fwdWr bad) = true) :
    (∀ pc ∈ pcsOf ivs, ∀ ins, kernel.code[pc]? = some ins → ins.op.isLocal = true →
      pc < nextPc ins.op pc) ∧
    ∀ pc ∈ pcsOf ivs, ∀ ins, kernel.code[pc]? = some ins → ins.op.isLocal = true →
      ∀ r ∈ writesRegs ins.op, bad pc r = true := by
  have key : ∀ pc ∈ pcsOf ivs, ∀ ins, kernel.code[pc]? = some ins → ins.op.isLocal = true →
      pc < nextPc ins.op pc ∧ ∀ r ∈ writesRegs ins.op, bad pc r = true := by
    intro pc hp ins hc hl
    obtain ⟨ins', hc', hb⟩ := scanBy_at h
      (by rw [← pcsOf_contains]; exact List.contains_iff_mem.mpr hp)
    obtain rfl := Option.some.inj (hc.symm.trans hc')
    simpa [fwdWr, hl] using hb
  exact ⟨fun pc hp ins hc hl => (key pc hp ins hc hl).1,
    fun pc hp ins hc hl => (key pc hp ins hc hl).2⟩

theorem pre_frame {j : Nat} (hj : j < 63) :
    frameSetG kernel ((pcsOf preIvs0).filter (681 + 2 * j ≤ ·))
      ((List.range (j + 1)).map preReg) = true := by
  obtain ⟨hf, hb⟩ := fw_of pre_fw
  refine frameSetG_tail (frameSetG_of_scan pre_scan) hf ?_
  intro pc hp ha ins hc hl r hr hw
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
  have hk' := List.mem_range.mp hk
  have := hb pc hp ins hc hl (preReg k) hw
  simp [preBad, preReg, show 263 + k < 327 by omega] at this
  omega

theorem nxt_frame {j : Nat} (hj : j < 64) :
    frameSetG kernel ((pcsOf nxtIvs0).filter (1125 + 2 * j ≤ ·))
      (packK ++ (List.range (j + 1)).map nxtReg) = true := by
  obtain ⟨hf, hb⟩ := fw_of nxt_fw
  refine frameSetG_tail (frameSetG_of_scan nxt_scan) hf ?_
  intro pc hp ha ins hc hl r hr hw
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hr
    have := hb pc hp ins hc hl _ hw
    have hm' := List.mem_range.mp hm
    simp [nxtBad] at this
    omega
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    have hk' := List.mem_range.mp hk
    have := hb pc hp ins hc hl _ hw
    simp only [nxtReg] at this hw
    split_ifs at this <;> simp [nxtBad] at this <;> omega

theorem pcs_free {ivs : List (Nat × Nat)}
    (h : ((pcsOf ivs).all fun pc => !Assumptions.emuSites.contains pc) = true) :
    ∀ q ∈ pcsOf ivs, Assumption.SegFreePc Assumptions.all q := fun q hq =>
  Kernels.InklingRelDecode.Proof.segFree (by simpa using List.all_eq_true.mp h q hq)

theorem pre_pc1 {j : Nat} (hj : j < 63) :
    ((pcsOf preIvs0).filter (681 + 2 * j ≤ ·)).contains (680 + 2 * j + 1) = true := by
  simp only [List.contains_iff_mem, List.mem_filter, decide_eq_true_eq, pcsOf, preIvs0,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, List.mem_range']
  exact ⟨⟨(681, 318), by simp, 680 + 2 * j + 1 - 681, by omega⟩, by omega⟩

theorem nxt_pc1 {j : Nat} (hj : j < 64) :
    ((pcsOf nxtIvs0).filter (1125 + 2 * j ≤ ·)).contains (1124 + 2 * j + 1) = true := by
  simp only [List.contains_iff_mem, List.mem_filter, decide_eq_true_eq, pcsOf, nxtIvs0,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, List.mem_range']
  exact ⟨⟨(1125, 132), by simp, 1124 + 2 * j + 1 - 1125, by omega⟩, by omega⟩

/-- **A preload but the last** adds its word. -/
theorem w_pre {d : D} {j : Fin 64} (hs : d.c.site = .pre j) (hj : j.val < 63) :
    DataStep (codeS e L g) wF d := by
  have hr : ∀ x ∈ wF d, x.1 ≠ 263 + j.val := fun x hx => by
    simp only [wF, hs, wFS] at hx
    exact (wordF_succ preReg_inj d.v.ld dflt j.val).2 x hx
  refine @w_load e L g d (680 + 2 * j.val) (263 + j.val)
    ((pcsOf preIvs0).filter (681 + 2 * j.val ≤ ·)) (by rw [hs]; rfl) (pre_ld ⟨j.val, hj⟩)
    (fun q hq => pcs_free pre_emu q (List.mem_of_mem_filter hq))
    (Bool.or_eq_true_iff.mpr (.inl (pre_pc1 hj))) hr (fun x bs v d' hv hn => by
      obtain ⟨c', hnc, rfl⟩ := succ_inv hn
      have hjj : j.val + 1 < 64 := by omega
      simp only [Control.next, hs, hjj, ↓reduceDIte, Option.some.injEq] at hnc
      subst hnc
      have hl : Lib.loadWord bs = v := by
        unfold Lib.loadWord
        rw [hv]
        rfl
      simp only [wF, hs, wFS, record, hl, loopB]
      refine ⟨fun y hy => ?_, ?_⟩
      · have := (wordF_succ preReg_inj d.v.ld v j.val).1 y (by simpa using hy)
        simpa [preReg, wF, hs, wFS] using this
      · simpa [wordF, List.map_map, Function.comp_def] using pre_frame hj)

/-- **A load of the loop** adds its word. -/
theorem w_nxt {d : D} {j : Fin 64} (hs : d.c.site = .nxt j) : DataStep (codeS e L g) wF d := by
  have hr : ∀ x ∈ wF d, x.1 ≠ nxtReg j.val := fun x hx => by
    simp only [wF, hs, wFS, wP, wN, packF, wordF, List.mem_append, List.mem_map, List.mem_range,
      ite_true] at hx
    rcases hx with ⟨m, hm, rfl⟩ | ⟨k, hk, rfl⟩
    · simp only [nxtReg]
      split_ifs <;> omega
    · exact fun h => by have := nxtReg_inj _ _ h; omega
  refine @w_load e L g d (1124 + 2 * j.val) (nxtReg j.val)
    ((pcsOf nxtIvs0).filter (1125 + 2 * j.val ≤ ·)) (by rw [hs]; rfl) (nxt_ld j)
    (fun q hq => pcs_free nxt_emu q (List.mem_of_mem_filter hq))
    (Bool.or_eq_true_iff.mpr (.inl (nxt_pc1 j.isLt))) hr (fun x bs v d' hv hn => by
      obtain ⟨c', hnc, rfl⟩ := succ_inv hn
      have hl : Lib.loadWord bs = v := by
        unfold Lib.loadWord
        rw [hv]
        rfl
      have hw : wF ⟨c', record L d ⟨1124 + 2 * j.val, .rd x bs⟩ c'.site⟩ =
          packF d.v.cur ++ wordF nxtReg (Function.update d.v.ld j.val v) (j.val + 1) := by
        by_cases h : j.val + 1 < 64
        · simp only [Control.next, hs, h, ↓reduceDIte, Option.some.injEq] at hnc
          subst hnc
          simp [wF, wFS, wP, wN, record, hs, hl]
        · have h63 : j.val + 1 = 64 := by omega
          simp only [Control.next, hs, h, ↓reduceDIte, Option.some.injEq] at hnc
          subst hnc
          simp [wF, wFS, wP, wN, record, hs, hl, h63]
      rw [hw]
      refine ⟨fun y hy => ?_, ?_⟩
      · rcases List.mem_append.mp hy with hy | hy
        · refine .inr ?_
          simp only [wF, hs, wFS, wP, wN, ite_true]
          exact List.mem_append_left _ hy
        · rcases (wordF_succ nxtReg_inj d.v.ld v j.val).1 y hy with h | h
          · exact .inl h
          · refine .inr ?_
            simp only [wF, hs, wFS, wP, wN, ite_true]
            exact List.mem_append_right _ h
      · simpa [packF, packK, wordF, List.map_map, Function.comp_def] using nxt_frame j.isLt)

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
