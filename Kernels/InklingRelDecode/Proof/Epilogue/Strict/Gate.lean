-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Addr
public import Kernels.InklingRelDecode.Proof.Lib.AddSeg
public import Lemmas.Flow.SegQDat
import Kernels.InklingRelDecode.Flow.Code.Part041

@[expose] public section

/-! # The strict address head and row selection of the epilogue (pcs 2674 to 2682)

The exact stretch 2674 to 2680 (the row index, the guard words) with one typed check, the `selp`
of the data word as a strict local piece, and the guard of the LSE store, then the branches. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption Control
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

set_option maxRecDepth 100000

variable {e : Entry} {L : Launch} {g : Nat} {v : Value}
local notation "F" => facts e L g v

theorem sel_exec (t : TState) (hp : t.pc = 2680) (hT : TypedF (lateQt 2680) t) :
    ∃ x, execLocalA Assumptions.all L g t (.int ⟨.selp, .int .b 32, false, [some 1831],
      [.imm (-8388608), .reg 524, .reg 178]⟩) = .ok (PTX.next (setReg t 1831 x)) ∧ Dat32 x := by
  have hr : (IntInstr.mk .selp (.int .b 32) false [some 1831]
      [.imm (-8388608), .reg 524, .reg 178]).rule = some .threadMove := by decide
  rw [Lib.workerSelp hr hp (by decide +kernel)]
  obtain ⟨b, hb⟩ := hT 178 (.old .pred) (by decide +kernel)
  obtain ⟨x, hx, hd⟩ := hT 524 .dat32 (by decide +kernel)
  have hx4 := hd.2.1
  cases b <;> simp [execMove, DType.width, readReg, hb, hx, readValue, readBits, Value.bytes,
    bind, Except.bind, pure, Except.pure, hx4]
  · exact ⟨x, rfl, hd⟩
  · exact ⟨_, rfl, dat32_bits _⟩

theorem tok_small (t : Nat) : token t < 11 := by
  unfold token row; omega

/-- The row index plus the first token: the addition of the first word, strictly. -/
theorem addr_2675s : Seg kernel Assumptions.all L g 1 2675 (F 2675) 2676 (F 2676) := by
  have ok : e.firstWord.regBits.isSome ∧ e.tokens * e.split + 11 < 2^31 := e.addr.good
  have small : e.tokens * e.split + token (g % L.block) < 2^31 := by
    have := tok_small (g % L.block)
    have := ok.2
    omega
  have hval : valueOf e L g v 1897 = Lib.addBase e.firstWord
      (e.tokens * e.split + token (g % L.block)) := by
    change u32 (e.firstToken + _) = Lib.addBase e.firstWord _
    have bits := ok.1
    clear small
    unfold Entry.firstToken
    cases h : e.firstWord <;> simp_all [Lib.addBase, u32]
    exact absurd ok.1 (by simp [Value.regBits])
  refine Lib.add_seg (K := kernel) (pc := 2675) (dst := 1897) (r := 610) (op := .reg 1896)
    true small Flow.code_2675 (fun t hp => Lib.workerInt (by decide) hp (by decide +kernel))
    rfl ok.1 (fun R hR => holds_mem hR (mem_factsFrom (by decide : 610 ∈ ctlLive 2675)))
    (fun t hR => Lib.delta_reg (L := L) (g := g) hR (by decide : 1896 ∈ ctlLive 2675)
      (δ := e.tokens * e.split + token (g % L.block)) (by
        change b32 _ = _
        rw [Nat.mod_eq_of_lt (by omega)]) (by omega))
    fun R hR => ?_
  rw [← hval]
  exact Lib.writeLive (by decide +kernel) hR

theorem guard_words : Seg kernel Assumptions.all L g 2 2678 (F 2678) 2680 (F 2680) := by
  have mask : Seg kernel Assumptions.all L g 1 2678 (F 2678) 2679 (F 2679) := by
    intro t ht; seg_fp ht using rfl
  have cmp : Seg kernel Assumptions.all L g 1 2679 (F 2679) 2680 (F 2680) := by
    intro t ht; seg_fp ht using rfl
  exact mask.comp cmp

/-- The row index, the first token and the guard words, as one exact stretch. -/
theorem gate_exact : Seg kernel Assumptions.all L g 6 2674 (F 2674) 2680 (F 2680) :=
  addr_2674.comp (addr_2675s.comp (addr_2676.comp (addr_2677.comp guard_words)))

theorem gate_ok : epiOk 2674 2680 = true ∧
    checkF absF5 lateQt 2674 2680 [] [] ((kernel.code.drop 2674).take (2680 - 2674)) = true := by
  decide +kernel

theorem gate_head : SegQ kernel Assumptions.all L g (QTF lateQt) 2674 (F 2674) 2680 (F 2680) :=
  segQF_of_seg_typed lateQt (Ft := []) (n := 6) gate_exact rfl (by decide)
    (by have := kernel_code_length; omega) (absF5_sound (fp3_epi gate_ok.1))
    (factTags_of_B (by rfl)) gate_ok.2

variable {R : TState → Prop}
local notation "Lane" => (fun t => QTF lateQt t ∧ TauAll kernel Assumptions.all L g R t)

/-- The `selp` of the data word writes a datum (an immediate word or the data register). -/
theorem sel_seg : SegQ kernel Assumptions.all L g
    Lane 2680 (F 2680) 2681 (F 2681) := by
  refine segQ_dat (d := 1831) Flow.code_2680 (by rfl) (by decide +kernel) ?_ ?_
    fun t hp hT _ => sel_exec t hp hT
  · intro p hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
    exact mem_factsFrom
      ((by decide +kernel : ∀ r ∈ ctlLive 2681, r ∈ ctlLive 2680 ∧ r ≠ 1831) r hr).1
  · intro p hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
    exact ((by decide +kernel : ∀ r ∈ ctlLive 2681, r ∈ ctlLive 2680 ∧ r ≠ 1831) r hr).2

theorem both_ok : epiOk 2681 2682 = true ∧
    checkF absF5 lateQt 2681 2682 [] [] ((kernel.code.drop 2681).take (2682 - 2681)) = true := by
  decide +kernel

theorem both_seg : SegQ kernel Assumptions.all L g (QTF lateQt) 2681 (F 2681) 2682 (F 2682) := by
  have one : Seg kernel Assumptions.all L g 1 2681 (F 2681) 2682 (F 2682) := by
    intro t ht; seg_fp ht using rfl
  exact segQF_of_seg_typed lateQt (Ft := []) (n := 1) one rfl (by decide)
    (by have := kernel_code_length; omega) (absF5_sound (fp3_epi both_ok.1))
    (factTags_of_B (by rfl)) both_ok.2

/-- **The row selection**: from the head of the address to the guarded LSE store. -/
theorem gate_seg : SegQ kernel Assumptions.all L g
    Lane 2674 (F 2674) 2682 (F 2682) :=
  (SegQ.tauAll R gate_head).comp (sel_seg.comp (SegQ.tauAll R both_seg))

/-- **A masked LSE store** is skipped; the address chain goes on to the first word store. -/
theorem masked_seg (h : (lead (g % L.block) && e.valid) = false) : SegQ kernel Assumptions.all L g
    Lane 2682 (F 2682) 2751 (F 2751) := by
  obtain ⟨a, ins, -, -, -⟩ := store_fetch (by decide +kernel : storeCheck 2682 174 = true)
  have val : valueOf e L g v 174 = .pred false := congrArg Value.pred h
  have skip := SegQF.skipG (A := Assumptions.all) (L := L) (g := g) (qt := lateQt)
    (G := F 2683) ins (fun _ hR => holds_mem hR (mem_factsFrom_eq (by decide) val)) rfl
    (fun _ hR => holds_of_forall fun p hp => holds_mem hR (fsub (v := v) (p := 2682) (q := 2683)
      (by decide +kernel) p hp)) (by decide +kernel)
  exact (SegQ.tauAll R skip).comp (SegQ.tauAll R tail_seg)

/-- **The whole span from the row index to the first store site.** -/
theorem store_gate_seg : SegQ kernel Assumptions.all L g
    Lane 2674 (F 2674)
    (firstStore e.valid (lead (g % L.block))).pc
    (F (firstStore e.valid (lead (g % L.block))).pc) := by
  refine gate_seg.comp ?_
  cases ok : e.valid
  · simp only [firstStore, Bool.false_eq_true, ↓reduceIte]
    exact (masked_seg (by simp [ok])).comp (skip_stores R ok (n := 0) (by decide))
  · cases lane : lead (g % L.block)
    · simp only [firstStore, Bool.false_eq_true, ↓reduceIte]
      exact masked_seg (by simp [lane])
    · simp only [firstStore, ↓reduceIte]
      exact SegQ.weaken fun _ h => h

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
