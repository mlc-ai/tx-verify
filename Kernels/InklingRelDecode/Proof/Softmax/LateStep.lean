-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.LateDiv
public import Kernels.InklingRelDecode.Proof.Softmax.LatePack
public import Kernels.InklingRelDecode.Proof.Softmax.LateSingles
public import Kernels.InklingRelDecode.Proof.Lib.AlphaAt
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Lemmas.Flow.TypedSingleG

@[expose] public section

/-! # The single pieces of the data lanes, proved once

`SingleStep` (`Lemmas/Flow/TypedSingleG.lean`) at every pc of the softmax and epilogue outside the
software `exp2` blocks: the instruction is one of the single forms, and the fact `LateR` of the
states the lane reaches (`Iface.LateValues.noDecline`, `Iface.LateValues.pack`) is all it needs
beyond the tags of its operands. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Assumption
open PTX.Kernels.InklingRelDecode.Proof.Iface PTX.Kernels.InklingRelDecode.Proof.Lib

noncomputable section
variable {L : Launch} {g : Nat}

/-- The pcs of the softmax and the epilogue outside the software `exp2` blocks. -/
def lateRange (pc : Nat) : Bool :=
  ((574 ≤ pc && pc < 2331) || (2560 ≤ pc && pc < 2853)) && !Assumptions.emuSites.contains pc

/-- What the single pieces use of a state the lane reaches. -/
def LateR (L : Launch) (g : Nat) (t : TState) : Prop :=
  (declinePc t.pc = true → ∀ i, kernel.code[t.pc]? = some i → execIdealFloat L g t i.op ≠ none) ∧
  (packPc t.pc = true → ∀ c, kernel.code[t.pc]? = some ⟨none, .cvt c⟩ →
    ∀ r ∈ c.srcs, ∀ a, r = .reg a → ∃ x : EReal, readERealOpnd t .f32 r = some (.ok x))

/-- The floating operation of the instruction at a pc. -/
def fop (pc : Nat) : Option FOp :=
  match kernel.code[pc]? with
  | some ⟨_, .float f⟩ => some f.op
  | _ => none

/-- The pcs a window may take as single pieces: the only `neg` and `lg2` are at the single
readings' pcs. -/
def lateOk (pc : Nat) : Bool :=
  lateRange pc && (fop pc != some .neg || pc == 807) && (fop pc != some .lg2 || pc == 2562)

theorem fop_special : fop 600 = some .div ∧ fop 807 = some .neg ∧ fop 2562 = some .lg2 := by
  decide +kernel

theorem ideal_five {f : FloatForm} {t : TState}
    (hf : f ∈ [.add .f32, .subRn .f32, .mul .f32, .addRnF32x2, .mulF32x2])
    (h : Assumptions.emuSites.contains t.pc = false) : IdealAt Assumptions.all f L g t := by
  show IdealAt (Assumption.idealReal _ _ _ :: _) f L g t
  exact idealAt_head (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl <;> decide) (segFree h).tail

theorem lateRange_emu {pc : Nat} (h : lateRange pc = true) :
    Assumptions.emuSites.contains pc = false := by
  simpa [lateRange] using (Bool.and_eq_true_iff.mp h).2

theorem declinePc_of {pc : Nat} {i : Instr} (hr : lateRange pc = true)
    (hc : kernel.code[pc]? = some i) (hd : declineOp i.op = true) : declinePc pc = true := by
  show (lateRange pc && match kernel.code[pc]? with | some i => declineOp i.op | none => false) =
    true
  rw [hr, hc]
  exact hd

theorem packPc_of {pc : Nat} {i : Instr} (hr : lateRange pc = true)
    (hc : kernel.code[pc]? = some i) (hd : packOp i.op = true) : packPc pc = true := by
  show (lateRange pc && match kernel.code[pc]? with | some i => packOp i.op | none => false) = true
  rw [hr, hc]
  exact hd

/-- **The single pieces of the data lanes** at the pcs `lateOk` takes. -/
theorem single_step {pc : Nat} (hk : lateOk pc = true) :
    SingleStep kernel Assumptions.all L g (LateR L g) pc := by
  intro op nd hc hn t hpc hT hR
  subst hpc
  have hr : lateRange t.pc = true := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hk).1).1
  have hemu := lateRange_emu hr
  cases singleNeeds_sound hn with
  | scalar o fz d a b ho ha hb =>
    obtain ⟨va, hva, hda⟩ := d32o_is (L := L) (g := g) ha hT
    obtain ⟨vb, hvb, hdb⟩ := d32o_is (L := L) (g := g) hb hT
    have hnd := hR.1 (declinePc_of hr hc (by rcases ho with rfl | rfl | rfl <;> rfl)) _ hc
    rcases ho with rfl | rfl | rfl
    · obtain ⟨v, hv, hdv⟩ := addD_step (ideal_five (by simp) hemu) hva hvb hda hdb hnd
      exact ⟨v, hv, _, rfl, hdv⟩
    · obtain ⟨v, hv, hdv⟩ := subD_step (ideal_five (by simp) hemu) hva hvb hda hdb hnd
      exact ⟨v, hv, _, rfl, hdv⟩
    · obtain ⟨v, hv, hdv⟩ := mulD_step' (ideal_five (by simp) hemu) hva hvb hda hdb hnd
      exact ⟨v, hv, _, rfl, hdv⟩
  | pair o d x y ho =>
    have hx : d64 [(x, .dat64), (y, .dat64)] x = true := by simp [d64, TagF.sat, List.lookup]
    have hy : d64 [(x, .dat64), (y, .dat64)] y = true := by
      rcases hb : (y == x) <;> simp [d64, TagF.sat, List.lookup, hb]
    obtain ⟨va, hva, hda⟩ := d64_ok hx hT
    obtain ⟨vb, hvb, hdb⟩ := d64_ok hy hT
    have hnd := hR.1 (declinePc_of hr hc (by rcases ho with rfl | rfl <;> rfl)) _ hc
    rcases ho with rfl | rfl
    · obtain ⟨v, hv, hdv⟩ := add2D_step (ideal_five (by simp) hemu) hva hvb hda hdb hnd
      exact ⟨v, hv, _, rfl, hdv⟩
    · obtain ⟨v, hv, hdv⟩ := mul2D_step (ideal_five (by simp) hemu) hva hvb hda hdb hnd
      exact ⟨v, hv, _, rfl, hdv⟩
  | neg d a ha =>
    obtain ⟨va, hva, hda⟩ := d32o_is (L := L) (g := g) ha hT
    have hp : t.pc = 807 := by
      have h2 := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hk).1).2
      simpa [fop, hc] using h2
    obtain ⟨v, hv, hdv⟩ := neg_step hp hva hda
    exact ⟨v, hv, _, rfl, hdv⟩
  | lg2 d a ha =>
    obtain ⟨va, hva, hda⟩ := d32o_is (L := L) (g := g) ha hT
    have hp : t.pc = 2562 := by
      have h2 := (Bool.and_eq_true_iff.mp hk).2
      simpa [fop, hc] using h2
    obtain ⟨v, hv, hdv⟩ := lg2_step hp hva hda
    exact ⟨v, hv, _, rfl, hdv⟩
  | pack c a b hs hd hs' hr' hp =>
    have hpk := hR.2 (packPc_of hr hc (by simp [packOp, hd, hs', hr'])) c hc
    obtain ⟨v, hv, hdv⟩ := pack_step hd hs' hr' hp hs hemu
      (hpk _ (by simp [hs]) a rfl) (hpk _ (by simp [hs]) b rfl)
    exact ⟨v, hv, _, rfl, hdv⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax
