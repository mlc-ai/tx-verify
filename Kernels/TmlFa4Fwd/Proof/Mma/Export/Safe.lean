-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Machine
public import Lemmas.Flow.Step.ShapeRegs
public import Lemmas.Flow.UbStop
import Kernels.TmlFa4Fwd.Flow.Code.Part029
import Kernels.TmlFa4Fwd.Flow.Code.Part033
import Kernels.TmlFa4Fwd.Flow.Code.Part034
import Kernels.TmlFa4Fwd.Flow.Code.Part035
import Kernels.TmlFa4Fwd.Flow.Code.Part036
import Kernels.TmlFa4Fwd.Flow.Code.Part037
import Kernels.TmlFa4Fwd.Flow.Code.Part038
import Kernels.TmlFa4Fwd.Flow.Code.Part039
import Kernels.TmlFa4Fwd.Flow.Code.Part040
import Kernels.TmlFa4Fwd.Flow.Code.Part041
import Kernels.TmlFa4Fwd.Flow.Code.Part043
import Kernels.TmlFa4Fwd.Proof.Lib.LoadAl
import Kernels.TmlFa4Fwd.Proof.Mma.Shape
import Lemmas.Flow.LoadShared
import Lemmas.Flow.TmplOkSync
import Lemmas.Flow.WordBound

@[expose] public section

/-! # The MMA warp's polls, elections and Tensor Memory resource operations are no undefined
behaviour

A poll faults only on a misaligned barrier (`fires_wait_reg_al`); every barrier address of the
MMA warp's table is the shared base (1024-aligned, `Pre.shared`) plus a multiple of 8, the ring
slot's barrier included (`slotAddr`: plus `8 * slot`), so none does. An election with the
immediate full mask is never undefined behaviour (`elect_imm_ok`). The relinquish only needs a
launch of whole warps. `sync_safe` collects these sites; the reads, the MMAs, the commits and the
deallocation (whose address operand is the recorded allocation word `ta`, a 32-bit word only by
the reference invariant) are not covered here (`DECISIONS.md`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

/-- A shared address whose word and offset are multiples of 8 is 8-aligned. -/
theorem smLoc_al {x : BitVec 64} {off : Int} (hx : x.toNat % 8 = 0) (ho : off % 8 = 0) :
    (smLoc L g x off).addr % 8 = 0 := by
  simp only [smLoc, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  omega

theorem sbW_al (hp : Pre p L m) : (sbW L).toNat % 8 = 0 := by
  have h := hp.shared
  have : L.sharedBase < 2 ^ 64 := by omega
  simp only [sbW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]
  omega

theorem addi_al {x : BitVec 64} {n : Int} (hx : x.toNat % 8 = 0) (hn : n % 8 = 0) :
    (addi x n).toNat % 8 = 0 := by
  simp only [addi, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  omega

theorem slotAddr_al (hp : Pre p L m) (s : BitVec 64) : (slotAddr L s).toNat % 8 = 0 := by
  have h0 := sbW_al hp
  have h1 : (r32 (shl s 3)).toNat % 8 = 0 := by
    have h := toNat_shl (k := 3) s (by decide)
    rw [show ((3 : Nat) : Int) = 3 from rfl] at h
    rw [r32_of_lt (by rw [h]; omega), h]; omega
  have h2 : (r32 (sbW L)).toNat % 8 = 0 := by
    rw [r32_of_lt (by have := hp.shared; simp only [sbW, BitVec.toNat_ofNat]; omega)]; exact h0
  show (truncBits 32 (r32 (sbW L) + r32 (shl s 3))).toNat % 8 = 0
  generalize r32 (sbW L) = a at h2
  generalize r32 (shl s 3) = b at h1
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add]
  omega

/-- An election of the MMA warp is no undefined behaviour. -/
theorem elect_safe {t : TState} {dst : Option Nat} {pr : Nat} {ty : Option DType} {pc : Nat}
    {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.warp ⟨.elect, ty, [dst, some pr], [], some (.imm (-1))⟩)) e o) (f : Fault) :
    e.kind ≠ .ub f := fun hk => elect_imm_ok f (fires_ub hf hk)

set_option maxHeartbeats 4000000 in
/-- **No poll, election or Tensor Memory resource operation of the MMA warp is undefined
behaviour.** -/
theorem sync_safe (hp : Pre p L m) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (code p L g ent).AtD d t) (hc : kernel.code[(code p L g ent).pc d]? =
      some ins)
    (hf : Fires ((code p L g ent).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : (∃ k, d.site = .wt k) ∨ (∃ b l, d.site = .mw b l) ∨ (∃ b, d.site = .eq b) ∨
      (∃ b, d.site = .ep b) ∨ (∃ c, d.site = .ce c) ∨ (∃ l, d.site = .relinq l)) (f : Fault) :
    e.kind ≠ .ub f := by
  replace h : At t d.site.pc (facts p L g ent d) := h
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  have hblk : L.block % 32 = 0 := by rw [hp.block]
  have h0 := sbW_al hp
  obtain ⟨site, v⟩ := d
  intro hk
  rcases hs with ⟨k, rfl⟩ | ⟨b, l, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨l, rfl⟩
  · fin_cases k <;> site_code <;>
    · rcases fires_wait_reg_al (wx := 32) (wq := 32) (by rw [h.1]; decide)
          (reg_bits h (by lit_mem) rfl) (reg_bits h (by lit_mem) rfl) hf with
        ⟨ok, hk'⟩ | ⟨f', -, hal⟩
      · rw [hk'] at hk; cases hk
      · exact hal (smLoc_al (by first
          | exact h0
          | exact addi_al h0 (by decide)
          | exact addi_al (slotAddr_al hp _) (by decide)) (by decide))
  · fin_cases b <;> cases l <;> site_code <;>
    · rcases fires_wait_reg_al (wx := 32) (wq := 32) (by rw [h.1]; decide)
          (reg_bits h (by lit_mem) rfl) (reg_bits h (by lit_mem) rfl) hf with
        ⟨ok, hk'⟩ | ⟨f', -, hal⟩
      · rw [hk'] at hk; cases hk
      · exact hal (smLoc_al (addi_al h0 (by decide)) (by decide))
  · fin_cases b <;> site_code <;> exact elect_safe hf f hk
  · fin_cases b <;> site_code <;> exact elect_safe hf f hk
  · fin_cases b <;> site_code <;> exact elect_safe hf f hk
  · cases l <;> site_code <;>
    · refine (show eventTmpl Assumptions.all L g t _ ≠ .ub f from ?_) (fires_ub hf hk)
      simp [eventTmpl, tcTmpl, hblk, ofExec, pure, Except.pure]

set_option maxHeartbeats 4000000 in
/-- **The MMA warp's read of the allocated Tensor Memory address is no undefined behaviour**: it
reads the shared word at the shared base plus 312, 4-aligned. -/
theorem alloc_read_safe (hp : Pre p L m) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (code p L g ent).AtD d t)
    (hc : kernel.code[(code p L g ent).pc d]? = some ins)
    (hf : Fires ((code p L g ent).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : d.site = .ldAlloc) (f : Fault) : e.kind ≠ .ub f := by
  replace h : At t d.site.pc (facts p L g ent d) := h
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  have hsh := hp.shared
  obtain ⟨site, v⟩ := d
  simp only at hs
  subst hs
  intro hk
  site_code
  change Fires _ (loadTmpl Assumptions.all L g t .shared false 32 [1179] 2535 312) e o at hf
  have hr : t.regs 2535 = some (b32 L.sharedBase) :=
    (reg_of (d := ⟨.ldAlloc, v⟩) h (by lit_mem)).trans rfl
  have hea := effAddr_b32_off (L := L) (g := g) (off := 312) hr (by omega)
  rcases fires_load_al hf hea rfl hk with h0 | h0
  · simp at h0
  · simp only [List.length_cons, List.length_nil] at h0
    omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
