-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.UbFree
public import Lemmas.Flow.LoadNcAt
import Lemmas.Flow.LoadShared
import Lemmas.Flow.ShflOps

@[expose] public section

/-! # Operand checks of the index warp's instructions

An `ld.global.nc` of a pair of 32-bit words through a 64-bit register whose word is 8-aligned
(`ncLoad2_ok`), a store of one or a pair of 32-bit values to shared memory through a 32-bit register
(`st32_ok`), and a butterfly shuffle of a 32-bit register (`shflReg_ok`) are no undefined
behaviour. -/

namespace PTX.Flow

open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

/-- **A `.nc` pair load at an 8-aligned address reads its element.** -/
theorem ncLoad2_eq {base : Nat} {ds : List Nat} {off : Int} {x : BitVec 64}
    (hds : ds.length = 2) (hr : t.regs base = some (.bits 64 x))
    (hal : (truncBits 64 x + BitVec.ofInt 64 off).toNat % 8 = 0)
    (hnc : A.any (·.ncLoads t.pc) = true) :
    ∃ a, loadTmpl A L g t .global true 32 ds base off = .readNC a (afterLoad t ds) := by
  unfold loadTmpl
  rw [effAddr_global_bits hr]
  simp only [bind, Except.bind, hds, Nat.reduceDiv]
  rw [elemAcc_ok (n := 4) (count := 2) (by norm_num) hal]
  simp [hnc]

/-- **A store of a pair of 32-bit values at an 8-aligned shared address writes the element's
bytes.** -/
theorem stPair_eq {base r0 r1 : Nat} {off : Int} {x : BitVec 64} {y0 y1 : BitVec 64}
    (hr : t.regs base = some (.bits 32 x)) (h0 : t.regs r0 = some (.bits 32 y0))
    (h1 : t.regs r1 = some (.bits 32 y1)) (hs : t.sub < 2)
    (hal : (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat % 8 = 0) :
    ∃ a, storeTmpl L g t .shared 32 base off [.reg r0, .reg r1] =
      .write a (Value.bits 32 (if t.sub = 0 then y0 else y1)).toBytes
        (afterStore t [.reg r0, .reg r1]) := by
  unfold storeTmpl
  rw [effAddr_shared32 hr]
  simp only [bind, Except.bind, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceDiv]
  rw [elemAcc_ok (n := 4) (count := 2) (by norm_num) hal]
  have : t.sub = 0 ∨ t.sub = 1 := by omega
  rcases this with h | h <;>
    simp [h, readValue, readReg, h0, h1, storeValue, Value.bytes, pure, Except.pure]

/-- **A byte store of a 32-bit value at a shared address writes its low byte.** -/
theorem stByte_eq {base r : Nat} {off : Int} {x y : BitVec 64}
    (hr : t.regs base = some (.bits 32 x)) (hv : t.regs r = some (.bits 32 y))
    (hs : t.sub = 0) :
    ∃ a, storeTmpl L g t .shared 8 base off [.reg r] =
      .write a (Value.bits 8 (truncBits 8 y)).toBytes (afterStore t [.reg r]) := by
  unfold storeTmpl
  rw [effAddr_shared32 hr]
  simp only [bind, Except.bind, List.length_singleton, Nat.reduceDiv]
  rw [elemAcc_ok (n := 1) (count := 1) (by norm_num) (Nat.mod_one _)]
  simp [hs, readValue, readReg, hv, storeValue, Value.bytes, Value.bitPattern, pure, Except.pure]

/-- **A butterfly shuffle of a 32-bit register fires a shuffle of its value.** -/
theorem fires_shflBfly_ok {r d p : Nat} {b c : Int} {y : BitVec 64}
    (hr : t.regs r = some (.bits 32 y))
    (hblk : L.block % 32 = 0) {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.warp ⟨.shfl .bfly, some (.int .b 32), [some d, some p],
      [.reg r, .imm b, .imm c], some (.imm (-1))⟩)) e o) :
    ∃ bv cv recv ok, e = ⟨pc, .shfl .bfly (.bits 32 y) bv cv recv ok⟩ := by
  simp only [eventTmpl] at hf
  have hw : warpTmpl L g t ⟨.shfl .bfly, some (.int .b 32), [some d, some p],
      [.reg r, .imm b, .imm c], some (.imm (-1))⟩ =
      shflTmpl L g t .bfly d (some p) (.reg r) (.imm b) (.imm c) (.imm (-1)) := by
    unfold warpTmpl
    have : WarpInstr.rule ⟨.shfl .bfly, some (.int .b 32), [some d, some p],
      [.reg r, .imm b, .imm c], some (.imm (-1))⟩ = some .threadShfl := rfl
    simp [this]
  rw [hw] at hf
  obtain ⟨recv, ok, he⟩ := fires_shflTmpl (m := truncBits 32 (BitVec.ofInt 64 (-1)))
    (av := .bits 32 y)
    (bv := truncBits 32 (BitVec.ofInt 64 b)) (cv := truncBits 32 (BitVec.ofInt 64 c))
    (by simp [readBits, pure, Except.pure]) (by simp [readValue, readReg, hr, pure, Except.pure])
    (by simp [readBits, pure, Except.pure]) (by simp [readBits, pure, Except.pure])
    (by decide) hblk rfl hf
  exact ⟨_, _, recv, ok, he⟩

end

end PTX.Flow
