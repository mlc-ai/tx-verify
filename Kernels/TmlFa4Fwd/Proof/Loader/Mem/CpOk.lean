-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.WordAlign
public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
public import Lemmas.Flow.UbStop
import Lemmas.Protocol.CpAsync

@[expose] public section

/-! # The facts a loader row copy needs

Core's `cpAsyncTmpl` faults when an address is not a multiple of the copy size or the source size
exceeds it (THREAD-CP-ASYNC). A row copy is `cp.async` of 16 bytes: its shared destination is a
swizzled row base plus multiples of 16 (`Al 4` of the register word, by the closure of
`WordAlign.lean`), its global source a row address, whose low word is a multiple of 16 (`AOk`),
plus the lane's column offset (a multiple of 16) and 0 or 128, and its source size 16 or 0
(`cp_ok`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

theorem al4_m16 {x : BitVec 64} (h : Al 4 x) : x.toNat % 16 = 0 := h

/-- **A 16-byte `cp.async` with a source-size register has a rule** when its destination word
plus offset and its source word plus offset are multiples of 16 and the size is at most 16. -/
theorem cp_ok {A : List Assumption} {t : TState} {db sb r : Nat} {doff soff : Int}
    {x y z : BitVec 64} {f : Fault}
    (hu : eventTmpl A L g t (.cpAsync db doff sb soff 16 (.size (.reg r)) none) = .ub f)
    (hd : t.regs db = some (.bits 32 x)) (hs : t.regs sb = some (.bits 64 y))
    (hr : t.regs r = some (.bits 32 z)) (hx : Al 4 x) (hdo : 0 ≤ doff ∧ doff % 16 = 0)
    (hy : y.toNat % 16 = 0) (hso : 0 ≤ soff ∧ soff % 16 = 0) (hz : (truncBits 32 z).toNat ≤ 16) :
    False := by
  have hx' := al4_m16 hx
  have hD : effAddr L g t .shared db doff =
      .ok ⟨.shared, g / L.block, (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 doff)).toNat⟩ := by
    simp [effAddr, sharedEffAddr, readReg, readBits, hd, bind, Except.bind, pure, Except.pure]
  have hS : effAddr L g t .global sb soff =
      .ok ⟨.global, 0, (truncBits 64 y + BitVec.ofInt 64 soff).toNat⟩ := by
    simp [effAddr, readReg, readBits, hs, bind, Except.bind, pure, Except.pure]
  have hal1 : (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 doff)).toNat % 16 = 0 := by
    obtain ⟨h0, h1⟩ := hdo
    simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
    have e : ((doff % ((2 ^ 64 : Nat) : Int)).toNat) % 16 = 0 := by omega
    generalize (doff % ((2 ^ 64 : Nat) : Int)).toNat = b at e ⊢
    omega
  have hal2 : (truncBits 64 y + BitVec.ofInt 64 soff).toNat % 16 = 0 := by
    obtain ⟨h0, h1⟩ := hso
    simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
    have e : ((soff % ((2 ^ 64 : Nat) : Int)).toNat) % 16 = 0 := by omega
    generalize (soff % ((2 ^ 64 : Nat) : Int)).toNat = b at e ⊢
    omega
  have hN : cpAsyncSourceSize L g t 16 (.size (.reg r)) = .ok (truncBits 32 z).toNat :=
    cpAsyncSourceSize_size (v := truncBits 32 z)
      (by simp [readBits, readReg, hr, bind, Except.bind, pure, Except.pure]) hz
  have hT := cpAsyncTmpl_copy (L := L) (g := g) (t := t) (policy := none) hD hS
    ⟨by decide, hal1, hal2⟩ hN rfl
  have hE : eventTmpl A L g t (.cpAsync db doff sb soff 16 (.size (.reg r)) none) =
      cpAsyncTmpl L g t (.cpAsync db doff sb soff 16 (.size (.reg r)) none) := rfl
  rw [hE, hT] at hu
  cases hu

/-- A register's value at a loader state is the table's. -/
theorem lreg {d : D} {t : TState} {r : Nat} {v : Value} (h : (code p L g w ent).AtD d t)
    (hr : r ∈ Flow.live d.site.pc) (hv : valueOf p L g w ent d r = v) : t.regs r = some v :=
  (holds_mem h.2.2.2.2 (mem_factsFrom hr)).trans (congrArg some hv)

/-! ### The row words modulo 16 -/

theorem pair_m16 {x0 x1 : BitVec 64} (h : x0.toNat % 16 = 0) :
    (x0 ||| x1 <<< 32).toNat % 16 = 0 := by
  have h1 : (x1 <<< 32).toNat % 16 = 0 := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    rw [Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 64)]
    exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (by decide) _)
  have := @al_or 4 _ _ h h1
  exact this

theorem wideU2_m16 {x : BitVec 64} (h : Al 3 x) : (wideU2 x).toNat % 16 = 0 := by
  have h2 : (i32 2).toNat = 2 := by decide
  unfold Al at h
  simp only [wideU2, mulWide, h2]
  simp only [show ((some IType.u == some IType.s) = true) = False by decide, ite_false,
    BitVec.toNat_ofNat, r32, truncBits]
  have : x.toNat % 2 ^ 32 % 8 = 0 := by omega
  omega

theorem and112_m16 (x : BitVec 64) : (and64 (zext x) 112).toNat % 16 = 0 := by
  have h : Al 4 (m64 112) := by unfold Al; decide
  exact al4_m16 (al_and_right h)

theorem al_tidc (L : Launch) (g : Nat) : Al 3 (Epilogue.andi (Epilogue.shl (tidW L g) 3) 56) := by
  apply al_andi; unfold Al; decide

theorem al_shl1 {x : BitVec 64} (h : Al 3 x) : Al 4 (Epilogue.shl x 1) := by
  unfold Al at h ⊢
  unfold Epilogue.shl
  have h1 : (i32 1).toNat = 1 := by decide
  rw [h1]
  simp only [show ¬ (1 ≥ 32) by decide, ↓reduceIte, truncBits, BitVec.toNat_ofNat,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, r32]
  omega

/-- The columns of a lane's rows in a warm or steady round, doubled: a multiple of 16. -/
theorem al_rowsAt (hp : Pre p L m) (g : Nat) :
    Al 4 (rowsAt L g (Epilogue.andi (Epilogue.shl (tidW L g) 3) 56)) := by
  have hsb : Al 4 (Mma.sbW L) := by
    have := hp.shared.1
    unfold Al Mma.sbW; simp only [BitVec.toNat_ofNat]; omega
  unfold rowsAt
  refine al_add32 (by decide) hsb (al_or ?_ ?_)
  · apply al_r32 (k := 4) (by decide); apply al_andi; unfold Al; decide
  · exact al_r32 (k := 4) (by decide) (al_shl1 (al_tidc L g))

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
