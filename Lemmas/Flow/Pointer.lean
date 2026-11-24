-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Run
public import Lemmas.Flow.Regs

@[expose] public section

/-! # Offsetting and mapping shared pointers

A proof tool. Adding an immediate to a symbolic shared pointer checks that the offset stays
in the 32-bit window, and `mapa` maps an address through the launch's cluster layout; with
symbolic operands neither reduces by evaluation, so a segment proof splits at such an
instruction and uses `run_add_sharedPtr` or `run_mapa`, which take those facts as premises. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

theorem execLocal_add_sharedPtr {L : Launch} {g : Nat} {t : TState} {d r : Nat}
    {i c a k : Nat} {ik : IType}
    (hr : t.regs r = some (.ptr 32 false (.shared i c) (BitVec.ofNat 64 a)))
    (ha : a + k < 2 ^ 32) (hk : k < 2 ^ 31) (hik : ik ≠ .b := by decide) :
    execLocal L g t (.int ⟨.add, .int ik 32, false, [some d], [.reg r, .imm k]⟩) =
      .ok (next (setReg t d (.ptr 32 false (.shared i c) (BitVec.ofNat 64 (a + k))))) := by
  have hka : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hkk : (truncBits 32 (BitVec.ofInt 64 (k : Int))).toNat = k := by
    simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    omega
  have hs : toSigned 32 (truncBits 32 (BitVec.ofInt 64 (k : Int))) = k := by
    unfold toSigned
    simp only [BitVec.toNat_ofNat, truncBits, BitVec.toNat_ofInt]
    split_ifs <;> omega
  have hv : BitVec.ofInt 64 ((a : Int) + k) = BitVec.ofNat 64 (a + k) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega
  rw [execLocal_int (by cases ik <;> first | rfl | exact absurd rfl hik)]
  simp only [execInt, DType.width, readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
  have hp : decide (a < 2 ^ 32) = true := by simp; omega
  have hlo : (0 : Int) ≤ (a : Int) + k := by omega
  have hhi : (a : Int) + k < 2 ^ 32 := by omega
  simp only [readBits, offsetPointer, hka, hs, hv, hp, hlo, hhi, bind, Except.bind, pure,
    Except.pure]
  simp

/-- One local step: adding an immediate to a shared pointer register. -/
theorem run_add_sharedPtr {K : Kernel} {A : List Assumption} {L : Launch} {g pc : Nat}
    {t : TState} {F : List (Nat × Value)} {d r : Nat} {i c a k : Nat} {ik : IType}
    (hc : K.code[pc]? = some ⟨none, .int ⟨.add, .int ik 32, false, [some d], [.reg r, .imm k]⟩⟩)
    (h : At t pc F)
    (hr : (r, .ptr 32 false (.shared i c) (BitVec.ofNat 64 a)) ∈ F) (ha : a + k < 2 ^ 32)
    (hk : k < 2 ^ 31) (hik : ik ≠ .b := by decide)
    (hL : ∀ a ∈ A,
      a.localRule L g t (.int ⟨.add, .int ik 32, false, [some d], [.reg r, .imm k]⟩) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc) :
    run K A L g 1 t =
      some (next (setReg t d (.ptr 32 false (.shared i c) (BitVec.ofNat 64 (a + k))))) := by
  have hreg := holds_mem h.2.2.2.2 hr
  simp [run, tauStep, out, h.2.2.2.1, h.1, hc, guardHolds, Op.isLocal, Op.varyingSregs,
    Opnd.varying?, hA.exec, execLocalRule_of_none hL, execLocal_add_sharedPtr hreg ha hk hik,
    pure, Except.pure]

/-- A 32-bit integer register read as a shared address of the thread's own CTA. -/
theorem readSharedAddress_b32 {L : Launch} {g : Nat} {t : TState} {r : Nat} {x : Nat}
    (hg : g < L.threads) (hcta : g / L.block < L.grid) (hx : x < 2 ^ 32)
    (hr : t.regs r = some (b32 x)) :
    readSharedAddress L g t 32 false true (.reg r) = .ok ⟨.shared, g / L.block, x⟩ := by
  have h64 : x < 18446744073709551616 := by omega
  have h32 : x < 4294967296 := hx
  simp [readSharedAddress, readValue, readReg, hr, b32, truncBits_ofNat hx (by decide),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, hg, hcta, h32, bind, Except.bind, pure, Except.pure]

/-- One local step: `mapa` of an address whose mapping is known. -/
theorem run_mapa {K : Kernel} {A : List Assumption} {L : Launch} {g pc w : Nat} {gen : Bool}
    {t : TState} {F : List (Nat × Value)} {d : Nat} {a rank : Opnd} {loc peer : Loc}
    {rv : BitVec 64}
    (hc : K.code[pc]? = some ⟨none, .addr (.mapa gen w d a rank)⟩) (h : At t pc F)
    (hl : readSharedAddress L g t w gen true a = .ok loc)
    (hr : readBits L g t 32 rank = .ok rv)
    (hp : L.mapShared (g / L.block) rv.toNat loc = some peer)
    (hL : ∀ as ∈ A, as.localRule L g t (.addr (.mapa gen w d a rank)) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc) :
    run K A L g 1 t =
      some (next (setReg t d
            (.ptr w gen (.shared (g / L.block) peer.cta) (BitVec.ofNat 64 peer.addr)))) := by
  simp [run, tauStep, out, h.2.2.2.1, h.1, hc, guardHolds, Op.isLocal,
    hA.exec, execLocalRule_of_none hL, execLocal, Op.rule, AddrInstr.rule, execSharedAddress,
    hl, hr, hp, bind, Except.bind, pure, Except.pure]

end
end PTX.Flow
