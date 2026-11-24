-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Run
public import Lemmas.Flow.Regs
public import Lemmas.Flow.Facts

@[expose] public section

/-! # One local step from a computed result

A proof tool. Segment proofs evaluate local code by `rfl`; an instruction whose result
depends on launch data the evaluation cannot see (the cluster layout, the kernel's
parameter objects) is taken as one step whose result is computed separately, typically by
`simp` with the launch's facts. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

theorem run_local {K : Kernel} {A : List Assumption} {L : Launch} {g pc : Nat} {t t' : TState}
    {F : List (Nat × Value)} {op : Op} (hc : K.code[pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = true) (h : At t pc F) (he : execLocalA A L g t op = .ok t') :
    run K A L g 1 t = some t' := by
  simp only [run, tauStep, out, h.2.2.2.1, h.1, hc, guardHolds, hl, ↓reduceIte, he]
  rfl

/-- A register outside the live set is not among the facts. -/
theorem not_mem_factsFrom {live : List Nat} {val : Nat → Value} {r : Nat}
    (hr : r ∉ live) : ∀ p ∈ factsFrom live val, p.1 ≠ r := by
  intro p hp he
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hp
  exact hr (he ▸ hr')

/-- A shared pointer register read as a shared address. -/
theorem readSharedAddress_ptr {L : Launch} {g w : Nat} {gen cl : Bool} {t : TState} {r : Nat}
    {cta : Nat} {off : BitVec 64}
        (hr : t.regs r = some (.ptr w gen (.shared (g / L.block) cta) off))
    (hw : w = 32 ∨ w = 64) (hg : g < L.threads) (hcta : cta < L.grid)
    (hcl : L.clusterOfCta cta = L.clusterOfCta (g / L.block)) (hc : cl = true ∨ cta = g / L.block)
    (hgc : gen = true ∨ cl = true) (hoff : off.toNat < 2 ^ 32) :
    readSharedAddress L g t w gen cl (.reg r) = .ok ⟨.shared, cta, off.toNat⟩ := by
  have h32 : off.toNat < 4294967296 := hoff
  simp [readSharedAddress, readValue, readReg, hr, hw, hg, hcta, hcl, hc, hgc, h32, bind,
    Except.bind, pure, Except.pure]

/-- An integer register read as a shared address of the thread's own CTA. -/
theorem readSharedAddress_bits {L : Launch} {g w : Nat} {cl : Bool} {t : TState} {r : Nat}
    {x : Nat} (hr : t.regs r = some (.bits w (BitVec.ofNat 64 x)))
    (hw : w = 32 ∨ w = 64) (hg : g < L.threads) (hcta : g / L.block < L.grid) (hx : x < 2 ^ 32) :
    readSharedAddress L g t w false cl (.reg r) = .ok ⟨.shared, g / L.block, x⟩ := by
  have h64 : x < 18446744073709551616 := by omega
  have h32 : x < 4294967296 := hx
  have hw' : w ≤ 64 := by omega
  have ht : truncBits w (BitVec.ofNat 64 x) = BitVec.ofNat 64 x := by
    rcases hw with rfl | rfl
    · exact truncBits_ofNat hx (by decide)
    · exact truncBits_ofNat (by omega) (by decide)
  simp [readSharedAddress, readValue, readReg, hr, hw, ht, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h64, hg, hcta, h32, bind, Except.bind, pure, Except.pure]

/-- `cvta` of a shared address register to a generic or `.shared::cluster` pointer. No assumption
of `A` names the instruction (`hL`), since the local step consults the assumptions before the
Core rule. -/
theorem exec_cvtaShared {A : List Assumption} {L : Launch} {g w : Nat} {toShared cl : Bool}
    {t : TState} {d : Nat} {a : Opnd} {loc : Loc}
    (hl : readSharedAddress L g t w toShared cl a = .ok loc)
    (hk : (toShared && !cl) = false := by decide)
    (hL : ∀ b ∈ A, b.localRule L g t
      (.addr (.cvta toShared (.shared (if cl then .cluster else .cta)) w d a)) = none)
    (hA : Assumption.SegFreePc A t.pc := by seg_free) :
    execLocalA A L g t
        (.addr (.cvta toShared (.shared (if cl then .cluster else .cta)) w d a)) =
      .ok (next (setReg t d
        (.ptr w (!toShared) (.shared (g / L.block) loc.cta) (BitVec.ofNat 64 loc.addr)))) := by
  have hb : (SharedWindow.cta == SharedWindow.cluster) = false := rfl
  cases cl <;> cases toShared <;>
    (try simp only [Bool.not_false, Bool.and_true] at hk) <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at hL ⊢ <;>
    rw [hA.exec, execLocalRule_of_none hL, execLocal_cvta (by rfl), execCvta_shared] <;>
    simp only [hb, beq_self_eq_true, hl, bind, Except.bind, pure, Except.pure,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true] <;>
    first | rfl | exact absurd hk (by decide)

/-- Adding an immediate to a shared pointer that stays in the 32-bit window. No assumption of
`A` names the instruction (`hL`), since the local step consults the assumptions before the Core
rule. -/
theorem exec_add_sharedPtr {A : List Assumption} {L : Launch} {g w : Nat} {gen : Bool}
    {t : TState} {d r : Nat} {i c a k : Nat} {ik : IType}
    (hr : t.regs r = some (.ptr w gen (.shared i c) (BitVec.ofNat 64 a))) (hw : w = 32 ∨ w = 64)
    (ha : a + k < 2 ^ 32) (hk : k < 2 ^ 31) (hik : ik ≠ .b := by decide)
    (hL : ∀ b ∈ A, b.localRule L g t
      (.int ⟨.add, .int ik w, false, [some d], [.reg r, .imm k]⟩) = none)
    (hA : Assumption.SegFreePc A t.pc := by seg_free) :
    execLocalA A L g t (.int ⟨.add, .int ik w, false, [some d], [.reg r, .imm k]⟩) =
      .ok (next (setReg t d (.ptr w gen (.shared i c) (BitVec.ofNat 64 (a + k))))) := by
  have hka : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hkk : (truncBits w (BitVec.ofInt 64 (k : Int))).toNat = k := by
    rcases hw with rfl | rfl <;> simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt] <;>
      omega
  have hs : toSigned w (truncBits w (BitVec.ofInt 64 (k : Int))) = k := by
    rcases hw with rfl | rfl <;> unfold toSigned <;>
      simp only [BitVec.toNat_ofNat, truncBits, BitVec.toNat_ofInt] <;> split_ifs <;> omega
  have hv : BitVec.ofInt 64 ((a : Int) + k) = BitVec.ofNat 64 (a + k) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega
  have hrule : (IntInstr.mk .add (.int ik w) false [some d] [.reg r, .imm k]).rule =
      some .threadInt := by
    rcases hw with rfl | rfl <;> cases ik <;> first | rfl | exact absurd rfl hik
  have hcond : decide (a < 2 ^ 32) = true ∧ (0 : Int) ≤ (a : Int) + k ∧
      (a : Int) + k < 2 ^ 32 := by
    refine ⟨?_, by omega, by omega⟩
    simpa using (show a < 2 ^ 32 by omega)
  simp only [hA.exec, execLocalRule_of_none hL, execLocal_int hrule, execInt, DType.width,
    readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
  simp only [readBits, offsetPointer, hka, hs, hv, bind, Except.bind, pure, Except.pure]
  rw [ite_eq_left ⟨trivial, hw⟩, ite_eq_left hcond]

/-- `mapa` of an address whose mapping is known. No assumption of `A` names the instruction
(`hL`), since the local step consults the assumptions before the Core rule. -/
theorem exec_mapa {A : List Assumption} {L : Launch} {g w : Nat} {gen : Bool} {t : TState}
    {d : Nat} {a rank : Opnd} {loc peer : Loc} {rv : BitVec 64}
    (hl : readSharedAddress L g t w gen true a = .ok loc) (hr : readBits L g t 32 rank = .ok rv)
    (hp : L.mapShared (g / L.block) rv.toNat loc = some peer)
    (hL : ∀ b ∈ A, b.localRule L g t (.addr (.mapa gen w d a rank)) = none)
    (hA : Assumption.SegFreePc A t.pc := by seg_free) :
    execLocalA A L g t (.addr (.mapa gen w d a rank)) =
      .ok (next (setReg t d
        (.ptr w gen (.shared (g / L.block) peer.cta) (BitVec.ofNat 64 peer.addr)))) := by
  simp only [hA.exec, execLocalRule_of_none hL, execLocal_shared (c := .mapa gen w d a rank) rfl,
    execSharedAddress, hl, hr, hp, bind, Except.bind, pure, Except.pure]

/-- Prefetching a tensor map held in a kernel parameter object. No assumption of `A` names the
instruction (`hL`), since the local step consults the assumptions before the Core rule. -/
theorem exec_prefetchTensorMap {A : List Assumption} {L : Launch} {g w : Nat} {gen : Bool}
    {t : TState} {r : Nat} {name : String} {decl : ParamObjectDecl} {base : Nat}
    (hr : t.regs r = some (.ptr w gen (.param name) 0)) (hw : w = 32 ∨ w = 64)
    (hp : L.paramObjects name = some (decl, base))
    (hok : decl.name = name ∧ 0 < decl.bytes ∧ 0 < decl.alignment ∧ base % decl.alignment = 0 ∧
      base + decl.bytes ≤ 2 ^ w)
    (hL : ∀ b ∈ A, b.localRule L g t (.prefetchTensorMap gen w (.reg r)) = none)
    (hA : Assumption.SegFreePc A t.pc := by seg_free) :
    execLocalA A L g t (.prefetchTensorMap gen w (.reg r)) = .ok (next t) := by
  simp [hA.exec, execLocalRule_of_none hL, execLocal, Op.rule, execTensorMapPrefetch, readValue,
    readReg, hr, hw, hp, hok, bind, Except.bind, pure, Except.pure]

end
end PTX.Flow
