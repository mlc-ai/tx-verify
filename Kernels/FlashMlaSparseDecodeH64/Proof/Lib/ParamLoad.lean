-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamObj
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Seg
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.ParamObject
public import Lemmas.Flow.Local

@[expose] public section

/-! # `ld.param` of `param_0` through its pointer register, as one segment step

Every role reads the scalar parameters through the pointer register `%rd2` (register 2991,
`.ptr 64 false (.param "…_param_0") 0`). The symbolic walk of a segment evaluates such a load only
under the explicit launch (`p0_eq`), which for a symbolic field costs more than a declaration's
heartbeats. `seg_ldParam0` is the step as a lemma: the loaded register holds the field's
little-endian number (`leNat x 0 n`, the term the value tables write as `pw`/`pw8`). Moved from the
old tree's `Proof/Thread/Wg1Idle.lean` (`exec_ldParamReg`, `asms_localRule_mem`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The register facts of a concrete state. -/
theorem atHolds {t : TState} {pc : Nat} {F : List (Nat × Value)} (h : At t pc F) :
    Holds t.regs F := by
  obtain ⟨-, -, -, -, hF⟩ := h
  exact hF

/-- The `ld.param` access of a by-value parameter object through a 64-bit pointer register. -/
def paramLoad (ty : DType) (off r d : Nat) : MemAccess :=
  { kind := .load, space := some .param, sem := .weak, elem := ty, vec := 1, ext := .same,
    addr := { base := .reg r 64, off := (off : Int) }, dsts := [some d] }

/-- No assumption of the kernel's list has a local rule for an `ld.param` outside the
parameter-pointer sites. -/
theorem asms_localRule_ldParam {t : TState} {a : MemAccess} (h1 : t.pc ∉ paramAdds)
    (h2 : t.pc ∉ prefetchTensorMapSites) : ∀ b ∈ asms, b.localRule L g t (.mem a) = none := by
  intro b hb
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Assumption.idealReal_localRule_none (fun f hf => by
      simp [Assumption.FloatForm.ofOp] at hf)
  · exact Assumption.approxExact_localRule_none (fun f hf => by
      simp [Assumption.ApproxForm.ofOp] at hf)
  · simp only [Assumptions.mulBf16x2]
  · simp only [Assumptions.cvtBf16x2]
  · simp only [Assumptions.cvtUe8m0]
  · simp only [Assumptions.lg2Exact]
  · rfl
  · simp [Assumptions.paramPointers, h1, h2]
  · rfl
  · simp [Assumptions.sharedBits, Assumptions.deadPackRule]
  · rfl

/-- `ld.param` of one element of a by-value parameter object named by a register. -/
theorem ldParamReg_exec {w off r d : Nat} {t : TState} {p : String} {ty : DType}
    {decl : ParamObjectDecl} {base : Nat}
    (hrp : t.regs r = some (.ptr 64 false (.param p) 0))
    (hobj : L.paramObjects p = some (decl, base))
    (hsz : off + w / 8 ≤ decl.bytes)
    (halign : 0 < w / 8 ∧ off % (w / 8) = 0 ∧ decl.alignment % (w / 8) = 0)
    (hsup : ParamSupplied L p off (w / 8))
    (hA : Assumption.SegFreePc asms t.pc)
    (hL : ∀ b ∈ asms, b.localRule L g t (.mem (paramLoad ty off r d)) = none)
    (hw : ty.width = w) (hr : (paramLoad ty off r d).rule = some .threadMove) :
    execLocalA asms L g t (.mem (paramLoad ty off r d)) =
      .ok (PTX.next (setReg t d (paramElem w w (paramNat L p off (w / 8))))) := by
  subst hw
  have ho : (off : Int).toNat = off := Int.toNat_natCast off
  have hpo : paramObjectOf L t r (off : Int) (ty.width / 8) = .ok p := by
    simp only [paramObjectOf, readReg, hrp, hobj, Int.natCast_nonneg, ho, hsz, halign.1,
      halign.2.1, halign.2.2, pure, Except.pure, bind, Except.bind, ite_true, and_true]
  have hsup' : ParamSupplied L p off (ty.width / 8 * [d].length) := by simpa using hsup
  have hregs : ([some d].filterMap id) = [d] := rfl
  rw [hA.exec rfl, execLocalRule_of_none hL, execLocal_mem hr]
  simp only [paramLoad, execMove, MemAccess.regs, hregs, Nat.mul_one, hpo, bind, Except.bind,
    ho]
  rw [loadParamObject_eq (ds := [d]) (t := t) (off := off) hsup']
  rfl

/-- The bytes of a field read as its little-endian number. -/
theorem paramNat_leNat {p : String} {off x : Nat} :
    ∀ n k, (∀ j < n, L.paramBytes p (off + (k + j)) = some (leByteOf x (k + j))) →
      paramNat L p (off + k) n = leNat x k n
  | 0, _, _ => rfl
  | n + 1, k, h => by
    have h0 := h 0 (Nat.succ_pos n)
    simp only [Nat.add_zero] at h0
    have ih := paramNat_leNat n (k + 1) fun j hj => by
      have := h (j + 1) (by omega)
      rwa [show k + (j + 1) = k + 1 + j by omega] at this
    simp only [paramNat, leNat, h0, Option.getD_some]
    rw [show off + k + 1 = off + (k + 1) by omega, ih]

/-- **An `ld.param` of a field of `param_0` through register 2991, as one step**: the register
`d` holds the field's number. -/
theorem seg_ldParam0 (hp : Pre P L m) {pc w off d x : Nat} {ty : DType}
    {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨none, .mem (paramLoad ty off 2991 d)⟩)
    (hf : (off, x, w / 8) ∈ p0fields P L)
    (hrp : (2991, .ptr 64 false (.param (param "0")) 0) ∈ F)
    (hd : ∀ q ∈ F, q.1 ≠ d) (hsz : off + w / 8 ≤ 304)
    (hal : 0 < w / 8 ∧ off % (w / 8) = 0 ∧ 8 % (w / 8) = 0) (hw128 : w ≠ 128)
    (h1 : pc ∉ paramAdds) (h2 : pc ∉ prefetchTensorMapSites)
    (hw : ty.width = w) (hr : (paramLoad ty off 2991 d).rule = some .threadMove) :
    Seg kernel asms L g 1 pc F (pc + 1)
      ((d, .bits w (BitVec.ofNat 64 (leNat x 0 (w / 8)))) :: F) := by
  intro t ht
  have hb := p0fields_ok hp _ hf
  have hsup : ParamSupplied L (param "0") off (w / 8) := fun k hk => ⟨_, hb k hk⟩
  have hn : paramNat L (param "0") (off + 0) (w / 8) = leNat x 0 (w / 8) :=
    paramNat_leNat _ 0 fun j hj => by simpa using hb j hj
  have hL : ∀ b ∈ asms, b.localRule L g t (.mem (paramLoad ty off 2991 d)) = none :=
    asms_localRule_ldParam (by rw [ht.1]; exact h1) (by rw [ht.1]; exact h2)
  have hex := ldParamReg_exec (holds_mem (atHolds ht) hrp) hp.param0Object hsz hal hsup
    (Assumption.SegFreePc.of_eq ht.1 (noSegments.segFreePc)) hL hw hr
  refine ⟨_, run_local hc rfl ht hex, ?_⟩
  rw [Nat.add_zero] at hn
  rw [paramElem_of_ne hw128, hn]
  exact At.set ht hd

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
