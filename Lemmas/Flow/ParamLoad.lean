-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ParamObject
public import Lemmas.Flow.Local
public import Lemmas.Flow.SegFree
public import Lemmas.Flow.SegChain

@[expose] public section

/-! # `ld.param` of a by-value parameter object through its pointer register, as one step

A proof tool, generic over the kernel (promoted from FlashMLA's `Proof2/Lib/ParamLoad.lean`).
A role reads its scalar parameters with `ld.param.b<w> d, [r+off]`, where register `r` holds the
generic pointer of a by-value parameter object `p`. A symbolic walk evaluates such a load only
under a launch whose parameter bytes are explicit, which costs more than a declaration's budget
for a symbolic field. `seg_ldParam` is the step as a lemma: with no assumption taking a segment or
having a local rule at the load, and the field's bytes the little-endian bytes of `x`, register
`d` holds `x`'s number (`leNat x 0 (w / 8)`).

* `paramLoad ty off r d`: the access;
* `ldParamReg_exec`: its step, `paramElem` of the field's bytes;
* `paramNat_leNat`: the bytes `leByteOf x` read as `leNat x`;
* `seg_ldParam`: the segment of one step;
* `seg_of_localRule`: the hook for a step an assumption's local rule defines (a kernel's pointer
  arithmetic on a parameter, as FlashMLA's `paramPointers`): one segment step from the step of
  `execLocalRule` at every state with the facts. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The little-endian number of the `n` bytes of `x` from byte `k`. -/
def leNat (x : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => (leByteOf x k).toNat + 256 * leNat x (k + 1) n

/-- The `ld.param` access of a by-value parameter object through a 64-bit pointer register. -/
def paramLoad (ty : DType) (off r d : Nat) : MemAccess :=
  { kind := .load, space := some .param, sem := .weak, elem := ty, vec := 1, ext := .same,
    addr := { base := .reg r 64, off := (off : Int) }, dsts := [some d] }

/-- **`ld.param` of one element of a parameter object named by a register.** -/
theorem ldParamReg_exec {w off r d : Nat} {t : TState} {p : String} {ty : DType}
    {decl : ParamObjectDecl} {base : Nat}
    (hrp : t.regs r = some (.ptr 64 false (.param p) 0))
    (hobj : L.paramObjects p = some (decl, base))
    (hsz : off + w / 8 ≤ decl.bytes)
    (halign : 0 < w / 8 ∧ off % (w / 8) = 0 ∧ decl.alignment % (w / 8) = 0)
    (hsup : ParamSupplied L p off (w / 8))
    (hA : SegFreePc A t.pc)
    (hL : ∀ b ∈ A, b.localRule L g t (.mem (paramLoad ty off r d)) = none)
    (hw : ty.width = w) (hr : (paramLoad ty off r d).rule = some .threadMove) :
    execLocalA A L g t (.mem (paramLoad ty off r d)) =
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

/-- **An `ld.param` of a field through the parameter's pointer register, as one step**: register
`d` holds the field's number, every other fact stays. -/
theorem seg_ldParam {pc w off r d x base : Nat} {p : String} {decl : ParamObjectDecl}
    {ty : DType} {F : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨none, .mem (paramLoad ty off r d)⟩)
    (hobj : L.paramObjects p = some (decl, base))
    (hb : ∀ j < w / 8, L.paramBytes p (off + j) = some (leByteOf x j))
    (hrp : (r, .ptr 64 false (.param p) 0) ∈ F)
    (hd : ∀ q ∈ F, q.1 ≠ d) (hsz : off + w / 8 ≤ decl.bytes)
    (hal : 0 < w / 8 ∧ off % (w / 8) = 0 ∧ decl.alignment % (w / 8) = 0) (hw128 : w ≠ 128)
    (hS : SegFreePc A pc)
    (hL : ∀ t : TState, t.pc = pc → ∀ b ∈ A, b.localRule L g t (.mem (paramLoad ty off r d)) = none)
    (hw : ty.width = w) (hr : (paramLoad ty off r d).rule = some .threadMove) :
    Seg K A L g 1 pc F (pc + 1) ((d, .bits w (BitVec.ofNat 64 (leNat x 0 (w / 8)))) :: F) := by
  intro t ht
  have hsup : ParamSupplied L p off (w / 8) := fun k hk => ⟨_, hb k hk⟩
  have hn : paramNat L p (off + 0) (w / 8) = leNat x 0 (w / 8) :=
    paramNat_leNat _ 0 fun j hj => by simpa using hb j hj
  have hex := ldParamReg_exec (holds_mem ht.2.2.2.2 hrp) hobj hsz hal hsup
    (SegFreePc.of_eq ht.1 hS) (hL t ht.1) hw hr
  refine ⟨_, run_local hc rfl ht hex, ?_⟩
  rw [Nat.add_zero] at hn
  rw [paramElem_of_ne hw128, hn]
  exact At.set ht hd

/-- **One step given by the local rule** (an assumption's or Core's) at every state with the
facts `F`, where no assumption takes a segment, as a segment. -/
theorem seg_of_localRule {pc : Nat} {op : Op} {F G : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true) (hS : SegFreePc A pc)
    (hstep : ∀ t, At t pc F → ∃ t', execLocalRule A L g t op = .ok t' ∧ At t' (pc + 1) G) :
    Seg K A L g 1 pc F (pc + 1) G := by
  intro t ht
  obtain ⟨t', he, ht'⟩ := hstep t ht
  exact ⟨t', run_local hc hl ht (by rw [hS.exec ht.1]; exact he), ht'⟩

end
end PTX.Flow
