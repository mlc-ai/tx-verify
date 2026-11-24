-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Local
public import Lemmas.Flow.Hooks

@[expose] public section

/-! # Reads of by-value parameter objects

A proof tool. `ld.param` of a by-value parameter object reads the bytes the host passed
(`Launch.paramBytes`), which a segment's evaluation cannot see. `paramNat` is the
little-endian number those bytes form, and `exec_ldParamObject` takes the read as one local
step (`run_local`) once the launch supplies every byte read: register `j` of the destination
list receives element `j`, zero-extended. `exec_ldParam` does the same for a scalar
parameter. `explicitObject` writes an object's declaration and the bytes of the fields a kernel
reads into the launch, so that `seg_fp`/`seg_sym` evaluate those reads under it, and
`explicitObject_eq` returns to the launch (the object form of `explicitParams`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- The little-endian number in the `n` bytes of parameter object `name` from byte `off`; a
byte the launch does not supply counts as zero. -/
def paramNat (L : Launch) (name : String) (off : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ((L.paramBytes name off).getD 0).toNat + 256 * paramNat L name (off + 1) n

/-- The launch supplies the `n` bytes of parameter object `name` from byte `off`. -/
def ParamSupplied (L : Launch) (name : String) (off n : Nat) : Prop :=
  ∀ k < n, ∃ b, L.paramBytes name (off + k) = some b

theorem paramObjectBits_eq {L : Launch} {name : String} :
    ∀ {off n : Nat}, ParamSupplied L name off n →
      paramObjectBits L name off n = .ok (paramNat L name off n)
  | _, 0, _ => rfl
  | off, n + 1, h => by
    obtain ⟨b, hb⟩ := h 0 (Nat.succ_pos n)
    have hr : ParamSupplied L name (off + 1) n := fun k hk => by
      obtain ⟨b', hb'⟩ := h (k + 1) (by omega)
      exact ⟨b', by rw [show off + 1 + k = off + (k + 1) by omega]; exact hb'⟩
    rw [Nat.add_zero] at hb
    simp only [paramObjectBits, paramNat, hb, paramObjectBits_eq hr, Option.getD_some, bind,
      Except.bind, pure, Except.pure]

/-- The registers after loading consecutive `w`-bit elements from byte `off` into `ds`. -/
def loadParamRegs (L : Launch) (w dw : Nat) (p : String) (t : TState) : Nat → List Nat → TState
  | _, [] => t
  | off, d :: ds =>
    loadParamRegs L w dw p (setReg t d (paramElem w dw (paramNat L p off (w / 8))))
      (off + w / 8) ds

theorem loadParamObject_eq {L : Launch} {w dw : Nat} {p : String} :
    ∀ {t : TState} {off : Nat} {ds : List Nat}, ParamSupplied L p off (w / 8 * ds.length) →
      loadParamObject L w dw p t off ds = .ok (loadParamRegs L w dw p t off ds)
  | _, _, [], _ => rfl
  | t, off, d :: ds, h => by
    have h1 : ParamSupplied L p off (w / 8) := fun k hk =>
      h k (by simp only [List.length_cons]; rw [Nat.mul_succ]; omega)
    have h2 : ParamSupplied L p (off + w / 8) (w / 8 * ds.length) := fun k hk => by
      obtain ⟨b, hb⟩ := h (w / 8 + k) (by simp only [List.length_cons]; rw [Nat.mul_succ]; omega)
      exact ⟨b, by rw [show off + w / 8 + k = off + (w / 8 + k) by omega]; exact hb⟩
    simp only [loadParamObject, loadParamRegs, paramObjectBits_eq h1, bind, Except.bind]
    exact loadParamObject_eq h2

/-- `ld.param` of a by-value parameter object whose bytes the launch supplies, as one step. The
element has type `ty` of `w` bits and the registers are `dw` bits wide (zero-extended when
`dw ≠ w`); `hr` is the rule premise (THREAD-MOVE), which holds by `rfl` for a concrete
access, and no assumption of `A` names the instruction (`hL`), since the local step consults
the assumptions before the Core rule. -/
theorem exec_ldParamObject {A : List Assumption} {L : Launch} {g w dw off : Nat} {t : TState}
    {ds : List Nat} {p : String} {ty : DType} (h : ParamSupplied L p off (w / 8 * ds.length))
    (hA : Assumption.SegFreePc A t.pc := by seg_free)
    (hL : ∀ b ∈ A, b.localRule L g t (.mem
      { kind := .load, space := some .param, sem := .weak, elem := ty, vec := ds.length,
        ext := if dw = w then .same else .zero dw, addr := ⟨.param p true, (off : Int)⟩,
        dsts := ds.map some }) = none) (hw : ty.width = w := by rfl)
    (hr : MemAccess.rule
      { kind := .load, space := some .param, sem := .weak, elem := ty, vec := ds.length,
        ext := if dw = w then .same else .zero dw, addr := ⟨.param p true, (off : Int)⟩,
        dsts := ds.map some } = some .threadMove := by rfl) :
    execLocalA A L g t (.mem
      { kind := .load, space := some .param, sem := .weak, elem := ty, vec := ds.length,
        ext := if dw = w then .same else .zero dw, addr := ⟨.param p true, (off : Int)⟩,
        dsts := ds.map some }) =
      .ok (next (loadParamRegs L w dw p t off ds)) := by
  subst hw
  have hregs : (ds.map some).filterMap id = ds := by
    induction ds <;> simp_all
  simp only [hA.exec, execLocalRule_of_none hL, execLocal_mem hr, execMove, MemAccess.regs, hregs,
    Int.toNat_natCast]
  split_ifs with hd
  · subst hd
    simp only [loadParamObject_eq h, Functor.map, Except.map]
  · simp only [loadParamObject_eq h, Functor.map, Except.map]

/-- `ld.param` of a scalar parameter the launch supplies, as one step. No assumption of `A`
names the instruction (`hL`), since the local step consults the assumptions before the Core
rule. -/
theorem exec_ldParam {A : List Assumption} {L : Launch} {g w d : Nat} {t : TState} {p : String}
    {x : BitVec 64} {ty : DType} (h : L.params p = some x)
    (hA : Assumption.SegFreePc A t.pc := by seg_free)
    (hL : ∀ b ∈ A, b.localRule L g t (.mem
      { kind := .load, space := some .param, sem := .weak, elem := ty,
        addr := ⟨.param p false, 0⟩, dsts := [some d] }) = none) (hw : ty.width = w := by rfl)
    (hr : MemAccess.rule
      { kind := .load, space := some .param, sem := .weak, elem := ty,
        addr := ⟨.param p false, 0⟩, dsts := [some d] } = some .threadMove := by rfl) :
    execLocalA A L g t (.mem
      { kind := .load, space := some .param, sem := .weak, elem := ty,
        addr := ⟨.param p false, 0⟩, dsts := [some d] }) =
      .ok (next (setReg t d (.bits w (truncBits w x)))) := by
  subst hw
  simp [hA.exec, execLocalRule_of_none hL, execLocal_mem hr, execMove, MemAccess.regs, h, pure,
    Except.pure]


/-! ### A launch with an object's bytes written out -/

/-- Byte `k` of the little-endian encoding of the number `x`. -/
def leByteOf (x k : Nat) : BitVec 8 := BitVec.ofNat 8 (x / 256 ^ k)

/-- The bytes of the fields `(offset, value, width)` of an object, little-endian, by offset. -/
def fieldBytes (fs : List (Nat × Nat × Nat)) : List (Nat × BitVec 8) :=
  fs.flatMap fun f => (List.range f.2.2).map fun k => (f.1 + k, leByteOf f.2.1 k)

/-- **The launch with by-value parameter object `name` explicit**: its declaration `decl` and the
bytes of the fields `fs`, so that a segment's evaluation of `ld.param` from those bytes computes
their little-endian number (the bytes of other offsets and objects are the launch's). -/
def explicitObject (L : Launch) (name : String) (decl : ParamObjectDecl × Nat)
    (fs : List (Nat × Nat × Nat)) : Launch :=
  { L with
    paramObjects := fun n => if n = name then some decl else L.paramObjects n
    paramBytes := fun n o => if n = name then ((fieldBytes fs).lookup o).orElse
      (fun _ => L.paramBytes n o) else L.paramBytes n o }

theorem lookup_mem_of {α β : Type} [BEq α] [LawfulBEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, l.lookup a = some b → (a, b) ∈ l
  | [], h => by simp at h
  | (x, y) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hx
      simp only [Option.some.injEq] at h
      subst h
      have : a = x := by simpa using hx
      subst this
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem_of h)

/-- **The explicit launch is the launch** when the launch declares the object as `decl` and passes
the fields' bytes. -/
theorem explicitObject_eq {L : Launch} {name : String} {decl : ParamObjectDecl × Nat}
    {fs : List (Nat × Nat × Nat)} (hd : L.paramObjects name = some decl)
    (hb : ∀ f ∈ fs, ∀ k < f.2.2, L.paramBytes name (f.1 + k) = some (leByteOf f.2.1 k)) :
    explicitObject L name decl fs = L := by
  cases L
  simp only [explicitObject, Launch.mk.injEq, true_and]
  refine ⟨funext fun n => ?_, funext fun n => funext fun o => ?_, trivial⟩
  · split_ifs with h
    · subst h; exact hd.symm
    · rfl
  · split_ifs with h
    · subst h
      cases hl : (fieldBytes fs).lookup o with
      | none => rfl
      | some b =>
        simp only [Option.orElse_some]
        have hm := lookup_mem_of hl
        simp only [fieldBytes, List.mem_flatMap, List.mem_map, List.mem_range] at hm
        obtain ⟨f, hf, k, hk, he⟩ := hm
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact (hb f hf k hk).symm
    · rfl

end

end PTX.Flow
