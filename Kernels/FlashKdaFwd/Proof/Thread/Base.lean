-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Assumptions
public import Kernels.FlashKdaFwd.Spec
public import Kernels.FlashKdaFwd.Flow.Sites
public import Kernels.FlashKdaFwd.Proof.Thread.Sites
public import Kernels.FlashKdaFwd.Proof.Thread.Kinds
public import Kernels.FlashKdaFwd.Proof.Thread.Lib
public import Kernels.FlashKdaFwd.Proof.Thread.DataLib
public import Kernels.FlashKdaFwd.Proof.Thread.EventLib
public import Kernels.FlashKdaFwd.Proof.Thread.ParamNames
public import Kernels.FlashKdaFwd.Proof.Thread.Vocab
public import Lemmas.Flow.Arith32Wide
public import Lemmas.Flow.Code
public import Lemmas.Flow.Facts
public import Lemmas.Flow.Scalars
public import Lemmas.Flow.WordRead

@[expose] public section

/-! # The register file of the thread machine

One site machine follows every thread of the kernel. Its state is a site (`Site`, generated from
the flow table) and a **register file** with three parts:

* `w`: one 64-bit word per integer register (the bits Core stores, zero-extended);
* `p`: one Boolean per predicate register;
* `x`: one value per *opaque* register (a slot; slots are rewritten with the library's
  `valueEx x l`). A register is opaque when its content derives from
  memory: what a load or a warp matrix instruction returned, and what floating-point
  instructions computed from that. The machine records such a value as it is and never judges
  it: the thread keeps its control flow and its addresses whatever the data are.

The kind of a register is static (`kind`, generated), so the value of a register at a state is
its kind applied to the file (`valueOf`), and the facts of a state are the registers live at its
site, each with that value. The transition functions (generated, `After/`) rewrite the file with
the arithmetic the local instructions perform, in the vocabulary of `Lemmas/Flow/Arith32.lean`,
so that the segment equations close by `rfl`. Nothing is derived here: no closed form, no
invariant. The machine follows every returned value, or says the thread is dead exactly when
Core faults, with one exception: at the 21 loads of the read-only offsets array it follows a
64-bit integer only and stops following (`next d e = some none`) on any other value
(`loadWord`; `Never.lean` states that this is the only case). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-- A state: the site and the register file. -/
structure D where
  site : Site
  /-- Integer registers of any width, by register id: the bits Core stores (zero-extended). -/
  w : Nat → BitVec 64
  /-- Predicate registers, by register id. -/
  p : Nat → Bool
  /-- Opaque registers, by register id: the value as an event returned it or as the data path
  computed it. -/
  x : Nat → Value

/-- The word file `w` with the registers of `l` rewritten (a register is listed once). -/
def setW (l : List (Nat × BitVec 64)) (w : Nat → BitVec 64) : Nat → BitVec 64 :=
  fun r => (l.lookup r).getD (w r)

/-- The predicate file `p` with the registers of `l` rewritten. -/
def setP (l : List (Nat × Bool)) (p : Nat → Bool) : Nat → Bool :=
  fun r => (l.lookup r).getD (p r)

/-- A read of a rewritten file at a register (for `simp`, at literal registers with the
library's `lookupLit`). -/
theorem setW_apply (l : List (Nat × BitVec 64)) (w : Nat → BitVec 64) (r : Nat) :
    setW l w r = (l.lookup r).getD (w r) := rfl

theorem setP_apply (l : List (Nat × Bool)) (p : Nat → Bool) (r : Nat) :
    setP l p r = (l.lookup r).getD (p r) := rfl

/-- A read of rewritten opaque slots (the library's `valueEx x l`: the slots of `l` rewritten). -/
theorem valueEx_apply (l : List (Nat × Value)) (x : Nat → Value) (r : Nat) :
    valueEx x l r = (l.lookup r).getD (x r) := rfl

/-- The value of register `r` at state `d`. -/
def valueOf (d : D) (r : Nat) : Value :=
  match kind r with
  | .pred => .pred (d.p r)
  | .word n => .bits n (d.w r)
  | .paramPtr i => .ptr 64 false (.param (paramName i)) 0
  | .gparamPtr i => .ptr 64 true (.param (paramName i)) 0
  | .opaque => d.x r

/-- An opaque register's value is its slot. -/
theorem valueOf_opaque {d : D} {r : Nat} (h : isOpaque r = true) : valueOf d r = d.x r := by
  simp only [valueOf, kind, h, Bool.cond_true]

/-- A register that is not opaque does not read the slots. -/
theorem valueOf_not_opaque {s s' : Site} {w : Nat → BitVec 64} {p : Nat → Bool}
    {x x' : Nat → Value} {r : Nat} (h : isOpaque r = false) :
    valueOf ⟨s, w, p, x⟩ r = valueOf ⟨s', w, p, x'⟩ r := by
  simp only [valueOf, kind, h, Bool.cond_false]
  have hk := plainKind_ne r
  cases hK : plainKind r <;> first | rfl | exact absurd hK hk

/-- **Slots written by an event or a run**: the values of the file with the slots of `E`
rewritten are the values of the file, rewritten at `E`, when `E` names opaque registers only (a
Boolean check on the literal register list). -/
theorem valueOf_ex {s : Site} {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}
    {E : List (Nat × Value)} (hE : (E.map Prod.fst).all isOpaque = true) :
    valueOf ⟨s, w, p, valueEx x E⟩ = valueEx (valueOf ⟨s, w, p, x⟩) E := by
  funext r
  by_cases hr : r ∈ E.map Prod.fst
  · have ho : isOpaque r = true := List.all_eq_true.mp hE r hr
    obtain ⟨v, hv⟩ := lookup_of_mem_keys hr
    rw [valueOf_opaque ho]
    simp [valueEx, hv]
  · rw [valueEx_of_not_mem hr]
    cases ho : isOpaque r
    · exact valueOf_not_opaque ho
    · rw [valueOf_opaque ho, valueOf_opaque ho]
      exact valueEx_of_not_mem hr x

/-- `valueOf_ex` for the registers an event wrote with the values `vs`. -/
theorem valueOf_zip {s : Site} {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}
    {ds : List Nat} {vs : List Value} (hds : ds.all isOpaque = true) :
    valueOf ⟨s, w, p, valueEx x (ds.zip vs)⟩ = valueEx (valueOf ⟨s, w, p, x⟩) (ds.zip vs) :=
  valueOf_ex (List.all_eq_true.mpr fun r hr => by
    obtain ⟨⟨a, b⟩, hm, rfl⟩ := List.mem_map.mp hr
    exact List.all_eq_true.mp hds a (List.of_mem_zip hm).1)

/-- The value a scalar load of `w` bits with extension `ext` writes for the bytes `bs`
(`loadedValue` of the instruction, by `rfl`). -/
abbrev ldVal (ext : MemExt) (w : Nat) (bs : List (Option Byte)) : Exec Value :=
  rebuild 3 bs >>= extendLoaded ext w

/-- The state after the row read of an `ldmatrix`: the second-event site `s` with the row (an
unknown byte faults the thread). -/
def ldRow (d : D) (bs : List (Option Byte)) (s : List (Option Byte) → Site) :
    Option (Option D) :=
  if bs.all Option.isSome then some (some ⟨s bs, d.w, d.p, d.x⟩) else none

/-- The state after the matrix event of an `stmatrix`: the second-event site `s` with the 16
bytes received (anything else faults the thread). -/
def stRecv (d : D) (recv : List (Option Byte)) (s : List (Option Byte) → Site) :
    Option (Option D) :=
  if recv.length = 16 ∧ recv.all Option.isSome then some (some ⟨s recv, d.w, d.p, d.x⟩) else none

theorem ldRow_ne (d : D) (bs : List (Option Byte)) (s : List (Option Byte) → Site) :
    ldRow d bs s ≠ some none := by
  unfold ldRow; split_ifs <;> simp

theorem stRecv_ne (d : D) (recv : List (Option Byte)) (s : List (Option Byte) → Site) :
    stRecv d recv s ≠ some none := by
  unfold stRecv; split_ifs <;> simp

/-- The facts of the file of `d` at program counter `pc`: the registers live there, valued by
the file. -/
abbrev factsAt (pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf d)

/-- The facts of a state: those of its file at its site. -/
abbrev facts (d : D) : List (Nat × Value) := factsAt d.site.pc d

/-- A special register's word, as `mov.u32` reads it. -/
abbrev sreg (n : Nat) : BitVec 64 := truncBits 32 (BitVec.ofNat 64 n)

/-- The bits of the scalar parameter `i` (0 when the launch does not pass it). -/
def paramBits (L : Launch) (i : Nat) : BitVec 64 := (L.params (paramName i)).getD 0

/-- The 32-bit field at byte 128 of the by-value parameter object `i`, as `ld.param.b32 r,
[obj + 128]` reads it through the object's address (the objects 0 and 10 hold there the scale of
their tensor map's first coordinate). -/
def objField (L : Launch) (i : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (paramNat L (paramName i) 128 (32 / 8))

/-- **The launch facts the thread machine needs**: the launch passes the scalar parameters the
code loads (11: the output pointer, 12: the number of tokens, 13: the number of heads, 15: the
offsets pointer, 16: the number of tiles), and declares the by-value parameter objects 0 and 10
with the four bytes at offset 128 inside them, 4-byte aligned, and supplied. Nothing is needed
for the special registers, for the addresses of the parameter objects, or for the operands of the
events. `Start.lean` proves these facts from the specification's precondition. -/
structure Launched (L : Launch) : Prop where
  param : ∀ i ∈ [11, 12, 13, 15, 16], ∃ x, L.params (paramName i) = some x
  obj : ∀ i ∈ [0, 10], ∃ decl base, L.paramObjects (paramName i) = some (decl, base) ∧
    128 + 32 / 8 ≤ decl.bytes ∧ decl.alignment % (32 / 8) = 0
  bytes : ∀ i ∈ [0, 10], ParamSupplied L (paramName i) 128 (32 / 8)

theorem Launched.p {L : Launch} (h : Launched L) {i : Nat} (hi : i ∈ [11, 12, 13, 15, 16]) :
    L.params (paramName i) = some (paramBits L i) := by
  obtain ⟨x, hx⟩ := h.param i hi
  rw [paramBits, hx]; rfl

theorem Launched.p11 {L : Launch} (h : Launched L) :
    L.params (paramName 11) = some (paramBits L 11) := h.p (by decide)
theorem Launched.p12 {L : Launch} (h : Launched L) :
    L.params (paramName 12) = some (paramBits L 12) := h.p (by decide)
theorem Launched.p13 {L : Launch} (h : Launched L) :
    L.params (paramName 13) = some (paramBits L 13) := h.p (by decide)
theorem Launched.p15 {L : Launch} (h : Launched L) :
    L.params (paramName 15) = some (paramBits L 15) := h.p (by decide)
theorem Launched.p16 {L : Launch} (h : Launched L) :
    L.params (paramName 16) = some (paramBits L 16) := h.p (by decide)

/-- The segments of the thread layer: evaluation on the footprint, each value equation by `rfl`,
else by deciding the conditions of the stated value (`sym_close`). -/
macro "th_seg" : tactic => `(tactic| (intro t h; seg_fp h using first | rfl | sym_close))

/-- `th_site [lemmas]`: one site by `site_step`. The lemmas are the site's transition equation
and transition function; the rest of the simp set reads rewritten files at literal registers and
evaluates `sel` and comparisons of closed words. -/
syntax "th_site " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| th_site [$ls,*]) => `(tactic|
      site_step trans [$ls,*, setW_apply, setP_apply, valueEx_apply, lookupLit, Option.getD_some,
          Option.getD_none, PTX.Flow.Arith32.sel, cmpLit]
        seg_by (th_seg) inv_by (exact fun _ => trivial) guard_by (trivial))

/-- `th_elect q H [lemmas]`: one election site, with the cut at `q` after the election's
guarded move and the facts `H ld b` there. -/
syntax "th_elect " term:max term:max " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| th_elect $q $H [$ls,*]) => `(tactic|
      elect_step $q $H
        trans [$ls,*, setW_apply, setP_apply, valueEx_apply, lookupLit, Option.getD_some,
          Option.getD_none, PTX.Flow.Arith32.sel, cmpLit]
        seg_by (th_seg) inv_by (exact fun _ => trivial) guard_by (trivial))

/-- `th_shfl_word [lemmas]`: one shuffle site whose received value the next instruction reads
as an integer. -/
syntax "th_shfl_word " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| th_shfl_word [$ls,*]) => `(tactic|
      shfl_word_step trans [$ls,*, setW_apply, setP_apply, valueEx_apply, lookupLit,
          Option.getD_some, Option.getD_none, PTX.Flow.Arith32.sel, cmpLit]
        seg_by (th_seg) inv_by (exact fun _ => trivial) guard_by (trivial))

/-- `C.sub d' = 0` or `C.acc d' = []` for a successor that is a literal state or a decision
tree of literal states. -/
macro "sub0" : tactic => `(tactic| first | rfl | ((repeat' split) <;> rfl))

/-- The last piece of a path: evaluated code up to the successor's site (`Local.site`). -/
macro "lsite" : tactic =>
  `(tactic| exact PTX.Kernels.FlashKdaFwd.Proof.Thread.Local.site (by lseg) (by sub0) (by sub0)
    trivial)

/-- `th_trap`: the state at a `brkpt` (decoded as `trap`): no event that continues fires. -/
macro "th_trap" : tactic => `(tactic| ev_trap)

/-- `th_load64 k hl [lemmas]`: one of the 21 loads of the offsets array, whose transition is
`loadWord e k` (`k x` the state after the code that follows the load, for the loaded 64-bit
integer `x`); `hl x` proves the outcome of that code. -/
syntax "th_load64 " term:max term:max " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| th_load64 $k $hl [$ls,*]) => `(tactic| (
      refine PTX.Flow.Code.StepAt.of ?site ?_
      case site => site_event (trivial)
      refine' (PTX.Kernels.FlashKdaFwd.Proof.Thread.step_load_o
        (nv := fun v => PTX.Kernels.FlashKdaFwd.Proof.Thread.onWord64 v $k)
        ?hc ?hk ?hnc ?he ?hregs ?hr ?hok ?herr ?hs ?ha ?hl)
      case hc => code_lookup
      case hk => rfl
      case hnc => rfl
      case he => rfl
      case hregs => rfl
      case hs => rfl
      case ha => rfl
      case hr => fact_free
      case hok =>
        intro x bs v hv
        site_norm
        simp only [$ls,*]
        exact PTX.Kernels.FlashKdaFwd.Proof.Thread.loadWord_rd hv
      case herr =>
        intro x bs f hv
        site_norm
        simp only [$ls,*]
        exact PTX.Kernels.FlashKdaFwd.Proof.Thread.loadWord_err hv
      case hl =>
        intro v
        site_norm
        exact PTX.Kernels.FlashKdaFwd.Proof.Thread.Local.onWord64 $hl))

end

end PTX.Kernels.FlashKdaFwd.Proof.Thread
