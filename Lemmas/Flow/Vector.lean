-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Events
public import Lemmas.Flow.MemTmpl

@[expose] public section

/-! # Elements of four-element vector accesses

A proof tool. A `ld.v4.b32` or `st.v4.b32` from an address `loc` aligned to its 16 bytes is four
events, one per element (EXT-VECTOR-ELEM): element `t.sub` accesses the four bytes at
`loc + 4 * t.sub` (`loadTmpl_v4`, `storeTmpl_v4`). After an element that is not the last, a
load keeps the value read in `acc` and moves to the next element (`afterLoad_mid`); after the
last it writes all four destinations (`afterLoad_last`). A store moves to the next element
(`afterStore_mid`) or past the instruction (`afterStore_last`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

/-- Element `t.sub` of a four-element 32-bit vector load from an aligned address. -/
theorem loadTmpl_v4 {sp : Space} {ds : List Nat} {base : Nat} {loc : Loc}
    (heff : effAddr L g t sp base 0 = .ok loc) (hal : loc.addr % 16 = 0) (hds : ds.length = 4) :
    loadTmpl A L g t sp false 32 ds base 0 =
      .read { loc := loc.at (4 * t.sub), size := 4, elem := t.sub } (afterLoad t ds) := by
  unfold loadTmpl
  rw [heff]
  simp only [bind, Except.bind, hds]
  rw [elemAcc_ok (by decide) (by simpa using hal)]
  simp

/-- Element `t.sub` of a four-element 32-bit vector store to an aligned address: the element
source keeps its own bytes, a wider source is truncated to them (`storeValue`), and a narrower
one faults. -/
theorem storeTmpl_v4 {sp : Space} {srcs : List Opnd} {base r : Nat} {loc : Loc} {v : Value}
    (heff : effAddr L g t sp base 0 = .ok loc) (hal : loc.addr % 16 = 0) (hsrc : srcs.length = 4)
    (hs : srcs[t.sub]? = some (.reg r)) (hv : t.regs r = some v) :
    storeTmpl L g t sp 32 base 0 srcs =
      match storeValue 32 v with
      | .error f => .ub f
      | .ok v' => .write { loc := loc.at (4 * t.sub), size := 4, elem := t.sub } v'.toBytes
        (afterStore t srcs) := by
  unfold storeTmpl
  rw [heff]
  simp only [bind, Except.bind, hsrc]
  rw [elemAcc_ok (by decide) (by simpa using hal)]
  simp [hs, readValue, readReg, hv, pure, Except.pure]
  cases storeValue 32 v <;> rfl

theorem afterLoad_mid {ds : List Nat} {bs : List (Option Byte)} {v : Value}
    (hv : rebuild 3 bs = .ok v) (h : t.sub + 1 < ds.length) :
    afterLoad t ds bs = { t with sub := t.sub + 1, acc := t.acc ++ [v] } := by
  simp [afterLoad, hv, h]

theorem afterLoad_last {ds : List Nat} {bs : List (Option Byte)} {v : Value}
    (hv : rebuild 3 bs = .ok v) (h : ¬ t.sub + 1 < ds.length) :
    afterLoad t ds bs = { setRegs t ds (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] } :=
      by
  simp [afterLoad, hv, h]

theorem afterLoad_fault {ds : List Nat} {bs : List (Option Byte)} {f : Fault}
    (hv : rebuild 3 bs = .error f) : (afterLoad t ds bs).fault = some f := by
  simp [afterLoad, hv]

theorem afterStore_mid {srcs : List Opnd} (h : t.sub + 1 < srcs.length) :
    afterStore t srcs = { t with sub := t.sub + 1 } := by
  simp [afterStore, h]

theorem afterStore_last {srcs : List Opnd} (h : ¬ t.sub + 1 < srcs.length) :
    afterStore t srcs = { t with pc := t.pc + 1, sub := 0 } := by
  simp [afterStore, h]

end
end PTX.Flow
