-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.LateKinds
public import Kernels.InklingRelDecode.Proof.Softmax.Data.PkTyped
public import Kernels.InklingRelDecode.Proof.Softmax.GenRulesE
public import Kernels.InklingRelDecode.Proof.Lib.WinLane

@[expose] public section

/-! # The first pack's window, checked

The probability pack of pcs 951 to 998 is entered from the code after the row sum (pcs 2235 to
2330) through the update at pc 949: the window `packWin` is left by no local step and entered
only after one of the events of that code, and its instructions write none of the exponentials'
registers `pkDom`. The pack's items on the kinds of the exponentials are accepted, and each pack
reads numbers. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Lib

set_option maxRecDepth 100000

noncomputable section

/-- The positions of the update, the first pack and the code after the row sum. -/
def packWin : List (Nat × Nat) := [(949, 999), (2235, 2330)]

/-- The registers of the exponentials' pairs. -/
def pkDom : List Nat := (List.range 24).map (1994 + ·)

/-- The kinds the pack reads: pairs of numbers in `pkDom`. -/
def kPair : Nat → Kd := fun r => if 1994 ≤ r ∧ r < 2018 then Kd.pr .fl else .no

/-- The first pack's items. -/
def pk1All : List XItem := Gen.pk1_items0 ++ Gen.pk1_items1

theorem packWin_fwd : fwdOk packWin pkDom = true := by decide +kernel
theorem packWin_enter : enterOk packWin 0 = true := by decide +kernel
theorem packWin_zero : inS packWin 0 = false := by decide +kernel
theorem packWin_events : ∀ q ∈ entryEvents packWin, q = 999 ∨ (2234 ≤ q ∧ q ≤ 2329) := by
  decide +kernel
theorem packWin_keep : ∀ q ∈ entryEvents packWin, q = 999 ∨
    (match kernel.code[q]? with
      | some ins => pkDom.all (fun r => !(EventFrame.eventWrites ins.op).contains r)
      | none => true) = true := by decide +kernel
theorem pkDom_xKeys : ∀ r ∈ pkDom, r ∈ xKeys := by decide +kernel
theorem pk1_enter : enterOk [(951, 998)] 951 = true := by decide +kernel
theorem pk1_after : fwdOk [(999, 999)] [] = true := by decide +kernel
theorem pk1_kRun : kOk kPair pk1All = true := by decide +kernel
theorem pk1_sites : packSites kPair pk1All pkDom 951 = true := by decide +kernel
theorem pk1_reads : xReadsB pkDom pk1All = true := by decide +kernel
theorem pk1_local : xLocalB pk1All = true := by decide +kernel
theorem pk1_req (V : Nat → Value) : xReq V pk1All = true := by rfl
theorem pk1_at (L : Launch) (g : Nat) : OAt kernel Assumptions.all L g 951 pk1All :=
  OAt.append (Gen.pk1_at0 L g) (Gen.pk1_at1 L g)

theorem packSpec_cvtBf : PackSpec cvtBfL := fun a b ha hb => by
  obtain ⟨-, r, hr⟩ := ha
  obtain ⟨-, q, hq⟩ := hb
  have e : cvtBfE a b = .ok (.pair (.float .bf16 q) (.float .bf16 r)) := by
    simp only [cvtBfE, hr, hq, erealValue_bf16_coe]
  refine ⟨_, e, ?_⟩
  refine ⟨by rfl, ?_, ?_⟩
  · intro _ _ _ h; cases h
  · intro _ _ h; cases h

theorem kFns_of_mem : ∀ {items : List XItem}, (∀ it ∈ items, it.FnOk) → kFns items
  | [], _ => trivial
  | it :: its, h => ⟨h it (by simp), kFns_of_mem fun x hx => h x (by simp [hx])⟩

theorem fnOk_cvt (d a b : Nat) : (XItem.fn (cvtBfOp d [a, b]) d [a, b] cvtBfL).FnOk :=
  packSpec_cvtBf

theorem fnOk_base (it : OItem) : (XItem.base it).FnOk := trivial

theorem pk1_fns : kFns pk1All := by
  refine kFns_of_mem ?_
  simp only [pk1All, Gen.pk1_items0, Gen.pk1_items1, List.forall_mem_append,
    List.forall_mem_cons, fnOk_cvt, fnOk_base, and_self, List.not_mem_nil,
    false_imp_iff, implies_true]

/-! ### The second pack -/

/-- The positions of the second pack, its mask and the store with its wait. -/
def pack2Win : List (Nat × Nat) := [(1000, 1010)]

/-- The registers of the singles the second pack reads. -/
def pkS : List Nat := (List.range 16).map (508 + ·)

def kSing : Nat → Kd := fun r => if 508 ≤ r ∧ r < 524 then Kd.s .fl else .no

theorem pack2_fwd : fwdOk pack2Win pkS = true := by decide +kernel
theorem pack2_enter : enterOk pack2Win 0 = true := by decide +kernel
theorem pack2_zero : inS pack2Win 0 = false := by decide +kernel
theorem pack2_events : ∀ q ∈ entryEvents pack2Win, q = 999 ∨ q = 1009 ∨ q = 1010 := by
  decide +kernel
theorem pack2_keep : (match kernel.code[999]? with
      | some ins => pkS.all (fun r => !(EventFrame.eventWrites ins.op).contains r)
      | none => true) = true := by decide +kernel
theorem pkS_kB20 : ∀ r ∈ pkS, r ∈ kB20 := by decide +kernel
theorem pk2_late : fwdOk [(1009, 1010)] [] = true := by decide +kernel
theorem pk2_enter : enterOk [(1000, 1007)] 1000 = true := by decide +kernel
theorem pk2_after : fwdOk [(1008, 1010)] [] = true := by decide +kernel
theorem pk2_kRun : kOk kSing Gen.pk2_items0 = true := by decide +kernel
theorem pk2_sites : packSites kSing Gen.pk2_items0 pkS 1000 = true := by decide +kernel
theorem pk2_reads : xReadsB pkS Gen.pk2_items0 = true := by decide +kernel
theorem pk2_local : xLocalB Gen.pk2_items0 = true := by decide +kernel
theorem pk2_req (V : Nat → Value) : xReq V Gen.pk2_items0 = true := by rfl
theorem pk2_fns : kFns Gen.pk2_items0 := by
  refine kFns_of_mem ?_
  simp only [Gen.pk2_items0, List.forall_mem_cons, fnOk_cvt, and_self,
    List.not_mem_nil, false_imp_iff, implies_true]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
