-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.OutputSlots
public import Kernels.TmlFa4Fwd.Flow.Code.Part046
public import Lemmas.Flow.Run
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Rule
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The output tensor stores' operands

The coordinates (`storeCoords`), staging source (`stageSource`) and map (`outputMapOperand`) of the
eight tensor stores, and the specification a store with given operand words has
(`storeSpec_of_ok`). -/

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX
noncomputable section

section
variable {p : Params} {l : Launch} {m : Mem0}

def originOf (vs : List (BitVec 64)) (axis : Fin 4) : Int :=
  (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt

def storeSpec (p : Params) (sl : Loc) (vs : List (BitVec 64)) : TensorStore.Spec :=
  ⟨⟨3, p.oMap, originOf vs, sl, none⟩, none⟩

def columnReg : Fin 4 → Nat
  | 0 => 7229
  | 1 => 2396
  | 2 => 2397
  | 3 => 2398

def rowReg (stage : Fin 2) : Nat := if stage = 0 then 2395 else 2399

def stageSource (stage : Fin 2) (subbox : Fin 4) : Nat × Int :=
  if stage = 1 ∧ subbox = 0 then (1178, 0)
  else (2535, (3072 + 65536 * stage.val + 16384 * subbox.val : Nat))

theorem sharedAddress {l : Launch} {g : Nat} {t : TState} {r a off : Nat}
    (hr : t.regs r = some (.bits 32 (BitVec.ofNat 64 a))) (ha : a + off < 2 ^ 32) :
    sharedEffAddr l g t false r off = .ok ⟨.shared, g / l.block, a + off⟩ := by
  have ha' : a < 2 ^ 32 := by omega
  simp only [sharedEffAddr, readReg, hr, readBits, bind, Except.bind, pure, Except.pure,
    PTX.Proof.truncBits_ofNat ha' (by decide), BitVec.ofInt_natCast, ← BitVec.ofNat_add,
    PTX.Proof.truncBits_ofNat ha (by decide), BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show a + off < 2 ^ 64 by omega)]

def storeWords (p : Params) (batch head tile : Nat) (stage : Fin 2) (subbox : Fin 4) :
    List (BitVec 64) :=
  [BitVec.ofNat 64 (32 * subbox.val),
   BitVec.ofNat 64 (2 ^ 30 - p.qLength batch + stageRow tile stage),
   BitVec.ofNat 64 head, BitVec.ofNat 64 (p.qOffset (batch + 1))]

private theorem signedWord {n : Nat} (hn : n < 2 ^ 31) :
    (BitVec.ofNat 32 (BitVec.ofNat 64 n).toNat).toInt = (n : Int) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega), BitVec.toInt_ofNat']
  apply Int.bmod_eq_of_le <;> omega

theorem rowWord_lt {p : Params} {batch tile : Nat}
    (hlen : p.qLength batch ≤ 2 ^ 30) (htile : 256 * tile < p.qLength batch) (stage : Fin 2) :
    2 ^ 30 - p.qLength batch + stageRow tile stage < 2 ^ 31 := by
  have hs := stage.isLt
  unfold stageRow
  omega

/-- The four arguments at each store have the coordinate order of the ABI's ragged O map. -/
theorem storeOrigin (hp : Pre p l m) {batch head tile : Nat} (hb : batch < p.batch)
    (hh : head < p.heads) (htile : 256 * tile < p.qLength batch) (stage : Fin 2) (subbox : Fin 4) :
    originOf (storeWords p batch head tile stage subbox) =
      oCoordinate p batch head (stageRow tile stage) (32 * subbox.val) := by
  have hQEnd := hp.qOffset_le_total (b := batch + 1) (by omega)
  obtain ⟨-, -, -, -, hTotal⟩ := hp.shape
  have hEnd : p.qOffset (batch + 1) < 2 ^ 31 := by omega
  have hGridPos : 0 < (p.totalQ + 255 * p.batch) / 256 := by
    by_contra! he
    have hg := hp.grid.1
    simp [Params.grid, Nat.eq_zero_of_le_zero he] at hg
  have hHeadGrid : p.heads ≤ p.grid := Nat.le_mul_of_pos_left _ hGridPos
  have hGrid := hp.grid.2
  have hHead : head < 2 ^ 31 := by omega
  have hd : 32 * subbox.val < 2 ^ 31 := by have := subbox.isLt; omega
  funext axis
  fin_cases axis
  · exact signedWord hd
  · exact signedWord (rowWord_lt (hp.qLength_fits hb) htile stage)
  · exact signedWord hHead
  · exact signedWord hEnd

def storeCoords (stage : Fin 2) (subbox : Fin 4) : List Opnd :=
  [.reg (columnReg subbox), .reg (rowReg stage), .reg 7227, .reg 2393]

def storeOp (stage : Fin 2) (subbox : Fin 4) : Op :=
  .cpTensorStore (.reg 7868) (storeCoords stage subbox) (stageSource stage subbox).1
    (stageSource stage subbox).2 (some (.reg 7869)) .tile none

theorem storeInstr (stage : Fin 2) (subbox : Fin 4) :
    kernel.code[storePc stage subbox]? = some ⟨none, storeOp stage subbox⟩ := by
  have hCode :
      (List.ofFn fun i : Fin 2 => List.ofFn fun j : Fin 4 => kernel.code[storePc i j]?) =
        (List.ofFn fun i : Fin 2 => List.ofFn fun j : Fin 4 =>
          some (⟨none, storeOp i j⟩ : Instr)) := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hSlot := congrArg (fun rows => rows[stage.val]?.bind fun row => row[subbox.val]?) hCode
  simpa only [List.getElem?_ofFn, stage.isLt, subbox.isLt, ↓reduceDIte,
    Option.bind_some, Option.some.injEq] using hSlot

theorem outputMapOperand (hpre : Pre p l m) (g : Nat) (t : TState) (cs : List Opnd)
    (hptr : t.regs 7868 = some (.ptr 64 true (.param (param 10)) 0)) (hcs : cs.length = 4) :
    tensorMap l g t (.reg 7868) cs .tile = .ok (p.oMapAddress, ⟨3, p.oMap⟩) := by
  obtain ⟨hObject, hAlign, hRange, hDesc, hValid, _⟩ :=
    hpre.maps 10 p.oMapAddress ⟨3, p.oMap⟩ (by simp)
  have hAddress : tensorMapAddress l g t (.reg 7868) = .ok p.oMapAddress := by
    have hDecl : (mapParam 10).name = param 10 := rfl
    have hBytes : (mapParam 10).bytes = 128 := rfl
    have hAl : (mapParam 10).alignment = 64 := rfl
    have hEnd : p.oMapAddress ≤ 18446744073709551488 := by omega
    simp [tensorMapAddress, readValue, readReg, hptr, hObject, hDecl, hBytes, hAl,
      bind, Except.bind, pure, Except.pure, hAlign, hEnd]
  simp [tensorMap, hAddress, hAlign, hDesc, hValid, hcs, TensorMode.coordinates, bind, Except.bind,
    pure, Except.pure]

/-- The staging slot of a store, from the shared base and, for the second stage's first
subbox, its second base register. -/
theorem storeSource_of (hpre : Pre p l m) (g : Nat) (t : TState) (stage : Fin 2) (subbox : Fin 4)
    (hbase : t.regs 2535 = some (.bits 32 (BitVec.ofNat 64 l.sharedBase)))
    (hsecond : stage = 1 ∧ subbox = 0 →
      t.regs 1178 = some (.bits 32 (BitVec.ofNat 64 (l.sharedBase + 68608)))) :
    sharedEffAddr l g t false (stageSource stage subbox).1 (stageSource stage subbox).2 =
      .ok (sharedSlot l g stage subbox) := by
  have hLimit := hpre.shared.2.1
  have hAlign := hpre.shared.1
  unfold stageSource
  split
  · rename_i h
    obtain ⟨rfl, rfl⟩ := h
    have hs : l.sharedBase + 68608 < 2 ^ 32 := by omega
    exact sharedAddress (off := 0) (hsecond ⟨rfl, rfl⟩) (by simpa only [Nat.add_zero] using hs)
  · have hs := stage.isLt
    have hb := subbox.isLt
    exact sharedAddress hbase (by omega)

/-- A tensor store at an output site with a specification names the O map and the store
specification of its operand words and source slot. -/
theorem storeSpec_of_ok (hpre : Pre p l m) (stage : Fin 2) (subbox : Fin 4) (g : Nat)
    (t : TState) {vs : List (BitVec 64)} {sl : Loc} {a : Nat} {s : TensorStore.Spec}
    (hptr : t.regs 7868 = some (.ptr 64 true (.param (param 10)) 0))
    (hcoords : (storeCoords stage subbox).mapM (readBits l g t 32) = .ok vs)
    (hshared : sharedEffAddr l g t false (stageSource stage subbox).1
      (stageSource stage subbox).2 = .ok sl)
    (h : tensorStoreSpec l g t (.reg 7868) (storeCoords stage subbox) (stageSource stage subbox).1
      (stageSource stage subbox).2 (some (.reg 7869)) .tile none = .ok (a, s)) :
    a = p.oMapAddress ∧ s = storeSpec p sl vs := by
  have hTensor := outputMapOperand hpre g t (storeCoords stage subbox) hptr rfl
  unfold tensorStoreSpec at h
  simp only [hTensor, hshared, hcoords, bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h <;> (try (cases h; done)))
  all_goals cases h; exact ⟨rfl, rfl⟩

end
end
end PTX.Kernels.TmlFa4Fwd.Epilogue
