-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Projection
public import Lemmas.Flow.MemTmpl

@[expose] public section
namespace FlashKda.Packed.MatrixLoad
open PTX

def move : MatrixMove := ⟨false, .m8n8, 4, false, .b16⟩

def load (addr : Nat) (dst : List Nat) : MatrixInstr :=
  ⟨.move move, some (.shared .cta), some ⟨.reg addr 32, 0⟩, dst, []⟩

theorem row_location (L : Launch) (g addr p : Nat) (dst : List Nat) (t : TState)
    (reg : t.regs addr = some (Proof.b32 p)) (fit : p < 2^32) (align : p%16 = 0) :
    matrixRowLoc L g t (load addr dst) = .ok ⟨.shared, g/L.block, p⟩ := by
  have pointer := @Proof.readBits_b32 L g t addr p reg fit
  change p < 4294967296 at fit
  have natVal : (BitVec.ofNat 64 p).toNat = p := Nat.mod_eq_of_lt (by omega)
  have wrap : wrapAddr 32 (BitVec.ofNat 64 p) 0 = p := by
    simp [wrapAddr, truncBits, natVal]
    omega
  simp [matrixRowLoc, load, accessLoc, readReg, reg, Proof.b32, pointer, natVal, fit,
    wrap, align, bind, Except.bind, pure, Except.pure]

def loaded (t : TState) (bs : List (Option Byte)) : TState :=
  if bs.length = 16 ∧ bs.all Option.isSome then
    { t with sub := 1, acc := bs.filterMap fun b => b.map byteValue }
  else { t with fault := some .uninitialized }

theorem read (L : Launch) (g addr p : Nat) (dst : List Nat) (t : TState)
    (reg : t.regs addr = some (Proof.b32 p)) (fit : p < 2^32) (align : p%16 = 0)
    (start : t.sub = 0) (block : L.block = 192) (width : dst.length = 4) :
    matrixTmpl L g t (load addr dst) =
      .read {loc := ⟨.shared, g/L.block, p⟩, size := 16} (loaded t) := by
  have addrOk := row_location L g addr p dst t reg fit align
  have rule : (load addr dst).rule = some .threadMatrix := by
    simp [load, move, MatrixInstr.rule, MatrixMove.supported, MatrixMove.regsPerMatrix, width]
  unfold matrixTmpl
  rw [rule]
  rw [ite_eq_left (by rw [block] : L.block%32 = 0)]
  change matrixMoveTmpl L g t (load addr dst) move = _
  have lane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  simp only [matrixMoveTmpl, move, MatrixMove.rows, Nat.reduceMul, lane, start, and_self,
    ↓reduceIte, Bool.false_eq_true, addrOk]
  congr 1
  funext bs
  simp [loaded, start]

theorem supply (L : Launch) (g addr : Nat) (dst : List Nat) (t : TState) (bs : List Byte)
    (len : bs.length = 16) (block : L.block = 192) (width : dst.length = 4) :
    let u := loaded t (bs.map some)
    matrixTmpl L g u (load addr dst) =
      .matrix (.move move) (bs.map some) (afterMatrix u 32 dst) := by
  dsimp only
  have rule : (load addr dst).rule = some .threadMatrix := by
    simp [load, move, MatrixInstr.rule, MatrixMove.supported, MatrixMove.regsPerMatrix, width]
  unfold matrixTmpl
  rw [rule, ite_eq_left (by rw [block] : L.block%32 = 0)]
  change matrixMoveTmpl L g (loaded t (bs.map some)) (load addr dst) move = _
  have lane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  simp [matrixMoveTmpl, move, MatrixMove.rows, lane, loaded, len, valueByte, byteValue,
    List.filterMap_map, Function.comp_def, load]

def rowBytes (atByte : Nat → Nat → Option Byte) (supplier : Nat) : List (Option Byte) :=
  (List.range 16).map (atByte supplier)

def registers (atByte : Nat → Nat → Option Byte) (lane : Nat) : List (Option Byte) :=
  (List.range 16).map fun x => atByte (8*(x/4)+lane/4) (4*(lane%4)+x%4)

theorem receive (atByte : Nat → Nat → Option Byte) (lane : Nat) :
    matrixMoveRecv move (rowBytes atByte) lane = .bytes (registers atByte lane) := by
  apply congrArg MatrixResult.bytes
  change (List.range 16).map _ = _
  apply List.map_congr_left
  intro x hx
  have bound : 4*(lane%4)+x%4 < 16 := by omega
  change ((rowBytes atByte (8*(x/4)+lane/4))[4*(lane%4)+x%4]?).join = _
  simp [rowBytes, bound]

theorem event (L : Launch) (X : Execution) (A : List Assumption) (atByte : Nat → Nat → Option Byte)
    {g i pc n own recv} (ok : MatrixOk L A X)
    (issued : X.get (g,i) = some ⟨pc, .matrix (.move move) own recv⟩) (idx : X.MatrixK (g,i) n)
    (inputs : MatrixInstance L X g n pc (.move move) (rowBytes atByte)) :
    recv = registers atByte (laneOf L g) := by
  have h := ok _ _ _ _ _ _ _ issued idx _ inputs
  simpa only [matrixRecv, pure, Except.pure, receive] using h

def aByte (a : Matrix.Tile) (supplier offset : Nat) : Option Byte :=
  some ((Value.float .bf16 (a (supplier%16) (8*(supplier/16)+offset/2))).byteAt (offset%2))

def bByte (b : Matrix.Tile) (supplier offset : Nat) : Option Byte :=
  some ((Value.float .bf16 (b (8*(supplier/8%2)+offset/2)
    (8*(supplier/16)+supplier%8))).byteAt (offset%2))

private theorem layout_a : ∀ l : Fin 32, ∀ i : Fin 8, ∀ b : Fin 2,
    let x := 2*i.val + b.val
    let s := 8*(x/4)+l.val/4
    let k := 4*(l.val%4)+x%4
    (s%16, 8*(s/16)+k/2, k%2) =
      ((Matrix.shape.fragA l.val i.val).2.1, (Matrix.shape.fragA l.val i.val).2.2, b.val) := by
  decide +kernel

private theorem layout_b : ∀ l : Fin 32, ∀ half : Fin 2, ∀ i : Fin 4, ∀ b : Fin 2,
    let x := 8*half.val+2*i.val+b.val
    let s := 8*(x/4)+l.val/4
    let k := 4*(l.val%4)+x%4
    (8*(s/8%2)+k/2, 8*(s/16)+s%8, k%2) =
      ((Matrix.shape.fragB l.val i.val).2.1,
        8*half.val+(Matrix.shape.fragB l.val i.val).2.2, b.val) := by
  decide +kernel

private def encoded (a : Matrix.Tile) (v : Nat × Nat × Nat) : Option (Option Byte) :=
  some (some ((Value.float .bf16 (a v.1 v.2.1)).byteAt v.2.2))

theorem fragment_a (a : Matrix.Tile) (lane : Fin 32) (i : Fin 8) (byte : Fin 2) :
    (registers (aByte a) lane.val)[2*i.val+byte.val]? =
      some (some ((Matrix.value .bf16 a (Matrix.shape.fragA lane.val i.val)).byteAt byte.val)) := by
  have h : 2*i.val+byte.val < 16 := by omega
  simp only [registers, List.getElem?_map, List.getElem?_range h, Option.map_some, aByte]
  exact congrArg (encoded a) (layout_a lane i byte)

theorem fragment_b (b : Matrix.Tile) (lane : Fin 32) (half : Fin 2) (i : Fin 4) (byte : Fin 2) :
    (registers (bByte b) lane.val)[8*half.val+2*i.val+byte.val]? =
      some (some ((Matrix.value .bf16 (fun k j => b k (8*half.val+j))
        (Matrix.shape.fragB lane.val i.val)).byteAt byte.val)) := by
  have h : 8*half.val+2*i.val+byte.val < 16 := by omega
  simp only [registers, List.getElem?_map, List.getElem?_range h, Option.map_some, bByte]
  exact congrArg (encoded b) (layout_b lane half i byte)

end FlashKda.Packed.MatrixLoad
