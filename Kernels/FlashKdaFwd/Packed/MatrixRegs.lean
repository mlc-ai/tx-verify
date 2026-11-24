-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Matrix
public import Kernels.FlashKdaFwd.Packed.Pointer
public import Kernels.FlashKdaFwd.Packed.Bfloat

@[expose] public section
namespace FlashKda.Packed.Matrix
open PTX
noncomputable section

def first : MatrixInstr := {
  op := .mma shape, dsts := [1188,1189,1190,1191],
  srcs := [1162,1163,1164,1165,1166,1167,1168,1168,1168,1168].map Opnd.reg }

def pairA (a : Tile) (l i : Nat) : Value :=
  .pair (value .bf16 a (shape.fragA l (2*i))) (value .bf16 a (shape.fragA l (2*i+1)))

def pairB (b : Tile) (l i : Nat) : Value :=
  .pair (value .bf16 b (shape.fragB l (2*i))) (value .bf16 b (shape.fragB l (2*i+1)))

theorem first_own (L : Launch) (g : Nat) (t : TState) (a b : Tile)
    (ha : ∀ i : Fin 4, t.regs (1162+i.val) = some (pairA a (laneOf L g) i.val))
    (hb : ∀ i : Fin 2, t.regs (1166+i.val) = some (pairB b (laneOf L g) i.val))
    (hz : t.regs 1168 = some (Proof.b32 0)) :
    mmaOwn L g t shape first.srcs = .ok (inputBytes a b .zeroWord (laneOf L g)) := by
  have fromReg (r : Nat) (v : Value) (h : t.regs r = some v) :
      readValue L g t 32 (.reg r) = .ok v := by
    simp [readValue, readReg, h, pure, Except.pure]
  have a0 : readValue L g t 32 (.reg 1162) = .ok (pairA a (laneOf L g) 0) :=
    fromReg _ _ (ha 0)
  have a1 : readValue L g t 32 (.reg 1163) = .ok (pairA a (laneOf L g) 1) :=
    fromReg _ _ (ha 1)
  have a2 : readValue L g t 32 (.reg 1164) = .ok (pairA a (laneOf L g) 2) :=
    fromReg _ _ (ha 2)
  have a3 : readValue L g t 32 (.reg 1165) = .ok (pairA a (laneOf L g) 3) :=
    fromReg _ _ (ha 3)
  have b0 : readValue L g t 32 (.reg 1166) = .ok (pairB b (laneOf L g) 0) :=
    fromReg _ _ (hb 0)
  have b1 : readValue L g t 32 (.reg 1167) = .ok (pairB b (laneOf L g) 1) :=
    fromReg _ _ (hb 1)
  have z := fromReg _ _ hz
  change (do
    let x ← regBytes L g t 32 ([1162,1163,1164,1165,1166,1167].map Opnd.reg)
    let y ← regBytes L g t 32 ([1168,1168,1168,1168].map Opnd.reg)
    let e ← regBytes L g t 32 []
    pure (x++y++e)) = _
  simp only [regBytes, List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil,
    a0, a1, a2, a3, b0, b1, z, bind, Except.bind, pure, Except.pure]
  rfl

theorem first_issue (L : Launch) (g : Nat) (t : TState) (a b : Tile) (block : L.block = 192)
    (ha : ∀ i : Fin 4, t.regs (1162+i.val) = some (pairA a (laneOf L g) i.val))
    (hb : ∀ i : Fin 2, t.regs (1166+i.val) = some (pairB b (laneOf L g) i.val))
    (hz : t.regs 1168 = some (Proof.b32 0)) :
    matrixTmpl L g t first = .matrix (.mma shape) (inputBytes a b .zeroWord (laneOf L g))
      (afterMatrix t 32 first.dsts) := by
  unfold matrixTmpl
  rw [ite_eq_left (by rw [block] : L.block % 32 = 0)]
  change (match mmaOwn L g t shape first.srcs with
    | .error e => Tmpl.ub e | .ok bs => .matrix (.mma shape) bs (afterMatrix t 32 first.dsts)) = _
  rw [first_own L g t a b ha hb hz]

def outputValue (a b c : Tile) (l i : Nat) : Value :=
  .float .f32 (dot a b c (row l i) (col l i))

theorem first_writeback (t : TState) (a b c : Tile) (l : Nat) :
    afterMatrix t 32 first.dsts (result a b c l) =
      next (setRegs { t with sub := 0, acc := [] } first.dsts
        ((List.range 4).map (outputValue a b c l))) := by
  have read (i : Nat) : rebuild 3 (bytes (outputValue a b c l i)) = .ok (outputValue a b c l i) :=
    rebuild_scalar (v := outputValue a b c l i) (fun _ => rfl) (by change 0 < 4; decide)
  change (match ([bytes (outputValue a b c l 0), bytes (outputValue a b c l 1),
      bytes (outputValue a b c l 2), bytes (outputValue a b c l 3)]).mapM (rebuild 3) with
    | .ok vs => next (setRegs { t with sub := 0, acc := [] } first.dsts vs)
    | .error f => { t with fault := some f }) = _
  simp only [List.mapM_cons, List.mapM_nil, read, bind, Except.bind, pure, Except.pure]
  rfl

theorem first_event (base : Nat → Nat → Nat) (L : Launch) (X : Execution) (a b : Tile)
    {g i n own recv}
    (ok : MatrixOk L [Pointer.representation base, Bfloat.exactNarrow, Activation.arithmetic,
      Activation.approximate] X)
    (event : X.get (g,i) = some ⟨2199, .matrix (.mma shape) own recv⟩)
    (index : X.MatrixK (g,i) n)
    (ins : MatrixInstance L X g n 2199 (.mma shape) (inputBytes a b .zeroWord)) :
    recv = result a b (fun _ _ => 0) (laneOf L g) := by
  have h := ok _ _ _ _ _ _ _ event index _ ins
  have lane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have resultBytes : mmaRecv [Pointer.representation base, Bfloat.exactNarrow,
      Activation.arithmetic, Activation.approximate] shape (inputBytes a b .zeroWord) (laneOf L g) =
      .ok (result a b (fun _ _ => 0) (laneOf L g)) := receive_words a b .zeroWord _ lane
  simp only [matrixRecv, resultBytes] at h
  exact h

end
end FlashKda.Packed.Matrix
