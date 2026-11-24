-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Decode.Cache
public import Kernels.FlashKdaFwd.Packed.Decode.Names
public import Lemmas.Kernel.DecodeChunks
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Prologue
open PTX PTX.Decode FlashKda.Packed.Transfers

set_option maxRecDepth 60000

def address (i : Nat) : Instr := ⟨none, .move {
  kind := .scalar, ty := .int .b 64, dsts := [some (2251+i)], srcs := [.paramSym (param i)] }⟩

def offsets : Instr := ⟨none, .mem {
  kind := .load, space := some .param, sem := .weak, elem := .int .b 64,
  addr := ⟨.param (param 15) false, 0⟩, dsts := [some 2262] }⟩

def globalPointer : Instr := ⟨none, .addr (.cvta true .global 64 2247 (.reg 2262))⟩

private def rawMov (r n : String) : Isa.Raw :=
  ⟨.mov, [(.type,some .b64)],
    [⟨"d",.reg,.w,some .b64,1,.register r⟩,⟨"a",.regvar,.r,some .b64,1,.symbol n⟩]⟩
private theorem parse_mov (pred : String → Bool) (r n : String) :
    Isa.Grammar.parse pred "mov.b64" [.register r,.symbol n] = .ok (rawMov r n) := by kernel_rfl
private theorem lowerMove (e : Decode.Env) (r n : String) (d : Nat)
    (localSym : e.locals.lookup n = none)
    (register : Decode.reg e 64 (.register r) = .ok d)
    (known : Decode.src e 64 (.symbol n) = .ok (.paramSym n)) :
    Decode.op e "mov.b64" [.register r,.symbol n] = .ok (.move {
      kind := .scalar, ty := .int .b 64, dsts := [some d], srcs := [.paramSym n] }) := by
  let dst : Isa.ROpnd := ⟨"d",.reg,.w,some .b64,1,.register r⟩
  let srcOp : Isa.ROpnd := ⟨"a",.regvar,.r,some .b64,1,.symbol n⟩
  have ds : Decode.rdsts e dst = .ok [some d] := by
    have dt : Decode.ROpnd.dtype dst = .ok (.int .b 64) := rfl
    have typed : Decode.typedDst e (.int .b 64) (.register r) = .ok (some d) := by
      change (some <$> Decode.reg e 64 (.register r)) = _
      rw [register]
      rfl
    simp [Decode.rdsts, dt, dst, typed, bind, Except.bind, pure, Except.pure]
  have ss : Decode.rsrcs e srcOp = .ok [.paramSym n] := by
    change (do pure [← Decode.src e 64 (.symbol n)]) = _
    rw [known]
    rfl
  have os : Decode.operands e (rawMov r n) = .ok ([some d],[.paramSym n]) := by
    unfold Decode.operands
    change List.foldlM _ ([],[]) [dst,srcOp] = _
    simp only [List.foldlM_cons, List.foldlM_nil, show dst.role = .w from rfl,
      show srcOp.role = .r from rfl, ds, ss, bind, Except.bind, pure, Except.pure]
    rfl
  unfold Decode.op
  rw [parse_mov]
  change (Op.move <$> Decode.MoveInstr.ofRaw e (rawMov r n)) = _
  unfold Decode.MoveInstr.ofRaw
  have dtype : Decode.dtype ((rawMov r n).get .type) = .ok (.int .b 64) := rfl
  rw [dtype]
  dsimp only [bind, Except.bind]
  simp only [show (rawMov r n).entry = .mov from rfl,
    show (rawMov r n).opnds = [dst,srcOp] from rfl]
  dsimp only [srcOp]
  simp [localSym, os, pure, Except.pure]

private def regName (i : Nat) := "%rd" ++ toString (i+5)

private def syntaxMove (i : Nat) : Decode.SourceInstr :=
  (none,"mov.b64",[.register (regName i), .symbol (param i)])

set_option maxHeartbeats 0 in
private theorem move_operands (i : Fin 11) :
    Decode.src env 64 (.symbol (param i.val)) = .ok (.paramSym (param i.val)) ∧
    Decode.reg env 64 (.register (regName i.val)) = .ok (2251+i.val) := by
  have entry : env.params[6+i.val]? = some (param i.val, 2048) := by fin_cases i <;> kernel_rfl
  have known := List.lookup_isSome_iff.mpr
    (⟨_, List.mem_of_getElem? entry, by simp⟩ : ∃ p ∈ env.params, (param i.val == p.1) = true)
  have sh : env.shared.lookup (param i.val) = none := by fin_cases i <;> kernel_rfl
  constructor
  · simp [Decode.src, sh, known, pure, Except.pure]
  · fin_cases i <;> kernel_rfl

private theorem individual (i : Nat) (hi : i < 11) :
    Decode.code env i [syntaxMove i] = .ok [address i] := by
  have args := move_operands ⟨i,hi⟩
  have op := lowerMove {env with pc := i} (regName i) (param i) (2251+i) rfl args.2 args.1
  exact singleton_code op

private theorem initialMoves (n : Nat) (h : n ≤ 11) :
    Decode.code env 0 ((List.range n).map syntaxMove) = .ok ((List.range n).map address) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_append]
    apply Decode.code_append_ok (ih (by omega))
    simpa using individual n (by omega)

private def resolvedMove (i : Nat) : Decode.SourceInstr :=
  (none, "mov.b64", [.register (regName i), Decode.resolveOperand topBindings (.symbol (param i))])

set_option maxHeartbeats 0 in
theorem descriptor_sites : slice 0 11 = some ((List.range 11).map address) := by
  have raw : prepared.toOption.map (fun q => q.instrs.take 11) =
      some ((List.range 11).map resolvedMove) := by kernel_rfl
  have forms : (List.range 11).map resolvedMove = (List.range 11).map syntaxMove := by
    apply List.map_congr_left
    intro i hi
    have lt := List.mem_range.mp hi
    exact congrArg (fun x : Syntax.Operand => (none,"mov.b64",[.register (regName i),x]))
      (resolvedParam ⟨i, by omega⟩)
  rw [forms] at raw
  exact @checked 0 11 _ _ raw (initialMoves 11 (by decide))

end FlashKda.Packed.Prologue
