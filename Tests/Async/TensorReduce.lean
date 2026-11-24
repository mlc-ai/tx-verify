-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Lemmas.TensorStore.TensorStore
public import Lemmas.TensorStore.TensorStoreThread
public import Mathlib.Tactic

/-! `cp.reduce.async.bulk.tensor` (EXT-TMA-REDUCE): decoding, the element-type table, the issue
rule and the effect rule: a reduction writes each element whole, after reading its shared bytes
and its old destination bytes. -/
namespace PTX.Tests.TensorReduce
open TensorStore
noncomputable section

private def env : Decode.Env :=
  { classes := [⟨"r".toList, 8, 32⟩, ⟨"rd".toList, 2, 64⟩], labels := [], params := [] }
private def vec (cs : List String) : Syntax.Operand := .vector (cs.map Syntax.Operand.literal)

/-! ## Decoding -/

example : Decode.op env "cp.reduce.async.bulk.tensor.2d.global.shared::cta.add.tile.bulk_group"
    [.address [.register "rd0", vec ["16", "3"]], .address [.register "r0"]] =
    .ok (.cpTensorStore (.reg 8) [.imm 16, .imm 3] 0 0 none .tile (some .add)) := rfl
example : Decode.op env "cp.reduce.async.bulk.tensor.1d.global.shared::cta.xor.bulk_group"
    [.address [.register "rd0", vec ["0"]], .address [.register "r0"]] =
    .ok (.cpTensorStore (.reg 8) [.imm 0] 0 0 none .tile (some .xor)) := rfl
example : Decode.op env
    "cp.reduce.async.bulk.tensor.3d.global.shared::cta.min.bulk_group.L2::cache_hint"
    [.address [.register "rd0", vec ["0", "1", "2"]], .address [.register "r0"], .register "rd1"] =
    .ok (.cpTensorStore (.reg 8) [.imm 0, .imm 1, .imm 2] 0 0 (some (.reg 9)) .tile
      (some .min)) := rfl
example : ∀ op ∈ ["add", "min", "max", "inc", "dec", "and", "or", "xor"],
    (Decode.op env s!"cp.reduce.async.bulk.tensor.1d.global.shared::cta.{op}.bulk_group"
      [.address [.register "rd0", vec ["0"]], .address [.register "r0"]]).isOk = true := by decide
-- Unknown reductions and wrong coordinate counts are rejected; an im2col form decodes to
-- `Op.unmodeled`, which has no rule.
private def unmodeled : Except String Op → Bool
  | .ok (.unmodeled _) => true
  | _ => false
example : (Decode.op env "cp.reduce.async.bulk.tensor.1d.global.shared::cta.mul.bulk_group"
    [.address [.register "rd0", vec ["0"]], .address [.register "r0"]]).isOk = false := rfl
example : (Decode.op env "cp.reduce.async.bulk.tensor.2d.global.shared::cta.add.bulk_group"
    [.address [.register "rd0", vec ["0"]], .address [.register "r0"]]).isOk = false := rfl
example : unmodeled (Decode.op env
    "cp.reduce.async.bulk.tensor.3d.global.shared::cta.add.im2col_no_offs.bulk_group"
    [.address [.register "rd0", vec ["0", "1", "2"]], .address [.register "r0"]]) = true := rfl
-- A plain store records no reduction.
example : Decode.op env "cp.async.bulk.tensor.1d.global.shared::cta.bulk_group"
    [.address [.register "rd0", vec ["0"]], .address [.register "r0"]] =
    .ok (.cpTensorStore (.reg 8) [.imm 0] 0 0 none .tile none) := rfl

/-! ## Element types (§9.7.10.28.5.4 table) -/

example : ReduceSupported .add .f32 ∧ ReduceSupported .add .bf16 ∧ ReduceSupported .add .u64 ∧
    ¬ ReduceSupported .add .s64 ∧ ¬ ReduceSupported .add .u8 ∧ ¬ ReduceSupported .add .f64 := by
  decide
example : ReduceSupported .min .s64 ∧ ReduceSupported .max .f16 ∧ ¬ ReduceSupported .max .f32 := by
  decide
-- inc and dec are u32 only (an s32 map traps on the B200).
example : ReduceSupported .inc .u32 ∧ ¬ ReduceSupported .inc .s32 ∧ ¬ ReduceSupported .dec .u64 :=
    by
  decide
example : ReduceSupported .and .s64 ∧ ReduceSupported .xor .u32 ∧ ¬ ReduceSupported .or .f32 ∧
    ¬ ReduceSupported .xor .u16 := by decide

/-! ## The issue rule -/

private def map (f : TensorDescriptor.Format) : TensorDescriptor.Descriptor 1 :=
  ⟨f, 4096, ![64, 32], ![256], ⟨![16, 8], ![1, 1]⟩, .none, .zero, .small⟩
private def maps (address : Nat) : Option ((outer : Nat) × TensorDescriptor.Descriptor outer) :=
  if address = 1024 then some ⟨1, map .u32⟩
  else if address = 2048 then some ⟨1, map .s32⟩
  else if address = 3072 then some ⟨1, map .f32⟩
  else none
private def L : Launch := { grid := 1, block := 128, params := fun _ => none, tensorMaps := maps }
private def t : TState := { regs := fun
  | 0 => some (.bits 32 256)
  | 8 => some (.bits 64 1024)
  | 9 => some (.bits 64 2048)
  | 10 => some (.bits 64 3072)
  | _ => none }
private def op (m : Nat) (r : AtomOp) (cs : List Opnd := [.imm 16, .imm 3]) : Op :=
  .cpTensorStore (.reg m) cs 0 0 none .tile (some r)
private def issued : Tmpl → Option (List Int × Option AtomOp × Nat)
  | .tensorStore _ s _ => some (List.ofFn s.origin, s.reduce, TensorTransfer.bytes s.descriptor)
  | _ => none

example : issued (tensorStoreTmpl L 0 t (op 8 .add)) = some ([16, 3], some .add, 512) := rfl
example : issued (tensorStoreTmpl L 0 t (op 9 .min)) = some ([16, 3], some .min, 512) := rfl
example : issued (tensorStoreTmpl L 0 t (op 10 .add)) = some ([16, 3], some .add, 512) := rfl
-- Unsupported element types have no issue.
example : tensorStoreTmpl L 0 t (op 9 .inc) = .ub .badValue := rfl
example : tensorStoreTmpl L 0 t (op 10 .and) = .ub .badValue := rfl
example : tensorStoreTmpl L 0 t (op 10 .max) = .ub .badValue := rfl
-- As for stores: nonnegative coordinates and a 128-byte-aligned local source.
example : tensorStoreTmpl L 0 t (op 8 .add [.imm (-4), .imm 0]) = .ub .badValue := rfl
example : tensorStoreTmpl L 0 t (.cpTensorStore (.reg 8) [.imm 0, .imm 0] 0 64 none .tile
    (some .add)) = .ub .misaligned := rfl
-- Reductions are tile-mode only.
example : tensorStoreTmpl L 0 t (.cpTensorStore (.reg 8) [.imm 0, .imm 0, .imm 1, .imm 2, .imm 3]
    0 0 none .fourRows (some .add)) = .ub .badValue := rfl
-- A successful issue records the instruction's reduction.
example {a : Nat} {s : Spec} {u : TState} (h : tensorStoreTmpl L 0 t (op 8 .xor) =
    .tensorStore a s u) :
    s.reduce = some .xor := by
  obtain ⟨hc, -⟩ := tensorStoreTmpl_issue h
  obtain ⟨-, d, -, -, -, -, hr⟩ := tensorStoreSpec_ok hc
  exact hr

/-! ## Effects: a reduction writes a whole element, each byte with its old byte

The written values are DEP-REDUCTION-VALUES (`Tests/Async/TensorReduceAtomic.lean`). -/

private def spec (r : Option AtomOp) : Spec := ⟨⟨1, map .u32, ![0, 0], ⟨.shared, 0, 0⟩,
    none⟩, r⟩
private def slot0 : TensorTransfer.Slot (map .u32) := ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by
    decide⟩⟩
private def b (v : Nat) : Byte := (.bits 8 (BitVec.ofNat 64 v), 0)
private def elem0 (v : Nat) (s : TensorTransfer.Slot (map .u32)) : Option Byte :=
  if s.1 = slot0.1 ∧ s.2.1 = slot0.2.1 then some (b v) else none
private def eff : Effects (spec (some .add)) := { read := elem0 1, old := elem0 5, write :=
                                                  elem0 9 }
private def effStore : Effects (spec none) :=
  { read := fun (s : TensorTransfer.Slot (map .u32)) => if s = slot0 then some (b 1) else none,
    write := fun (s : TensorTransfer.Slot (map .u32)) => if s = slot0 then some (b 9) else none }

example : CopyOk (spec (some .add)) eff := by
  refine ⟨fun s byte hw => ?_, fun h => (by cases h), fun h => (by cases h), ?_, ?_⟩
  · simp only [eff, elem0] at hw
    split_ifs at hw with hs
    refine ⟨?_, b 1, by simp [eff, elem0, hs], fun h => by cases h⟩
    rcases s with ⟨x, y, k⟩
    obtain ⟨rfl, rfl⟩ := hs
    fin_cases k <;> exact ⟨_, rfl⟩
  · intro s byte hw _ o h1 h2
    simp only [eff, elem0] at hw ⊢
    split_ifs at hw with hs
    simp [h1, h2, hs]
  · intro s byte ho
    simp only [eff, elem0] at ho ⊢
    split_ifs at ho with hs
    exact ⟨rfl, b 9, by simp [hs]⟩
-- A reduction cannot write one byte of an element alone, nor without its old byte.
example : ¬ CopyOk (spec (some .add))
    { read := elem0 1,
      write := fun (s : TensorTransfer.Slot (map .u32)) => if s = slot0 then some (b 9) else
        none } := by
  intro h
  obtain ⟨⟨_, hw⟩, -⟩ := h.element slot0 (b 9) (by simp) rfl
    ⟨slot0.1, slot0.2.1, ⟨1, by decide⟩⟩ rfl rfl
  dsimp only at hw
  rw [ite_eq_right (fun he => by
    have := congrArg (fun s : TensorTransfer.Slot (map .u32) => s.2.2.val) he
    simp [slot0] at this)] at hw
  cases hw
example : ¬ CopyOk (spec (some .add)) { eff with old := fun _ => none } := by
  intro h
  obtain ⟨-, _, ho⟩ := h.element slot0 (b 9) (by simp [eff, elem0]) rfl slot0 rfl rfl
  cases ho
-- The same effects are not a store's: its byte must be the read one.
example : ¬ CopyOk (spec none) effStore := by
  intro h
  obtain ⟨-, src, hr, he⟩ := h.writes slot0 (b 9) (by simp [effStore])
  simp [effStore] at hr
  subst hr
  have := he rfl
  simp [b] at this
-- A write still needs a recorded shared read, even for a reduction.
example : ¬ CopyOk (spec (some .add)) { write := fun _ => some (b 9) } := by
  intro h
  obtain ⟨-, src, hr, -⟩ := h.writes slot0 (b 9) rfl
  cases hr

end
end PTX.Tests.TensorReduce
