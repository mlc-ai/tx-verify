-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Lemmas.Flow.Run
public import Core.Thread.Run
public import Core.Async.Tensor.TensorAllocation
public import Mathlib.Data.Fin.VecNotation

namespace PTX.Tests.TensorPrefetch
noncomputable section
private def decl : ParamObjectDecl := ⟨"map", 8, 128, 128⟩
private def L : Launch := {
  grid := 1, block := 32, params := fun _ => none
  paramObjects := fun name => if name = "map" then some (decl, 1024) else none }
private def t : TState := { regs := fun
  | 0 => some (.ptr 64 true (.param "map") 0)
  | 1 => some (.ptr 64 false (.param "map") 0)
  | 2 => some (.bits 64 1024)
  | _ => none }

-- No tensorMaps entry is needed merely to prefetch this immutable parameter.
example : execLocal L 0 t (.prefetchTensorMap true 64 (.reg 0)) = .ok (next t) := rfl
example : execLocal L 0 t (.prefetchTensorMap false 64 (.reg 1)) = .ok (next t) := rfl
example : execLocal L 0 t (.prefetchTensorMap true 64 (.reg 1)) = .error .badValue := rfl
example : execLocal L 0 t (.prefetchTensorMap true 64 (.reg 2)) = .error .noRule := rfl
example : execLocal { L with paramObjects := fun _ => none } 0 t
    (.prefetchTensorMap true 64 (.reg 0)) = .error .badParam := rfl
example : execLocal L 0 t (.prefetchTensorMap true 64 (.reg 3)) =
    .error .uninitialized := rfl

private def source : Syntax.Function := {
  name := "prefetch_map"
  header := [".visible", ".entry", "prefetch_map", "(", ".param", ".align", "128",
    ".b8", "map", "[", "128", "]", ")"]
  body := [.declaration [".reg", ".b64", "%rd", "<", "2", ">"],
    .instruction none "mov.b64" [.register "%rd0", .symbol "map"],
    .instruction none "cvta.param.u64" [.register "%rd1", .register "%rd0"],
    .instruction none "prefetch.tensormap" [.address [.register "%rd1"]],
    .instruction none "ret" []] }
private def K : Kernel := {
  name := "prefetch_map", params := [], paramObjects := [decl], regNames := ["%rd0", "%rd1"]
  code := [⟨none, .move ⟨.scalar, .int .b 64, [some 0], [.paramSym "map"]⟩⟩,
    ⟨none, .addr (.cvta false .param 64 1 (.reg 0))⟩,
    ⟨none, .prefetchTensorMap true 64 (.reg 1)⟩,
    ⟨none, .ret⟩] }
example : Decode.kernel source = .ok K := rfl
private def moved := next (setReg ({} : TState) 0 (.ptr 64 false (.param "map") 0))
private def converted := next (setReg moved 1 (.ptr 64 true (.param "map") 0))
-- The entire source prefix computes only addresses; prefetch preserves them.
example : run K [] L 0 3 {} = some (next converted) := rfl
example : out K [] L 0 (next converted) = .ev .exit := rfl

/-! ## `cp.async.bulk.prefetch.tensor` -/

private def env : Decode.Env :=
  { classes := [⟨"r".toList, 8, 32⟩, ⟨"rd".toList, 2, 64⟩], labels := [], params := [] }
private def vec (cs : List String) : Syntax.Operand := .vector (cs.map Syntax.Operand.literal)

example : Decode.op env "cp.async.bulk.prefetch.tensor.2d.L2.global.tile"
    [.address [.register "rd0", vec ["16", "-3"]]] =
    .ok (.prefetchTensor (.reg 8) [.imm 16, .imm (-3)] .tile none) := rfl
example : Decode.op env "cp.async.bulk.prefetch.tensor.3d.L2.global"
    [.address [.register "rd0", vec ["0", "1", "2"]]] =
    .ok (.prefetchTensor (.reg 8) [.imm 0, .imm 1, .imm 2] .tile none) := rfl
example : Decode.op env "cp.async.bulk.prefetch.tensor.2d.L2.global.tile::gather4.L2::cache_hint"
    [.address [.register "rd0", vec ["0", "1", "2", "3", "4"]], .register "rd1"] =
    .ok (.prefetchTensor (.reg 8) [.imm 0, .imm 1, .imm 2, .imm 3, .imm 4] .fourRows
      (some (.reg 9))) := rfl
-- Coordinate counts follow the rank and mode; a cache hint needs its operand.
example : (Decode.op env "cp.async.bulk.prefetch.tensor.3d.L2.global"
    [.address [.register "rd0", vec ["0", "1"]]]).isOk = false := rfl
example : (Decode.op env "cp.async.bulk.prefetch.tensor.3d.L2.global.tile::gather4"
    [.address [.register "rd0", vec ["0", "1", "2", "3", "4"]]]).isOk = false := rfl
example : (Decode.op env "cp.async.bulk.prefetch.tensor.2d.L2.global.L2::cache_hint"
    [.address [.register "rd0", vec ["0", "1"]]]).isOk = false := rfl
-- The im2col form is rejected; the eviction-priority form decodes to the plain prefetch, which
-- has a rule (the priority does not change the footprint).
example : (Decode.op env "cp.async.bulk.prefetch.tensor.3d.L2.global.im2col"
    [.address [.register "rd0", vec ["0", "1", "2"]]]).isOk = false := rfl
example : Decode.op env "cp.async.bulk.prefetch.tensor.2d.L2.global.L2::evict_last"
    [.address [.register "rd0", vec ["0", "1"]]] =
    .ok (.prefetchTensor (.reg 8) [.imm 0, .imm 1] .tile none) := rfl

private def u8 (w h : Nat) : TensorDescriptor.Descriptor 1 :=
  ⟨.u8, 4096, ![256, 64], ![256], ⟨![w, h], ![1, 1]⟩, .none, .zero, .small⟩
/-- The 1D u8 large-class map of the review witness: base 4096, extent and box 16, traversal 1. -/
private def line : TensorDescriptor.Descriptor 0 :=
  ⟨.u8, 4096, ![16], ![], ⟨![16], ![1]⟩, .none, .zero, .large⟩
private def maps (address : Nat) : Option ((outer : Nat) × TensorDescriptor.Descriptor outer) :=
  if address = 1024 then some ⟨1, u8 64 8⟩
  else if address = 2048 then some ⟨1, u8 64 1⟩
  else if address = 3072 then some ⟨1, u8 64 300⟩
  else if address = 4160 then some ⟨1, { u8 64 8 with allocationClass := .large }⟩
  else if address = 4224 then some ⟨0, line⟩
  else none
private def LT : Launch := {
  grid := 1, block := 32, params := fun _ => none, tensorMaps := maps
  tensorLargeAllocMinBytes := some 64 }
private def tt : TState := { regs := fun
  | 10 => some (.bits 64 1024)
  | 11 => some (.bits 64 2048)
  | 12 => some (.bits 64 3072)
  | 13 => some (.bits 64 1056)
  | 14 => some (.bits 64 4096)
  | 15 => some (.bits 32 (-16 : Int).toNat)
  | 16 => some (.bits 64 7)
  | 17 => some (.bits 64 4160)
  | 18 => some (.bits 64 4224)
  | _ => none }
private def pf (m : Nat) (cs : List Opnd) (mode : TensorMode) (p : Option Opnd) : Op :=
  .prefetchTensor (.reg m) cs mode p

/-- The map address and continuation of a prefetch event, or the fault. -/
private def issued : Tmpl → Option (Nat × TState)
  | .tensorPrefetch a _ u => some (a, u)
  | _ => none
private def fault : Tmpl → Option Fault
  | .ub f => some f
  | _ => none

-- A prefetch is an event: one `tensorPrefetch` issue, then the next instruction. It has no
-- data access, completion or notification.
example : (pf 10 [.imm 0, .imm 0] .tile none).isLocal = false := rfl
example : eventTmpl [] LT 0 tt (pf 10 [.imm 16, .imm 3] .tile none) =
    tensorPrefetchTmpl LT 0 tt (pf 10 [.imm 16, .imm 3] .tile none) := rfl
example : issued (tensorPrefetchTmpl LT 0 tt (pf 10 [.imm 16, .imm 3] .tile none)) =
    some (1024, next tt) := rfl
-- Out-of-bounds boxes of a small-class map are allowed (no data moves); coordinates must be
-- defined and the box start 16-byte aligned (§5.5.3.1).
example : issued (tensorPrefetchTmpl LT 0 tt (pf 10 [.reg 15, .imm 100] .tile (some (.reg 16)))) =
    some (1024, next tt) := rfl
example : fault (tensorPrefetchTmpl LT 0 tt (pf 10 [.imm 8, .imm 0] .tile none)) =
    some .misaligned := rfl
example : fault (tensorPrefetchTmpl LT 0 tt (pf 10 [.reg 3, .imm 0] .tile none)) =
    some .uninitialized := rfl
example : fault (tensorPrefetchTmpl LT 0 tt (pf 10 [.imm 0, .imm 0] .tile (some (.reg 3)))) =
    some .uninitialized := rfl
-- The map: published, 64-byte aligned, valid, of the instruction's rank.
example : fault (tensorPrefetchTmpl LT 0 tt (pf 14 [.imm 0, .imm 0] .tile none)) =
    some .noRule := rfl
example : fault (tensorPrefetchTmpl LT 0 tt (pf 13 [.imm 0, .imm 0] .tile none)) =
    some .misaligned := rfl
example : fault (tensorPrefetchTmpl LT 0 tt (pf 12 [.imm 0, .imm 0] .tile none)) =
    some .badValue := rfl
example : fault (tensorPrefetchTmpl LT 0 tt (pf 10 [.imm 0, .imm 0, .imm 0] .tile none)) =
    some .badValue := rfl
-- gather4: five coordinates over a 2D map whose box dimension 1 is one.
example : issued (tensorPrefetchTmpl LT 0 tt
    (pf 11 [.imm 0, .imm 1, .imm 2, .imm 3, .imm 4] .fourRows none)) = some (2048, next tt) := rfl
example : fault (tensorPrefetchTmpl LT 0 tt
    (pf 10 [.imm 0, .imm 1, .imm 2, .imm 3, .imm 4] .fourRows none)) = some .badValue := rfl
example : fault (tensorPrefetchTmpl LT 0 tt (pf 11 [.imm 0, .imm 1] .fourRows none)) =
    some .badValue := rfl
-- A large-class map: an out-of-bounds box is issued like an in-bounds one; its §5.5.3.3
-- backing requirement is checked on the execution (ERR-TENSOR-LARGE-OOB).
example : issued (tensorPrefetchTmpl LT 0 tt (pf 17 [.imm (-16), .imm 0] .tile none)) =
    some (4160, next tt) := rfl
example : issued (tensorPrefetchTmpl LT 0 tt (pf 17 [.imm 16, .imm 0] .tile none)) =
    some (4160, next tt) := rfl

/-! ### The large-class backing requirement of a prefetch -/

/-- The witness prefetch: the 1D large-class map at origin −16 (one box wholly before the
tensor). -/
private def witness : TensorPrefetch.Spec := ⟨0, line, ![-16], none⟩

/-- What a prefetch event selects: map address, origin, large class, and whether an element
is out of bounds. -/
private def selection : Tmpl → Option (Nat × Int × Bool × Bool)
  | .tensorPrefetch a s _ => some (a, s.origin 0, decide (s.descriptor.allocationClass = .large),
      decide (TensorHasOob s.descriptor s.origin s.rows))
  | _ => none

-- The thread issues this prefetch: large class, wholly out of bounds, no local fault.
example : selection (tensorPrefetchTmpl LT 0 tt (pf 18 [.imm (-16)] .tile none)) =
    some (4224, -16, true, true) := by decide +kernel
example : issued (tensorPrefetchTmpl LT 0 tt (pf 18 [.imm (-16)] .tile none)) =
    some (4224, next tt) := rfl

private def X (s : TensorPrefetch.Spec) : Execution := {
  tr := fun g => if g = 0 then [⟨0, .tensorPrefetch 4224 s⟩] else [],
  rf := fun _ _ => none }

private theorem X_get {s : TensorPrefetch.Spec} {i : EvId} {e : Event}
    (h : (X s).get i = some e) : e = ⟨0, .tensorPrefetch 4224 s⟩ := by
  rcases i with ⟨g, k⟩
  by_cases hg : g = 0
  · subst hg
    rcases k with _ | k
    · simp only [X, Execution.get] at h; simpa using h.symm
    · simp [X, Execution.get] at h
  · simp [X, Execution.get, hg] at h

private theorem witness_oob : TensorHasOob line ![-16] none := by decide +kernel

/-- Global memory allocated at and after the map base (contents unknown). -/
private def backed : Mem0 := fun l => if l.space = .global ∧ 4096 ≤ l.addr then some none else none

-- Backing fully accessible: the out-of-bounds large-class prefetch is not unsafe.
example : ¬ TensorAllocationUnsafe LT backed (X witness) := by
  rintro ⟨i, ⟨a, s, ⟨pc, h⟩, -⟩ | ⟨a, s, ⟨pc, h⟩, -⟩ | ⟨a, s, ⟨pc, h⟩, -, -, hb⟩⟩
  · cases X_get h
  · cases X_get h
  · cases X_get h
    exact hb ⟨64, rfl, fun k _ => by simp [backed, witness, line]⟩

-- Backing not accessible: the same prefetch is unsafe (§5.5.3.3).
example : TensorAllocationUnsafe LT (fun _ => none) (X witness) :=
  ⟨(0, 0), .inr (.inr ⟨4224, witness, ⟨0, rfl⟩, rfl, witness_oob,
    fun ⟨_, hn, hm⟩ => by cases hn; exact hm 0 (by decide) rfl⟩)⟩

-- A small-class map has no backing obligation, whatever memory holds.
example (mem0 : Mem0) :
    ¬ TensorAllocationUnsafe LT mem0 (X { witness with descriptor := { line with
      allocationClass := .small } }) := by
  rintro ⟨i, ⟨a, s, ⟨pc, h⟩, -⟩ | ⟨a, s, ⟨pc, h⟩, -⟩ | ⟨a, s, ⟨pc, h⟩, hc, -⟩⟩
  · cases X_get h
  · cases X_get h
  · cases X_get h
    cases hc

end
end PTX.Tests.TensorPrefetch
