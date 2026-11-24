-- SPDX-License-Identifier: Apache-2.0
module

public meta import Lean
public meta import ImportGraph.Lean.Environment
public import Kernels.CopyDynamic.Theorem
public import Kernels.CopyLdg.Theorem
public import Kernels.RowSum.Theorem
public import Kernels.BlockSum.Theorem
public import Kernels.RmsNorm.Theorem
public import Kernels.TmaCopy.Theorem
public import Kernels.TcGemm.Theorem
public import Kernels.Fp16Gemm8192.Theorem
public import Kernels.AddOne.Theorem
public import Kernels.FlashAttn4Fwd.Theorem
public import Kernels.FlashMlaSparseDecodeH64.Theorem
public import Kernels.InklingRelDecode.Theorem
public import Kernels.TmlFa4Fwd.Theorem

@[expose] public section

/-!
# What a theorem's meaning depends on

For each kernel theorem, the build fails unless:

* its proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`, so nothing
  in `Lemmas/`, `Tactics/` or the proof can add an assumption;
* every constant its statement mentions is defined in `Core/`, `Assumption/`, the kernel's
  `Spec.lean`, `Ptx.lean`, `Assumptions.lean` or a file under its `Assumptions/`,
  `Data/Decoded.lean` or `Data/TensorMaps.lean`,
  `Lemmas/Arith/FastDivmod.lean`, or the Lean and Mathlib libraries;
* the kernel's `Spec.lean` and its assumption files import only those or the reviewed CuTeDSL
  software exp2 template shared by the two FA4 kernels.

Together: the statement means what the reviewed files say it means, and the only assumptions
it makes are the kernel's own, declared in its `Assumptions.lean`.
-/

namespace PTX.StatementCheck

open Lean Elab Command

meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

private meta def sharedExp2Template (kernel : String) (m : Name) : Bool :=
  kernel == "TmlFa4Fwd" && m == `Kernels.FlashAttn4Fwd.Assumptions.Exp2Template

meta def reviewed (kernel : String) (m : Name) : Bool :=
  let s := m.toString
  -- A kernel's program data: the decoder cache (`Data.Decoded`, the Core decoder's output on
  -- the source, certified by the kernel's `decode_eq`) and the host-built tensor maps
  -- (`Data.TensorMaps`). FlashMLA also defines its launch parameters, sparse-slot indexing,
  -- and audited assumption sites in dedicated data modules.
  let programData :=
    s == s!"Kernels.{kernel}.Data.Decoded" || s == s!"Kernels.{kernel}.Data.TensorMaps" ||
    (kernel == "FlashMlaSparseDecodeH64" &&
      ["Params", "Indices", "Sites"].any (fun suffix => s == s!"Kernels.{kernel}.Data.{suffix}"))
  -- The device-side FastDivmod quotient, the instruction sequence a launch premise states
  -- exact (`FastDivmod.quot`); the file defines arithmetic only.
  let arith := s == "Lemmas.Arith.FastDivmod"
  -- The kernel's assumptions: `Assumptions.lean` and the files under its `Assumptions/` (such
  -- as a code template that one of its assumptions reads as an exact function).
  let assumptions := s == s!"Kernels.{kernel}.Assumptions" ||
    s.startsWith s!"Kernels.{kernel}.Assumptions."
  s.startsWith "Core." || s.startsWith "Assumption." || s.startsWith "Mathlib." ||
    s.startsWith "Init" || s.startsWith "Lean" || s.startsWith "Lake." || s.startsWith "Std" ||
    s.startsWith "Batteries" || s == s!"Kernels.{kernel}.Spec" || s == s!"Kernels.{kernel}.Ptx" ||
    assumptions || programData || arith || sharedExp2Template kernel m

elab "#check_theorem " kernel:ident thm:ident : command => do
  let env ← getEnv
  let k := kernel.getId.toString
  let n := thm.getId
  let some ci := env.find? n | throwError "no theorem {n}"
  let mut errs : Array String := #[]
  for a in ← collectAxioms n do
    unless a ∈ standardAxioms do errs := errs.push s!"{n} uses axiom {a}"
  for c in ci.type.getUsedConstants do
    match env.getModuleFor? c with
    | some m => unless reviewed k m do errs := errs.push s!"{n} mentions {c}, defined in {m}"
    | none => pure ()
  let spec := s!"Kernels.{k}.Spec".toName
  let asm := s!"Kernels.{k}.Assumptions".toName
  if (env.getModuleIdx? spec).isNone then errs := errs.push s!"no module {spec}"
  -- The reviewed modules a statement can reach: Spec and the kernel's assumption files, which
  -- may import only reviewed modules. Core imports only Core and Mathlib
  -- (Tests/Kernel/Contract.lean).
  let mut todo := [spec, asm]
  let mut seen : List Name := []
  while !todo.isEmpty do
    let m := todo.head!
    todo := todo.tail!
    if m ∈ seen then continue
    seen := m :: seen
    let some i := env.getModuleIdx? m | continue
    for imp in env.header.moduleData[i.toNat]!.imports do
      unless reviewed k imp.module do errs := errs.push s!"{m} imports {imp.module}"
      if imp.module == spec || imp.module.toString.startsWith s!"Kernels.{k}.Assumptions." ||
          sharedExp2Template k imp.module then
        todo := imp.module :: todo
  if errs.isEmpty then logInfo m!"{n}: statement and axioms checked"
  else throwError (String.intercalate "\n" errs.toList)

#check_theorem CopyDynamic PTX.Kernels.CopyDynamic.correct
#check_theorem CopyLdg PTX.Kernels.CopyLdg.correct
#check_theorem RowSum PTX.Kernels.RowSum.correct
#check_theorem BlockSum PTX.Kernels.BlockSum.correct
#check_theorem RmsNorm PTX.Kernels.RmsNorm.correct
#check_theorem TmaCopy PTX.Kernels.TmaCopy.correct
#check_theorem TcGemm PTX.Kernels.TcGemm.correct
#check_theorem AddOne PTX.Kernels.AddOne.correct

#check_theorem CopyDynamic PTX.Kernels.CopyDynamic.completed_execution
#check_theorem CopyLdg PTX.Kernels.CopyLdg.completed_execution
#check_theorem RowSum PTX.Kernels.RowSum.completed_execution
#check_theorem BlockSum PTX.Kernels.BlockSum.completed_execution
#check_theorem RmsNorm PTX.Kernels.RmsNorm.completed_execution
#check_theorem TmaCopy PTX.Kernels.TmaCopy.completed_execution
#check_theorem TcGemm PTX.Kernels.TcGemm.completed_execution
#check_theorem AddOne PTX.Kernels.AddOne.completed_execution

#check_theorem CopyDynamic PTX.Kernels.CopyDynamic.realizable_result
#check_theorem CopyLdg PTX.Kernels.CopyLdg.realizable_result
#check_theorem RowSum PTX.Kernels.RowSum.realizable_result
#check_theorem BlockSum PTX.Kernels.BlockSum.realizable_result
#check_theorem RmsNorm PTX.Kernels.RmsNorm.realizable_result
#check_theorem TmaCopy PTX.Kernels.TmaCopy.realizable_result
#check_theorem TcGemm PTX.Kernels.TcGemm.realizable_result
#check_theorem AddOne PTX.Kernels.AddOne.realizable_result

end PTX.StatementCheck

#check_theorem Fp16Gemm8192 PTX.Kernels.Fp16Gemm8192.correct

#check_theorem Fp16Gemm8192 PTX.Kernels.Fp16Gemm8192.completed_execution

#check_theorem Fp16Gemm8192 PTX.Kernels.Fp16Gemm8192.realizable_result

#check_theorem FlashAttn4Fwd PTX.Kernels.FlashAttn4Fwd.correct

#check_theorem FlashAttn4Fwd PTX.Kernels.FlashAttn4Fwd.completed_execution

#check_theorem FlashAttn4Fwd PTX.Kernels.FlashAttn4Fwd.realizable_result

#check_theorem FlashMlaSparseDecodeH64 PTX.Kernels.FlashMlaSparseDecodeH64.correct

#check_theorem FlashMlaSparseDecodeH64 PTX.Kernels.FlashMlaSparseDecodeH64.completed_execution

#check_theorem FlashMlaSparseDecodeH64 PTX.Kernels.FlashMlaSparseDecodeH64.realizable_result

#check_theorem InklingRelDecode PTX.Kernels.InklingRelDecode.correct

#check_theorem InklingRelDecode PTX.Kernels.InklingRelDecode.completed_execution

#check_theorem InklingRelDecode PTX.Kernels.InklingRelDecode.realizable_result

#check_theorem TmlFa4Fwd PTX.Kernels.TmlFa4Fwd.correct

#check_theorem TmlFa4Fwd PTX.Kernels.TmlFa4Fwd.completed_execution

#check_theorem TmlFa4Fwd PTX.Kernels.TmlFa4Fwd.realizable_result
