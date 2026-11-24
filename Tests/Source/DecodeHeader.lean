-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Assembly.Correctness
import all Init.Data.ToString.Extra
import all Core.Source.Decode
import all Core.Source.Instr
import all Init.Data.String.TakeDrop
import all Init.Data.String.Slice
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Defs
import all Batteries.Data.Except

namespace PTX.Tests.DecodeHeader

example : Decode.headerTail [".maxntid", "384", ".minnctapersm", "1"] =
    .ok { maxThreads := some 384 } := rfl
example : Decode.headerTail [".minnctapersm", "4", ".maxntid", "128"] =
    .ok { maxThreads := some 128 } := rfl
-- An occupancy hint is not a thread-count constraint or a scheduling guarantee.
example : Decode.headerTail [".minnctapersm", "4"] = .ok {} := rfl
example : Decode.headerTail [".maxntid", "0"] = .error "zero .maxntid" := rfl
example : Decode.headerTail [".minnctapersm", "0"] = .error "zero .minnctapersm" := rfl
example : Decode.headerTail [".maxntid", "128", ".maxntid", "256"] =
    .error "duplicate .maxntid" := rfl
example : Decode.headerTail [".minnctapersm", "1", ".minnctapersm", "2"] =
    .error "duplicate .minnctapersm" := rfl
-- A launch-shape requirement is kept, not dropped as a performance hint.
example : Decode.headerTail [".reqntid", "128"] = .ok { reqThreads := some (128, 1, 1) } := rfl
-- `.reqntid` keeps each extent; one not written is 1.
example : Decode.headerTail [".reqntid", "16", ",", "16"] =
    .ok { reqThreads := some (16, 16, 1) } := rfl
example : Decode.headerTail [".reqntid", "512", ",", "1", ",", "1", ".minnctapersm", "1"] =
    .ok { reqThreads := some (512, 1, 1) } := rfl
example : Decode.headerTail [".maxntid", "16", ",", "16", ",", "4"] =
    .ok { maxThreads := some 1024 } := rfl
example : Decode.headerTail [".maxntid", "128", ".reqntid", "128"] =
    .error ".reqntid with .maxntid" := rfl
-- `.maxnreg` is checked and dropped: the model represents no register counts.
example : Decode.headerTail [".maxnreg", "64"] = .ok {} := rfl
example : Decode.headerTail [".maxnreg", "64", ".maxnreg", "64"] =
    .error "duplicate .maxnreg" := rfl
-- `.maxclusterrank` is checked and dropped: the cluster's size comes from the launch.
example : Decode.headerTail [".maxclusterrank", "1"] = .ok {} := rfl
example : Decode.headerTail [".maxntid", "384", ".minnctapersm", "1", ".maxclusterrank", "1"] =
    .ok { maxThreads := some 384 } := rfl
example : Decode.headerTail [".maxclusterrank", "0"] = .error "zero .maxclusterrank" := rfl
example : Decode.headerTail [".maxclusterrank", "8", ".maxclusterrank", "8"] =
    .error "duplicate .maxclusterrank" := rfl

-- Pointer attributes.
example : (Decode.param [".param", ".u64", ".nonsense", ".tokens", "p"]).isOk = false := by
  decide +kernel
example : Decode.param [".param", ".u64", ".ptr", ".global", ".align", "16", "p"] =
    .ok ([("p", 64)], some ⟨some .global, 16⟩) := by decide +kernel
example : Decode.param [".param", ".u64", ".ptr.global.align", "16", "p"] =
    .ok ([("p", 64)], some ⟨some .global, 16⟩) := by decide +kernel
example : Decode.param [".param", ".u64", ".ptr", "p"] =
    .ok ([("p", 64)], some ⟨none, 4⟩) := by decide +kernel
-- The alignment is an integer literal (§4.5.1), so the `U` suffix is accepted.
example : Decode.param [".param", ".u64", ".ptr", ".align", "16U", "p"] =
    .ok ([("p", 64)], some ⟨none, 16⟩) := by decide +kernel
example : (Decode.param [".param", ".u64", ".ptr", ".align", "3U", "p"]).isOk = false := by
  decide +kernel
-- Parameterized names (§5.4.6).
example : Decode.param [".param", ".u32", "p", "<", "2", ">"] =
    .ok ([("p0", 32), ("p1", 32)], none) := by decide +kernel
example : Decode.parameterDecls ["(", ".param", ".u64", ".ptr", ".global", "q", "<", "2", ">",
    ")"] =
    .ok ([("q0", 64), ("q1", 64)], [("q0", ⟨some .global, 4⟩), ("q1", ⟨some .global, 4⟩)], []) := by
  decide +kernel
example : (Decode.param [".param", ".u32", "p", "<", "0", ">"]).isOk = false := by decide +kernel
-- A scalar storage alignment is legal PTX (§5.4.5) that the decoder does not support.
example : (Decode.param [".param", ".align", "8", ".u64", "p"]).isOk = false := by decide +kernel
example : (Decode.param [".param", ".u64", ".ptr", ".align", "3", "p"]).isOk = false := by
  decide +kernel
example : Decode.parameterDecls ["(", ".param", ".u64", ".ptr", ".align", "1", "p", ")"] =
    .ok ([("p", 64)], [], []) := by decide +kernel
example : Decode.parameterDecls ["(", ".param", ".u64", ".ptr", ".global", ".align", "16", "p",
    ")"] =
    .ok ([("p", 64)], [("p", ⟨some .global, 16⟩)], []) := by decide +kernel

-- CORRECT-LAUNCH.
private def kernel : Kernel := { name := "k", params := [("p", 64)], code := [] }
private def launch : Launch := { grid := 4, block := 128, params := fun _ => none, clusterSize :=
                                 2 }
private def launch256 : Launch :=
  { grid := 4, block := 256, params := fun _ => none, clusterSize := 2 }

example : ¬ launch256.Valid { kernel with maxThreads := some 128 } :=
  fun h => by have := h.2.1 128 rfl; simp [launch256] at this
example : launch.Valid { kernel with maxThreads := some 128 } := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro n h; cases h; decide
  · intro n h; cases h
  · intro name p v h hv; simp [launch] at hv
-- `.reqntid` is compared per dimension with the launch's CTA shape `%ntid`.
example : ¬ launch256.Valid { kernel with reqThreads := some (16, 16, 1) } :=
  fun h => by have := h.2.2.1 _ rfl; simp [launch256] at this
example : launch256.Valid { kernel with reqThreads := some (256, 1, 1) } := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro n h; cases h
  · intro s h; cases h; rfl
  · intro name p v h hv; simp [launch256] at hv
-- A two-dimensional CTA shape is compared per dimension too.
private def launch2D : Launch :=
  { grid := 4, block := 256, params := fun _ => none, clusterSize := 2, ntid := ⟨16, 16, 1⟩ }
example : launch2D.Valid { kernel with reqThreads := some (16, 16, 1) } := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro n h; cases h
  · intro s h; cases h; rfl
  · intro name p v h hv; simp [launch2D] at hv
example : ¬ launch.Valid { kernel with reqThreads := some (256, 1, 1) } :=
  fun h => by have := h.2.2.1 _ rfl; simp [launch] at this
-- `.minperctamemory` is kept; it admits the `%perctamemory` registers (PROG-OPERAND).
example : Decode.headerTail [".minperctamemory", "2048"] = .ok { minPerCtaMemory := some 2048 } :=
  rfl
example : (Decode.headerTail [".minperctamemory", "2048", ".minperctamemory", "16"]).toOption =
    none := rfl
-- The decoded `.reqntid 256` and `.reqntid 256,1,1` are that shape.
example : Decode.headerTail [".reqntid", "256"] = .ok { reqThreads := some (256, 1, 1) } := rfl
example : Decode.headerTail [".reqntid", "256", ",", "1", ",", "1"] =
    .ok { reqThreads := some (256, 1, 1) } := rfl
example : ¬ ({ launch with grid := 3 } : Launch).Valid kernel :=
  fun h => by have := h.1; revert this; decide
example : ¬ ({ launch with params := fun _ => some 8 } : Launch).Valid
    { kernel with ptrParams := [("p", ⟨none, 16⟩)] } :=
  fun h => by have := h.2.2.2 "p" ⟨none, 16⟩ 8 (by simp) rfl; simp at this
example : ({ launch with params := fun _ => some 32 } : Launch).Valid
    { kernel with ptrParams := [("p", ⟨none, 16⟩)] } := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro n h; cases h
  · intro n h; cases h
  · intro name p v h hv; simp at h; obtain ⟨rfl, rfl⟩ := h; simp at hv; subst hv; decide

end PTX.Tests.DecodeHeader
