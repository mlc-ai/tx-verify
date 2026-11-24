-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Mathlib.Tactic
public import Lemmas.Order.Order

namespace PTX.Tests.Acquire
noncomputable section
private def L : Launch := { grid := 1, block := 32, params := fun _ => none }
private def env : Decode.Env :=
  { classes := [⟨"q".toList, 1, 128⟩, ⟨"r".toList, 1, 32⟩], labels := [], params := [] }
example : Decode.op env "ld.acquire.cta.shared.b128" [.register "q0", .address [.register "r0"]] =
    .ok (.mem {
      kind := .load, space := some (.shared .cta), sem := .acquire, scope := some .cta,
      elem := .int .b 128, addr := ⟨.reg 1 32, 0⟩, dsts := [some 0] }) := rfl
private def t : TState := { regs := fun _ => some (.bits 32 16) }
private def a : Acc := { loc := ⟨.shared, 0, 16⟩, size := 16, acquire := true }
example : acquireLoadTmpl [] L 0 t .cta .shared 128 0 1 0 =
    .read a (afterLoad t [0]) := rfl
-- Acquire is still an ordinary 16-byte read, checked by RfWf and Unsafe.
example {X : Execution} {e : EvId} {bs : List (Option Byte)} (h : X.Reads e a bs) :
    X.MemReads (.thread e) a bs := .inl h
-- Reading a CLC payload preserves its identity through byte reconstruction.
example (r : ClcResponse) : rebuild 3 ((Value.clc r).toBytes.map some) = .ok (.clc r) := by
  have he : (Value.clc r).toBytes.map some =
      some (Value.clc r, 0) :: (List.range 15).map (fun k =>
        some ((Value.clc r).byteAt (k + 1))) := by
    simp [Value.toBytes, Value.bytes, List.range_succ_eq_map, Value.byteAt]
  rw [he]
  simp only [rebuild]
  rw [ite_eq_left ⟨by simp [Value.bytes], he.symm⟩]
  rfl
-- A matching release contributes a real base causality edge.
example {X : Execution} {e f : EvId} (h : synchronizesWith L X e f) : baseCausality L X e f :=
  .single (.inr (.inr (.inr (.inr (.inr (.inl h))))))
-- An acquire whose bytes all come from W0 cannot create such a release edge.
example {X : Execution} {e f : EvId} (h0 : ∀ k, X.rf (.thread f) k = none) :
    ¬ synchronizesWith L X e f := by
  rintro ⟨a, b, bs, cs, _, _, _, _, _, _, hn, _, _, hr⟩
  have := hr 0 hn
  rw [h0] at this
  contradiction
-- A weak writer cannot be silently treated as a release writer.
example {X : Execution} {e f : EvId} {a : Acc} {bs : List Byte}
    (hw : X.MemWrites (.thread e) a bs) (weak : a.release = false) :
    ¬ synchronizesWith L X e f := by
  rintro ⟨a', b, bs', cs, hw', _, rel, _⟩
  have heq : a' = a := by
    rcases hw with ⟨pc, h⟩ | ⟨old, pc, h⟩
    · rcases hw' with ⟨pc', h'⟩ | ⟨old', pc', h'⟩
      · rw [h] at h'
        cases h'
        rfl
      · rw [h] at h'
        cases h'
    · rcases hw' with ⟨pc', h'⟩ | ⟨old', pc', h'⟩
      · rw [h] at h'
        cases h'
      · rw [h] at h'
        cases h'
        rfl
  rw [heq, weak] at rel
  contradiction

private def envScope : Decode.Env :=
  { classes := [⟨"rd".toList, 1, 64⟩, ⟨"r".toList, 2, 32⟩], labels := [], params := [] }
private def ldGpu : MemAccess :=
  { kind := .load, space := some .global, sem := .relaxed, scope := some .gpu,
    elem := .int .u 32, addr := ⟨.reg 0 64, 0⟩, dsts := [some 1] }
private def stSys : MemAccess :=
  { kind := .store, space := some .global, sem := .release, scope := some .sys,
    elem := .int .u 32, addr := ⟨.reg 0 64, 0⟩, srcs := [.reg 2] }
-- `.gpu` and `.sys` accesses decode to `Op.mem` with the scope recorded; a strong access with a
-- scope is THREAD-ACCESS.
example : Decode.op envScope "ld.relaxed.gpu.global.u32"
    [.register "r0", .address [.register "rd0"]] = .ok (.mem ldGpu) := rfl
example : ldGpu.rule = some .threadAccess := rfl
example : Decode.op envScope "st.release.sys.global.u32"
    [.address [.register "rd0"], .register "r1"] = .ok (.mem stSys) := rfl
example : stSys.rule = some .threadAccess := rfl
-- The same entry at `.cta` scope is the same representation, with THREAD-ACCESS.
example : Decode.op envScope "st.release.cta.global.u32"
    [.address [.register "rd0"], .register "r1"] = .ok (.mem { stSys with scope := some .cta }) :=
  rfl
-- The syntax of `mbarrier.arrive` lists `.cta` and `.cluster` only; `.gpu` is rejected.
example : (Decode.op envScope "mbarrier.arrive.release.gpu.shared::cta.b64"
    [.register "rd0", .address [.register "r0"]]).toOption = none := rfl
example : Decode.op envScope "mbarrier.arrive.release.cluster.shared::cta.b64"
    [.register "rd0", .address [.register "r0"]] =
    .ok (.mbarArrive 1 0 (.imm 0) (.imm 1) false true .cluster (some 0)) := rfl

-- Scope inclusion (MEM-SCOPE) in a launch of two CTAs of 32 threads each, one CTA per cluster.
private def L2 : Launch := { grid := 2, block := 32, params := fun _ => none }
example : MbarScopeIncludes L2 .cta 0 31 := by
  simp [MbarScopeIncludes, SameCta, L2, Launch.threads]
example : ¬ MbarScopeIncludes L2 .cta 0 32 := by
  simp [MbarScopeIncludes, SameCta, L2, Launch.threads]
example : MbarScopeIncludes L2 .gpu 0 32 := by simp [MbarScopeIncludes, L2, Launch.threads]
example : MbarScopeIncludes L2 .sys 63 0 := by simp [MbarScopeIncludes, L2, Launch.threads]
-- `.gpu` and `.sys` include no thread outside the launch.
example : ¬ MbarScopeIncludes L2 .sys 0 64 := by simp [MbarScopeIncludes, L2, Launch.threads]
example : ¬ MbarScopeIncludes L2 .gpu 64 0 := by simp [MbarScopeIncludes, L2, Launch.threads]

end
end PTX.Tests.Acquire
