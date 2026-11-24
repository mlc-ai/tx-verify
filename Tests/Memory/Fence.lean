-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Core.Source.Decode
public import Mathlib.Tactic

/-!
# Fences, strong loads and stores, and the forms without a rule (PROG-ISA-FENCE, THREAD-FENCE,
THREAD-ACCESS)

* Every `fence` and `membar` form of the instruction table decodes to `Op.fence` with THREAD-FENCE;
  `fence.mbarrier_init` keeps `Op.fenceMbarInit`. Malformed forms are rejected at decoding.
* `fence.proxy.proxykind{.sem}.scope` decodes with its semantics and scope (an absent `.sem` is
  `.acq_rel`) and performs the event of the proxy fence of its kind.
* A fence performs one event; `fence.proxy.tensormap::generic.acquire` at a shared address is
  undefined behaviour.
* `.relaxed`, `.acquire`, `.release` accesses at every scope and `.volatile` accesses have
  THREAD-ACCESS and carry their semantics in the footprint; `.mmio` accesses keep their `.relaxed`,
  `.acquire` or `.release` at `.sys`. A strong access at a space the text does not allow has no
  rule.
* `multimem` decodes to `Op.unmodeled` and has no rule.
-/

namespace PTX.Tests.Fence
noncomputable section

private def env : Decode.Env :=
  { classes := [⟨"rd".toList, 2, 64⟩, ⟨"r".toList, 2, 32⟩], labels := [], params := [] }

/-! ## Decoding -/

example : Decode.op env "fence.sc.cta" [] = .ok (.fence (.thread .sc .cta)) := rfl
example : Decode.op env "fence.cluster" [] = .ok (.fence (.thread .acqRel .cluster)) := rfl
example : Decode.op env "fence.acq_rel.gpu" [] = .ok (.fence (.thread .acqRel .gpu)) := rfl
example : Decode.op env "fence.acquire.sys" [] = .ok (.fence (.thread .acquire .sys)) := rfl
example : Decode.op env "fence.release.cta" [] = .ok (.fence (.thread .release .cta)) := rfl
-- `membar` is `fence.sc`; the level `gl` is the scope `.gpu`.
example : Decode.op env "membar.gl" [] = .ok (.fence (.thread .sc .gpu)) := rfl
example : Decode.op env "membar.cta" [] = .ok (.fence (.thread .sc .cta)) := rfl
example : Decode.op env "membar.sys" [] = .ok (.fence (.thread .sc .sys)) := rfl
example : Decode.op env "fence.proxy.alias" [] = .ok (.fence (.proxy .alias)) := rfl
example : Decode.op env "fence.proxy.async" [] = .ok (.fence (.proxy (.async none))) := rfl
example : Decode.op env "fence.proxy.async.global" [] =
    .ok (.fence (.proxy (.async (some .global)))) := rfl
example : Decode.op env "fence.proxy.async.shared::cta" [] =
    .ok (.fence (.proxy (.async (some (.shared .cta))))) := rfl
example : Decode.op env "fence.proxy.async.shared::cluster" [] =
    .ok (.fence (.proxy (.async (some (.shared .cluster))))) := rfl
example : Decode.op env "fence.proxy.tensormap::generic.release.gpu" [] =
    .ok (.fence (.proxy .tensormap (some (.release, .gpu)))) := rfl
example : Decode.op env "fence.proxy.tensormap::generic.acquire.cta"
    [.address [.register "rd0"], .literal "128"] =
    .ok (.fence (.proxy .tensormap (some (.acquire, .cta)) (some ⟨.reg 0 64, 0⟩))) := rfl
example : Decode.op env "fence.proxy.generic::fabric.alias.release.sys" [] =
    .ok (.fence (.proxy (.fabric .genericFabric) (some (.release, .sys)))) := rfl
example : Decode.op env "fence.proxy.fabric::generic.alias.acquire.sys" [] =
    .ok (.fence (.proxy (.fabric .fabricGeneric) (some (.acquire, .sys)))) := rfl
-- `fence.proxy.proxykind{.sem}.scope` (§9.7.15.4), the forms of the section's own example.
example : Decode.op env "fence.proxy.alias.release.sys" [] =
    .ok (.fence (.proxy .alias (some (.release, .sys)))) := rfl
example : Decode.op env "fence.proxy.alias.acquire.sys" [] =
    .ok (.fence (.proxy .alias (some (.acquire, .sys)))) := rfl
example : Decode.op env "fence.proxy.async.acquire.gpu" [] =
    .ok (.fence (.proxy (.async none) (some (.acquire, .gpu)))) := rfl
example : Decode.op env "fence.proxy.async.shared::cta.sc.cluster" [] =
    .ok (.fence (.proxy (.async (some (.shared .cta))) (some (.sc, .cluster)))) := rfl
example : Decode.op env "fence.proxy.async.global.acq_rel.cta" [] =
    .ok (.fence (.proxy (.async (some .global)) (some (.acqRel, .cta)))) := rfl
-- Without `.sem` the fence is `.acq_rel` ("If the optional .sem qualifier is absent, .acq_rel is
-- assumed by default.").
example : Decode.op env "fence.proxy.alias.cluster" [] =
    .ok (.fence (.proxy .alias (some (.acqRel, .cluster)))) := rfl
example : Decode.op env "fence.mbarrier_init.release.cluster" [] = .ok .fenceMbarInit := rfl
-- Rejected: a thread fence needs a scope, `membar` has no `.gpu` level, the alias proxy fence has
-- no state space, the tensormap acquire fence's size is 128.
example : (Decode.op env "fence.sc" []).toOption = none := rfl
example : (Decode.op env "membar.gpu" []).toOption = none := rfl
example : (Decode.op env "fence.proxy.alias.global" []).toOption = none := rfl
example : (Decode.op env "fence.proxy.alias.release.global.sys" []).toOption = none := rfl
example : (Decode.op env "fence.proxy.alias.shared::cta.release.sys" []).toOption = none := rfl
example : (Decode.op env "fence.proxy.async.release" []).toOption = none := rfl
example : (Decode.op env "fence.proxy.async.release.gl" []).toOption = none := rfl
example : (Decode.op env "fence.proxy.tensormap::generic.acquire.cta"
    [.address [.register "rd0"], .literal "64"]).toOption = none := rfl

-- Every fence form has THREAD-FENCE, and performs an event.
example (f : FenceInstr) : (Op.fence f).rule = some .threadFence := rfl
example (f : FenceInstr) : (Op.fence f).isLocal = false := rfl

/-! ## Events -/

private def L : Launch := { grid := 2, block := 32, params := fun _ => none }
private def tg : TState := { regs := fun _ => some (.bits 64 64) }

example : fenceTmpl L 0 tg (.fence (.thread .sc .gpu)) = .fence .sc .gpu (next tg) := rfl
example : fenceTmpl L 0 tg (.fence (.proxy .alias)) = .fenceProxy .alias none (next tg) := rfl
-- A proxy fence with a `.sem` and a scope is the event of the proxy fence of its kind with that
-- scope: its semantics create no synchronization (THREAD-FENCE, stricter).
example : fenceTmpl L 0 tg (.fence (.proxy .alias (some (.release, .sys)))) =
    .fenceProxy .alias (some .sys) (next tg) := rfl
example : fenceTmpl L 0 tg (.fence (.proxy (.async (some .global)) (some (.acquire, .cta)))) =
    .fenceProxy (.async (some .global)) (some .cta) (next tg) := rfl
-- The tensormap acquire fence at a generic number (a global address) is an event.
example : fenceTmpl L 0 tg (.fence (.proxy .tensormap (some (.acquire, .gpu))
    (some ⟨.reg 0 64, 0⟩))) = .fenceProxy .tensormap (some .gpu) (next tg) := by
  simp [fenceTmpl, accessLoc, readReg, tg, wrapAddr, readBits]
  rfl
-- At a local address it is undefined behaviour.
private def tl : TState := { regs := fun _ => some (.ptr 64 true (.local 0) (BitVec.ofNat 64 8)) }
example : fenceTmpl L 0 tl (.fence (.proxy .tensormap (some (.acquire, .gpu))
    (some ⟨.reg 0 64, 0⟩))) = .ub .badValue := by
  simp [fenceTmpl, accessLoc, readReg, tl]
  rfl

/-! ## Strong loads and stores -/

private def ld (sem : Sem) (scope : Option MbarScope) (sp : Option StateSpace)
    (mmio : Bool := false) : MemAccess :=
  { kind := .load, space := sp, sem := sem, scope := scope, elem := .int .u 32,
    addr := ⟨.reg 0 64, 0⟩, dsts := [some 2], mmio := mmio }
private def st (sem : Sem) (scope : Option MbarScope) (sp : Option StateSpace)
    (mmio : Bool := false) : MemAccess :=
  { kind := .store, space := sp, sem := sem, scope := scope, elem := .int .u 32,
    addr := ⟨.reg 0 64, 0⟩, srcs := [.reg 2], mmio := mmio }

example : Decode.op env "ld.relaxed.gpu.global.u32" [.register "r0", .address [.register "rd0"]] =
    .ok (.mem (ld .relaxed (some .gpu) (some .global))) := rfl
example : Decode.op env "ld.volatile.global.u32" [.register "r0", .address [.register "rd0"]] =
    .ok (.mem (ld .volatile none (some .global))) := rfl
example : Decode.op env "ld.mmio.relaxed.sys.global.u32"
    [.register "r0", .address [.register "rd0"]] =
    .ok (.mem (ld .relaxed (some .sys) (some .global) true)) := rfl
-- `.mmio` keeps the access's `.sem` (§9.7.10.8: "ld.mmio.sem.sys{.global}.type d, [a];").
example : Decode.op env "ld.mmio.acquire.sys.global.u32"
    [.register "r0", .address [.register "rd0"]] =
    .ok (.mem (ld .acquire (some .sys) (some .global) true)) := rfl
example : Decode.op env "st.mmio.release.sys.global.u32"
    [.address [.register "rd0"], .register "r0"] =
    .ok (.mem (st .release (some .sys) (some .global) true)) := rfl
example : Decode.op env "st.mmio.relaxed.sys.u32" [.address [.register "rd0"], .register "r0"] =
    .ok (.mem (st .relaxed (some .sys) none true)) := rfl
example : Decode.op env "st.release.sys.u32" [.address [.register "rd0"], .register "r0"] =
    .ok (.mem (st .release (some .sys) none)) := rfl

example : (ld .relaxed (some .gpu) (some .global)).rule = some .threadAccess := rfl
example : (ld .acquire (some .cluster) none).rule = some .threadAccess := rfl
example : (st .relaxed (some .cta) (some (.shared .cluster))).rule = some .threadAccess := rfl
example : (st .release (some .sys) (some .global)).rule = some .threadAccess := rfl
example : (ld .volatile none (some .local)).rule = some .threadAccess := rfl
example : (st .relaxed (some .sys) (some .global) true).rule = some .threadAccess := rfl
example : (st .release (some .sys) (some .global) true).rule = some .threadAccess := rfl
example : (ld .relaxed (some .sys) none true).rule = some .threadAccess := rfl
example : (ld .acquire (some .sys) (some .global) true).rule = some .threadAccess := rfl
-- Without a rule: `.relaxed` of the local space, `.mmio` of the shared space, at another scope
-- than `.sys`, as a vector, an `.mmio` acquire store or release load, a weak `.mmio` access,
-- `.release` loads.
example : (ld .relaxed (some .gpu) (some .local)).rule = none := rfl
example : (ld .relaxed (some .sys) (some (.shared .cta)) true).rule = none := rfl
example : (ld .relaxed (some .gpu) (some .global) true).rule = none := rfl
example : ({ ld .relaxed (some .sys) (some .global) true with vec := 2, dsts := [some 2, some 3] } :
    MemAccess).rule = none := rfl
example : (st .acquire (some .sys) (some .global) true).rule = none := rfl
example : (ld .release (some .sys) (some .global) true).rule = none := rfl
example : (ld .weak none (some .global) true).rule = none := rfl
example : (ld .release (some .gpu) (some .global)).rule = none := rfl

/-- The footprint of the event of a load or store template, if it is one. -/
private def accOf : Tmpl → Option Acc
  | .read a _ | .write a _ _ => some a
  | _ => none

private def g16 : Loc := ⟨.global, 0, 64⟩
private def t2 : TState :=
  { regs := fun r => if r = 0 then some (.bits 64 64) else some (.bits 32 7) }

-- A `.relaxed.gpu` load reads with its semantics and scope.
example : accOf (memTmpl [] L 0 t2 (ld .relaxed (some .gpu) (some .global))) =
    some { loc := g16, size := 4, relaxed := true, scope := .gpu } := by
  simp [memTmpl, MemAccess.rule, MemAccess.locSpace?, ld, accessTmpl, accessAcc, accessLoc,
    effAddr, readReg, t2, readBits, MemAccess.strongLocOk, elemAcc, accOf, g16, Loc.at]
  rfl
-- A `.volatile` store is `.relaxed` at `.sys`.
example : accOf (memTmpl [] L 0 t2 (st .volatile none (some .global))) =
    some { loc := g16, size := 4, relaxed := true, scope := .sys } := by
  simp [memTmpl, MemAccess.rule, MemAccess.locSpace?, st, accessTmpl, accessAcc, accessLoc,
    effAddr, readReg, t2, readBits, MemAccess.strongLocOk, elemAcc, accOf, g16, Loc.at,
    readValue, storeValue]
  rfl
-- An `.acquire.gpu` load located directly reads with acquire semantics at `.gpu`.
example : accOf (memTmpl [] L 0 t2 (ld .acquire (some .gpu) (some .global))) =
    some { loc := g16, size := 4, acquire := true, scope := .gpu } := by
  simp [memTmpl, MemAccess.rule, MemAccess.locSpace?, ld, acquireLoadTmpl, loadTmpl, effAddr,
    readReg, t2, readBits, elemAcc, accOf, g16, Loc.at]
  rfl
-- An `.mmio.acquire.sys` load reads with acquire semantics at `.sys`, so it ends an acquire
-- pattern (MEM-RELEASE-ACQUIRE), directly located or through `accessLoc`.
example : accOf (memTmpl [] L 0 t2 (ld .acquire (some .sys) (some .global) true)) =
    some { loc := g16, size := 4, acquire := true, scope := .sys } := by
  simp [memTmpl, MemAccess.rule, MemAccess.locSpace?, ld, acquireLoadTmpl, loadTmpl, effAddr,
    readReg, t2, readBits, elemAcc, accOf, g16, Loc.at]
  rfl
example : accOf (memTmpl [] L 0 t2 (ld .acquire (some .sys) none true)) =
    some { loc := g16, size := 4, acquire := true, scope := .sys } := by
  simp [memTmpl, MemAccess.rule, MemAccess.locSpace?, ld, accessTmpl, accessAcc, accessLoc,
    readReg, t2, readBits, MemAccess.strongLocOk, elemAcc, accOf, g16, Loc.at, wrapAddr]
  rfl
-- An `.mmio.release.sys` store writes with release semantics at `.sys`; `.mmio.relaxed.sys` is
-- `.relaxed` at `.sys`, as before.
example : accOf (memTmpl [] L 0 t2 (st .release (some .sys) (some .global) true)) =
    some { loc := g16, size := 4, release := true, scope := .sys } := by
  simp [memTmpl, MemAccess.rule, MemAccess.locSpace?, st, releaseStoreTmpl, storeTmpl, effAddr,
    readReg, t2, readBits, elemAcc, accOf, g16, Loc.at, readValue, storeValue]
  rfl
example : accOf (memTmpl [] L 0 t2 (st .relaxed (some .sys) (some .global) true)) =
    some { loc := g16, size := 4, relaxed := true, scope := .sys } := by
  simp [memTmpl, MemAccess.rule, MemAccess.locSpace?, st, accessTmpl, accessAcc, accessLoc,
    effAddr, readReg, t2, readBits, MemAccess.strongLocOk, elemAcc, accOf, g16, Loc.at,
    readValue, storeValue]
  rfl
-- A weak load is unchanged by the strong rule.
example : accOf (memTmpl [] L 0 t2 (ld .weak none (some .global))) =
    some { loc := g16, size := 4 } := by
  simp [memTmpl, MemAccess.rule, MemAccess.locSpace?, ld, loadTmpl, effAddr, readReg, t2,
    readBits, elemAcc, accOf, g16, Loc.at]
  rfl

/-! ## `multimem` has no rule -/

example : ∃ r, Decode.op env "multimem.ld_reduce.relaxed.gpu.global.add.u32"
    [.register "r0", .address [.register "rd0"]] = .ok (.unmodeled r) := ⟨_, rfl⟩
example (r : Isa.Raw) : (Op.unmodeled r).rule = none := rfl

end
end PTX.Tests.Fence
