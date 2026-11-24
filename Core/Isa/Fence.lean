-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Isa.Mem

@[expose] public section

namespace PTX

/-! ## PROG-ISA-FENCE — thread fences and proxy fences
Statement: A thread fence is its memory semantics and scope; `membar` is the thread fence
  `fence.sc` at the scope its level names. A proxy fence is its proxy kind (the alias proxy, the
  async proxy restricted to a state space or to all of them, the tensormap proxy, or a fabric
  direction) with its memory semantics and scope when it has a scope. The tensormap acquire fence
  keeps its address operand.

Defs: FenceSem, FenceSem.releases, FenceSem.acquires, FabricDir, ProxyFence, FenceInstr,
  FenceInstr.rule, Decode.FenceInstr.ofRaw

Source:
- §9.7.15.4: "fence{.sem}.scope;"
- §9.7.15.4: ".sem = { .sc, .acq_rel, .acquire, .release };"
- §9.7.15.4: "If the optional .sem qualifier is absent, .acq_rel is assumed by default."
- §9.7.15.4: "On sm_70 and higher membar is a synonym for fence.sc 1 , and the membar levels cta ,
    gl and sys are synonymous with the fence scopes cta , gpu and sys respectively."
- §9.7.15.4: "fence.proxy.proxykind; fence.proxy.proxykind{.sem}.scope;"
- §9.7.15.4: ".scope = { .cta, .cluster, .gpu, .sys };"
- §9.7.15.4: ".proxykind = { .alias, .async, .async.global, .async.shared::{cta, cluster} };"
- §9.7.15.4: "If no state space is specified, then the memory ordering applies on all state spaces."
- §9.7.15.4: ".to_proxykind::from_proxykind = {.tensormap::generic};"
- §9.7.15.4: ".to_proxykind::from_proxykind_fabric = {.generic::fabric, .fabric::generic,
    .fabric::fabric };"
- §9.7.15.4: ".sem_fabric = { .acquire, .release };"

Direction: representation

Applies: Every `fence` entry of the instruction table other than `fence.mbarrier_init`,
  `fence.proxy.proxykind{.sem}.scope` and `membar.{cta,gl,sys}`

Premises: The instruction is recognized by `Grammar.parse`.

Effect: Representation; `FenceInstr.rule` selects THREAD-FENCE for every form.
  `fence.mbarrier_init.release.cluster` keeps its own constructor `Op.fenceMbarInit`
  (OBJ-MBAR-INIT-PUBLICATION). `fence.proxy.proxykind{.sem}.scope`, which the instruction table
  leaves out, is an entry of its own (`fence_proxy_sem`, PROG-ISA-ENTRY); an absent `.sem` is
  `.acq_rel`, as for every fence. A proxy fence without a scope (`fence.proxy.proxykind`) has no
  semantics and scope; the tensormap fences have theirs, the fabric fences their `.sem_fabric` at
  `.sys`. The `.sync_restrict` fences (including the uni-directional `fence.proxy.async::generic`
  ones), `fence.alias.sync_restrict::read.release.sys` and `membar.proxy` are not entries of the
  instruction table or of the added entries and are not decoded.
-/

/-- The `.sem` of a thread fence (§9.7.15.4); `.acq_rel` when absent. -/
inductive FenceSem where
  | sc | acqRel | acquire | release
  deriving DecidableEq, Repr

/-- The fence is a release or acquire-release fence (§8.8 release pattern). -/
def FenceSem.releases : FenceSem → Bool
  | .acqRel | .release => true
  | _ => false

/-- The fence is an acquire or acquire-release fence (§8.8 acquire pattern). -/
def FenceSem.acquires : FenceSem → Bool
  | .acqRel | .acquire => true
  | _ => false

/-- The direction `.to_proxykind::from_proxykind_fabric` of a fabric proxy fence. -/
inductive FabricDir where
  | genericFabric | fabricGeneric | fabricFabric
  deriving DecidableEq, Repr

/-- The proxy kind of a proxy fence. `async none` applies to all state spaces; `async (some sp)`
to `.global`, `.shared::cta` or `.shared::cluster`; `tensormap` is `.tensormap::generic`. -/
inductive ProxyFence where
  | alias
  | async (space : Option StateSpace)
  | tensormap
  | fabric (dir : FabricDir)
  deriving DecidableEq, Repr

/-- A fence instruction other than `fence.mbarrier_init`: a thread fence (also `membar`), or a
proxy fence with its memory semantics and scope (`none` for a bi-directional proxy fence without a
scope) and the address operand of the tensormap acquire fence. -/
inductive FenceInstr where
  | thread (sem : FenceSem) (scope : MbarScope)
  | proxy (k : ProxyFence) (order : Option (FenceSem × MbarScope) := none)
      (addr : Option Addr := none)
  deriving DecidableEq, Repr

/-- Every fence form has THREAD-FENCE as its rule. -/
def FenceInstr.rule (_ : FenceInstr) : Option RuleId := some .threadFence

namespace Decode
open PTX.Syntax

/-- The fence of a recognized `fence` or `membar` entry, or `none` for an entry without a
representation (`fence.mbarrier_init`, decoded separately). -/
def FenceInstr.ofRaw (env : Env) (r : Isa.Raw) : M (Option FenceInstr) := do
  let scope : M MbarScope := do
    let some s ← MemAccess.scope? (r.get .scope) | throw "fence scope"
    pure s
  let sem : M FenceSem := match r.get .sem with
    | none | some .acq_rel => pure FenceSem.acqRel
    | some .sc => pure .sc
    | some .acquire => pure .acquire
    | some .release => pure .release
    | some _ => throw "fence semantics"
  let kind : M ProxyFence := match r.get .proxykind, r.get .space with
    | some .alias, none => pure .alias
    | some .async, none => pure (.async none)
    | some .async, some .global_ => pure (.async (some .global))
    | some .async, some .shared_cta => pure (.async (some (.shared .cta)))
    | some .async, some .shared_cluster => pure (.async (some (.shared .cluster)))
    | _, _ => throw "proxy fence kind"
  match r.entry with
  | .fence => return some (.thread (← sem) (← scope))
  | .fence_proxy => return some (.proxy (← kind))
  | .fence_proxy_sem => return some (.proxy (← kind) (some (← sem, ← scope)))
  | .fence_proxy_tensormap_release => return some (.proxy .tensormap (some (.release, ← scope)))
  | .fence_proxy_tensormap_acquire =>
    let addr ← MemAccess.addrOf env (← arg r "addr")
    return some (.proxy .tensormap (some (.acquire, ← scope)) (some addr))
  | .fence_proxy_fabric =>
    let dir ← match r.get .direction with
      | some .generic_fabric => pure FabricDir.genericFabric
      | some .fabric_generic => pure .fabricGeneric
      | some .fabric_fabric => pure .fabricFabric
      | _ => throw "fabric fence direction"
    return some (.proxy (.fabric dir) (some (← sem, ← scope)))
  | .membar =>
    let scope ← match r.get .level with
      | some .cta => pure MbarScope.cta
      | some .gl => pure .gpu
      | some .sys => pure .sys
      | _ => throw "membar level"
    return some (.thread .sc scope)
  | _ => return none

end Decode

end PTX
