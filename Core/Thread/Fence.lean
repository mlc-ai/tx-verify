-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Access

@[expose] public section

/-!
# Thread semantics: fences

The event a fence performs. Which orderings a fence creates is decided by the execution rules
(MEM-RELEASE-ACQUIRE, MEM-FENCE-SC, MEM-MODEL-CAUSALITY).
-/

namespace PTX

noncomputable section

/-! ## THREAD-FENCE — thread fences and proxy fences
Statement: Each thread fence performs one event that records its semantics and scope, and each
  proxy fence performs one event that records its proxy kind and its scope (none for a form without
  a scope). The `.sem` of a proxy fence creates no synchronization; the scope of an async proxy
  fence bounds the threads its order reaches (MEM-MODEL-CAUSALITY).
  `fence.proxy.tensormap::generic.acquire` whose address does not lie in the global state space is
  undefined behaviour.

Defs: fenceTmpl, fenceTmpl_asyncCta, fenceTmpl_proxy_order

Source:
- §9.7.15.4: "The fence instruction establishes an ordering between memory accesses requested by
    this thread ( ld , st , atom and red instructions) as described in the Memory Consistency
    Model ."
- §9.7.15.4: "Generic Addressing is used unconditionally, and the address specified by the operand
    addr must fall within the .global state space. Otherwise, the behavior is undefined."
- §9.7.15.4: "Bi-directional proxy fences do not directly synchronize with other fences in the sense
    that fences with .release or .acquire semantics do."
- §9.7.15.4: "Instead, bi-directional proxy fences take effect within a single thread and therefore
    do not have a .scope qualifier."
- §9.7.15.4 (syntax): "// Proxy fence (bi-directional): fence.proxy.proxykind;
    fence.proxy.proxykind{.sem}.scope;"
- §9.7.15.4: "A .release proxy fence can form a release sequence that synchronizes with an acquire
    sequence that contains a .acquire proxy fence."
- §9.7.15.4: "Value .alias of the .proxykind qualifier refers to memory accesses performed using
    virtually aliased addresses to the same memory location."
- §8.4 (Table 20): "memory fence operation A membar , fence.sc or fence.acq_rel instruction."
- §8.4 (Table 20): "proxy fence operation A fence.proxy or a membar.proxy instruction."
- §8.6: "Operations using methods of access distinct from the generic method include: textures and
    surface accesses, accesses to the same location via the same proxy using distinct virtual memory
    addresses, async-proxy and tensormap-proxy accesses by .async.bulk operations, fabric-proxy
    accesses by fabric operations, readonly-proxy accesses by ld.proxy::readonly operations."
- EXT-LAUNCH (no aliases)

Direction: stricter

Applies: Every `Op.fence` (PROG-ISA-FENCE), `fence.proxy.proxykind{.sem}.scope` included

Premises: The tensormap acquire fence's generic address names a global location.

Effect: Event production (`.fence`, `.fenceProxy`) and one local fault. A thread fence (`fence.sc`,
  `fence.acq_rel`, `fence.acquire`, `fence.release`, `membar`) is the event `.fence sem scope`; its
  synchronization is MEM-RELEASE-ACQUIRE (release and acquire patterns) and MEM-FENCE-SC
  (`fence.sc`). A proxy fence is the event `.fenceProxy k scope`: `scope` is the scope of
  `fence.proxy.proxykind{.sem}.scope` and of the tensormap and fabric proxy fences, and `none` for
  `fence.proxy.proxykind`, which has no scope. The syntax lists both forms as bi-directional proxy
  fences although the text says that bi-directional proxy fences have no scope; the event keeps the
  scope so that MEM-MODEL-CAUSALITY can bound the fence's reach by it. An async proxy fence orders
  generic and async-proxy accesses at the bytes of its state space for the threads it reaches
  (MEM-MODEL-CAUSALITY, `ProxyFenceReach`). The other proxy fences create no order in the model,
  which is stricter than the text wherever they would: the alias proxy fence orders accesses through
  distinct virtual addresses of one location, and the model's launches have no aliases (EXT-LAUNCH);
  the tensormap proxy fences order generic accesses with tensormap-proxy reads, and the model's
  tensormap-proxy reads read only the launch's tensor maps; the fabric proxy fences order generic
  accesses with fabric operations, which have no rule. The `.sem` of a proxy fence
  (`fence.proxy.proxykind{.sem}.scope`, the tensormap and the fabric proxy fences) gives no
  synchronization (stricter). The text lets a `.release` proxy fence form a release sequence that
  synchronizes with an acquire sequence containing a `.acquire` proxy fence, but it does not say
  whether such a sequence also synchronizes with a release or acquire pattern without a proxy fence,
  nor what `.sc` adds to a proxy fence (Table 20 names `fence.sc` and `fence.acq_rel` as memory
  fence operations and `fence.proxy` as a proxy fence operation). Leaving the synchronization of the
  `.sem` out removes no execution: a kernel that needs it is rejected, for example by a race report.
  The scope is not left out: leaving it out would let a fence of a narrower scope order the accesses
  of threads outside that scope, which removes the executions in which those accesses do not see the
  ordered access. The address of `fence.proxy.tensormap::generic.acquire` is located as a load's
  generic address (THREAD-ADDR): a generic number is a global address (EXT-CVTA), a shared, local or
  constant pointer is undefined (`badValue`), and an address `accessLoc` cannot locate has no rule.
-/

/-- The event of a fence (THREAD-FENCE). -/
def fenceTmpl (L : Launch) (g : Nat) (t : TState) : Op → Tmpl
  | .fence (.thread sem scope) => .fence sem scope (next t)
  | .fence (.proxy k o (some a)) =>
    let acc : MemAccess :=
      { kind := .load, space := none, sem := .weak, elem := .int .b 8, addr := a }
    match accessLoc L g t acc with
    | .error f => .ub f
    | .ok loc => if loc.space = .global then .fenceProxy k (o.map (·.2)) (next t) else .ub .badValue
  | .fence (.proxy k o none) => .fenceProxy k (o.map (·.2)) (next t)
  | _ => .ub .noRule

/-- `fence.proxy.async.shared::cta` performs its proxy fence event without a scope. -/
theorem fenceTmpl_asyncCta (L : Launch) (g : Nat) (t : TState) :
    fenceTmpl L g t (.fence (.proxy (.async (some (.shared .cta))))) =
      .fenceProxy (.async (some (.shared .cta))) none (next t) := rfl

/-- A proxy fence with a `.sem` and a scope and without an address performs the event of the
proxy fence of its kind with that scope. -/
theorem fenceTmpl_proxy_order (L : Launch) (g : Nat) (t : TState) (k : ProxyFence)
    (sem : FenceSem) (scope : MbarScope) :
    fenceTmpl L g t (.fence (.proxy k (some (sem, scope)) none)) =
      .fenceProxy k (some scope) (next t) := rfl

end

end PTX
