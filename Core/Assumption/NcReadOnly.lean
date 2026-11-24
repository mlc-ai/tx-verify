-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Core.Assumption.ClusterScopeMbar

@[expose] public section

/-!
# Assumption constructor `ncReadOnly`

A kernel declares a read-only non-coherent load assumption with `Assumption.ncReadOnly`, naming
exactly the `ld.global.nc` sites (`pc`) its proof relies on. This file is not itself an
assumption.
-/

namespace PTX.Assumption

/-! ## ASM-NC — ld.global.nc at named sites reads launch content
Statement: At the `ld.global.nc` sites a kernel names, the model trusts that the load returns the
  launch content of the bytes it reads, and a write of those bytes by any operation of the kernel is
  undefined behaviour. A kernel that reads such data with a plain `ld.global` does not need this
  assumption.

Defs: Assumption.ncReadOnly

Source:
- §8.1 (the memory model does not apply to ld.global.nc)
- §9.7.10.9 (ld.global.nc)
- CUDA `__ldg` / `const __restrict__` contract

Direction: trust

Effect: The core has no rule for `ld.global.nc`. `ncReadOnly name sites why` sets three fields,
  each for exactly the sites (`pc`) in `sites`:
  * `ncLoads`: allows the load there, as a read outside the memory model (no `baseCausality`, no
    reads-from, no races).
  * `wf` (**removes executions**): an `nc` read at one of the sites returns the launch content
    of every byte whose launch content is known, using the same fixed `X.initial` choice for
    unspecified allocated bytes as ordinary reads. Executions where it returns anything else are
    not possible.
  * `ub` (only stricter): undefined if any byte an `nc` read at one of the sites reads is
    written by any issued ordinary or asynchronous operation of the execution, in any order.
  The statement is generated from the sites and lists every site it covers.

Evidence: Data that no thread writes during the kernel is read-only for the texture path.

Review: `wf` is only relied on when nothing writes the bytes.
-/

/-- `ld.global.nc` at exactly `sites` reads unwritten launch content; `why` says why the kernel
needs it. -/
noncomputable def ncReadOnly (name : String) (sites : List Nat) (why : String) : Assumption where
  name := name
  statement := s!"ld.global.nc at exactly these sites: {siteText sites} returns the launch \
    content of bytes no operation of the kernel writes; writing such a byte is undefined. {why}"
  ncLoads pc := sites.contains pc
  wf _ mem0 X := ∀ e pc a bs, X.get e = some ⟨pc, .nc a bs⟩ → sites.contains pc →
    bs.length = a.size ∧ ∀ k < a.size, ∀ c, mem0 (a.loc.at k) = some c →
      bs[k]? = some (X.initialByte c (a.loc.at k))
  ub _ _ X := ∃ e pc a bs w a' l, X.get e = some ⟨pc, .nc a bs⟩ ∧ sites.contains pc ∧
    a.Covers l ∧ X.Intent w a' true ∧ a'.Covers l

end PTX.Assumption
