-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Types

@[expose] public section

/-!
# Assumption constructor `clusterScopeMbarAt`

A kernel declares a cluster-scope mbarrier assumption with `Assumption.clusterScopeMbarAt`,
naming exactly the instruction sites (`pc`) whose `.cta`-scoped mbarrier synchronization its
proof treats as cluster-scoped. This file is not itself an assumption.
-/

namespace PTX.Assumption

/-! ## ASM-MBAR-SCOPE — CTA-scoped mbarrier synchronization reaches the cluster, at named sites
Statement: At the mbarrier sites a kernel names, the model treats `.cta`-scoped release arrivals and
  acquire waits as `.cluster`-scoped, so an arrival on a peer CTA's mbarrier synchronizes with the
  threads of that CTA that wait on it. A kernel that writes `.release.cluster` and
  `.acquire.cluster` at these sites does not need this assumption.

Defs: Assumption.siteText, Assumption.clusterScopeMbarAt

Source:
- §9.7.15.16.16 (arrive): "If the .scope qualifier is not specified then it defaults to .cta"
- §9.7.15.16.16 (.scope): "the set of threads that directly observe the memory synchronizing
    effect"
- §9.7.15.16.19 (try_wait: same default)
- CuTeDSL `cute/arch/mbar.py` `mbarrier_arrive`

Direction: trust

Effect: The ISA gives a `.cta`-scoped release arrival on a peer CTA's mbarrier no synchronizing
  effect for the waiting thread of that CTA, so the core (MEM-MBAR-SYNCHRONIZES) adds no
  `baseCausality` edge. Production code nevertheless hands off data this way: CUTLASS
  `ClusterBarrier::arrive` (`include/cutlass/arch/barrier.h`), DeepGEMM, ThunderKittens and
  Triton/Gluon remote arrivals use the default `.cta` scope. `clusterScopeMbarAt name sites why`
  sets one field, `clusterScopeMbar`, which adds synchronization: at exactly the sites (`pc`) in
  `sites`, `.cta`-scoped release arrivals and acquire waits, including the default
  `try_wait.parity`, are treated as `.cluster`-scoped (THREAD-RUN `widenMbarScope`). Relaxed
  operations and every other site are unchanged. Same-CTA pairs gain no new edge. Peer-CTA pairs on
  the same object in one cluster synchronize. The statement is generated from the sites and lists
  every site it covers.

Evidence: NVIDIA's CuTeDSL keeps `.cta` as the default for remote arrivals. Its source comment,
  which is not PTX text, states: “Remote CTA arrivals should be cluster-scoped for formal
  cross-CTA memory-model ordering. Keep the historical CTA default because existing retry-sync
  protocols rely only on the barrier count and current hardware/compiler behavior”. This is a
  statement about current hardware and compilers. The ISA does not guarantee it. A kernel that
  uses `.release.cluster` / `.acquire.cluster` for its peer-CTA handoffs does not need this
  assumption.
-/

def siteText (sites : List Nat) : String :=
  ", ".intercalate (sites.map fun pc => s!"pc {pc}")

/-- Cluster-scope synchronization for the `.cta`-scoped mbarrier release arrivals and acquire
waits at exactly `sites`; `why` says why the kernel needs it. -/
def clusterScopeMbarAt (name : String) (sites : List Nat) (why : String) : Assumption where
  name := name
  statement := s!"A .cta-scoped mbarrier release arrival or acquire wait synchronizes at \
    cluster scope, at exactly these sites: {siteText sites}. {why}"
  clusterScopeMbar pc := sites.contains pc

end PTX.Assumption
