-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Tmem
public import Lemmas.Tmem.Alloc512
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # The Tensor Memory allocation of a CTA pair

Warp 12 of each CTA of a cluster makes the pair's resource operations: it allocates all 512
columns, relinquishes its permit and deallocates, in that order (`TmemFacts.event`,
`warpOps`). From the library's pair protocol (`Lemmas/Tmem/PairProtocol`):

* **TmemBase0.** Every allocation a CTA's history records is of all 512 columns at column 0
  (`base0`): it is the history's first record, and an empty allocator places 512 columns only
  at column 0. The address lane 0 stores after its allocation is therefore 0 (`store_zero`), and
  a read of the base word that returns that store's bytes reads 0 (`read_zero`).
* **The pair facts of warp 12** (`pairFacts`): a deallocation frees the column its thread read
  from the base word (`TmemFacts.dealloc_base`), which is 0 (`dealloc_zero`), the column of
  every recorded allocation; a thread of warp 12 exits after its three operations.
* **ResourceOk** (`resource_ok`): no CTA's allocator history faults or leaves an allocation live
  (`Tmem.Pair.no_resource_unsafe`, `Tmem.Pair.no_release_unsafe`).

That a read of the base word returns lane 0's store (`BaseRead`) is a fact of the memory model
and the barrier `bar.sync 2` between the store and the reads, outside the thread layer; it is a
premise here. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.TmemAlloc
open PTX PTX.Proof Tmem.Pair

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The resource operations are warp 12's.** -/
theorem warpOps (hpre : Pre P L mem0) (ht : TmemFacts L X) : TmemWarpOps L X 12 where
  cluster := hpre.cluster
  launch := hpre.oneDimLaunch
  warp_lt := by rw [hpre.block]; decide
  event hg he := by
    obtain ⟨h1, h2, h3, -⟩ := ht.event hg he
    exact ⟨h1, h2, h3⟩

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) (ht : TmemFacts L X)
include hpre hX ht

/-- The address lane 0 of warp 12 stores right after its allocation is 0. -/
theorem store_zero {cta j pca pcw n : Nat} {grp : CtaGroup} {dst : Option Loc} {wa : Acc}
    {wbs : List Byte}
    (hal : X.get (lane0 L cta, j) = some ⟨pca, .tc (.resource grp dst (.alloc n))⟩)
    (hw : X.get (lane0 L cta, j + 1) = some ⟨pcw, .wr wa wbs⟩) : wbs = (b32 0).toBytes := by
  have hto := warpOps hpre ht
  have hlen : j + 1 < (X.tr (lane0 L cta)).length := len_of_get hw
  obtain ⟨r, hr, hwi, hz⟩ := alloc_recorded hX hto (cta := cta)
    (hX.tmemPairBlocking.covered ⟨pca, _, _, _, hal, trivial⟩ hlen)
  obtain ⟨base, hwa⟩ : ∃ base, r.action = .alloc n base := by
    obtain ⟨-, -, -, hreq, -⟩ := record_info hX hto hr
    have hev := ((hX.tmemPair.1 _).1 r hr).2.2.2.2.1 0
    rw [hwi, hal] at hev
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hev
    exact Tmem.Action.request_eq_alloc (hreq.trans hev.2.2.2.symm)
  have h0 := hz _ _ hwa
  subst h0
  exact hX.tmemPairResult _ _ _ _ _ hal _ r 0 hr hwi hwa _ _ _ hw

/-- A read of the base word by warp 12 returns the 32-bit value 0. -/
theorem read_zero (hbr : BaseRead L X) {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (hk : X.get (g, k) = some ⟨pc, .rd a bs⟩) (hloc : a.loc = baseLoc L (ctaOf L g))
    (hsz : a.size = 4) (hw : warpOf L g = 12) :
    bs = (b32 0).toBytes.map some := by
  obtain ⟨j, pca, grp, dst, n, pcw, wa, wbs, hal, hwr, rfl⟩ :=
    hbr (Frame.lt_of_get hX hk) hk hloc hsz hw
  rw [store_zero hpre hX ht hal hwr]

/-- A deallocation frees column 0. -/
theorem dealloc_zero (hbr : BaseRead L X) {g k pc a n : Nat} {grp : CtaGroup} {dst : Option Loc}
    (hk : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩) : a = 0 := by
  have hg := Frame.lt_of_get hX hk
  obtain ⟨hw, -⟩ := ht.event hg hk
  obtain ⟨j, -, pcr, ra, bs, hrd, hloc, hsz, hcol⟩ := ht.dealloc_base hg hk
  rw [hcol 0 (read_zero hpre hX ht hbr hrd hloc hsz hw)]
  rfl

/-- **The Tensor Memory pair facts of warp 12.** -/
theorem pairFacts (hbr : BaseRead L X) : TmemPairFacts L X 12 where
  toTmemWarpOps := warpOps hpre ht
  dealloc _ hk r hr col hra := by
    rw [dealloc_zero hpre hX ht hbr hk, (alloc_zero hX (warpOps hpre ht) hr _ _ hra).2]
    rfl
  exit hg hw hk := ht.exit hg hw hk

/-- **ResourceOk**: no CTA's allocator history faults or records an allocation after a release,
and none leaves an allocation live once every thread has exited and every operation completed. -/
theorem resource_ok (hbr : BaseRead L X) : ¬ ResourceUnsafe L X ∧ ¬ ReleaseUnsafe L X :=
  have hp := pairFacts hpre hX ht hbr
  ⟨no_resource_unsafe hX hp, no_release_unsafe hX hp⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.TmemAlloc
