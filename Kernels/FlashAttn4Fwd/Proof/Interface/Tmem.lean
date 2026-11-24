-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Bars
public import Kernels.FlashAttn4Fwd.Proof.Thread.Common
public import Lemmas.Tmem.PairProtocol
public import Lemmas.Flow.Regs

@[expose] public section

/-! # What the thread layer exports for the Tensor Memory allocation

Warp 12 of each CTA makes the CTA pair's Tensor Memory resource operations (`cta_group::2`): it
allocates all 512 columns into the base word `+328` (`baseLoc`), reads the word back after
`bar.sync 2`, relinquishes its permit after the item loop, and, after `bar.sync 2`, the
handshake on the peer CTA's `+320` barrier and the wait on its own, deallocates the column it
read. The handshake barrier `+320` (`FBar.dealloc`, count 32) is a one-phase barrier: each lane
of the peer CTA's warp 12 arrives on it once, with one arrival and no transaction bytes, and only
the CTA's own warp 12 polls it, at parity 0; no tensor copy, commit, bulk copy, cancellation
request or invalidation names it.

The fields are facts of each thread's own events (`TmemFacts`), proved from the MMA role's run
invariant and the other roles' (whose copies, commits and arrivals name other barriers). The value
a lane of warp 12 reads back from the base word is lane 0's store after its allocation
(`TmemAlloc.BaseRead`), a premise of the thread layer that the base-word protocol proves. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof Tmem.Pair

noncomputable section

/-- The base word of CTA `cta`, where warp 12's allocation stores the Tensor Memory address. -/
def baseLoc (L : Launch) (cta : Nat) : Loc := ⟨.shared, cta, L.sharedBase + 328⟩

/-- The other CTA of `cta`'s pair. -/
def pairCta (cta : Nat) : Nat := cta / 2 * 2 + (1 - cta % 2)

/-- The Tensor Memory allocation and its handshake, from the threads' own events. -/
structure TmemFacts (L : Launch) (X : Execution) : Prop where
  /-- A resource operation is warp 12's, in group two, of the shape its count gives
  (allocate 512 columns, relinquish, deallocate 512 columns); an allocation stores into the base
  word. -/
  event : ∀ {g k pc : Nat} {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request},
    g < L.threads → X.get (g, k) = some ⟨pc, .tc (.resource grp dst act)⟩ →
      warpOf L g = 12 ∧ grp = .two ∧ TmemShape (tmemOps ((X.tr g).take k)) act ∧
        ∀ n, act = .alloc n → dst = some (baseLoc L (ctaOf L g))
  /-- A thread of warp 12 exits after its three resource operations. -/
  exit : ∀ {g k pc : Nat}, g < L.threads → warpOf L g = 12 →
    X.get (g, k) = some ⟨pc, .exit⟩ → tmemOps ((X.tr g).take k) = 3
  /-- A deallocation frees the column its thread read from its CTA's base word before it: the
  32-bit value of the read's bytes. -/
  dealloc_base : ∀ {g k pc : Nat} {grp : CtaGroup} {dst : Option Loc} {a n : Nat},
    g < L.threads → X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩ →
      ∃ j < k, ∃ pcr ra bs, X.get (g, j) = some ⟨pcr, .rd ra bs⟩ ∧
        ra.loc = baseLoc L (ctaOf L g) ∧ ra.size = 4 ∧
        ∀ col, bs = (b32 col).toBytes.map some → a = col % 2 ^ 32
  /-- An arrival on a CTA's handshake barrier is one arrival without transaction bytes, by a
  thread of warp 12 of the other CTA of the pair, its only arrival on that barrier. -/
  hs_arrive : ∀ {g k pc tx c cta : Nat} {m : Loc} {rel : Bool} {sc : MbarScope},
    g < L.threads → X.get (g, k) = some ⟨pc, .arrive m tx c rel sc⟩ →
    m = FBar.loc L cta .dealloc →
      warpOf L g = 12 ∧ cta = pairCta (ctaOf L g) ∧ tx = 0 ∧ c = 1 ∧
        ∀ k' pc' tx' c' rel' sc', X.get (g, k') = some ⟨pc', .arrive m tx' c' rel' sc'⟩ → k' = k
  /-- A poll of a CTA's handshake barrier is of parity 0, by a thread of the CTA's warp 12. -/
  hs_wait : ∀ {g k pc p cta : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope},
    g < L.threads → X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
    m = FBar.loc L cta .dealloc → warpOf L g = 12 ∧ cta = ctaOf L g ∧ p = 0
  /-- No tensor copy completes on a handshake barrier. -/
  hs_tensor : ∀ {i : EvId} {pc a cta : Nat} {sp : TensorCopy.Spec},
    X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar ≠ FBar.loc L cta .dealloc
  /-- No commit arrives on a handshake barrier. -/
  hs_commit : ∀ {i : EvId} {pc cta : Nat} {sp : TcCommit.Spec} {rank : Fin 16},
    X.get i = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp rank ≠ some (FBar.loc L cta .dealloc)
  /-- The kernel has no linear copy, cancellation request or barrier invalidation. -/
  no_bulk : ∀ {i : EvId} {pc : Nat} {s : AsyncCopy.Spec}, X.get i ≠ some ⟨pc, .copy s⟩
  no_clc : ∀ {i : EvId} {pc : Nat} {sp : Clc.Spec} {tg : List Nat},
    X.get i ≠ some ⟨pc, .clcIssue sp tg⟩
  no_inval : ∀ {i : EvId} {pc : Nat} {m : Loc}, X.get i ≠ some ⟨pc, .mbInval m⟩
  /-- The kernel has no `cp.async.mbarrier.arrive`. -/
  no_arriveOn : ∀ {i : EvId} {pc : Nat} {m : Loc} {noinc : Bool},
    X.get i ≠ some ⟨pc, .asyncArrive m noinc⟩
  /-- The kernel has no bulk prefetch. -/
  no_prefetch : ∀ {i : EvId} {pc : Nat} {a : Acc}, X.get i ≠ some ⟨pc, .bulkPrefetch a⟩
  /-- The kernel has no atomic read-modify-write. -/
  no_rmw : ∀ {i : EvId} {pc : Nat} {a : Acc} {old : List (Option Byte)} {new : Option (List Byte)},
    X.get i ≠ some ⟨pc, .rmw a old new⟩

namespace TmemAlloc

/-- Lane 0 of warp 12 of CTA `cta`. -/
abbrev lane0 (L : Launch) (cta : Nat) : Nat := cta * L.block + 12 * 32

/-- **The base word's value**: a read of a CTA's base word by its warp 12 returns the bytes of
the store that lane 0 of the CTA's warp 12 made right after an allocation. -/
def BaseRead (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}, g < L.threads →
    X.get (g, k) = some ⟨pc, .rd a bs⟩ → a.loc = baseLoc L (ctaOf L g) → a.size = 4 →
    warpOf L g = 12 →
      ∃ j pca grp dst n pcw wa wbs,
        X.get (lane0 L (ctaOf L g), j) = some ⟨pca, .tc (.resource grp dst (.alloc n))⟩ ∧
        X.get (lane0 L (ctaOf L g), j + 1) = some ⟨pcw, .wr wa wbs⟩ ∧ bs = wbs.map some

end TmemAlloc

end
end PTX.Kernels.FlashAttn4Fwd.Proof
