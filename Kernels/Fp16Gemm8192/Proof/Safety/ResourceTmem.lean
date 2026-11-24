-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.TcWrites
public import Lemmas.Tmem.PairProtocol

@[expose] public section

/-! # The Tensor Memory pair facts, from the interface

Warp 0 of each CTA allocates the 512 columns, relinquishes its permit and deallocates the base it
read from its CTA's base word, in that order (`ThreadFacts.warpOps`, `ThreadFacts.dealloc_base`);
the base word holds its CTA's allocated column (`BaseValue`), which is column 0, so a
deallocation frees column 0 (`dealloc_zero`). These are the library's pair facts of warp 0
(`pairFacts`), from which no CTA's history faults or leaves an allocation live
(`Tmem.Pair.no_resource_unsafe`, `Tmem.Pair.no_release_unsafe`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX Tmem.Pair

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A deallocation frees column 0, which its CTA's allocation at event 20 returned and its address
store at event 21 holds (OBJ-TMEM-ALLOC-RESULT). -/
theorem dealloc_zero (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hbv : BaseValue L X) {g k pc a n : Nat} {grp : CtaGroup}
    {dst : Option Loc} (hk : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩) :
    a = 0 := by
  have hg := Frame.lt_of_get hX hk
  obtain ⟨-, pcr, ra, bs, hrd, hloc, hsz, hcol⟩ := ht.dealloc_base hg hk
  obtain ⟨pca, pcw, col, hal, h21, hcl, hbs⟩ := hbv _ _ _ _ _ hrd hloc hsz
  have hlen : 20 + 1 < (X.tr (g / L.block * L.block)).length := len_of_get h21
  obtain ⟨r, hr, hwi, hz⟩ := alloc_recorded hX (ht.warpOps hpre) (cta := g / L.block) (by
    rw [Nat.zero_mul, Nat.add_zero]
    exact hX.tmemPairBlocking.covered ⟨pca, _, _, _, hal, trivial⟩ hlen)
  simp only [Nat.zero_mul, Nat.add_zero] at hwi
  obtain ⟨base, hwa⟩ : ∃ base, r.action = .alloc 512 base := by
    obtain ⟨-, -, -, hreq, -⟩ := record_info hX (ht.warpOps hpre) hr
    have hev := ((hX.tmemPair.1 _).1 r hr).2.2.2.2.1 0
    rw [hwi, hal] at hev
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hev
    exact Tmem.Action.request_eq_alloc (hreq.trans hev.2.2.2.symm)
  have h0 := hz _ _ hwa
  subst h0
  have hst := hX.tmemPairResult _ _ _ _ _ hal _ r 0 hr hwi hwa _ _ _ h21
  have hc0 : col = 0 := by
    have h0 := congrArg List.head? hst
    simp only [Value.toBytes, Value.bytes, PTX.Proof.b32, List.head?_map,
      show (List.range 4).head? = some 0 from rfl, Option.map_some, Option.some.injEq,
      Value.byteAt, Prod.mk.injEq, Value.bits.injEq, true_and, and_true] at h0
    have := congrArg BitVec.toNat h0
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega
  rw [hcol col hbs, hc0]
  rfl

/-- **The Tensor Memory pair facts of warp 0.** -/
theorem pairFacts (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hbv : BaseValue L X) : TmemPairFacts L X 0 where
  toTmemWarpOps := ht.warpOps hpre
  dealloc _ hk r hr col hra := by
    rw [dealloc_zero hpre hX ht hbv hk, (alloc_zero hX (ht.warpOps hpre) hr _ _ hra).2]
    rfl
  exit hg hw hk := ht.tmem_exit_at hg hw hk

end PTX.Kernels.Fp16Gemm8192.Proof.Safety
