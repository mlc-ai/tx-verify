-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec

@[expose] public section

/-!
# The output arrays are fixed by the launch

Two parameter sets that one launch satisfies (`Pre`) have the same O and LSE regions: the head
count and the batch count are scalar parameters, the total query count is the row extent of the
Q tensor map, the O base is the O tensor map's base, and the LSE base and stride are bytes of
parameter 4.
-/

namespace PTX.Kernels.TmlFa4Fwd
open TensorDescriptor

noncomputable section

/-- Equal little-endian bytes of two values below `256 ^ n` give equal values. -/
theorem leByte_inj {n x y : Nat} (hx : x < 256 ^ n) (hy : y < 256 ^ n)
    (h : ∀ k < n, leByte x k = leByte y k) : x = y := by
  have key : ∀ j ≤ n, x % 256 ^ j = y % 256 ^ j := by
    intro j
    induction j with
    | zero => intro _; simp only [pow_zero, Nat.mod_one]
    | succ j ih =>
      intro hj
      have hk := congrArg BitVec.toNat (h j (by omega))
      simp only [leByte, BitVec.toNat_ofNat] at hk
      rw [Nat.mod_pow_succ, Nat.mod_pow_succ, ih (by omega), hk]
  have := key n le_rfl
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

private theorem ofNat64_inj {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (h : BitVec.ofNat 64 x = BitVec.ofNat 64 y) : x = y := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

private theorem scalar_eq {p P : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (hP : Pre P l m) {i : Nat} {f : Params → Nat} (hpi : (i, f p) ∈ p.scalarWords)
    (hPi : (i, f P) ∈ P.scalarWords) : f P = f p := by
  obtain ⟨hlt, hv⟩ := hp.values _ hpi
  obtain ⟨hLt, hV⟩ := hP.values _ hPi
  exact ofNat64_inj (by omega) (by omega) (Option.some.inj (hV.symm.trans hv))

private theorem object_eq {p P : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (hP : Pre P l m) {i off bytes : Nat} {f : Params → Nat}
    (hpi : (i, off, bytes, f p) ∈ p.objectWords) (hPi : (i, off, bytes, f P) ∈ P.objectWords) :
    f P = f p := by
  obtain ⟨hlt, hv⟩ := hp.objectBytes _ _ _ _ hpi
  obtain ⟨hLt, hV⟩ := hP.objectBytes _ _ _ _ hPi
  exact leByte_inj hLt hlt fun k hk =>
    Option.some.inj ((hV k hk).symm.trans (hv k hk))

private theorem map_eq {p P : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (hP : Pre P l m) {i outer : Nat} {f : Params → Nat} {d : Params → Descriptor outer}
    (hpi : (i, f p, (⟨outer, d p⟩ : (outer : Nat) × Descriptor outer)) ∈
      [(9, p.qMapAddress, ⟨2, p.qMap⟩), (10, p.oMapAddress, ⟨3, p.oMap⟩),
        (11, p.biasMapAddress, ⟨2, p.biasMap⟩)])
    (hPi : (i, f P, (⟨outer, d P⟩ : (outer : Nat) × Descriptor outer)) ∈
      [(9, P.qMapAddress, ⟨2, P.qMap⟩), (10, P.oMapAddress, ⟨3, P.oMap⟩),
        (11, P.biasMapAddress, ⟨2, P.biasMap⟩)]) :
    d P = d p := by
  obtain ⟨hpo, -, -, hpt, -⟩ := hp.maps _ _ _ hpi
  obtain ⟨hPo, -, -, hPt, -⟩ := hP.maps _ _ _ hPi
  have hAddr : f P = f p := by
    have := hPo.symm.trans hpo
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    exact this.2
  rw [hAddr] at hPt
  have hSig := Option.some.inj (hPt.symm.trans hpt)
  exact eq_of_heq (Sigma.mk.inj hSig).2

/-- **The O and LSE regions are fixed by the launch.** -/
theorem Pre.outputs_pinned {p P : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (hP : Pre P l m) : P.oRegion = p.oRegion ∧ P.lseRegion = p.lseRegion := by
  have hHeads : P.heads = p.heads :=
    scalar_eq (i := 17) (f := Params.heads) hp hP (by simp [Params.scalarWords])
      (by simp [Params.scalarWords])
  have hQ : P.qMap = p.qMap :=
    map_eq (i := 9) (f := Params.qMapAddress) (d := Params.qMap) hp hP (by simp) (by simp)
  have hO : P.oMap = p.oMap :=
    map_eq (i := 10) (f := Params.oMapAddress) (d := Params.oMap) hp hP (by simp) (by simp)
  have hTotal : P.totalQ = p.totalQ := congrArg (fun d : Descriptor 2 => d.extent 1) hQ
  have hBase : P.oBase = p.oBase := by
    have h := congrArg Descriptor.base hO
    simp only [Params.oMap] at h
    have := hp.raggedBase
    have := hP.raggedBase
    rw [hHeads] at h
    omega
  have hLse : P.lseBase = p.lseBase :=
    object_eq (i := 4) (off := 0) (bytes := 8) (f := Params.lseBase) hp hP
      (by simp [Params.objectWords]) (by simp [Params.objectWords])
  have hStride : P.lseStride = p.lseStride :=
    object_eq (i := 4) (off := 16) (bytes := 8) (f := Params.lseStride) hp hP
      (by simp [Params.objectWords]) (by simp [Params.objectWords])
  simp only [Params.oRegion, Params.lseRegion, hHeads, hTotal, hBase, hLse, hStride, and_self]

end
end PTX.Kernels.TmlFa4Fwd
