-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderCopies
public import Kernels.TmlFa4Fwd.Flow.Code.Part012
public import Kernels.TmlFa4Fwd.Flow.Code.Part013
public import Kernels.TmlFa4Fwd.Flow.Code.Part014

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

/-- The V packet's pairs are uniformly spaced except for the local scratch load between halves. -/
def vCopyPc (group : Fin 16) : Nat := 810 + 6 * group.val + if group.val < 8 then 0 else 1

def vCopyDstReg (group : Fin 16) : Nat := if group.val % 2 = 0 then 1083 else 1084

def vCopySrcReg (group : Fin 16) : Nat := 7612 + 2 * group.val

def vCopyByteReg (group : Fin 16) : Nat := 1098 + group.val

private theorem vCopyCode (group : Fin 16) (upper : Bool) :
    kernel.code[vCopyPc group + if upper then 1 else 0]? =
      some ⟨none, .cpAsync (vCopyDstReg group)
        ((32768 + 2048 * (group.val / 2) + if upper then 16384 else 0 : Nat) : Int)
        (vCopySrcReg group) (if upper then 128 else 0) 16 (.size (.reg (vCopyByteReg group)))
        none⟩ := by
  cases upper <;> fin_cases group
  · exact Flow.code_810
  · exact Flow.code_816
  · exact Flow.code_822
  · exact Flow.code_828
  · exact Flow.code_834
  · exact Flow.code_840
  · exact Flow.code_846
  · exact Flow.code_852
  · exact Flow.code_859
  · exact Flow.code_865
  · exact Flow.code_871
  · exact Flow.code_877
  · exact Flow.code_883
  · exact Flow.code_889
  · exact Flow.code_895
  · exact Flow.code_901
  · exact Flow.code_811
  · exact Flow.code_817
  · exact Flow.code_823
  · exact Flow.code_829
  · exact Flow.code_835
  · exact Flow.code_841
  · exact Flow.code_847
  · exact Flow.code_853
  · exact Flow.code_860
  · exact Flow.code_866
  · exact Flow.code_872
  · exact Flow.code_878
  · exact Flow.code_884
  · exact Flow.code_890
  · exact Flow.code_896
  · exact Flow.code_902

/-- The priming V pair uses the buffer 32768 bytes above the priming K copy, with the
same row predicate and BF16 source planes. -/
def vCopySpec (l : Launch) (g lane src bytes : Nat) (group : Fin 16) (upper : Bool) :
    AsyncCopy.Spec :=
  ⟨{loc := globalLoc ((src + if upper then 128 else 0) % 2 ^ 64), size := bytes},
   {loc := ⟨.shared, g / l.block, kvCopyAddress l.sharedBase 1 lane group.val upper⟩,
    size := 16},
   .asyncGroup, .whole, none, true, none⟩

/-- Computed register operands of one V vector pair. -/
def vCopyFacts (l : Launch) (lane src bytes : Nat) (group : Fin 16) : List (Nat × Value) :=
  [(vCopyDstReg group, b32 (kvCopyAddress l.sharedBase 0 lane (group.val % 2) false)),
    (vCopySrcReg group, b64 src), (vCopyByteReg group, b32 bytes)]

/-- The decoded V copy issues the given source and destination operands. -/
theorem vCopyTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g lane src bytes : Nat} (hSrc : src < 2 ^ 64)
    (hAligned : src % 16 = 0) (hBytes : bytes ≤ 16)
    (group : Fin 16) (upper : Bool) {t : TState}
    (ht : At t (vCopyPc group + if upper then 1 else 0) (vCopyFacts l lane src bytes group)) :
    out kernel Assumptions.all l g t = .ev (.copy
      (vCopySpec l g lane src bytes group upper) (next t)) := by
  let d := kvCopyAddress l.sharedBase 0 lane (group.val % 2) false
  let dOff := 32768 + 2048 * (group.val / 2) + if upper then 16384 else (0 : Nat)
  let sOff := if upper then 128 else (0 : Nat)
  let locD : Loc := ⟨.shared, g / l.block, d + dOff⟩
  let locS := globalLoc ((src + sOff) % 2 ^ 64)
  let srcSize := CpAsyncSource.size (.reg (vCopyByteReg group))
  have hCode : kernel.code[t.pc]? = some
      ⟨none, .cpAsync (vCopyDstReg group) dOff (vCopySrcReg group) sOff 16 srcSize none⟩ := by
    rw [ht.1]
    cases upper <;> exact vCopyCode group _
  have hD : d + dOff = kvCopyAddress l.sharedBase 1 lane group.val upper := by
    have hTwo : group.val % 2 / 2 = 0 := by omega
    simp only [d, dOff, kvCopyAddress, hTwo, Nat.mod_mod, Bool.false_eq_true, ↓reduceIte]
    omega
  have hDRange := kvCopyAddress_range (lane := lane) (upper := upper) hp.shared.1
    (show 1 < 3 by decide) group.isLt (show 0 < 16 by decide)
  have hBound : d + dOff < 2 ^ 32 := by
    rw [hD]
    have := hp.shared.2.1
    omega
  have hDist := effAddr_b32_off (L := l) (g := g) ht.2.2.2.2.1 hBound
  have hSource : effAddr l g t .global (vCopySrcReg group) (sOff : Int) = .ok locS := by
    rw [effAddr, readBits_b64 ht.2.2.2.2.2.1 hSrc]
    simp only [bind, Except.bind, pure, Except.pure, BitVec.ofInt_natCast, ← BitVec.ofNat_add,
      BitVec.toNat_ofNat, locS, globalLoc]
  have hAlignD : locD.addr % 16 = 0 := by
    change (d + dOff) % 16 = 0
    rw [hD]
    exact kvCopyAddress_aligned hp.shared.1 1 lane group.val upper
  have hAlignS : locS.addr % 16 = 0 := by
    change ((src + sOff) % 2 ^ 64) % 16 = 0
    rw [Nat.mod_mod_of_dvd _ (show 16 ∣ (2 : Nat) ^ 64 by decide)]
    have ha : sOff % 16 = 0 := by cases upper <;> decide
    simp [Nat.add_mod, hAligned, ha]
  have hb : bytes < 2 ^ 32 := by omega
  have hs := readBits_b32 (L := l) (g := g) ht.2.2.2.2.2.2.1 hb
  have hSize : cpAsyncSourceSize l g t 16 srcSize = .ok bytes := by
    have hNat := toNat_ofNat_lt (show bytes < 2 ^ 64 by omega)
    simpa only [hNat] using
      (cpAsyncSourceSize_size hs (n := .reg (vCopyByteReg group)) (by rwa [hNat]))
  have hPcLo : 174 ≤ t.pc := by rw [ht.1]; unfold vCopyPc; omega
  have hPcHi : t.pc < 1906 := by
    rw [ht.1]
    have := group.isLt
    unfold vCopyPc
    split <;> split <;> omega
  rw [loaderOutCore hPcLo hPcHi, out_event ht.2.2.2.1 hCode rfl rfl]
  change Out.ev (cpAsyncTmpl l g t (.cpAsync (vCopyDstReg group) dOff (vCopySrcReg group)
    sOff 16 srcSize none)) = _
  rw [cpAsyncTmpl_copy hDist hSource ⟨by decide, hAlignD, hAlignS⟩ hSize rfl]
  rw [show kvCopyAddress l.sharedBase 0 lane (group.val % 2) false + dOff =
    kvCopyAddress l.sharedBase 1 lane group.val upper from hD]
  rfl

/-- The resolved V operands describe a single issued vector in a live prefix. -/
theorem vCopyPrefixObserved {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g i lane src bytes : Nat} (hSrc : src < 2 ^ 64)
    (hAligned : src % 16 = 0) (hBytes : bytes ≤ 16) (group : Fin 16) (upper : Bool)
    {t : TState} {ending : Option TState}
    (ht : At t (vCopyPc group + if upper then 1 else 0) (vCopyFacts l lane src bytes group))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hMore : (X.tr g).drop i ≠ []) :
    X.get (g, i) = some ⟨vCopyPc group + if upper then 1 else 0,
      .copy (vCopySpec l g lane src bytes group upper)⟩ ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (i + 1)) ending :=
  loaderCopyInPrefix ht (vCopyTemplate hp hSrc hAligned hBytes group upper ht) hr hMore

end
end PTX.Kernels.TmlFa4Fwd.Loader
