-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderCopyCommit
public import Kernels.TmlFa4Fwd.Proof.PagedKvGeometry
public import Kernels.TmlFa4Fwd.Flow.Code.Part008
public import Kernels.TmlFa4Fwd.Flow.Code.Part009
public import Lemmas.Flow.TcTmpl
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- Consume a copy that exists in a trace prefix, retaining the actual ending cursor. -/
theorem loaderCopyInPrefix {l : Launch} {X : Execution} {g i pc : Nat} {t : TState}
    {F : List (Nat × Value)} {spec : AsyncCopy.Spec} {ending : Option TState}
    (ht : At t pc F) (hout : out kernel Assumptions.all l g t = .ev (.copy spec (next t)))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hMore : (X.tr g).drop i ≠ []) :
    X.get (g, i) = some ⟨pc, .copy spec⟩ ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (i + 1)) ending := by
  have hNext : Next kernel Assumptions.all l g t t (.copy spec (next t)) := ⟨.refl, hout⟩
  obtain ⟨_, _, he, ⟨rfl, hu⟩, hTail⟩ := hNext.continuing_at_nonempty (by
    rintro e ⟨_, hBad⟩
    cases hBad) hr hMore
  obtain rfl := Option.some.inj hu
  exact ⟨by simpa only [ht.1] using he, hTail⟩

/-- A global address register plus an immediate offset is reduced modulo the address width. -/
private theorem globalOffset {l : Launch} {g r addr off : Nat} {t : TState}
    (hr : t.regs r = some (b64 addr)) (ha : addr < 2 ^ 64) :
    effAddr l g t .global r (off : Int) = .ok (globalLoc ((addr + off) % 2 ^ 64)) := by
  rw [effAddr, readBits_b64 hr ha]
  simp only [bind, Except.bind, pure, Except.pure, BitVec.ofInt_natCast, ← BitVec.ofNat_add,
    BitVec.toNat_ofNat, globalLoc]

/-- The K packet's pairs are uniformly spaced except for the local scratch load between halves. -/
def kCopyPc (group : Fin 16) : Nat := 550 + 8 * group.val + if group.val < 8 then 0 else 1

def kCopyDstReg (group : Fin 16) : Nat := if group.val % 2 = 0 then 1083 else 1084

def kCopySrcReg (group : Fin 16) : Nat := 7548 + 2 * group.val

def kCopyByteReg (group : Fin 16) : Nat := 1098 + group.val

private theorem kCopyCode (group : Fin 16) (upper : Bool) :
    kernel.code[kCopyPc group + if upper then 1 else 0]? =
      some ⟨none, .cpAsync (kCopyDstReg group)
        ((2048 * (group.val / 2) + if upper then 16384 else 0 : Nat) : Int)
        (kCopySrcReg group) (if upper then 128 else 0) 16 (.size (.reg (kCopyByteReg group)))
        none⟩ := by
  cases upper <;> fin_cases group
  · exact Flow.code_550
  · exact Flow.code_558
  · exact Flow.code_566
  · exact Flow.code_574
  · exact Flow.code_582
  · exact Flow.code_590
  · exact Flow.code_598
  · exact Flow.code_606
  · exact Flow.code_615
  · exact Flow.code_623
  · exact Flow.code_631
  · exact Flow.code_639
  · exact Flow.code_647
  · exact Flow.code_655
  · exact Flow.code_663
  · exact Flow.code_671
  · exact Flow.code_551
  · exact Flow.code_559
  · exact Flow.code_567
  · exact Flow.code_575
  · exact Flow.code_583
  · exact Flow.code_591
  · exact Flow.code_599
  · exact Flow.code_607
  · exact Flow.code_616
  · exact Flow.code_624
  · exact Flow.code_632
  · exact Flow.code_640
  · exact Flow.code_648
  · exact Flow.code_656
  · exact Flow.code_664
  · exact Flow.code_672

/-- One K vector pair uses two planes of the same stage and the same row predicate. -/
def kCopySpec (l : Launch) (g stage lane src bytes : Nat) (group : Fin 16) (upper : Bool) :
    AsyncCopy.Spec :=
  ⟨{loc := globalLoc ((src + if upper then 128 else 0) % 2 ^ 64), size := bytes},
   {loc := ⟨.shared, g / l.block, kvCopyAddress l.sharedBase stage lane group.val upper⟩,
    size := 16},
   .asyncGroup, .whole, none, true, none⟩

/-- Computed register operands of one K vector pair. -/
def kCopyFacts (l : Launch) (stage lane src bytes : Nat) (group : Fin 16) : List (Nat × Value) :=
  [(kCopyDstReg group, b32 (kvCopyAddress l.sharedBase stage lane (group.val % 2) false)),
    (kCopySrcReg group, b64 src), (kCopyByteReg group, b32 bytes)]

/-- The decoded template of either plane of a K copy pair. -/
theorem kCopyTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g stage lane src bytes : Nat} (hStage : stage < 3) (hSrc : src < 2 ^ 64)
    (hAligned : src % 16 = 0) (hBytes : bytes ≤ 16)
    (group : Fin 16) (upper : Bool) {t : TState}
    (ht : At t (kCopyPc group + if upper then 1 else 0) (kCopyFacts l stage lane src bytes group)) :
    out kernel Assumptions.all l g t = .ev (.copy
      (kCopySpec l g stage lane src bytes group upper) (next t)) := by
  let d := kvCopyAddress l.sharedBase stage lane (group.val % 2) false
  let dOff := 2048 * (group.val / 2) + if upper then 16384 else (0 : Nat)
  let sOff := if upper then 128 else (0 : Nat)
  let locD : Loc := ⟨.shared, g / l.block, d + dOff⟩
  let locS := globalLoc ((src + sOff) % 2 ^ 64)
  let srcSize := CpAsyncSource.size (.reg (kCopyByteReg group))
  have hCode : kernel.code[t.pc]? = some
      ⟨none, .cpAsync (kCopyDstReg group) dOff (kCopySrcReg group) sOff 16 srcSize none⟩ := by
    rw [ht.1]
    cases upper <;> exact kCopyCode group _
  have hD : d + dOff = kvCopyAddress l.sharedBase stage lane group.val upper := by
    have hTwo : group.val % 2 / 2 = 0 := by omega
    simp only [d, dOff, kvCopyAddress, hTwo, Nat.mod_mod, Bool.false_eq_true, ↓reduceIte]
    omega
  have hDRange := kvCopyAddress_range (lane := lane) (upper := upper) hp.shared.1
    hStage group.isLt (show 0 < 16 by decide)
  have hBound : d + dOff < 2 ^ 32 := by
    rw [hD]
    have := hp.shared.2.1
    omega
  have hDist := effAddr_b32_off (L := l) (g := g) ht.2.2.2.2.1 hBound
  have hSource := globalOffset (l := l) (g := g) (off := sOff) ht.2.2.2.2.2.1 hSrc
  have hAlignD : locD.addr % 16 = 0 := by
    change (d + dOff) % 16 = 0
    rw [hD]
    exact kvCopyAddress_aligned hp.shared.1 stage lane group.val upper
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
      (cpAsyncSourceSize_size hs (n := .reg (kCopyByteReg group)) (by rwa [hNat]))
  have hPcLo : 174 ≤ t.pc := by rw [ht.1]; unfold kCopyPc; omega
  have hPcHi : t.pc < 1906 := by
    rw [ht.1]
    have := group.isLt
    unfold kCopyPc
    split <;> split <;> omega
  rw [loaderOutCore hPcLo hPcHi, out_event ht.2.2.2.1 hCode rfl rfl]
  change Out.ev (cpAsyncTmpl l g t (.cpAsync (kCopyDstReg group) dOff (kCopySrcReg group)
    sOff 16 srcSize none)) = _
  rw [cpAsyncTmpl_copy hDist hSource ⟨by decide, hAlignD, hAlignS⟩ hSize rfl]
  rw [show kvCopyAddress l.sharedBase stage lane (group.val % 2) false + dOff =
    kvCopyAddress l.sharedBase stage lane group.val upper from hD]
  rfl

/-- The resolved K operands describe a single issued vector in a live prefix. -/
theorem kCopyPrefixObserved {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g i stage lane src bytes : Nat} (hStage : stage < 3) (hSrc : src < 2 ^ 64)
    (hAligned : src % 16 = 0) (hBytes : bytes ≤ 16) (group : Fin 16) (upper : Bool)
    {t : TState} {ending : Option TState}
    (ht : At t (kCopyPc group + if upper then 1 else 0) (kCopyFacts l stage lane src bytes group))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hMore : (X.tr g).drop i ≠ []) :
    X.get (g, i) = some ⟨kCopyPc group + if upper then 1 else 0,
      .copy (kCopySpec l g stage lane src bytes group upper)⟩ ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (i + 1)) ending :=
  loaderCopyInPrefix ht (kCopyTemplate hp hStage hSrc hAligned hBytes group upper ht) hr hMore

/-- The first row, specialized for callers that have already verified its operands. -/
abbrev firstKCopySpec (l : Launch) (g stage lane src bytes : Nat) (upper : Bool) :=
  kCopySpec l g stage lane src bytes 0 upper

def firstKCopyFacts (l : Launch) (stage lane src bytes : Nat) : List (Nat × Value) :=
  [(1083, b32 (kvCopyAddress l.sharedBase stage lane 0 false)), (7548, b64 src),
    (1098, b32 bytes)]

end
end PTX.Kernels.TmlFa4Fwd.Loader
