-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderCopyFootprint
public import Kernels.TmlFa4Fwd.Proof.LoaderPacketFlow
import Lemmas.Flow.OpPcsFast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The 16 ordered vector pairs in each of the six K/V copy packets. -/
def packetPairPc (site : Fin 6) (group : Fin 16) : Nat :=
  copyPacketFirst site + (if site.val % 2 = 0 then 8 else 6) * group.val +
    (if 2 ≤ site.val ∧ 0 < group.val then 1 else 0) + if 8 ≤ group.val then 1 else 0

def packetDstReg (site : Fin 6) (group : Fin 16) : Nat :=
  let rs : Fin 6 → Nat × Nat := ![(1083, 1084), (1083, 1084), (2003, 2006), (2082, 2085),
    (2161, 2164), (2203, 2206)]
  if group.val % 2 = 0 then (rs site).1 else (rs site).2

def packetSrcReg (site : Fin 6) (group : Fin 16) : Nat :=
  (![7548, 7612, 7667, 7722, 7782, 7826] : Fin 6 → Nat) site + 2 * group.val

def packetSizeReg (site : Fin 6) (group : Fin 16) : Nat :=
  (![1098, 1098, 1123, 1123, 1154, 1154] : Fin 6 → Nat) site + group.val

def packetPlanePc (site : Fin 6) (group : Fin 16) (upper : Bool) : Nat :=
  packetPairPc site group + if upper then 1 else 0

def packetStageShift (site : Fin 6) : Nat :=
  if site.val = 1 then 1 else 0

/-- The shared immediate covers the row group, BF16 plane, and priming V stage. -/
def packetDstOff (site : Fin 6) (group : Fin 16) (upper : Bool) : Nat :=
  32768 * packetStageShift site + 2048 * (group.val / 2) + if upper then 16384 else 0

/-- The upper BF16 plane is 128 bytes after its paired source vector. -/
def packetSrcOff (upper : Bool) : Nat :=
  if upper then 128 else 0

/-- The ordinary-copy instruction determined by its packet, vector pair and plane. -/
def packetCopyOpCode (site : Fin 6) (group : Fin 16) (upper : Bool) : Op :=
  .cpAsync (packetDstReg site group) (packetDstOff site group upper)
    (packetSrcReg site group) (packetSrcOff upper) 16 (.size (.reg (packetSizeReg site group))) none

private def packetCopyOpEntry (entry : Instr × Nat) : Option (Instr × Nat) :=
  if packetCopyOp entry.1.op then some entry else none

private def packetPairEntries (site : Fin 6) : List (Instr × Nat) :=
  (List.finRange 16).flatMap fun group => [false, true].map fun upper =>
    (⟨none, packetCopyOpCode site group upper⟩, packetPlanePc site group upper)

private theorem packetDecodeAudit (site : Fin 6) :
    (((kernel.code.drop (copyPacketFirst site)).take
      (copyCommitPc site - copyPacketFirst site)).zipIdx (copyPacketFirst site)).filterMap
        packetCopyOpEntry = packetPairEntries site := by
  fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)

/-- The actual decoded instruction at each of the 192 ordinary loader copy sites. -/
theorem packetFullCode (site : Fin 6) (group : Fin 16) (upper : Bool) :
    kernel.code[packetPlanePc site group upper]? =
      some ⟨none, packetCopyOpCode site group upper⟩ := by
  have hm : (⟨none, packetCopyOpCode site group upper⟩, packetPlanePc site group upper) ∈
      packetPairEntries site := by
    simp only [packetPairEntries, List.mem_flatMap]
    exact ⟨group, List.mem_finRange _, List.mem_map.mpr ⟨upper, by cases upper <;> simp, rfl⟩⟩
  rw [← packetDecodeAudit] at hm
  obtain ⟨entry, hEntry, hEq⟩ := List.mem_filterMap.mp hm
  have hSub : entry =
      (⟨none, packetCopyOpCode site group upper⟩, packetPlanePc site group upper) := by
    unfold packetCopyOpEntry at hEq
    split at hEq
    · exact Option.some.inj hEq
    · cases hEq
  subst entry
  obtain ⟨idx, hIdx⟩ := List.mem_iff_getElem?.mp hEntry
  simp only [List.getElem?_zipIdx] at hIdx
  cases hi : (((kernel.code.drop (copyPacketFirst site)).take
      (copyCommitPc site - copyPacketFirst site))[idx]?) with
  | none => simp [hi] at hIdx
  | some instr =>
    have hiLt := (List.getElem?_eq_some_iff.mp hi).1
    have hiLen : idx < copyCommitPc site - copyPacketFirst site :=
      hiLt.trans_le (List.length_take_le _ _)
    have hEq : instr = ⟨none, packetCopyOpCode site group upper⟩ ∧
        copyPacketFirst site + idx = packetPlanePc site group upper := by simpa [hi] using hIdx
    rw [List.getElem?_take_of_lt hiLen, List.getElem?_drop] at hi
    rwa [← hEq.2, ← hEq.1]

/-- An ordinary copy PC in this packet decodes to its vector group and plane. -/
theorem packetCopyCoordinates (site : Fin 6) {pc : Nat} (hLo : copyPacketFirst site ≤ pc)
    (hHi : pc < copyCommitPc site) (hCopy : packetCopyAt pc = true) :
    ∃ group : Fin 16, ∃ upper : Bool, pc = packetPlanePc site group upper := by
  unfold packetCopyAt at hCopy
  cases hc : kernel.code[pc]? with
  | none => simp [hc] at hCopy
  | some ins =>
    have hi : (ins, pc) ∈ ((kernel.code.drop (copyPacketFirst site)).take
        (copyCommitPc site - copyPacketFirst site)).zipIdx (copyPacketFirst site) := by
      apply List.mem_of_getElem? (i := pc - copyPacketFirst site)
      rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
        Nat.add_sub_of_le hLo, hc]
      rfl
    have hs : packetCopyOpEntry (ins, pc) = some (ins, pc) := by
      simpa [hc, packetCopyOpEntry] using hCopy
    have hm := List.mem_filterMap.mpr ⟨(ins, pc), hi, hs⟩
    rw [packetDecodeAudit] at hm
    obtain ⟨group, _, hG⟩ := List.mem_flatMap.mp hm
    obtain ⟨upper, _, hP⟩ := List.mem_map.mp hG
    exact ⟨group, upper, (congrArg Prod.snd hP).symm⟩

/-- An actual ordinary copy in a known packet interval decodes to its vector coordinates. -/
theorem actualPacketCopyCoordinates {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (site : Fin 6) {i : EvId} {pc : Nat}
    {spec : AsyncCopy.Spec} (hLo : copyPacketFirst site ≤ pc) (hHi : pc < copyCommitPc site)
    (he : X.get i = some ⟨pc, .copy spec⟩) :
    ∃ group : Fin 16, ∃ upper : Bool, pc = packetPlanePc site group upper := by
  have hBounds := loaderPacketBounds site
  rcases get_source hX he with ⟨_, hf⟩ | ⟨t, ins, o, _, hc, hFire⟩
  · cases hf
  have hBulk := fires_bulk_op hFire rfl
  have hAudit : ((kernel.code.drop 174).take (1906 - 174)).all
      (fun ins => !bulkOp ins.op || packetCopyOp ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hm : ins ∈ (kernel.code.drop 174).take (1906 - 174) := by
    apply List.mem_of_getElem? (i := pc - 174)
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le (by omega : 174 ≤ pc)]
    exact hc
  have hOp : packetCopyOp ins.op = true := by
    simpa only [hBulk, Bool.not_true, Bool.false_or] using List.all_eq_true.mp hAudit ins hm
  exact packetCopyCoordinates site hLo hHi (by simp [packetCopyAt, hc, hOp])

private theorem packetPlaneBounds (site : Fin 6) (group : Fin 16) (upper : Bool) :
    174 ≤ packetPlanePc site group upper ∧ packetPlanePc site group upper < 1906 := by
  fin_cases site <;> fin_cases group <;> cases upper <;> decide

/-- The register operands consumed by an arbitrary decoded K or V pair. For the
first V packet the PTX adds one 32-KiB stage to the destination's register. -/
def packetCopyFacts (l : Launch) (site : Fin 6) (stage lane src n : Nat)
    (group : Fin 16) : List (Nat × Value) :=
  [(packetDstReg site group, b32 (kvCopyAddress l.sharedBase stage lane (group.val % 2) false)),
   (packetSrcReg site group, b64 src), (packetSizeReg site group, b32 n)]

/-- The actual vector copy spec has two planes and accounts for the priming V offset. -/
def packetCopySpec (l : Launch) (g : Nat) (site : Fin 6) (stage lane src n : Nat)
    (group : Fin 16) (upper : Bool) : AsyncCopy.Spec :=
  kCopySpec l g (stage + packetStageShift site) lane src n group upper

/-- The decoded destination immediate places the pair at its full shared-layout coordinate. -/
theorem packetDestSum (base stage lane : Nat) (site : Fin 6)
    (group : Fin 16) (upper : Bool) :
    kvCopyAddress base stage lane (group.val % 2) false + packetDstOff site group upper =
      kvCopyAddress base (stage + packetStageShift site) lane group.val upper := by
  have hTwo : group.val % 2 / 2 = 0 := by omega
  simp only [kvCopyAddress, hTwo, Nat.mod_mod, Bool.false_eq_true, ↓reduceIte, packetDstOff]
  omega

private theorem packetGlobalOff {l : Launch} {g r addr off : Nat} {t : TState}
    (hr : t.regs r = some (b64 addr)) (ha : addr < 2 ^ 64) :
    effAddr l g t .global r (off : Int) = .ok (globalLoc ((addr + off) % 2 ^ 64)) := by
  rw [effAddr, readBits_b64 hr ha]
  simp only [bind, Except.bind, pure, Except.pure, BitVec.ofInt_natCast, ← BitVec.ofNat_add,
    BitVec.toNat_ofNat, globalLoc]

private theorem packetVectorTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g stage lane src n : Nat} (site : Fin 6) (group : Fin 16) (upper : Bool)
    (hStage : stage + packetStageShift site < 3) (hSrc : src < 2 ^ 64)
    (hAligned : src % 16 = 0) (hBytes : n ≤ 16) {t : TState}
    (ht : At t (packetPlanePc site group upper) (packetCopyFacts l site stage lane src n group)) :
    out kernel Assumptions.all l g t = .ev (.copy
      (packetCopySpec l g site stage lane src n group upper) (next t)) := by
  let d := kvCopyAddress l.sharedBase stage lane (group.val % 2) false
  let dOff := packetDstOff site group upper
  let sOff := packetSrcOff upper
  let locD : Loc := ⟨.shared, g / l.block, d + dOff⟩
  let locS := globalLoc ((src + sOff) % 2 ^ 64)
  have hCode : kernel.code[t.pc]? = some ⟨none, packetCopyOpCode site group upper⟩ := by
    rw [ht.1]
    exact packetFullCode site group upper
  have hD : d + dOff = kvCopyAddress l.sharedBase (stage + packetStageShift site) lane
      group.val upper := packetDestSum l.sharedBase stage lane site group upper
  have hDRange := kvCopyAddress_range (lane := lane) (upper := upper) hp.shared.1
    hStage group.isLt (show 0 < 16 by decide)
  have hBound : d + dOff < 2 ^ 32 := by
    rw [hD]
    have := hp.shared.2.1
    omega
  have hDist := effAddr_b32_off (L := l) (g := g) ht.2.2.2.2.1 hBound
  have hSource := packetGlobalOff (l := l) (g := g) (off := sOff) ht.2.2.2.2.2.1 hSrc
  have hAlignD : locD.addr % 16 = 0 := by
    change (d + dOff) % 16 = 0
    rw [hD]
    exact kvCopyAddress_aligned hp.shared.1 _ lane group.val upper
  have hAlignS : locS.addr % 16 = 0 := by
    change ((src + sOff) % 2 ^ 64) % 16 = 0
    rw [Nat.mod_mod_of_dvd _ (show 16 ∣ (2 : Nat) ^ 64 by decide)]
    have ha : sOff % 16 = 0 := by cases upper <;> decide
    simp [Nat.add_mod, hAligned, ha]
  have hb : n < 2 ^ 32 := by omega
  have hs := readBits_b32 (L := l) (g := g) ht.2.2.2.2.2.2.1 hb
  have hSize : cpAsyncSourceSize l g t 16 (.size (.reg (packetSizeReg site group))) = .ok n := by
    have hNat := toNat_ofNat_lt (show n < 2 ^ 64 by omega)
    simpa only [hNat] using
      (cpAsyncSourceSize_size hs (n := .reg (packetSizeReg site group)) (by rwa [hNat]))
  have hLo : 174 ≤ t.pc := by rw [ht.1]; exact (packetPlaneBounds site group upper).1
  have hHi : t.pc < 1906 := by rw [ht.1]; exact (packetPlaneBounds site group upper).2
  rw [loaderOutCore hLo hHi, out_event ht.2.2.2.1 hCode rfl rfl]
  change Out.ev (cpAsyncTmpl l g t (packetCopyOpCode site group upper)) = _
  unfold packetCopyOpCode
  rw [cpAsyncTmpl_copy hDist hSource ⟨by decide, hAlignD, hAlignS⟩ hSize rfl]
  change Out.ev (.copy ⟨⟨locS, n, _, _, _, _, _⟩,
    ⟨locD, 16, _, _, _, _, _⟩, .asyncGroup, .whole, .none, true, .none⟩ (next t)) = _
  unfold packetCopySpec kCopySpec
  exact congrArg (fun dst => Out.ev (.copy
    { src := {loc := locS, size := n}, dst := {loc := ⟨.shared, g / l.block, dst⟩, size := 16},
      completion := .asyncGroup, generic := true } (next t))) hD

end
end PTX.Kernels.TmlFa4Fwd.Loader
