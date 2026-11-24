-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Mma
public import Lemmas.Flow.TcMmaTs

@[expose] public section

/-! # The MMA warp's issues are MMAs

At an MMA site whose registers hold the table's values, the issue is an MMA event, never
undefined behaviour: the shared-memory descriptors decode (their low words stay below `2^15`
plus the K-major leading-offset bit 16, their high word `0x40004040` has version 1 and the
128-byte swizzle), the instruction descriptors decode as `kind::f16` with M = 256 over the CTA
pair, the CTA pair is the thread's cluster, the eight lane masks are zero, and the A address of
a PV MMA (`[tmem_a + 8 j]`) stays in its column field. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- A descriptor with high word `0x40004040` and a low word below `2^31` with bit 15 clear
decodes. -/
theorem desc_decode {lo : Nat} (hlo : lo < 2 ^ 31) (h15 : lo / 2 ^ 15 % 2 = 0) :
    ∃ d, TcShared.decode (lo + descHi * 2 ^ 32) = some d :=
  sharedDecode_some (sw := .b128) hlo h15 (by decide) (by decide) (by decide) rfl

/-- The CTAs of an MMA over the pair: the cluster of the issuing thread. -/
theorem operands_two (hpre : Pre P L mem0) (hg : g < L.threads) (dsc : TcMma.Descriptor)
    (da db : TcShared.Descriptor) (hd : dsc.group = .two) :
    ∃ spec, TcMma.makeOperands L (g / L.block) dsc da db = some spec := by
  have hcta := cta_lt hg
  have hcl := hpre.cluster
  have hgr := hpre.grid
  have hone := hpre.oneDimLaunch.1
  unfold ctaOf at hcta
  have hrank : L.rankOfCta (g / L.block) = (g / L.block) % 2 := by
    rw [Launch.oneDim_rankOfCta hone, hcl]
  have hsz : L.clusterSizeOf (g / L.block) = 2 := by
    rw [Launch.oneDim_clusterSizeOf hone, hcl]
  have hbase : L.clusterStart (L.clusterOfCta (g / L.block)) = (g / L.block) / 2 * 2 := by
    rw [Launch.oneDim_clusterStart hone, Launch.oneDim_clusterOfCta hone, hcl]
  have hr0 : L.rankOfCta (g / L.block) / 2 * 2 = 0 := by rw [hrank]; omega
  have hlo : L.peerCta (g / L.block) (L.rankOfCta (g / L.block) / 2 * 2) =
      some (L.clusterStart (L.clusterOfCta (g / L.block))) := by
    have hc : g / L.block < L.grid ∧ 0 < L.clusterSizeOf (g / L.block) ∧
        L.clusterStart (L.clusterOfCta (g / L.block)) < L.grid :=
      ⟨hcta, by rw [hsz]; omega, by rw [hbase]; omega⟩
    rw [hr0]
    simp only [Launch.peerCta, ite_eq_left hc, Nat.add_zero]
  have hhi : L.peerCta (g / L.block) (L.rankOfCta (g / L.block) / 2 * 2 + 1) =
      some (L.clusterStart (L.clusterOfCta (g / L.block)) + 1) := by
    have hc : g / L.block < L.grid ∧ 1 < L.clusterSizeOf (g / L.block) ∧
        L.clusterStart (L.clusterOfCta (g / L.block)) + 1 < L.grid :=
      ⟨hcta, by rw [hsz]; omega, by rw [hbase]; omega⟩
    rw [hr0]
    simp only [Launch.peerCta, ite_eq_left hc]
  refine ⟨⟨dsc, da, db, L.clusterStart (L.clusterOfCta (g / L.block)),
    L.clusterStart (L.clusterOfCta (g / L.block)) + 1, none, {}⟩, ?_⟩
  rw [TcMma.makeOperands, hd, Launch.ctaGroup_two, hlo, hhi]
  rfl

/-- Whether `e` is a Tensor Core MMA. -/
def isMma (e : Event) : Bool := match e.kind with
  | .tc (.mma ..) => true
  | _ => false

theorem isMma_of_fires {pc : Nat} {e : Event} {o : Option TState} {dd : Nat}
    {sp : TcMma.OperandSpec} {acc : Bool} {mk : List Nat} {u : TState}
    (hf : Fires pc (.tc (.mma dd sp acc mk) u) e o) : isMma e = true := by
  obtain ⟨rfl, -⟩ := hf
  rfl

/-- The eight zero lane masks of the MMAs. -/
abbrev masks0 : List Opnd := List.replicate 8 (.imm 0)

/-- **A QK MMA is an MMA**: its accumulator column, Q and K descriptors (low words `la`,
`lb`) and the QK instruction descriptor in its registers, any enable operand. -/
theorem qk_isMma (hpre : Pre P L mem0) (hg : g < L.threads) {t : TState}
    {pc dst ra rb c la lb : Nat}
    {en : Opnd} {e : Event} {o : Option TState}
    (hd : t.regs dst = some (b32 c)) (hc : c < 2 ^ 32)
    (hA : t.regs ra = some (desc la)) (hla : la < 2 ^ 31) (hla' : la / 2 ^ 15 % 2 = 0)
    (hB : t.regs rb = some (desc lb)) (hlb : lb < 2 ^ 31) (hlb' : lb / 2 ^ 15 % 2 = 0)
    (hI : t.regs 5351 = some (b32 qkIdesc)) (he : ∃ acc, mmaEnable t en = .ok acc)
    (hf : Fires pc (eventTmpl asms L g t (.tcMma (.dense .two false .f16 dst
      (.smem (.reg ra)) (.reg rb) (.reg 5351) masks0 en))) e o) :
    isMma e = true := by
  obtain ⟨da, hda⟩ := desc_decode hla hla'
  obtain ⟨db, hdb⟩ := desc_decode hlb hlb'
  obtain ⟨dsc, hdi, hgr⟩ : ∃ dsc, TcMma.decode .two false .f16 qkIdesc = some dsc ∧
      dsc.group = .two := ⟨_, rfl, rfl⟩
  obtain ⟨spec, hs⟩ := operands_two hpre hg dsc da db hgr
  obtain ⟨acc, he⟩ := he
  have ht := tc_mma_en (L := L) (mask := masks0) (ms := [0, 0, 0, 0, 0, 0, 0, 0]) hg hd hc
    hA (by unfold descHi; omega) hB
    (by unfold descHi; omega) hI (by decide) rfl rfl he hda hdb hdi hs
  simp only [eventTmpl] at hf
  rw [ht] at hf
  exact isMma_of_fires hf

/-- **A PV MMA is an MMA**: its accumulator and P columns, V descriptor (low word `lb`), the
PV instruction descriptor, an A offset that stays in the column field, any enable operand. -/
theorem pv_isMma (hpre : Pre P L mem0) (hg : g < L.threads) {t : TState}
    {pc dst ta rb ri c a lb : Nat} {aoff : Int} {en : Opnd} {e : Event} {o : Option TState}
    (hd : t.regs dst = some (b32 c)) (hc : c < 2 ^ 32)
    (hA : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32) (ho : ∃ a', tmemOffset a aoff = .ok a')
    (hB : t.regs rb = some (desc lb)) (hlb : lb < 2 ^ 31) (hlb' : lb / 2 ^ 15 % 2 = 0)
    (hI : t.regs ri = some (b32 pvIdesc)) (he : ∃ acc, mmaEnable t en = .ok acc)
    (hf : Fires pc (eventTmpl asms L g t
      (.tcMma (.dense .two false .f16 dst (.tmem ta aoff) (.reg rb) (.reg ri) masks0 en))) e o) :
    isMma e = true := by
  obtain ⟨db, hdb⟩ := desc_decode hlb hlb'
  obtain ⟨dsc, hdi, hgr, htr⟩ : ∃ dsc, TcMma.decode .two false .f16 pvIdesc = some dsc ∧
      dsc.group = .two ∧ dsc.transposeA = false := ⟨_, rfl, rfl, rfl⟩
  obtain ⟨spec, hs⟩ := operands_two hpre hg dsc db db hgr
  obtain ⟨acc, he⟩ := he
  obtain ⟨a', ho⟩ := ho
  have ht := tc_mmaTs (L := L) (mask := masks0) (ms := [0, 0, 0, 0, 0, 0, 0, 0]) hg hd hc
    hA ha ho hB
    (by unfold descHi; omega) hI (by decide) rfl rfl he hdb hdi htr hs
  simp only [eventTmpl] at hf
  rw [ht] at hf
  exact isMma_of_fires hf

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
