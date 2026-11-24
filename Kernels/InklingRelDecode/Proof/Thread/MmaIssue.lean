-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.MmaSound
public import Lemmas.Flow.TcMmaTs

@[expose] public section

/-! # The MMA warp's issues are MMAs

At an MMA site whose registers hold the table's values, the issue is an MMA event, never
undefined behaviour: the shared-memory descriptors decode (their low words stay below `2^15` plus
the V operand's bit 26, their high word `0x40004040` has version 1 and the 128-byte swizzle), the
instruction descriptors decode as `kind::f16` with `cta_group::1`, the four lane masks are zero,
and the A address of a PV MMA (`[tmem_a + 8 j]`) stays in its column field.

The one fact about the launch the issue needs is `OneCta`: the thread's CTA is the CTA of its
`cta_group::1` group (the CTA with its own rank in its cluster). This is the premise of these
lemmas; a launch whose cluster is a single CTA of the grid provides it. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- The thread's CTA has the CTA of its own rank in its cluster, which is the CTA of its
`cta_group::1` group. -/
def OneCta (L : Launch) (g : Nat) : Prop :=
  ∃ cta, L.peerCta (g / L.block) (L.rankOfCta (g / L.block)) = some cta

/-- With `OneCta`, every `cta_group::1` descriptor has an operand specification for the thread's
CTA. -/
theorem operands_one (h : OneCta L g) (dsc : TcMma.Descriptor) (da db : TcShared.Descriptor)
    (hd : dsc.group = .one) :
    ∃ spec, TcMma.makeOperands L (g / L.block) dsc da db = some spec := by
  obtain ⟨cta, hc⟩ := h
  refine ⟨⟨dsc, da, db, cta, cta, none, {}⟩, ?_⟩
  rw [TcMma.makeOperands, hd, Launch.ctaGroup_one, hc]
  rfl

/-- A descriptor with high word `0x40004040` and a low word below `2^31` with bit 15 clear
decodes. -/
theorem desc_decode {lo : Nat} (hlo : lo < 2 ^ 31) (h15 : lo / 2 ^ 15 % 2 = 0) :
    ∃ d, TcShared.decode (lo + descHi * 2 ^ 32) = some d :=
  sharedDecode_some (sw := .b128) hlo h15 (by decide) (by decide) (by decide) rfl

/-- The V operand's descriptor (bit 26 of the low word set) decodes when the start address field
is below `2^15`. -/
theorem vdesc_decode {lo : Nat} (hlo : lo < 2 ^ 15) :
    ∃ d, TcShared.decode (lo + 2 ^ 26 + descHi * 2 ^ 32) = some d :=
  desc_decode (lo := lo + 2 ^ 26) (by omega) (by omega)

/-- Whether `e` is a Tensor Core MMA. -/
def isMma (e : Event) : Bool := match e.kind with
  | .tc (.mma ..) => true
  | _ => false

theorem isMma_of_fires {pc : Nat} {e : Event} {o : Option TState} {dd : Nat}
    {sp : TcMma.OperandSpec} {acc : Bool} {mk : List Nat} {u : TState}
    (hf : Fires pc (.tc (.mma dd sp acc mk) u) e o) : isMma e = true := by
  obtain ⟨rfl, -⟩ := hf
  rfl

/-- The four zero lane masks of the MMAs. -/
abbrev masks0 : List Opnd := List.replicate 4 (.imm 0)

/-- **A QK MMA is an MMA**: its accumulator column, Q and K descriptors (low words `la`, `lb`) and
the QK instruction descriptor in its registers, any enable operand. -/
theorem qk_isMma (hone : OneCta L g) (hg : g < L.threads) {t : TState}
    {pc dst ra rb ri c la lb : Nat} {en : Opnd} {e : Event} {o : Option TState}
    (hd : t.regs dst = some (b32 c)) (hc : c < 2 ^ 32)
    (hA : t.regs ra = some (desc la)) (hla : la < 2 ^ 31) (hla' : la / 2 ^ 15 % 2 = 0)
    (hB : t.regs rb = some (desc lb)) (hlb : lb < 2 ^ 31) (hlb' : lb / 2 ^ 15 % 2 = 0)
    (hI : t.regs ri = some (b32 qkIdesc)) (he : ∃ acc, mmaEnable t en = .ok acc)
    (hf : Fires pc (eventTmpl asms L g t (.tcMma (.dense .one false .f16 dst
      (.smem (.reg ra)) (.reg rb) (.reg ri) masks0 en))) e o) :
    isMma e = true := by
  obtain ⟨da, hda⟩ := desc_decode hla hla'
  obtain ⟨db, hdb⟩ := desc_decode hlb hlb'
  obtain ⟨dsc, hdi, hgr⟩ : ∃ dsc, TcMma.decode .one false .f16 qkIdesc = some dsc ∧
      dsc.group = .one := ⟨_, rfl, rfl⟩
  obtain ⟨spec, hs⟩ := operands_one hone dsc da db hgr
  obtain ⟨acc, he⟩ := he
  have ht := tc_mma_en (L := L) (mask := masks0) (ms := [0, 0, 0, 0]) hg hd hc
    hA (by unfold descHi; omega) hB (by unfold descHi; omega) hI (by decide) rfl rfl he hda hdb
    hdi hs
  simp only [eventTmpl] at hf
  rw [ht] at hf
  exact isMma_of_fires hf

/-- **A PV MMA is an MMA**: its accumulator and P columns, V descriptor (start address field `lb`),
the PV instruction descriptor, an A offset that stays in the column field, any enable operand. -/
theorem pv_isMma (hone : OneCta L g) (hg : g < L.threads) {t : TState}
    {pc dst ta rb ri c a lb : Nat} {aoff : Int} {en : Opnd} {e : Event} {o : Option TState}
    (hd : t.regs dst = some (b32 c)) (hc : c < 2 ^ 32)
    (hA : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32) (ho : ∃ a', tmemOffset a aoff = .ok a')
    (hB : t.regs rb = some (vdesc lb)) (hlb : lb < 2 ^ 15)
    (hI : t.regs ri = some (b32 pvIdesc)) (he : ∃ acc, mmaEnable t en = .ok acc)
    (hf : Fires pc (eventTmpl asms L g t
      (.tcMma (.dense .one false .f16 dst (.tmem ta aoff) (.reg rb) (.reg ri) masks0 en))) e o) :
    isMma e = true := by
  obtain ⟨db, hdb⟩ := vdesc_decode hlb
  obtain ⟨dsc, hdi, hgr, htr⟩ : ∃ dsc, TcMma.decode .one false .f16 pvIdesc = some dsc ∧
      dsc.group = .one ∧ dsc.transposeA = false := ⟨_, rfl, rfl, rfl⟩
  obtain ⟨spec, hs⟩ := operands_one hone dsc db db hgr
  obtain ⟨acc, he⟩ := he
  obtain ⟨a', ho⟩ := ho
  have ht := tc_mmaTs (L := L) (mask := masks0) (ms := [0, 0, 0, 0]) hg hd hc
    hA ha ho (b := lb + 2 ^ 26 + descHi * 2 ^ 32) hB (by unfold descHi; omega) hI (by decide)
    rfl rfl he hdb hdi htr hs
  simp only [eventTmpl] at hf
  rw [ht] at hf
  exact isMma_of_fires hf

end
end PTX.Kernels.InklingRelDecode.Proof.Mma
