-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Tc
public import Lemmas.Flow.TcTmpl

@[expose] public section

/-!
# `tcgen05.mma` with A in Tensor Memory

The `[a-tmem]` form of `tcgen05.mma` (`.tcMma (.dense … (.tmem ta aoff) …)`), as
`Lemmas/Flow/Tc.lean` and `Lemmas/Flow/TcTmpl.lean` treat the shared-descriptor form:

* `fires_tcMmaTs`: the issue continues at the next instruction whatever its operands evaluate to;
* `tmemOffset_of`: the A address `[a + off]` (THREAD-TC) whose column stays below
  `2^16` is the sum `a + off`;
* `tc_mmaTs`: from register facts and decodable descriptors, the template is the MMA event whose
  A operand is that Tensor Memory address; `tc_mma_en` is `tc_mma` with any `enable-input-d`
  operand (a predicate register or an integer constant);
* `sharedDecode_some`: a shared-memory descriptor `lo + hi·2^32` whose low word keeps bits 15
  and 31 clear and whose high word has the version 1, zero reserved bits and a documented
  swizzle code decodes.
-/

namespace PTX.Flow
open PTX PTX.EventFrame

noncomputable section

theorem fires_tcMmaTs {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {group : CtaGroup} {ws : Bool} {kind : MmaKind} {dst ta : Nat} {aoff : Int} {bd id : Opnd}
    {mask : List Opnd} {en : Opnd} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t
      (.tcMma (.dense group ws kind dst (.tmem ta aoff) bd id mask en))) e (some u)) :
    u = next t := by
  have hm : CallbackFrame (· = next t)
      (eventTmpl A L g t
        (.tcMma (.dense group ws kind dst (.tmem ta aoff) bd id mask en))) := by
    simp only [eventTmpl, tcTmpl, mmaTmpl, TcMmaInstr.dense, TcMmaInstr.rule]
    cases kind <;> repeat' first
      | rfl
      | exact True.intro
      | (apply ofExec_frame)
      | (apply allOk_bind; intro v)
      | split
  exact callbackFrame_fires (P := (· = next t)) hm hf

end
end PTX.Flow

namespace PTX.Proof
open PTX

section
variable {L : Launch} {g : Nat} {t : TState}

/-- A constant offset that keeps the column field below `2^16` adds to the address. -/
theorem tmemOffset_of {a off : Nat} (h : a % 2 ^ 16 + off < 2 ^ 16) :
    tmemOffset a (off : Int) = .ok (a + off) := by
  have hc : (0 : Int) ≤ (a : Int) % 2 ^ 16 + (off : Int) ∧
      (a : Int) % 2 ^ 16 + (off : Int) < 2 ^ 16 := by omega
  simp only [tmemOffset, hc, and_self, ↓reduceIte, pure, Except.pure]
  congr 1
  omega

/-- A `tcgen05.mma` with A in Tensor Memory whose registers hold decodable descriptors issues
its MMA event. -/
theorem tc_mmaTs {group : CtaGroup} {kind : MmaKind} {d ta rB rI : Nat} {aoff : Int}
    {mask : List Opnd} {en : Opnd} {c a a' b i : Nat} {ms : List (BitVec 64)}
    {accumulate : Bool}
    (hg : g < L.threads) (hd : t.regs d = some (b32 c)) (hc : c < 2 ^ 32)
    (hA : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32) (ho : tmemOffset a aoff = .ok a')
    (hB : t.regs rB = some (b64 b)) (hb' : b < 2 ^ 64) (hI : t.regs rI = some (b32 i))
    (hi : i < 2 ^ 32) (hm : mask.mapM (readBits L g t 32) = .ok ms)
    (hn : mask.length = 4 * group.size) (he : mmaEnable t en = .ok accumulate)
    {db : TcShared.Descriptor} {desc : TcMma.Descriptor} {spec : TcMma.OperandSpec}
    (hdb : TcShared.decode b = some db)
    (hdi : TcMma.decode group false kind i = some desc) (ht : desc.transposeA = false)
    (hs : TcMma.makeOperands L (g / L.block) desc db db = some spec) :
    tcTmpl L g t (.tcMma (.dense group false kind d (.tmem ta aoff) (.reg rB) (.reg rI) mask
        en)) =
      .tc (.mma c { spec with aTmem := some a', collector := {} } accumulate
        (ms.map BitVec.toNat)) (next t) := by
  have hr : (TcMmaInstr.dense group false kind d (.tmem ta aoff) (.reg rB) (.reg rI) mask
      en).rule = some .threadTc := by
    simp only [TcMmaInstr.dense, TcMmaInstr.rule]
    cases kind with
    | i8 | f16 | tf32 | f8f6f4 => rfl
    | mxf4 | mxf4nvf4 | mxf8f6f4 | ti16 => simp [TcMma.decode, TcMma.decodeKind] at hdi
  have hmt : mmaTmpl L g t (.dense group false kind d (.tmem ta aoff) (.reg rB) (.reg rI) mask
      en) =
      mmaTmemTmpl L g t group false kind d ta aoff (.reg rB) (.reg rI) mask en none {} := by
    simp only [mmaTmpl, hr]
    rfl
  rw [tcTmpl, hmt]
  simp only [mmaTmemTmpl, readBits_b32 hd hc, readBits_b32 hA ha, readBits_b64 hB hb',
    readBits_b32 hI hi, bind, Except.bind, he, ho,
    Proof.toNat_ofNat_lt (show c < 2 ^ 64 by omega),
    Proof.toNat_ofNat_lt (show a < 2 ^ 64 by omega),
    Proof.toNat_ofNat_lt hb', Proof.toNat_ofNat_lt (show i < 2 ^ 64 by omega)]
  simp [ofExec, hg, hn, hdb, hdi, ht, hs, zeroColumnMaskOk, hm, pure, Except.pure]

/-- `tc_mma` with any `enable-input-d` operand. -/
theorem tc_mma_en {group : CtaGroup} {kind : MmaKind} {d rA rB rI : Nat} {mask : List Opnd}
    {en : Opnd} {c a b i : Nat} {ms : List (BitVec 64)} {accumulate : Bool}
    (hg : g < L.threads) (hd : t.regs d = some (b32 c)) (hc : c < 2 ^ 32)
    (hA : t.regs rA = some (b64 a)) (ha : a < 2 ^ 64)
    (hB : t.regs rB = some (b64 b)) (hb' : b < 2 ^ 64) (hI : t.regs rI = some (b32 i))
    (hi : i < 2 ^ 32) (hm : mask.mapM (readBits L g t 32) = .ok ms)
    (hn : mask.length = 4 * group.size) (he : mmaEnable t en = .ok accumulate)
    {da db : TcShared.Descriptor} {desc : TcMma.Descriptor} {spec : TcMma.OperandSpec}
    (hda : TcShared.decode a = some da) (hdb : TcShared.decode b = some db)
    (hdi : TcMma.decode group false kind i = some desc)
    (hs : TcMma.makeOperands L (g / L.block) desc da db = some spec) :
    tcTmpl L g t (.tcMma (.dense group false kind d (.smem (.reg rA)) (.reg rB) (.reg rI) mask
        en)) =
      .tc (.mma c { spec with collector := {} } accumulate (ms.map BitVec.toNat)) (next t) := by
  have hr : (TcMmaInstr.dense group false kind d (.smem (.reg rA)) (.reg rB) (.reg rI) mask
      en).rule = some .threadTc := by
    simp only [TcMmaInstr.dense, TcMmaInstr.rule]
    cases kind with
    | i8 | f16 | tf32 | f8f6f4 => rfl
    | mxf4 | mxf4nvf4 | mxf8f6f4 | ti16 => simp [TcMma.decode, TcMma.decodeKind] at hdi
  have hmt : mmaTmpl L g t (.dense group false kind d (.smem (.reg rA)) (.reg rB) (.reg rI) mask
      en) =
      mmaSmemTmpl L g t group false kind d (.reg rA) (.reg rB) (.reg rI) mask en none {} := by
    simp only [mmaTmpl, hr]
    rfl
  rw [tcTmpl, hmt]
  simp only [mmaSmemTmpl, readBits_b32 hd hc, readBits_b64 hA ha, readBits_b64 hB hb',
    readBits_b32 hI hi, bind, Except.bind, he,
    Proof.toNat_ofNat_lt (show c < 2 ^ 64 by omega), Proof.toNat_ofNat_lt ha,
      Proof.toNat_ofNat_lt hb',
    Proof.toNat_ofNat_lt (show i < 2 ^ 64 by omega)]
  simp [ofExec, hg, hn, hda, hdb, hdi, hs, zeroColumnMaskOk, hm, pure, Except.pure]

/-- A descriptor word with zero reserved bits, the version 1 and a documented swizzle code
decodes. -/
theorem sharedDecode_of {x : Nat} {sw : TcShared.Swizzle}
    (hs : TcShared.decodeSwizzle (x / 2 ^ 61 % 8) = some sw)
    (hc : x < 2 ^ 64 ∧ x / 2 ^ 15 % 2 = 0 ∧ x / 2 ^ 31 % 2 = 0 ∧ x / 2 ^ 46 % 8 = 1 ∧
      x / 2 ^ 54 % 128 = 0) :
    ∃ d, TcShared.decode x = some d := by
  unfold TcShared.decode
  rw [hs]
  simp only [hc, and_self, ↓reduceIte, Option.some.injEq, exists_eq']

/-- A descriptor `lo + hi·2^32` with bits 15 and 31 of `lo` clear and a high word with the
version 1, zero reserved bits and a documented swizzle code decodes. (Stated through
`sharedDecode_of`, so that the kernel never checks the decoder at the sum.) -/
theorem sharedDecode_some {lo hi : Nat} {sw : TcShared.Swizzle} (hlo : lo < 2 ^ 31)
    (h15 : lo / 2 ^ 15 % 2 = 0) (hhi : hi < 2 ^ 32) (hv : hi / 2 ^ 14 % 8 = 1)
    (hr : hi / 2 ^ 22 % 128 = 0) (hs : TcShared.decodeSwizzle (hi / 2 ^ 29 % 8) = some sw) :
    ∃ d, TcShared.decode (lo + hi * 2 ^ 32) = some d :=
  sharedDecode_of
    (by rw [show (lo + hi * 2 ^ 32) / 2 ^ 61 % 8 = hi / 2 ^ 29 % 8 by omega]; exact hs)
    (by omega)

end

end PTX.Proof
