-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TmaTmpl
public import Lemmas.Tcgen05.TcGroup

@[expose] public section

/-!
# `tcgen05` instructions

The event templates of `tcgen05` instructions, from register facts.
-/

namespace PTX.Proof
open PTX

section
variable {L : Launch} {g : Nat} {t : TState}

theorem readBits_b32 {r : Nat} {a : Nat} (h : t.regs r = some (b32 a)) (ha : a < 2 ^ 32) :
    readBits L g t 32 (.reg r) = .ok (BitVec.ofNat 64 a) := by
  simp only [readBits, readReg, h, b32, bind, Except.bind, pure, Except.pure,
    truncBits_ofNat ha (by decide)]

theorem readBits_b64 {r : Nat} {a : Nat} (h : t.regs r = some (b64 a)) (ha : a < 2 ^ 64) :
    readBits L g t 64 (.reg r) = .ok (BitVec.ofNat 64 a) := by
  simp only [readBits, readReg, h, b64, bind, Except.bind, pure, Except.pure,
    truncBits_ofNat ha (by decide)]

theorem readBits_imm32 : readBits L g t 32 (.imm 32) = .ok (BitVec.ofNat 64 32) := rfl

theorem tc_alloc {r : Nat} {a : Nat} (hb : L.block % 32 = 0) (h : t.regs r = some (b32 a))
    (ha : a < 2 ^ 32) (hal : a % 4 = 0) (hs : t.sub = 0) :
    tcTmpl L g t (.tcAlloc .one r 0 (.imm 32)) =
      .tc (.resource .one (some ⟨.shared, g / L.block, a⟩) (.alloc 32))
        (if laneOf L g = 0 then { t with sub := 1 } else next t) := by
  simp only [tcTmpl, Flow.effAddr_b32 h ha, readBits_imm32, bind,
    Except.bind, Proof.toNat_ofNat_lt (show 32 < 2 ^ 64 by decide)]
  simp [ofExec, hb, hal, hs, Tmem.validColumns, pure, Except.pure]

theorem tc_allocWrite {r : Nat} {a : Nat} (hb : L.block % 32 = 0)
    (h : t.regs r = some (b32 a)) (ha : a < 2 ^ 32) (hal : a % 4 = 0) (hs : t.sub = 1) :
    tcTmpl L g t (.tcAlloc .one r 0 (.imm 32)) =
      .tcAllocStore ⟨.shared, g / L.block, a⟩ { t with pc := t.pc + 1, sub := 0 } := by
  simp only [tcTmpl, Flow.effAddr_b32 h ha, readBits_imm32, bind,
    Except.bind, Proof.toNat_ofNat_lt (show 32 < 2 ^ 64 by decide)]
  simp [ofExec, hb, hal, hs, Tmem.validColumns, pure, Except.pure]

theorem tc_dealloc {r : Nat} {c : Nat} (hb : L.block % 32 = 0) (h : t.regs r = some (b32 c))
    (hc : c < 2 ^ 32) :
    tcTmpl L g t (.tcDealloc .one (.reg r) (.imm 32)) =
      .tc (.resource .one none (.dealloc c 32)) (next t) := by
  simp only [tcTmpl, readBits_b32 h hc, readBits_imm32, bind,
    Except.bind, Proof.toNat_ofNat_lt (show 32 < 2 ^ 64 by decide),
    Proof.toNat_ofNat_lt (show c < 2 ^ 64 by omega)]
  simp [ofExec, hb, Tmem.validColumns, pure, Except.pure]

theorem tc_commit {group : CtaGroup} {r : Nat} {a : Nat} {s : TcCommit.Spec}
    (h : t.regs r = some (b32 a)) (ha : a < 2 ^ 32) (hal : a % 8 = 0) (hg : g < L.threads)
    (hs : TcCommit.resolve L group (g / L.block) ⟨.shared, g / L.block, a⟩
      (BitVec.ofNat 16 (2 ^ L.rankOfCta (g / L.block))) = some s) :
    tcCommitTmpl L g t (.tcCommit group r 0 none) = .tc (.commit s) (next t) := by
  simp only [tcCommitTmpl, Flow.mbarClusterLoc_b32 h ha hal, bind, Except.bind, ofExec, hg, hs,
    ↓reduceIte, pure, Except.pure]

theorem tc_waitLd (hb : L.block % 32 = 0) : tcTmpl L g t .tcWaitLd = .tc .waitLd (next t) := by
  simp [tcTmpl, ofExec, hb, pure, Except.pure]

/-- A `tcgen05.ld` of a shape other than `.pack::16b` whose registers hold a data address is the
load event of `ds.length` words. The `.pack::16b` shapes are excluded: they load `2 * ds.length`
words and pack them (`TcPack16.pack`), so their event differs. -/
theorem tc_ld_supported {r : Nat} {ds : List Nat} {a : Nat} {sh : TcShape}
    (hsh : ∀ s, sh ≠ .packed16 s)
    (hb : L.block % 32 = 0) (h : t.regs r = some (b32 a)) (ha : a < 2 ^ 32)
    (hn : sh.countOk ds.length = true) (hc : tcDataAddressOk L g sh a = true) :
    tcTmpl L g t (.tcLd ds r sh) = .tcLd a ds.length sh fun vals => setRegs (next t) ds vals := by
  rw [tcTmpl_tcLd_none hsh]
  simp only [ofExec, readBits_b32 h ha, bind, Except.bind,
    Proof.toNat_ofNat_lt (show a < 2 ^ 64 by omega)]
  simp [hb, hn, hc, pure, Except.pure]

theorem tc_ld {r : Nat} {ds : List Nat} {a : Nat} {sh : TcShape}
    (hsh : ∀ s, sh ≠ .packed16 s) (hb : L.block % 32 = 0)
    (h : t.regs r = some (b32 a)) (ha : a < 2 ^ 32) (hn : sh.countOk ds.length = true)
    (hl : a / 2 ^ 16 = laneBase L g) (hs : sh.splitOk a = true := by rfl) :
    tcTmpl L g t (.tcLd ds r sh) = .tcLd a ds.length sh fun vals => setRegs (next t) ds vals := by
  exact tc_ld_supported hsh hb h ha hn (tcDataAddressOk_of_lane_base hs hl)

/-- A shared memory descriptor as the integer GEMM builds it: start `16 s`, leading byte
offset 128, stride byte offset 256, version 1, no swizzle. -/
theorem sharedDecode_canon {s x : Nat} (hs : s < 16384) (hx : s + 524288 + 70437463654400 = x) :
    TcShared.decode x = some ⟨s * 16, 128, 256, 0, false, false, .none⟩ := by
  have h0 : x / 2305843009213693952 % 8 = 0 := by omega
  have h1 : x < 18446744073709551616 := by omega
  have h2 : x / 32768 % 2 = 0 := by omega
  have h3 : x / 2147483648 % 2 = 0 := by omega
  have h4 : x / 70368744177664 % 8 = 1 := by omega
  have h5 : x / 18014398509481984 % 128 = 0 := by omega
  have h6 : x % 32768 = s := by omega
  have h7 : x / 65536 % 32768 = 8 := by omega
  have h8 : x / 4294967296 % 16384 = 16 := by omega
  have h9 : x / 562949953421312 % 8 = 0 := by omega
  have h10 : x / 4503599627370496 % 2 = 0 := by omega
  have h11 : x / 9007199254740992 % 2 = 0 := by omega
  simp only [TcShared.decode, Nat.reducePow, h0, TcShared.decodeSwizzle, h1, h2, h3, h4, h5, h6,
    h7, h8, h9, h10, h11, and_self, ↓reduceIte, Nat.reduceMul]
  simp

/-- A dense `tcgen05.mma` with A in shared memory, whose registers hold decodable descriptors,
issues its MMA event with the default collector usage. -/
theorem tc_mma {group : CtaGroup} {kind : MmaKind} {d rA rB rI p : Nat} {mask : List Opnd}
    {c a b i : Nat} {ms : List (BitVec 64)} {accumulate : Bool}
    (hg : g < L.threads) (hd : t.regs d = some (b32 c)) (hc : c < 2 ^ 32)
    (hA : t.regs rA = some (b64 a)) (ha : a < 2 ^ 64)
    (hB : t.regs rB = some (b64 b)) (hb' : b < 2 ^ 64) (hI : t.regs rI = some (b32 i))
    (hi : i < 2 ^ 32) (hm : mask.mapM (readBits L g t 32) = .ok ms)
    (hn : mask.length = 4 * group.size)
    (hp : t.regs p = some (.pred accumulate))
    {da db : TcShared.Descriptor} {desc : TcMma.Descriptor} {spec : TcMma.OperandSpec}
    (hda : TcShared.decode a = some da) (hdb : TcShared.decode b = some db)
    (hdi : TcMma.decode group false kind i = some desc)
    (hs : TcMma.makeOperands L (g / L.block) desc da db = some spec) :
    tcTmpl L g t (.tcMma (.dense group false kind d (.smem (.reg rA)) (.reg rB) (.reg rI) mask
        (.reg p))) =
      .tc (.mma c { spec with collector := {} } accumulate (ms.map BitVec.toNat)) (next t) := by
  have hr : (TcMmaInstr.dense group false kind d (.smem (.reg rA)) (.reg rB) (.reg rI) mask
      (.reg p)).rule = some .threadTc := by
    simp only [TcMmaInstr.dense, TcMmaInstr.rule]
    cases kind with
    | i8 | f16 | tf32 | f8f6f4 => rfl
    | mxf4 | mxf4nvf4 | mxf8f6f4 | ti16 => simp [TcMma.decode, TcMma.decodeKind] at hdi
  have hmt : mmaTmpl L g t (.dense group false kind d (.smem (.reg rA)) (.reg rB) (.reg rI) mask
      (.reg p)) =
      mmaSmemTmpl L g t group false kind d (.reg rA) (.reg rB) (.reg rI) mask (.reg p) none {} := by
    simp only [mmaTmpl, hr]
    rfl
  rw [tcTmpl, hmt]
  simp only [mmaSmemTmpl, readBits_b32 hd hc, readBits_b64 hA ha,
    readBits_b64 hB hb', readBits_b32 hI hi, bind, Except.bind, mmaEnable, readReg, hp,
    Proof.toNat_ofNat_lt (show c < 2 ^ 64 by omega), Proof.toNat_ofNat_lt ha,
      Proof.toNat_ofNat_lt hb',
    Proof.toNat_ofNat_lt (show i < 2 ^ 64 by omega)]
  simp [ofExec, hg, hn, hda, hdb, hdi, hs, zeroColumnMaskOk, hm, pure, Except.pure]

end

end PTX.Proof
