-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TcMmaTs
public import Lemmas.Flow.Step.ShapeRegs
public import Lemmas.Flow.Step.SiteCases

@[expose] public section

/-! # Step and shape lemmas for `tcgen05.cp` and every `tcgen05.mma` form

A proof tool. `Lemmas/Flow/Tc.lean` and `Lemmas/Flow/TcMmaTs.lean` treat the `.dense` forms of
`tcgen05.mma` (no zero-column mask, no collector reuse); a `.ws` MMA with a zero-column mask
descriptor, and `tcgen05.cp`, had no step lemma:

* `fires_tcMma_next`: every `tcgen05.mma` issue continues at the next instruction;
* `fires_tcCp_next`: a `tcgen05.cp` continues at the next instruction;
* `fires_tcCp_cases`, `shape_tcCp`: a `tcgen05.cp` fires a Tensor Core copy of its shape and
  decompression from the address register's word, or undefined behaviour;
* `shape_tcMma`: a `tcgen05.mma` fires an MMA issue, or undefined behaviour;
* `zeroColumnMaskOk_imm0`: the zero-column mask descriptor `0` generates the all-zero mask;
* `tc_mmaTmem`, `tc_mmaSmem`: the template of an MMA in any form with a rule (`.ws`, a
  zero-column mask, collector usage) from register facts and decodable descriptors;
* `advances_tc`: `advances` that also closes `tcgen05.cp` and every `tcgen05.mma`.

A TMA copy in four-row mode (`TensorMode.fourRows`, gather4) needs nothing new: `fires_next`
(`AdvancesOp`) and `shape_cpTensorAt` are stated for every tensor mode. -/

namespace PTX.Flow
open PTX PTX.EventFrame

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat} {e : Event}
  {o : Option TState}

/-- **Every `tcgen05.mma` issue continues at the next instruction.** -/
theorem fires_tcMma_next {u : TState} {m : TcMmaInstr}
    (hf : Fires pc (eventTmpl A L g t (.tcMma m)) e (some u)) : u = next t := by
  have hm : CallbackFrame (· = next t) (eventTmpl A L g t (.tcMma m)) := by
    simp only [eventTmpl, tcTmpl, mmaTmpl]
    split
    · simp only [mmaSmemTmpl]
      apply ofExec_frame
      repeat' first
        | rfl
        | exact True.intro
        | (apply allOk_bind; intro v)
        | split
    · simp only [mmaTmemTmpl]
      apply ofExec_frame
      repeat' first
        | rfl
        | exact True.intro
        | (apply allOk_bind; intro v)
        | split
    · exact True.intro
  exact callbackFrame_fires (P := (· = next t)) hm hf

/-- **A `tcgen05.cp` continues at the next instruction.** -/
theorem fires_tcCp_next {u : TState} {grp : CtaGroup} {sh : TcCpShape} {ta : Nat} {sd : Opnd}
    {fmt : Option TcCpFmt} (hf : Fires pc (eventTmpl A L g t (.tcCp grp sh ta sd fmt)) e (some u)) :
    u = next t := by
  have hm : CallbackFrame (· = next t) (eventTmpl A L g t (.tcCp grp sh ta sd fmt)) := by
    simp only [eventTmpl, tcTmpl]
    apply ofExec_frame
    repeat' first
      | rfl
      | exact True.intro
      | (apply allOk_bind; intro v)
      | split
  exact callbackFrame_fires (P := (· = next t)) hm hf

/-- The templates a `tcgen05.cp` of shape `sh` and decompression `fmt` has: its copy, continuing
at the next instruction, or undefined behaviour. -/
def CpOf (sh : TcCpShape) (fmt : Option TcCpFmt) (t : TState) : Tmpl → Prop
  | .tc (.cp s) u => s.shape = sh ∧ s.fmt = fmt ∧ u = next t
  | .ub _ => True
  | _ => False

theorem ofExec_cpOf {sh : TcCpShape} {fmt : Option TcCpFmt} {r : Exec Tmpl}
    (h : AllOk (CpOf sh fmt t) r) : CpOf sh fmt t (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- **A `tcgen05.cp` fires a copy of its shape and decompression**, continuing at the next
instruction, or undefined behaviour. -/
theorem fires_tcCp_cases {grp : CtaGroup} {sh : TcCpShape} {ta : Nat} {sd : Opnd}
    {fmt : Option TcCpFmt} (hf : Fires pc (eventTmpl A L g t (.tcCp grp sh ta sd fmt)) e o) :
    (∃ s : TcCopy.Spec, s.shape = sh ∧ s.fmt = fmt ∧ e = ⟨pc, .tc (.cp s)⟩ ∧ o = some (next t)) ∨
      ∃ f, e = ⟨pc, .ub f⟩ := by
  have hm : CpOf sh fmt t (eventTmpl A L g t (.tcCp grp sh ta sd fmt)) := by
    simp only [eventTmpl, tcTmpl]
    apply ofExec_cpOf
    repeat' first
      | (apply allOk_bind; intro _)
      | split
      | exact ⟨rfl, rfl, rfl⟩
      | exact trivial
  generalize eventTmpl A L g t (.tcCp grp sh ta sd fmt) = tm at hm hf
  cases tm <;> simp only [CpOf] at hm
  case tc k u =>
    cases k <;> simp only at hm
    obtain ⟨h1, h2, rfl⟩ := hm
    simp only [Fires] at hf
    exact .inl ⟨_, h1, h2, hf.1, hf.2⟩
  case ub f =>
    simp only [Fires] at hf
    exact .inr ⟨f, hf.1⟩

/-- **A `tcgen05.cp` in the form `site_shape` applies**: `P` of every copy of its shape and
decompression, and of undefined behaviour. -/
theorem shape_tcCp {P : Event → Prop} {grp : CtaGroup} {sh : TcCpShape} {ta : Nat} {sd : Opnd}
    {fmt : Option TcCpFmt} (hf : Fires pc (eventTmpl A L g t (.tcCp grp sh ta sd fmt)) e o)
    (hP : ∀ s : TcCopy.Spec, s.shape = sh → s.fmt = fmt → P ⟨pc, .tc (.cp s)⟩)
    (hub : ∀ f, P ⟨pc, .ub f⟩) : P e := by
  rcases fires_tcCp_cases hf with ⟨s, h1, h2, rfl, -⟩ | ⟨f, rfl⟩
  · exact hP s h1 h2
  · exact hub f

/-- **A `tcgen05.mma` in the form `site_shape` applies**: `P` of every MMA issue and of undefined
behaviour. -/
theorem shape_tcMma {P : Event → Prop} {m : TcMmaInstr}
    (hf : Fires pc (eventTmpl A L g t (.tcMma m)) e o)
    (hP : ∀ d s acc ms, P ⟨pc, .tc (.mma d s acc ms)⟩) (hub : ∀ f, P ⟨pc, .ub f⟩) : P e := by
  have hpc := fires_pc hf
  obtain ⟨epc, k⟩ := e
  simp only at hpc
  subst hpc
  rcases fires_tcMma_kind hf with ⟨d, s, acc, ms, hk⟩ | ⟨f, hk⟩
  · simp only at hk
    subst hk
    exact hP d s acc ms
  · simp only at hk
    subst hk
    exact hub f

end

/-- `advances` that also closes `tcgen05.cp` and every form of `tcgen05.mma`. -/
macro "advances_tc" : tactic => `(tactic| first
  | advances_of PTX.Op.tcCp PTX.Flow.fires_tcCp_next
  | advances_of PTX.Op.tcMma PTX.Flow.fires_tcMma_next
  | advances)

end PTX.Flow

namespace PTX.Proof
open PTX

section
variable {L : Launch} {g : Nat} {t : TState}

/-- The zero-column mask descriptor `0` generates the all-zero mask. -/
theorem zeroColumnMaskOk_imm0 : zeroColumnMaskOk L g t (some (.imm 0)) = .ok () := by
  simp [zeroColumnMaskOk, readBits, zeroColumnMaskNone, truncBits, bind, Except.bind, pure,
    Except.pure]

/-- **The template of a `tcgen05.cp`** whose address register holds a word the shape accepts and
whose source descriptor decodes. -/
theorem tc_cp {grp : CtaGroup} {sh : TcCpShape} {ta : Nat} {sd : Opnd} {fmt : Option TcCpFmt}
    {a s : Nat} {src : TcShared.Descriptor} {ctas : List Nat} (hg : g < L.threads)
    (hA : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32) (hok : TcCopy.AddressOk sh a)
    (hS : readBits L g t 64 sd = .ok (BitVec.ofNat 64 s)) (hs : s < 2 ^ 64)
    (hd : TcShared.decode s = some src) (hc : L.ctaGroup (g / L.block) grp = some ctas) :
    tcTmpl L g t (.tcCp grp sh ta sd fmt) =
      .tc (.cp { address := a, src, shape := sh, ctas, fmt }) (next t) := by
  simp only [tcTmpl, readBits_b32 hA ha, hS, bind, Except.bind,
    Proof.toNat_ofNat_lt (show a < 2 ^ 64 by omega), Proof.toNat_ofNat_lt hs]
  simp [ofExec, hg, hok, hd, hc, pure, Except.pure]

/-- **The template of a `tcgen05.mma` with A in Tensor Memory**, in any form with a rule (`.ws`,
a zero-column mask, collector usage), from register facts and decodable descriptors. -/
theorem tc_mmaTmem {m : TcMmaInstr} {ta rB rI : Nat} {aoff : Int} {c a a' b i : Nat}
    {ms : List (BitVec 64)} {accumulate : Bool}
    (hr : m.rule = some .threadTc) (hmA : m.a = .tmem ta aoff) (hmB : m.bdesc = .reg rB)
    (hmI : m.idesc = .reg rI)
    (hg : g < L.threads) (hd : t.regs m.d = some (b32 c)) (hc : c < 2 ^ 32)
    (hA : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32) (ho : tmemOffset a aoff = .ok a')
    (hB : t.regs rB = some (b64 b)) (hb' : b < 2 ^ 64) (hI : t.regs rI = some (b32 i))
    (hi : i < 2 ^ 32) (hm : m.mask.mapM (readBits L g t 32) = .ok ms)
    (hn : m.mask.length = 4 * m.group.size) (he : mmaEnable t m.enableD = .ok accumulate)
    (hz : zeroColumnMaskOk L g t m.zeroColumnMask = .ok ())
    {db : TcShared.Descriptor} {desc : TcMma.Descriptor} {spec : TcMma.OperandSpec}
    (hdb : TcShared.decode b = some db)
    (hdi : TcMma.decode m.group m.ws m.kind i = some desc) (ht : desc.transposeA = false)
    (hs : TcMma.makeOperands L (g / L.block) desc db db = some spec) :
    tcTmpl L g t (.tcMma m) =
      .tc (.mma c { spec with aTmem := some a', collector := m.collectors } accumulate
        (ms.map BitVec.toNat)) (next t) := by
  have hmt : mmaTmpl L g t m = mmaTmemTmpl L g t m.group m.ws m.kind m.d ta aoff (.reg rB)
      (.reg rI) m.mask m.enableD m.zeroColumnMask m.collectors := by
    simp only [mmaTmpl, hr, hmA, hmB, hmI]
  rw [tcTmpl, hmt]
  simp only [mmaTmemTmpl, readBits_b32 hd hc, readBits_b32 hA ha, readBits_b64 hB hb',
    readBits_b32 hI hi, bind, Except.bind, he, ho, hz,
    Proof.toNat_ofNat_lt (show c < 2 ^ 64 by omega),
    Proof.toNat_ofNat_lt (show a < 2 ^ 64 by omega),
    Proof.toNat_ofNat_lt hb', Proof.toNat_ofNat_lt (show i < 2 ^ 64 by omega)]
  simp [ofExec, hg, hn, hdb, hdi, ht, hs, hm, pure, Except.pure]

/-- **The template of a `tcgen05.mma` with A in shared memory**, in any form with a rule. -/
theorem tc_mmaSmem {m : TcMmaInstr} {rA rB rI : Nat} {c a b i : Nat}
    {ms : List (BitVec 64)} {accumulate : Bool}
    (hr : m.rule = some .threadTc) (hmA : m.a = .smem (.reg rA)) (hmB : m.bdesc = .reg rB)
    (hmI : m.idesc = .reg rI)
    (hg : g < L.threads) (hd : t.regs m.d = some (b32 c)) (hc : c < 2 ^ 32)
    (hA : t.regs rA = some (b64 a)) (ha : a < 2 ^ 64)
    (hB : t.regs rB = some (b64 b)) (hb' : b < 2 ^ 64) (hI : t.regs rI = some (b32 i))
    (hi : i < 2 ^ 32) (hm : m.mask.mapM (readBits L g t 32) = .ok ms)
    (hn : m.mask.length = 4 * m.group.size) (he : mmaEnable t m.enableD = .ok accumulate)
    (hz : zeroColumnMaskOk L g t m.zeroColumnMask = .ok ())
    {da db : TcShared.Descriptor} {desc : TcMma.Descriptor} {spec : TcMma.OperandSpec}
    (hda : TcShared.decode a = some da) (hdb : TcShared.decode b = some db)
    (hdi : TcMma.decode m.group m.ws m.kind i = some desc)
    (hs : TcMma.makeOperands L (g / L.block) desc da db = some spec) :
    tcTmpl L g t (.tcMma m) =
      .tc (.mma c { spec with collector := m.collectors } accumulate (ms.map BitVec.toNat))
        (next t) := by
  have hmt : mmaTmpl L g t m = mmaSmemTmpl L g t m.group m.ws m.kind m.d (.reg rA) (.reg rB)
      (.reg rI) m.mask m.enableD m.zeroColumnMask m.collectors := by
    simp only [mmaTmpl, hr, hmA, hmB, hmI]
  rw [tcTmpl, hmt]
  simp only [mmaSmemTmpl, readBits_b32 hd hc, readBits_b64 hA ha, readBits_b64 hB hb',
    readBits_b32 hI hi, bind, Except.bind, he, hz,
    Proof.toNat_ofNat_lt (show c < 2 ^ 64 by omega), Proof.toNat_ofNat_lt ha,
    Proof.toNat_ofNat_lt hb', Proof.toNat_ofNat_lt (show i < 2 ^ 64 by omega)]
  simp [ofExec, hg, hn, hda, hdb, hdi, hs, hm, pure, Except.pure]

end

end PTX.Proof
