-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
public import Kernels.TmlFa4Fwd.Proof.Lib.WordAlign
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part133
import Kernels.TmlFa4Fwd.Flow.Code.Part134
import Kernels.TmlFa4Fwd.Flow.Code.Part135
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Kernels.TmlFa4Fwd.Flow.Code.Part137
import Kernels.TmlFa4Fwd.Flow.Code.Part138
import Kernels.TmlFa4Fwd.Flow.Code.Part139
import Kernels.TmlFa4Fwd.Flow.Code.Part140
import Kernels.TmlFa4Fwd.Flow.Code.Part141
import Kernels.TmlFa4Fwd.Proof.Lib.MemAl

@[expose] public section

/-! # The correction warps' final shared stores and LSE stores are no undefined behaviour

A final store (`fst`, `st.shared.v4.b32`) faults only when its address is not a multiple of 16
(`elemAcc`); its base register is the row's swizzled staging address plus the lane's signed
offsets (`fAddrs`), and its offset a multiple of `16384`. Every term of the address is a multiple
of 16 (the shared base by `Pre.shared`, the row times 128, the swizzle's `and` with 112, the
offsets `±16`, `±32`, `±64`), and a shared address is truncated to 32 bits, so the address is a
multiple of 16 whether or not a sum wraps (`al_tac`). Its sources are the products of the
chunk's elements by the reciprocal row sum, four-byte floats.

An LSE store (`lse`, `st.global.b32` at `%rd203` plus 0 or 512) faults only when its address is not
a multiple of 4: the address is the LSE base (4-aligned, `Pre.alignment`) plus two words shifted
left by 2 (`lseAddr`), modulo `2 ^ 64`. Its source is the LSE or the code's `-inf` pattern, four
bytes either way. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- An element of a store of four registers names one of them. -/
theorem src4 {t : TState} {n i a b c d : Nat} (hi : i < 4)
    (ha : ∃ v, t.regs a = some v ∧ v.bytes = n) (hb : ∃ v, t.regs b = some v ∧ v.bytes = n)
    (hc : ∃ v, t.regs c = some v ∧ v.bytes = n) (hd : ∃ v, t.regs d = some v ∧ v.bytes = n) :
    ∃ r v, [Opnd.reg a, .reg b, .reg c, .reg d][i]? = some (.reg r) ∧ t.regs r = some v ∧
      v.bytes = n := by
  interval_cases i
  · obtain ⟨v, h1, h2⟩ := ha; exact ⟨a, v, rfl, h1, h2⟩
  · obtain ⟨v, h1, h2⟩ := hb; exact ⟨b, v, rfl, h1, h2⟩
  · obtain ⟨v, h1, h2⟩ := hc; exact ⟨c, v, rfl, h1, h2⟩
  · obtain ⟨v, h1, h2⟩ := hd; exact ⟨d, v, rfl, h1, h2⟩

/-- The shared base is a multiple of 16. -/
theorem al_sb (hp : Pre p L m) : Al 4 (Mma.sbW L) := by
  have h := hp.shared.1
  have h2 := hp.shared.2.1
  unfold Al
  simp only [Mma.sbW, BitVec.toNat_ofNat]
  omega

/-- The two staging rows of the thread are multiples of 16. -/
theorem al_stg0 (hp : Pre p L m) : Al 4 (stg0 L g) := by
  have := al_sb hp
  simp only [stg0]
  al_tac

theorem al_fStage {st : Fin 2} {a b : BitVec 64} (ha : Al 4 a) (hb : Al 4 b) :
    Al 4 (fStage st a b) := by
  fin_cases st <;> assumption

set_option maxHeartbeats 16000000 in
/-- **No final shared store of the correction warps is undefined behaviour.** -/
theorem fst_safe (hp : Pre p L m) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (code p L g).AtD d t)
    (hc : kernel.code[(code p L g).pc d]? = some ins)
    (hf : Fires ((code p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : ∃ st j hh, d.site = .fst st j hh) (f : Fault) : e.kind ≠ .ub f := by
  have hreg : ∀ r ∈ Flow.live (livePc d), t.regs r = some (valueOf p L g d r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub : t.sub < 4 := by rw [h.2.1]; exact d.k.isLt
  have h0 := al_stg0 (g := g) hp
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨site, v, k⟩ := d
  intro hk
  have hu := fires_ub hf hk
  obtain ⟨st, j, hh, rfl⟩ := hs
  fin_cases st <;> fin_cases j <;> fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    refine stShared_ok (n := 16) rfl rfl rfl rfl rfl rfl (by decide) (by decide)
      (hreg _ (by lit_mem)) ?_ (by decide) ?_ f hu
    swap
    · refine src4 hsub ?_ ?_ ?_ ?_ <;>
        exact ⟨_, hreg _ (by lit_mem), by simp [valueOf, values, fChunk, lookupLit, fv,
          Value.bytes, FloatFmt.bytes, DType.width]⟩
    show Al 4 _
    repeat (first | (with_reducible apply al_fStage) | al_step)

/-- **The LSE store address is 4-aligned**: the LSE base plus two words shifted left by 2,
modulo `2 ^ 64`. -/
theorem lseAddr_al (hp : Pre p L m) (v : V) : (lseAddr p L g v).toNat % 4 = 0 := by
  have h := hp.alignment.2.2.2.2.2.2.2.2.2.2.2
  unfold lseAddr
  simp only [show ¬ (2 ≥ 64) by decide, ↓reduceIte, truncBits, BitVec.toNat_ofNat,
    BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

set_option maxHeartbeats 4000000 in
/-- **No LSE store of the correction warps is undefined behaviour.** -/
theorem lse_safe (hp : Pre p L m) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (code p L g).AtD d t) (hk0 : d.k = 0)
    (hc : kernel.code[(code p L g).pc d]? = some ins)
    (hf : Fires ((code p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : ∃ hh, d.site = .lse hh) (f : Fault) : e.kind ≠ .ub f := by
  have hreg : ∀ r ∈ Flow.live (livePc d), t.regs r = some (valueOf p L g d r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub : t.sub = 0 := by rw [h.2.1]; simp [hk0]
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨site, v, k⟩ := d
  intro hk
  have hu := fires_ub hf hk
  obtain ⟨hh, rfl⟩ := hs
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    refine stGlobal_ok (n := 4) rfl rfl rfl rfl rfl rfl (by decide) (by decide)
      (hreg _ (by lit_mem)) (lseAddr_al hp v) (by decide) ⟨_, _, by rw [hsub]; rfl,
        hreg _ (by lit_mem), ?_⟩ f hu
    simp only [valueOf, values, valuesLse, lookupLit, lseSel]
    split
    · exact erealValue_f32_bytes _
    · rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
