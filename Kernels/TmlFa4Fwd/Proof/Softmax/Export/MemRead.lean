-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.MemWrite
import Kernels.TmlFa4Fwd.Flow.Code.Part054
import Kernels.TmlFa4Fwd.Flow.Code.Part055
import Kernels.TmlFa4Fwd.Flow.Code.Part081
import Kernels.TmlFa4Fwd.Flow.Code.Part082
import Lemmas.Flow.Arith32LineWord
import Lemmas.Flow.LoadAt
import Kernels.TmlFa4Fwd.Proof.Softmax.Align

@[expose] public section

/-! # Where the softmax warps' bias loads read

A bias load reads 16 bytes of the line of its lane's row in its stage's bias buffer, at a swizzled
column: every element's 4 bytes lie in `[sb + 166912 + 32768 st, sb + 199680 + 32768 st)`
(`bld_at`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **What a bias load reads**: 4 bytes of its stage's bias buffer. -/
def BiasAt (L : Launch) (g : Nat) (acc : Acc) : Prop :=
  acc.size = 4 ∧ acc.loc.space = .shared ∧ acc.loc.cta = g / L.block ∧
    L.sharedBase + 166912 + 32768 * stN L g ≤ acc.loc.addr ∧
    acc.loc.addr + 4 ≤ L.sharedBase + 166912 + 32768 * stN L g + 32768

set_option maxRecDepth 100000 in
theorem bias_words : ∀ i < 512, (andi (shl (BitVec.ofNat 64 i) 7) 16256).toNat = 128 * (i % 128) ∧
    (sel (scmpi .gt .s (BitVec.ofNat 64 (i / 32)) 3) (i32 32768) (i32 0)).toNat =
      32768 * (if 3 < i / 32 then 1 else 0) := by
  decide +kernel

/-- A base word of a bias load: a 16-byte column of the first half of the stage's buffer, or of
the second when `n` is above it. -/
theorem base_word (hp : Pre p L m) {x : BitVec 64} {r : Nat} (hr : r < 128) {n c : Nat} (hc : c < 2)
    (hn : n = 166912 + 16384 * c + n % 128) (hn16 : n % 16 = 0) {s : Nat} (hs : s ≤ 1)
    (hx : x.toNat = L.sharedBase + 128 * r + 32768 * s + n) :
    L.sharedBase + 166912 + 32768 * s + 16384 * c + 128 * r ≤ (swz x).toNat ∧
      (swz x).toNat + 16 ≤ L.sharedBase + 166912 + 32768 * s + 16384 * c + 128 * r + 128 := by
  have hsb := hp.shared
  obtain ⟨e1, e2, e3⟩ := swz_line x (by omega) (by omega)
  change (swz x).toNat / 128 = _ at e1
  change (swz x).toNat % 128 ≤ _ at e2
  omega

theorem words (hp : Pre p L m) :
    (rowSb L g).toNat = L.sharedBase + 128 * (g % L.block % 128) ∧
    (bOff L g).toNat = 32768 * stN L g ∧ stN L g ≤ 1 ∧ g % L.block % 128 < 128 := by
  have hs := hp.shared.2.1
  have hi : g % L.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  obtain ⟨h, h2⟩ := bias_words _ hi
  rw [← tidW_eq hp] at h
  have hr : g % L.block % 128 < 128 := Nat.mod_lt _ (by decide)
  have hst : stN L g ≤ 1 := by unfold stN; split <;> omega
  have h3 := iv_add32 (iv_sbW hp) (y := andi (shl (tidW L g) 7) 16256)
    ⟨h.ge, h.le⟩ (by omega)
  unfold Iv at h3
  exact ⟨by simp only [rowSb] at h3 ⊢; omega, h2, hst, hr⟩

theorem bAddr_val (hp : Pre p L m) {n c : Nat} (hc : c < 2)
    (hn : n = 166912 + 16384 * c + n % 128) (hn16 : n % 16 = 0) :
    L.sharedBase + 166912 + 32768 * stN L g + 16384 * c ≤ (bAddr L g n).toNat ∧
      (bAddr L g n).toNat + 16 ≤ L.sharedBase + 166912 + 32768 * stN L g + 16384 * c + 16384 := by
  have hsb := hp.shared
  obtain ⟨h1, h2, h3, h4⟩ := words (g := g) hp
  have ha := iv_add32 (x := rowSb L g) (y := bOff L g) ⟨h1.ge, h1.le⟩ ⟨h2.ge, h2.le⟩ (by omega)
  have hb := iv_addi ha n (by omega)
  unfold Iv at hb
  have := base_word hp h4 hc hn hn16 h3 (x := addi (add32 (rowSb L g) (bOff L g)) n) (by omega)
  simp only [bAddr]
  omega

theorem bAddr0_val (hp : Pre p L m) :
    L.sharedBase + 166912 + 32768 * stN L g ≤ (bAddr0 L g).toNat ∧
      (bAddr0 L g).toNat + 16 ≤ L.sharedBase + 166912 + 32768 * stN L g + 16384 := by
  have hsb := hp.shared
  obtain ⟨h1, h2, h3, h4⟩ := words (g := g) hp
  have hb := iv_addi (x := rowSb L g) (a := (rowSb L g).toNat) (b := (rowSb L g).toNat)
    ⟨le_rfl, le_rfl⟩ 166912 (by omega)
  unfold Iv at hb
  have h := base_word hp h4 (n := 166912) (c := 0) (by decide) (by decide) (by decide)
    (s := 0) (by decide) (x := addi (rowSb L g) 166912)
    (by simp only [Nat.cast_ofNat] at hb ⊢; omega)
  have ha := iv_add32 (x := swz (addi (rowSb L g) 166912)) (y := bOff L g) ⟨le_rfl, le_rfl⟩
    ⟨h2.ge, h2.le⟩ (by omega)
  unfold Iv at ha
  simp only [bAddr0]
  omega

/-- The bytes of an element of a bias load. -/
theorem biasAt_of (hp : Pre p L m) {x : BitVec 64} {c s : Nat} {off : Int} {acc : Acc} (hs : s < 4)
    (hx : L.sharedBase + 166912 + 32768 * stN L g + 16384 * c ≤ x.toNat ∧
      x.toNat + 16 ≤ L.sharedBase + 166912 + 32768 * stN L g + 16384 * c + 16384)
    (ho : off = 0 ∧ c < 2 ∨ off = 16384 ∧ c = 0)
    (hl : acc.loc = ⟨.shared, g / L.block,
      (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat + 4 * s⟩)
    (hz : acc.size = 4) : BiasAt L g acc := by
  have hsb := hp.shared
  have hst : stN L g ≤ 1 := by unfold stN; split <;> omega
  rw [eff_sharedI (by omega) (by omega)] at hl
  refine ⟨hz, by rw [hl], by rw [hl], ?_⟩
  rw [hl]
  simp only
  omega

set_option maxHeartbeats 4000000 in
/-- **What a bias load of the softmax warps reads.** -/
theorem bld_at (hp : Pre p L m) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (code p L g).AtD d t)
    (hc : kernel.code[(code p L g).pc d]? = some ins)
    (hf : Fires ((code p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    {b : Bool} {c : Fin 16} (hs : d.site = .bld b c) {acc : Acc} {bs : List (Option Byte)}
    (hk : e.kind = .rd acc bs) : BiasAt L g acc := by
  have h' := h
  have hreg : ∀ r ∈ ctlLive (livePc d), t.regs r = some (valueOf p L g d r) :=
    fun r hr => holds_mem h'.2.2.2.2 (mem_factsFrom hr)
  have hsub : t.sub < 4 := by rw [h.2.1]; exact d.k.isLt
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨site, v, k, ac⟩ := d
  simp only at hs
  subst hs
  cases b <;> fin_cases c
  all_goals
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    obtain ⟨h1, h2⟩ := ldShared_rd rfl rfl rfl rfl rfl
      (hreg _ (by simp only [ctlLive, List.mem_filter]; exact ⟨by lit_mem, by decide⟩)) hf hk
  · exact biasAt_of (c := 0) hp hsub (bAddr0_val hp) (by decide) h1 h2
  · exact biasAt_of (c := 0) hp hsub (bAddr_val hp (n := 166928)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 0) hp hsub (bAddr_val hp (n := 166944)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 0) hp hsub (bAddr_val hp (n := 166960)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 0) hp hsub (bAddr_val hp (n := 166976)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 0) hp hsub (bAddr_val hp (n := 166992)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 0) hp hsub (bAddr_val hp (n := 167008)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 0) hp hsub (bAddr_val hp (n := 167024)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 0) hp hsub (bAddr0_val hp) (by decide) h1 h2
  · exact biasAt_of (c := 1) hp hsub (bAddr_val hp (n := 183312)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 1) hp hsub (bAddr_val hp (n := 183328)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 1) hp hsub (bAddr_val hp (n := 183344)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 1) hp hsub (bAddr_val hp (n := 183360)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 1) hp hsub (bAddr_val hp (n := 183376)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 1) hp hsub (bAddr_val hp (n := 183392)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 1) hp hsub (bAddr_val hp (n := 183408)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 0) hp hsub (bAddr0_val hp) (by decide) h1 h2
  · exact biasAt_of (c := 0) hp hsub (bAddr_val hp (n := 166928)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 0) hp hsub (bAddr_val hp (n := 166944)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 0) hp hsub (bAddr_val hp (n := 166960)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 0) hp hsub (bAddr_val hp (n := 166976)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 0) hp hsub (bAddr_val hp (n := 166992)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 0) hp hsub (bAddr_val hp (n := 167008)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 0) hp hsub (bAddr_val hp (n := 167024)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 0) hp hsub (bAddr0_val hp) (by decide) h1 h2
  · exact biasAt_of (c := 1) hp hsub (bAddr_val hp (n := 183312)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 1) hp hsub (bAddr_val hp (n := 183328)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 1) hp hsub (bAddr_val hp (n := 183344)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 1) hp hsub (bAddr_val hp (n := 183360)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 1) hp hsub (bAddr_val hp (n := 183376)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 1) hp hsub (bAddr_val hp (n := 183392)
      (by decide) (by decide) (by decide)) (by decide) h1 h2
  · exact biasAt_of (c := 1) hp hsub (bAddr_val hp (n := 183408)
      (by decide) (by decide) (by decide)) (by decide) h1 h2

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
