-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Interval
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Proof.Softmax.Align
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Flow.Code.Part107
import Kernels.TmlFa4Fwd.Flow.Code.Part118
import Kernels.TmlFa4Fwd.Proof.Lib.StoreAt

@[expose] public section

/-! # Where the softmax warps' statistics stores write

The softmax warps store their statistics (`stat`, `fin`: `st.shared.b32 [statA + 368]` and
`[statA + 1392]`) at the stage's statistics address `statA = sb + 4 (128 stage + row)`
(`statA_val`), plus 368 (the sum) or 1392 (the maximum): `stat_at`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem iv_sbW (hp : Pre p L m) : Iv L.sharedBase L.sharedBase (Mma.sbW L) := by
  have := hp.shared.2.1
  exact iv_lit _ (by omega)

/-- The stage of a softmax lane: warps 4 to 7 are stage 1. -/
abbrev stN (L : Launch) (g : Nat) : Nat := if 3 < g % L.block / 32 then 1 else 0

set_option maxRecDepth 100000 in
theorem stat_words : ∀ i < 512, (shl (or32 (sel (scmpi .gt .s (BitVec.ofNat 64 (i / 32)) 3)
    (i32 128) (i32 0)) (andi (BitVec.ofNat 64 i) 127)) 2).toNat =
      4 * (128 * (if 3 < i / 32 then 1 else 0) + i % 128) := by
  decide +kernel

/-- **The stage's statistics address.** -/
theorem statA_val (hp : Pre p L m) : (statA L g).toNat =
    L.sharedBase + 4 * (128 * stN L g + g % L.block % 128) := by
  have hs := hp.shared.2.1
  have hi : g % L.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have h := stat_words _ hi
  rw [← tidW_eq hp] at h
  have hr : g % L.block % 128 < 128 := Nat.mod_lt _ (by decide)
  have hst : stN L g ≤ 1 := by unfold stN; split <;> omega
  have h3 := iv_add32 (iv_sbW hp) (y := shl (or32 (sel (stg L g)
    (i32 128) (i32 0)) (andi (tidW L g) 127)) 2) ⟨h.ge, h.le⟩ (by unfold stN at hst; omega)
  unfold Iv at h3
  simp only [statA, stN] at h3 ⊢
  omega

/-- **What a statistics store writes**: the sum word (`n = 0`) or the maximum word (`n = 1`) of
the lane's row and stage. -/
def StatAt (L : Launch) (g : Nat) (acc : Acc) : Prop :=
  acc.size = 4 ∧ ∃ n < 2, acc.loc = ⟨.shared, g / L.block,
    L.sharedBase + 368 + 1024 * n + 4 * (128 * stN L g + g % L.block % 128)⟩

/-- Which word a store site writes: the maximum (1) at the second final store, else the sum (0). -/
def statIx : Site → Nat
  | .fin 1 => 1
  | _ => 0

/-- **What a store of word `n` writes.** -/
def StatWord (L : Launch) (g n : Nat) (acc : Acc) : Prop :=
  acc.size = 4 ∧ acc.loc = ⟨.shared, g / L.block,
    L.sharedBase + 368 + 1024 * n + 4 * (128 * stN L g + g % L.block % 128)⟩

theorem StatWord.at {n : Nat} {acc : Acc} (h : StatWord L g n acc) (hn : n < 2) :
    StatAt L g acc := ⟨h.1, n, hn, h.2⟩

theorem statIx_lt (s : Site) : statIx s < 2 := by unfold statIx; split <;> decide

theorem statWord_of (hp : Pre p L m) {off : Int} {n : Nat} {acc : Acc}
    (ho : off = 368 ∧ n = 0 ∨ off = 1392 ∧ n = 1)
    (hl : acc.loc = ⟨.shared, g / L.block,
      (truncBits 32 (truncBits 32 (statA L g) + BitVec.ofInt 64 off)).toNat + 4 * 0⟩)
    (hz : acc.size = 4) : StatWord L g n acc := by
  have hsb := hp.shared
  have hv := statA_val (g := g) hp
  have hr : g % L.block % 128 < 128 := Nat.mod_lt _ (by decide)
  have hst : stN L g ≤ 1 := by unfold stN; split <;> omega
  rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · rw [eff_sharedI (by decide) (by omega)] at hl
    refine ⟨hz, hl.trans ?_⟩
    simp only [Loc.mk.injEq, true_and]
    omega

set_option maxHeartbeats 4000000 in
/-- **Which word a statistics store of the softmax warps writes.** -/
theorem stat_word (hp : Pre p L m) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (code p L g).AtD d t) (hi : (code p L g).inv d)
    (hc : kernel.code[(code p L g).pc d]? = some ins)
    (hf : Fires ((code p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : (∃ pl, d.site = .stat pl) ∨ ∃ k, d.site = .fin k) {acc : Acc} {bs : List Byte}
    (hk : e.kind = .wr acc bs) :
    StatWord L g (statIx d.site) acc := by
  have h' := h
  have hreg : ∀ r ∈ ctlLive (livePc d), t.regs r = some (valueOf p L g d r) :=
    fun r hr => holds_mem h'.2.2.2.2 (mem_factsFrom hr)
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  have hsub : t.sub = 0 := by
    have h0 : d.k = 0 := by
      rcases hi with hi | hi
      · exact hi.1
      · rcases hs with ⟨pl, hs⟩ | ⟨j, hs⟩ <;> rw [hs] at hi <;> exact hi.elim
    rw [h.2.1]
    exact congrArg Fin.val h0
  obtain ⟨site, v, k, ac⟩ := d
  rcases hs with ⟨pl, hs⟩ | ⟨j, hs⟩ <;> simp only at hs <;> subst hs
  · cases pl <;>
    · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      obtain ⟨h1, h2⟩ := stShared_wr rfl rfl rfl rfl rfl
        (hreg _ (by simp only [ctlLive, List.mem_filter]; exact ⟨by lit_mem, by decide⟩)) hf hk
      rw [hsub] at h1
      exact statWord_of hp (.inl ⟨rfl, rfl⟩) h1 h2
  · fin_cases j <;>
    · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      obtain ⟨h1, h2⟩ := stShared_wr rfl rfl rfl rfl rfl
        (hreg _ (by simp only [ctlLive, List.mem_filter]; exact ⟨by lit_mem, by decide⟩)) hf hk
      rw [hsub] at h1
      exact statWord_of hp (by first | exact .inl ⟨rfl, rfl⟩ | exact .inr ⟨rfl, rfl⟩) h1 h2

/-- **What a statistics store of the softmax warps writes.** -/
theorem stat_at (hp : Pre p L m) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (code p L g).AtD d t) (hi : (code p L g).inv d)
    (hc : kernel.code[(code p L g).pc d]? = some ins)
    (hf : Fires ((code p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : (∃ pl, d.site = .stat pl) ∨ ∃ k, d.site = .fin k) {acc : Acc} {bs : List Byte}
    (hk : e.kind = .wr acc bs) : StatAt L g acc :=
  (stat_word hp h hi hc hf hs hk).at (statIx_lt _)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
