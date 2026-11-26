-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
public import Kernels.TmlFa4Fwd.Proof.Correction.SafeSt
public import Lemmas.Flow.Arith32Interval
public import Lemmas.Flow.Arith32LineWord
public import Lemmas.Flow.StoreAt
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

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine

@[expose] public section

/-! # Where the correction warps' final shared stores write

A final store (`fst`, `st.shared.v4.b32`) writes at its base register plus an offset of `0`,
`16384`, `32768` or `49152` and its element's four bytes. The base register is the row's swizzled
staging address `a` (`sb + 3072` plus the row's offset for the first stage, `sb + 68608` plus it
for the second) moved by the lane's signed offsets `±16`, `±32`, `±64`, at most 112 in all; the
swizzle moves `a` by at most 112 too. So every final store writes at `sb + 2848` or above
(`fst_wr`), by the interval closure (`Lib/Interval.lean`) with the bounds stated as literals. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The shared base. -/
theorem iv_sb (hp : Pre p L m) : Iv L.sharedBase L.sharedBase (Mma.sbW L) := by
  have := hp.shared.2.1
  exact iv_lit _ (by omega)

/-- The row of a thread of the four warps: its index below 128. -/
abbrev rowN (L : Launch) (g : Nat) : Nat := g % L.block % 128

theorem tidW_eq (hp : Pre p L m) : tidW L g = BitVec.ofNat 64 (g % L.block) := by
  simp only [tidW]
  rw [Launch.oneDim_tidOf hp.cluster.2.2]
  have : g % L.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  apply BitVec.eq_of_toNat_eq
  simp [Dim3.get, truncBits, BitVec.toNat_ofNat]
  omega

set_option maxRecDepth 100000 in
theorem row_words : ∀ i < 512,
    (r32 (shl (shru (andi (BitVec.ofNat 64 i) 127) 5) 12) |||
      r32 (andi (shl (BitVec.ofNat 64 i) 7) 3968)).toNat = 128 * (i % 128) ∧
    scmpi .eq .b (andi (BitVec.ofNat 64 i) 1) 0 = decide (i / 2 ^ 0 % 2 = 0) ∧
    scmpi .eq .b (andi (BitVec.ofNat 64 i) 2) 0 = decide (i / 2 ^ 1 % 2 = 0) ∧
    scmpi .eq .b (andi (BitVec.ofNat 64 i) 4) 0 = decide (i / 2 ^ 2 % 2 = 0) := by
  decide +kernel

/-- **The first staging row**: the shared base plus the row's 128-byte line. -/
theorem stg0_val (hp : Pre p L m) : (stg0 L g).toNat = L.sharedBase + 128 * rowN L g := by
  have hs := hp.shared.2.1
  have hi : g % L.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hr : rowN L g < 128 := Nat.mod_lt _ (by decide)
  have h := (row_words _ hi).1
  rw [← tidW_eq hp] at h
  have h1 := iv_add32 (iv_sb hp) (y := r32 (shl (quarter L g) 12) |||
    r32 (andi (shl (tidW L g) 7) 3968)) (c := 128 * rowN L g) (d := 128 * rowN L g)
    (by unfold Iv; exact ⟨h.ge, h.le⟩) (by omega)
  unfold Iv at h1
  simp only [stg0]
  omega

/-- The line of a row in a staging buffer. -/
def lineAt (L : Launch) (g : Nat) (st : Fin 2) : Nat :=
  L.sharedBase + 3072 + 65536 * st.val + 128 * rowN L g

/-- **The swizzled staging address of each stage** is column 0 of the row's line. -/
theorem col_fa (hp : Pre p L m) (st : Fin 2) :
    Col (lineAt L g st) (g % L.block) 0
      (fStage st (xor32 (andi (shru (stg1 L g) 3) 112) (stg1 L g))
        (xor32 (andi (shru (addi (stg0 L g) 68608) 3) 112) (addi (stg0 L g) 68608))) := by
  have hs := hp.shared
  have h0 := stg0_val (g := g) hp
  have h0' : Iv (L.sharedBase + 128 * rowN L g) (L.sharedBase + 128 * rowN L g) (stg0 L g) := by
    unfold Iv; omega
  have hr : rowN L g < 128 := Nat.mod_lt _ (by decide)
  have key : ∀ (n : Nat) (x : BitVec 64), x.toNat = L.sharedBase + 128 * rowN L g + n →
      n % 1024 = 0 → n ≤ 68608 → Col (L.sharedBase + n + 128 * rowN L g) (g % L.block) 0
        (xor32 (andi (shru x 3) 112) x) := by
    intro n x hx hn hn'
    have h := col_swz (x := x) (n := (L.sharedBase + n) / 128 + rowN L g) (i := g % L.block)
      (by omega) (by omega) (by simp only [rowN]; omega)
    rwa [show 128 * ((L.sharedBase + n) / 128 + rowN L g) =
      L.sharedBase + n + 128 * rowN L g by omega] at h
  fin_cases st
  · have h1 := iv_addi h0' 3072 (by omega)
    unfold Iv at h1
    have := key 3072 (stg1 L g) (by simp only [stg1, Nat.cast_ofNat] at h1 ⊢; omega) (by decide)
      (by decide)
    simpa only [lineAt, fStage] using this
  · have h1 := iv_addi h0' 68608 (by omega)
    unfold Iv at h1
    have := key 68608 (addi (stg0 L g) 68608) (by simp only [Nat.cast_ofNat] at h1 ⊢; omega)
      (by decide) (by decide)
    simpa only [lineAt, fStage] using this

/-- **The signed moves of a lane's column.** -/
theorem col_d1 (hp : Pre p L m) {st : Fin 2} {k : Nat} {x : BitVec 64}
    (h : Col (lineAt L g st) (g % L.block) k x) (hk : k < 8) (hb : k / 2 ^ 0 % 2 = 0) :
    Col (lineAt L g st) (g % L.block) (k ^^^ 2 ^ 0)
      (add32 x (sel (scmpi .eq .b (andi (tidW L g) 1) 0) (i32 16) (i32 (-16)))) := by
  have hs := hp.shared
  have hi : g % L.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hr : rowN L g < 128 := Nat.mod_lt _ (by decide)
  have := st.isLt
  refine col_move (s := 0) h hk (by decide) hb (by unfold lineAt; omega) ?_
  rw [tidW_eq hp]
  exact (row_words _ hi).2.1

theorem col_d2 (hp : Pre p L m) {st : Fin 2} {k : Nat} {x : BitVec 64}
    (h : Col (lineAt L g st) (g % L.block) k x) (hk : k < 8) (hb : k / 2 ^ 1 % 2 = 0) :
    Col (lineAt L g st) (g % L.block) (k ^^^ 2 ^ 1)
      (add32 x (sel (scmpi .eq .b (andi (tidW L g) 2) 0) (i32 32) (i32 (-32)))) := by
  have hs := hp.shared
  have hi : g % L.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hr : rowN L g < 128 := Nat.mod_lt _ (by decide)
  have := st.isLt
  refine col_move (s := 1) h hk (by decide) hb (by unfold lineAt; omega) ?_
  rw [tidW_eq hp]
  obtain ⟨-, -, h, -⟩ := row_words _ hi
  exact h

theorem col_d4 (hp : Pre p L m) {st : Fin 2} {k : Nat} {x : BitVec 64}
    (h : Col (lineAt L g st) (g % L.block) k x) (hk : k < 8) (hb : k / 2 ^ 2 % 2 = 0) :
    Col (lineAt L g st) (g % L.block) (k ^^^ 2 ^ 2)
      (add32 x (sel (scmpi .eq .b (andi (tidW L g) 4) 0) (i32 64) (i32 (-64)))) := by
  have hs := hp.shared
  have hi : g % L.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hr : rowN L g < 128 := Nat.mod_lt _ (by decide)
  have := st.isLt
  refine col_move (s := 2) h hk (by decide) hb (by unfold lineAt; omega) ?_
  rw [tidW_eq hp]
  obtain ⟨-, -, -, h⟩ := row_words _ hi
  exact h

/-- **What a final store writes**: 4 bytes of the line of its lane's row, in one of the four
16384-byte quarters of its stage's staging buffer. -/
def FstAt (L : Launch) (g : Nat) (st : Fin 2) (acc : Acc) : Prop :=
  acc.size = 4 ∧ ∃ q < 4, ∃ w, w + 4 ≤ 128 ∧
    acc.loc = ⟨.shared, g / L.block,
      L.sharedBase + 3072 + 65536 * st.val + 16384 * q + 128 * rowN L g + w⟩

/-- A final store's bytes from the column of its base register. -/
theorem fstAt_of_col (hp : Pre p L m) {st : Fin 2} {k s : Nat} {x : BitVec 64} {off : Int}
    (h : Col (lineAt L g st) (g % L.block) k x) (hk : k < 8) (hs : s < 4) {acc : Acc}
    (ho : ∃ q < 4, off = ((16384 * q : Nat) : Int))
    (hl : acc.loc = ⟨.shared, g / L.block,
      (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat + 4 * s⟩)
    (hz : acc.size = 4) : FstAt L g st acc := by
  have hsb := hp.shared
  obtain ⟨q, hq, rfl⟩ := ho
  have hb := h.bounds hk
  have hr : rowN L g < 128 := Nat.mod_lt _ (by decide)
  have := st.isLt
  unfold lineAt at hb
  rw [eff_shared (by omega)] at hl
  refine ⟨hz, q, hq, x.toNat - lineAt L g st + 4 * s, by unfold lineAt; omega, ?_⟩
  rw [hl]
  simp only [Loc.mk.injEq, true_and]
  unfold lineAt
  omega

/-- The base word of a final store: column `2 (j mod 4) + hh`. -/
def colW (L : Launch) (g : Nat) (st : Fin 2) (k : Fin 8) : BitVec 64 :=
  let a := fStage st (xor32 (andi (shru (stg1 L g) 3) 112) (stg1 L g))
    (xor32 (andi (shru (addi (stg0 L g) 68608) 3) 112) (addi (stg0 L g) 68608))
  let d1 := sel (scmpi .eq .b (andi (tidW L g) 1) 0) (i32 16) (i32 (-16))
  let d2 := sel (scmpi .eq .b (andi (tidW L g) 2) 0) (i32 32) (i32 (-32))
  let d4 := sel (scmpi .eq .b (andi (tidW L g) 4) 0) (i32 64) (i32 (-64))
  match k with
  | 0 => a
  | 1 => add32 a d1
  | 2 => add32 a d2
  | 3 => add32 (add32 a d2) d1
  | 4 => add32 a d4
  | 5 => add32 (add32 a d4) d1
  | 6 => add32 (add32 a d4) d2
  | 7 => add32 (add32 (add32 a d4) d2) d1

theorem colW_col (hp : Pre p L m) (st : Fin 2) (k : Fin 8) :
    Col (lineAt L g st) (g % L.block) k.val (colW L g st k) := by
  have h0 := col_fa (g := g) hp st
  have h2 := col_d2 hp h0 (by decide) (by decide)
  have h4 := col_d4 hp h0 (by decide) (by decide)
  have h6 := col_d2 hp h4 (by decide) (by decide)
  fin_cases k
  · exact h0
  · exact col_d1 hp h0 (by decide) (by decide)
  · exact h2
  · exact col_d1 hp h2 (by decide) (by decide)
  · exact h4
  · exact col_d1 hp h4 (by decide) (by decide)
  · exact h6
  · exact col_d1 hp h6 (by decide) (by decide)

set_option hygiene false in
/-- The final store at stage `st`, chunk `j`, half `hh` (one theorem per site, so that the site's
indices are literals). -/
macro "fst_site " n:ident st:num j:num hh:num k:num q:num : command => `(
set_option maxHeartbeats 4000000 in
theorem $n (hp : Pre p L m) {d : Control.D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (Control.code p L g).AtD d t)
    (hc : kernel.code[(Control.code p L g).pc d]? = some ins)
    (hf : Fires ((Control.code p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : d.site = .fst $st $j $hh) {acc : Acc} {bs : List Byte}
    (hk : e.kind = .wr acc bs) : FstAt L g $st acc := by
  have hreg : ∀ r ∈ Control.live d, t.regs r = some (Control.valueOf p L g d r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub : t.sub < 4 := by rw [h.2.1]; exact d.k.isLt
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨site, v, k⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  obtain ⟨h1, h2⟩ := stShared_wr rfl rfl rfl rfl rfl (hreg _ (by lit_mem)) hf hk
  exact fstAt_of_col hp (colW_col hp $st $k) (Fin.is_lt _) hsub ⟨$q, by decide, rfl⟩ h1 h2)

fst_site fst_0_0_0 0 0 0 0 0
fst_site fst_0_0_1 0 0 1 1 0
fst_site fst_0_1_0 0 1 0 2 0
fst_site fst_0_1_1 0 1 1 3 0
fst_site fst_0_2_0 0 2 0 4 0
fst_site fst_0_2_1 0 2 1 5 0
fst_site fst_0_3_0 0 3 0 6 0
fst_site fst_0_3_1 0 3 1 7 0
fst_site fst_0_4_0 0 4 0 0 1
fst_site fst_0_4_1 0 4 1 1 1
fst_site fst_0_5_0 0 5 0 2 1
fst_site fst_0_5_1 0 5 1 3 1
fst_site fst_0_6_0 0 6 0 4 1
fst_site fst_0_6_1 0 6 1 5 1
fst_site fst_0_7_0 0 7 0 6 1
fst_site fst_0_7_1 0 7 1 7 1
fst_site fst_0_8_0 0 8 0 0 2
fst_site fst_0_8_1 0 8 1 1 2
fst_site fst_0_9_0 0 9 0 2 2
fst_site fst_0_9_1 0 9 1 3 2
fst_site fst_0_10_0 0 10 0 4 2
fst_site fst_0_10_1 0 10 1 5 2
fst_site fst_0_11_0 0 11 0 6 2
fst_site fst_0_11_1 0 11 1 7 2
fst_site fst_0_12_0 0 12 0 0 3
fst_site fst_0_12_1 0 12 1 1 3
fst_site fst_0_13_0 0 13 0 2 3
fst_site fst_0_13_1 0 13 1 3 3
fst_site fst_0_14_0 0 14 0 4 3
fst_site fst_0_14_1 0 14 1 5 3
fst_site fst_0_15_0 0 15 0 6 3
fst_site fst_0_15_1 0 15 1 7 3
fst_site fst_1_0_0 1 0 0 0 0
fst_site fst_1_0_1 1 0 1 1 0
fst_site fst_1_1_0 1 1 0 2 0
fst_site fst_1_1_1 1 1 1 3 0
fst_site fst_1_2_0 1 2 0 4 0
fst_site fst_1_2_1 1 2 1 5 0
fst_site fst_1_3_0 1 3 0 6 0
fst_site fst_1_3_1 1 3 1 7 0
fst_site fst_1_4_0 1 4 0 0 1
fst_site fst_1_4_1 1 4 1 1 1
fst_site fst_1_5_0 1 5 0 2 1
fst_site fst_1_5_1 1 5 1 3 1
fst_site fst_1_6_0 1 6 0 4 1
fst_site fst_1_6_1 1 6 1 5 1
fst_site fst_1_7_0 1 7 0 6 1
fst_site fst_1_7_1 1 7 1 7 1
fst_site fst_1_8_0 1 8 0 0 2
fst_site fst_1_8_1 1 8 1 1 2
fst_site fst_1_9_0 1 9 0 2 2
fst_site fst_1_9_1 1 9 1 3 2
fst_site fst_1_10_0 1 10 0 4 2
fst_site fst_1_10_1 1 10 1 5 2
fst_site fst_1_11_0 1 11 0 6 2
fst_site fst_1_11_1 1 11 1 7 2
fst_site fst_1_12_0 1 12 0 0 3
fst_site fst_1_12_1 1 12 1 1 3
fst_site fst_1_13_0 1 13 0 2 3
fst_site fst_1_13_1 1 13 1 3 3
fst_site fst_1_14_0 1 14 0 4 3
fst_site fst_1_14_1 1 14 1 5 3
fst_site fst_1_15_0 1 15 0 6 3
fst_site fst_1_15_1 1 15 1 7 3

/-- **What a final shared store of the correction warps writes.** -/
theorem fst_at (hp : Pre p L m) {d : Control.D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (Control.code p L g).AtD d t)
    (hc : kernel.code[(Control.code p L g).pc d]? = some ins)
    (hf : Fires ((Control.code p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    {st : Fin 2} {j : Fin 16} {hh : Fin 2} (hs : d.site = .fst st j hh) {acc : Acc} {bs : List Byte}
    (hk : e.kind = .wr acc bs) : FstAt L g st acc := by
  fin_cases st <;> fin_cases j <;> fin_cases hh
  · exact fst_0_0_0 hp h hc hf hs hk
  · exact fst_0_0_1 hp h hc hf hs hk
  · exact fst_0_1_0 hp h hc hf hs hk
  · exact fst_0_1_1 hp h hc hf hs hk
  · exact fst_0_2_0 hp h hc hf hs hk
  · exact fst_0_2_1 hp h hc hf hs hk
  · exact fst_0_3_0 hp h hc hf hs hk
  · exact fst_0_3_1 hp h hc hf hs hk
  · exact fst_0_4_0 hp h hc hf hs hk
  · exact fst_0_4_1 hp h hc hf hs hk
  · exact fst_0_5_0 hp h hc hf hs hk
  · exact fst_0_5_1 hp h hc hf hs hk
  · exact fst_0_6_0 hp h hc hf hs hk
  · exact fst_0_6_1 hp h hc hf hs hk
  · exact fst_0_7_0 hp h hc hf hs hk
  · exact fst_0_7_1 hp h hc hf hs hk
  · exact fst_0_8_0 hp h hc hf hs hk
  · exact fst_0_8_1 hp h hc hf hs hk
  · exact fst_0_9_0 hp h hc hf hs hk
  · exact fst_0_9_1 hp h hc hf hs hk
  · exact fst_0_10_0 hp h hc hf hs hk
  · exact fst_0_10_1 hp h hc hf hs hk
  · exact fst_0_11_0 hp h hc hf hs hk
  · exact fst_0_11_1 hp h hc hf hs hk
  · exact fst_0_12_0 hp h hc hf hs hk
  · exact fst_0_12_1 hp h hc hf hs hk
  · exact fst_0_13_0 hp h hc hf hs hk
  · exact fst_0_13_1 hp h hc hf hs hk
  · exact fst_0_14_0 hp h hc hf hs hk
  · exact fst_0_14_1 hp h hc hf hs hk
  · exact fst_0_15_0 hp h hc hf hs hk
  · exact fst_0_15_1 hp h hc hf hs hk
  · exact fst_1_0_0 hp h hc hf hs hk
  · exact fst_1_0_1 hp h hc hf hs hk
  · exact fst_1_1_0 hp h hc hf hs hk
  · exact fst_1_1_1 hp h hc hf hs hk
  · exact fst_1_2_0 hp h hc hf hs hk
  · exact fst_1_2_1 hp h hc hf hs hk
  · exact fst_1_3_0 hp h hc hf hs hk
  · exact fst_1_3_1 hp h hc hf hs hk
  · exact fst_1_4_0 hp h hc hf hs hk
  · exact fst_1_4_1 hp h hc hf hs hk
  · exact fst_1_5_0 hp h hc hf hs hk
  · exact fst_1_5_1 hp h hc hf hs hk
  · exact fst_1_6_0 hp h hc hf hs hk
  · exact fst_1_6_1 hp h hc hf hs hk
  · exact fst_1_7_0 hp h hc hf hs hk
  · exact fst_1_7_1 hp h hc hf hs hk
  · exact fst_1_8_0 hp h hc hf hs hk
  · exact fst_1_8_1 hp h hc hf hs hk
  · exact fst_1_9_0 hp h hc hf hs hk
  · exact fst_1_9_1 hp h hc hf hs hk
  · exact fst_1_10_0 hp h hc hf hs hk
  · exact fst_1_10_1 hp h hc hf hs hk
  · exact fst_1_11_0 hp h hc hf hs hk
  · exact fst_1_11_1 hp h hc hf hs hk
  · exact fst_1_12_0 hp h hc hf hs hk
  · exact fst_1_12_1 hp h hc hf hs hk
  · exact fst_1_13_0 hp h hc hf hs hk
  · exact fst_1_13_1 hp h hc hf hs hk
  · exact fst_1_14_0 hp h hc hf hs hk
  · exact fst_1_14_1 hp h hc hf hs hk
  · exact fst_1_15_0 hp h hc hf hs hk
  · exact fst_1_15_1 hp h hc hf hs hk

set_option maxHeartbeats 4000000 in
/-- **An LSE store of the correction warps writes in the global space.** -/
theorem lse_wr {d : Control.D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (Control.code p L g).AtD d t)
    (hc : kernel.code[(Control.code p L g).pc d]? = some ins)
    (hf : Fires ((Control.code p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : ∃ hh, d.site = .lse hh) {acc : Acc} {bs : List Byte}
    (hk : e.kind = .wr acc bs) : acc.loc.space = .global := by
  have hreg : ∀ r ∈ Control.live d, t.regs r = some (Control.valueOf p L g d r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨site, v, k⟩ := d
  obtain ⟨hh, rfl⟩ := hs
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact stGlobal_wr rfl rfl rfl rfl rfl (hreg _ (by lit_mem)) hf hk

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
