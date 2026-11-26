-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Global
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.GlobalCls
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Reads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Grid
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.LseWord
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MaskRead
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Result.ScoreRead
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.LseOnce
public import Lemmas.Kernel.Goals
public import Lemmas.Kernel.Memory
public import Lemmas.Tcgen05.MemFloat
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem

@[expose] public section

/-! # The stored log-sum-exp values

The second and the third conjunct of the Spec's `Post`: a row with a nonzero sum stores `lse`
(`Res.LseValues`), an empty row stores `+inf` (`Res.LseEmpty`). `Res.lse` proves them from the
valid words of warpgroup 0's loop (`Res.W0TraceIn`, a field of the Tensor Memory class's open
part): the masks (`Res.Lse.mask`) and the scores (`score_read`) they read. -/

/-! # The final LSE word of a row

The row `(e, q, h)`'s lane stores its word at pc 1178 (`w0_lse_row`: `+inf` for a zero row sum,
the Spec's `lse` otherwise); that store's four bytes are the final bytes of the word
(`lse_final`). So the memory after the execution holds `+inf` bytes at an empty row's word and the
number `lse` at the others. -/

/-! # The final byte of an LSE word is its store's byte

A write of a thread that covers a global byte is a lane's LSE store (pc 1178, `global_access`).
Every other write covering the byte is that store: an output tensor store's byte is apart from the
LSE output (`Pre`), and another lane's LSE store is at another word (the word is
`64 ctaOf + tid`, so the lane is the same) or is the same event (`w0_lse_once`). So the memory
after the execution holds the byte the store writes (`IsFinal.unique`). -/

/-! # The lane of a row and the word its LSE store covers

The row `(e, q, h)` is lane `g = (e s_q + q) 384 + h` of warpgroup 0 (`lse_lane`: the CTA
`e s_q + q` has `%ctaid` `(q, e)`, the thread `%tid.x = h`). A store of the lane at pc 1178 covers
exactly the four bytes of the row's word `lseLoc` (`lse_store_loc`): the memory row of warpgroup 0
at pc 1178 is the LSE write at the lane's word. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The lane of a row**: a lane of warpgroup 0 below thread 64 in the CTA of the batch `e` and
query `q`, with thread index `h`. -/
theorem lse_lane (hp : Pre P L m) {e q h : Nat} (he : e < P.b) (hq : q < P.s_q) (hh : h < 64) :
    ∃ g, g < L.threads ∧ warp L g < 4 ∧ tidOf L g < 64 ∧ w0Batch L g = e ∧ w0Query L g = q ∧
      w0Head L g = h := by
  have hb : L.block = 384 := by have := hp.block; omega
  have hc : e * P.s_q + q < P.s_q * P.b := by
    have := Nat.mul_le_mul_right P.s_q (Nat.succ_le_of_lt he)
    rw [Nat.succ_mul] at this
    rw [Nat.mul_comm P.s_q P.b]
    omega
  refine ⟨(e * P.s_q + q) * 384 + h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hth : L.threads = L.grid * 384 := by simp only [Launch.threads, hb]
    rw [hth, hp.grid]
    nlinarith
  · simp only [warp, tidOf_x_eq hp]
    omega
  · show (L.tidOf _).x < 64
    rw [tidOf_x_eq hp]
    omega
  · unfold w0Batch
    have hd : ((e * P.s_q + q) * 384 + h) / L.block = e * P.s_q + q := by
      rw [hb]; omega
    rw [hd, ctaidOf_eq hp]
    have h1 : (e * P.s_q + q) / P.s_q = e := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by have := hp.sqPos; omega),
        Nat.div_eq_of_lt hq, Nat.zero_add]
    simp only [h1]
    have := hp.bLt
    rw [Nat.mod_eq_of_lt he]
    exact Nat.mod_eq_of_lt (by omega)
  · unfold w0Query
    have hd : ((e * P.s_q + q) * 384 + h) / L.block = e * P.s_q + q := by
      rw [hb]; omega
    rw [hd, ctaidOf_eq hp]
    simp only
    have h1 : (e * P.s_q + q) % P.s_q = q := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]
    rw [h1]
    have := hp.sqLt
    exact Nat.mod_eq_of_lt (by omega)
  · unfold w0Head
    rw [tidOf_x_eq hp]
    omega

/-- **The LSE store covers its row's word**: the write at pc 1178 of a lane below thread 64 is at
the four bytes `lseLoc` of the lane's row. -/
theorem lse_store_loc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {a : Acc} {bs : List Byte}
    (hget : X.get (g, k) = some ⟨1178, .wr a bs⟩) (hw : warp L g < 4) (hlow : tidOf L g < 64) :
    a.loc = lseLoc P (w0Batch L g) (w0Query L g) (w0Head L g) ∧ a.size = 4 := by
  have hg := Frame.lt_of_get hX hget
  have hat : Wg0At L g 1178 := ⟨hw, by omega, by omega⟩
  have hm : MemRow.MemEvent (⟨1178, .wr a bs⟩ : Event) := .inr (.inr (.inl ⟨a, bs, rfl⟩))
  have hl : MemRow.Wg0Lse P L g 1178 a := by
    rcases memRow_wg0 hp hX hFw hg hget hat hm with ⟨a', bs', h⟩ | ⟨a', bs', h, -⟩ |
      ⟨a', bs', h, hw'⟩ | ⟨a', bs', h, hl | hs⟩
    · cases h
    · cases h
    · exfalso
      cases h
      rcases hw' with ⟨k', hk', hpc, -⟩ | ⟨hpc, -⟩ | ⟨k', hk', el, hel, hpc, -⟩ <;>
        simp only at hpc <;> omega
    · cases h; exact hl
    · exfalso
      cases h
      obtain ⟨c, hc, k', hk', el, hel, hpc, -⟩ := hs
      interval_cases c <;> simp at hpc <;> omega
  obtain ⟨-, hloc, hsz⟩ := hl
  refine ⟨?_, hsz⟩
  have hrow := ctaOf_row hp hg
  have hb : L.block = 384 := by have := hp.block; omega
  have h128 : (L.tidOf g).x < 64 := hlow
  have hcta : ctaOf L g < P.s_q * P.b := by
    rw [← hp.grid]
    exact (Nat.div_lt_iff_lt_mul (by rw [hb]; decide)).mpr hg
  have hN : lseBytes P = 256 * (P.s_q * P.b) := by unfold lseBytes; ring
  obtain ⟨-, -, hr⟩ := hp.tensorRange
  rw [hloc]
  have hy : ctaidY L g * P.s_q + ctaidX L g = ctaOf L g := hrow.symm
  unfold lseLoc w0Batch w0Query w0Head
  change (⟨.global, 0, (P.lseBase + 4 * (((L.ctaidOf (g / L.block)).y % 2 ^ 32 * P.s_q +
    (L.ctaidOf (g / L.block)).x % 2 ^ 32) * 64 + (L.tidOf g).x % 128)) % 2 ^ 64⟩ : Loc) = _
  have hy' : (L.ctaidOf (g / L.block)).y % 2 ^ 32 * P.s_q +
      (L.ctaidOf (g / L.block)).x % 2 ^ 32 = ctaOf L g := hrow.symm
  rw [hy', Nat.mod_eq_of_lt (a := (L.tidOf g).x) (by omega : (L.tidOf g).x < 128)]
  rw [Nat.mod_eq_of_lt (a := (L.tidOf g).x) (by omega : (L.tidOf g).x < 64)]
  unfold lseBytes at hr hN
  simp only [Loc.mk.injEq, true_and]
  exact Nat.mod_eq_of_lt (by omega)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **The final byte of an LSE word**: a thread's write that covers a global byte `l` is the only
write of it, so the memory after the execution holds its byte. -/
theorem lse_final (hp : Pre P L mem0) {X : Execution} {mf : FinalMem}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X)
    (hF : IsFinal L mem0 X mf) {g k : Nat} {a : Acc} {bs : List Byte} {l : Loc}
    (hw : X.MemWrites (.thread (g, k)) a bs) (hc : a.Covers l) (hl : l.space = .global) :
    mf l = some (wbyte a bs l) := by
  have hns : l.space ≠ .shared := by rw [hl]; exact nofun
  have hI : X.Access (g, k) a true := hw.intent
  have hgl : a.loc.space = .global := hc.1.symm.trans hl
  obtain ⟨-, pc, bs1, hget, hat, hpc1, -, -⟩ := global_access hp hX hFw hI hgl
  subst hpc1
  refine hF.unique hw hc fun w' a' bs' hw' hc' => ?_
  have hG := global_at hp hX hFw hnu hw.intent hc hns
  have hG' := global_at hp hX hFw hnu hw'.intent hc' hns
  cases hG with
  | lse hget1 htid1 hb1 hlo1 hhi1 =>
    cases hG' with
    | lse hget2 htid2 hb2 hlo2 hhi2 =>
      rename_i g2 k2 pc2 a2 bs2
      have hI2 : X.Access (g2, k2) a' true := hw'.intent
      have hgl2 : a'.loc.space = .global := hc'.1.symm.trans hl
      obtain ⟨-, pc3, bs3, hget3, hat3, hpc3, -, -⟩ := global_access hp hX hFw hI2 hgl2
      have hsame : ctaOf L g * 64 + tidOf L g = ctaOf L g2 * 64 + tidOf L g2 := by omega
      have hx1 := tidOf_x_eq hp g
      have hx2 := tidOf_x_eq hp g2
      have hb := hp.block
      have hgg : g = g2 := by
        simp only [ctaOf, tidOf, hx1, hx2, hb] at hsame htid1 htid2
        have e1 := Nat.div_add_mod g 384
        have e2 := Nat.div_add_mod g2 384
        omega
      subst hgg
      have hkk := w0_lse_once hp hX hFw hnu hat.1 hget
        (by rw [hpc3] at hget3; exact hget3)
      rw [hkk]
    | store _ _ _ _ _ _ _ _ hb =>
      obtain ⟨-, -, h1, h2⟩ := hb
      obtain ⟨-, -, h3, h4⟩ := (‹LseByte P l›)
      rcases hp.outApartLse with h | h <;> omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0}

/-- **The final bytes of a row's LSE word** (valid rows, complete, no undefined behaviour). -/
theorem lse_row_final (hp : Pre P L m) {X : Execution} {mf : FinalMem}
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) (hnu : ¬ HasUb X)
    (hR : BarRows P L X) (hC : Complete L X) (hF : IsFinal L m X mf) (hV : W0Rows P L X)
    (hS : ScoreRead P L X hV) (hM : MaskRead P L X hV) {e q h : Nat} (he : e < P.b)
    (hq : q < P.s_q) (hh : h < 64) :
    (rowSum P e q h = 0 → ∀ k < 4, mf ((lseLoc P e q h).at k) = some (some (infByte k))) ∧
      (rowSum P e q h ≠ 0 → memFloat .f32 mf (lseLoc P e q h) = .ok (lse P e q h)) := by
  obtain ⟨g, hg, hw, hlow, rfl, rfl, rfl⟩ := lse_lane hp he hq hh
  obtain ⟨k, a, bs, hget, hcase⟩ := w0_lse_row hp hX hFw hnu hR hC hV hS hM hw hg hlow
  obtain ⟨hloc, hsz⟩ := lse_store_loc hp hX hFw hget hw hlow
  have hMW : X.MemWrites (.thread (g, k)) a bs := .inl ⟨1178, hget⟩
  have hbyte : ∀ kk < 4, mf ((lseLoc P (w0Batch L g) (w0Query L g) (w0Head L g)).at kk) =
      some (bs[kk]?) := by
    intro kk hkk
    have hc : a.Covers (a.loc.at kk) := Acc.covers_at (by omega)
    have := lse_final hp hX hFw hnu hF hMW hc (by rw [hloc]; rfl)
    rw [hloc] at this
    rw [this, ← hloc]
    simp [wbyte, Loc.at]
  constructor
  · intro h0 kk hkk
    rcases hcase with ⟨-, hbs⟩ | ⟨h1, -⟩
    · rw [hbyte kk hkk, hbs]
      have : (FVal.inf false).toValue .f32 = Value.bits 32 (BitVec.ofNat 64 2139095040) := by
        decide
      simp only [infByte, this, Value.toBytes]
      interval_cases kk <;> simp [Value.bytes]
    · exact absurd h0 h1
  · intro h0
    rcases hcase with ⟨h1, -⟩ | ⟨-, hbs⟩
    · exact absurd h1 h0
    · refine memFloat_float fun kk hkk => ?_
      have hkk' : kk < 4 := hkk
      rw [hbyte kk hkk', hbs]
      have hb : (Value.float .f32 (lse P (w0Batch L g) (w0Query L g) (w0Head L g))).bytes = 4 :=
        rfl
      simp only [Value.toBytes, hb]
      interval_cases kk <;> simp [Value.byteAt]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- The second conjunct of `Post`: a non-empty row's LSE is `lse`. -/
def Res.LseValues (P : Params) (mf : FinalMem) : Prop :=
  ∀ e < P.b, ∀ q < P.s_q, ∀ h < 64, rowSum P e q h ≠ 0 →
    memFloat .f32 mf (lseLoc P e q h) = .ok (lse P e q h)

/-- The third conjunct of `Post`: an empty row's LSE is `+inf`. -/
def Res.LseEmpty (P : Params) (mf : FinalMem) : Prop :=
  ∀ e < P.b, ∀ q < P.s_q, ∀ h < 64, rowSum P e q h = 0 →
    ∀ k < 4, mf ((lseLoc P e q h).at k) = some (some (infByte k))

/-- The valid words of warpgroup 0's loop, as `Safe.W0TraceValid.w0Trace` states them
(in an execution without undefined behaviour). -/
abbrev Res.W0TraceIn (P : Params) (L : Launch) (mem0 : Mem0) : Prop :=
  ∀ X, Consistent L kernel Assumptions.all mem0 X → Follow P L X → ¬ HasUb X →
    ∀ g, MbarRow.warp L g < 4 → W0Trace P X g

/-- **The masks the lanes of warpgroup 0 read**, from their valid words. -/
theorem Res.Lse.mask (hp : Pre P L mem0) (hT : Res.W0TraceIn P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    ∃ hV : W0Rows P L X, MaskRead P L X hV := by
  have hV : W0Rows P L X := fun g _ ht => hT X hX hFw hnu g (by simp only [MbarRow.warp]; omega)
  have hIn := Inputs.of_pre hp
  exact ⟨hV, mask_read hp hX hFw (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw)
    (hIn.bar0 hp X hX hFw) (hIn.coord hp X hX hFw) hnu hV⟩

/-- **The LSE values of a complete, followed execution.** -/
theorem Res.lse (hp : Pre P L mem0) (hRn : Safe.W0TraceValid P L mem0) {X : Execution}
    {mf : FinalMem} (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    (hnu : ¬ HasUb X) (hC : Complete L X) (hF : IsFinal L mem0 X mf) :
    Res.LseValues P mf ∧ Res.LseEmpty P mf := by
  obtain ⟨hV, hM⟩ := Res.Lse.mask hp hRn.w0Trace hX hFw hnu
  have hS : ScoreRead P L X hV := score_read hp (Inputs.of_pre hp) hRn hX hFw hnu hV
  have hB := Inputs.bar (Inputs.of_pre hp) hp X hX hFw
  exact ⟨fun e he q hq h hh hne =>
      (lse_row_final hp hX hFw hnu hB hC hF hV hS hM he hq hh).2 hne,
    fun e he q hq h hh h0 =>
      (lse_row_final hp hX hFw hnu hB hC hF hV hS hM he hq hh).1 h0⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
