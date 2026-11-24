-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Page
public import Kernels.TmlFa4Fwd.Proof.Loader.Move
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.Epilogue.Assign
import Kernels.TmlFa4Fwd.Proof.LdWarp.Mem
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.Local
import Lemmas.Flow.WordBound

@[expose] public section

/-! # The loader's page, row and address words in numbers

The page-table word of a row is a page of the cache (`PageW`), the row word is below 16 (`RowV`),
the head bases of the setup are those of a K/V head (`HeadOk`), and the address a pointer round
stores is a row's of the K or V cache (`RowA`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A page word. -/
def PageW (p : Params) (x : BitVec 64) : Prop := x.toNat < p.pages ∧ x.toNat < 2 ^ 31

/-- A row word. -/
def RowV (x : BitVec 64) : Prop := x.toNat < 16

/-- **The address of a K/V row.** -/
def RowA (p : Params) (y : BitVec 64) : Prop :=
  ∃ lay, (lay = p.kLayout ∨ lay = p.vLayout) ∧ ∃ page < p.pages, ∃ h < p.kvHeads, ∃ r < 16,
    y.toNat = lay.base + 2 * (page * lay.pageStride + h * lay.headStride + r * lay.rowStride)

/-- The head bases of the setup words are a head's. -/
def HeadOk (p : Params) (v : V) : Prop :=
  ∃ h < p.kvHeads,
    v.su.rd12.toNat = p.kLayout.base + 2 * (h * p.kLayout.headStride) ∧
    v.su.rd13.toNat = p.vLayout.base + 2 * (h * p.vLayout.headStride)

/-- The bytes of a row end inside the address space. -/
theorem row_room (hp : Pre p L m) {lay : CacheLayout} (hl : lay = p.kLayout ∨ lay = p.vLayout)
    {page h r : Nat} (hpg : page < p.pages) (hh : h < p.kvHeads) (hr : r < 16) :
    lay.base + 2 * (page * lay.pageStride + h * lay.headStride + r * lay.rowStride) + 256 ≤
      2 ^ 64 := by
  have hR : lay.base + 2 * ((p.pages - 1) * lay.pageStride + (p.kvHeads - 1) * lay.headStride +
      15 * lay.rowStride + 128) ≤ 2 ^ 64 := by
    have := hp.ranges (lay.region p.pages p.kvHeads) (by
      rcases hl with rfl | rfl <;> simp [Params.inputRegions])
    exact this
  have h1 : page * lay.pageStride ≤ (p.pages - 1) * lay.pageStride :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : h * lay.headStride ≤ (p.kvHeads - 1) * lay.headStride :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : r * lay.rowStride ≤ 15 * lay.rowStride := Nat.mul_le_mul_right _ (by omega)
  omega

theorem toNat_sx32 {x : BitVec 64} (h : x.toNat < 2 ^ 31) : (sx32 x).toNat = x.toNat := by
  have : toSigned 32 x = (x.toNat : Int) := by
    simp only [toSigned]
    rw [Nat.mod_eq_of_lt (by omega)]
    simp only [show x.toNat < 2 ^ (32 - 1) by omega, ↓reduceIte]
  simp only [sx32, this, toNat_tb64, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  omega

/-- A base plus twice an offset, when it fits. -/
theorem add_shl1 {b x : BitVec 64} {B o : Nat} (hb : b.toNat = B) (hx : x.toNat = o % 2 ^ 64)
    (hfit : B + 2 * o < 2 ^ 64) : (add64 b (shl64 x 1)).toNat = B + 2 * o := by
  have h1 : (i32 1).toNat = 1 := by decide
  simp only [add64, shl64, h1, show ¬ (1 ≥ 64) by decide, ↓reduceIte, r64, toNat_tb64,
    BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hb, hx]
  omega

theorem toNat_mul64 (s : Nat) (y : BitVec 64) :
    (mul64 (BitVec.ofNat 64 s) y).toNat = s * y.toNat % 2 ^ 64 := by
  simp only [mul64, r64, toNat_tb64, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem toNat_mad64 (s : Nat) (y z : BitVec 64) :
    (mad64 (BitVec.ofNat 64 s) y z).toNat = (s * y.toNat + z.toNat) % 2 ^ 64 := by
  have h1 := toNat_mul64 s y
  simp only [mul64, r64, truncBits64] at h1
  simp only [mad64, r64, truncBits64, BitVec.toNat_add, h1]
  omega

/-- **The address a pointer round stores is a row's.** -/
theorem pt_row (hp : Pre p L m) {w : Nat} {per : Per} {b : Bool} {it : Fin 2} {v : V}
    {kk : Fin 2} (hH : HeadOk p v) (hpg : PageW p v.lp) (hr : RowV v.lr) :
    RowA p (rv p L g w ⟨.ptS per b it, v, kk⟩ (ptRegs (pk per b)).ad) := by
  obtain ⟨h, hh, h12, h13⟩ := hH
  obtain ⟨base, lay, hbl, he⟩ := rv_ptAd p L g w per b it v kk
  have hl : lay = p.kLayout ∨ lay = p.vLayout := by
    rcases hbl with ⟨-, h⟩ | ⟨-, h⟩
    · exact .inl h
    · exact .inr h
  have hbase : base.toNat = lay.base + 2 * (h * lay.headStride) := by
    rcases hbl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h12
    · exact h13
  have hroom := row_room hp hl hpg.1 hh hr
  refine ⟨lay, hl, v.lp.toNat, hpg.1, h, hh, v.lr.toNat, hr, ?_⟩
  unfold RowV at hr
  rw [he, add_shl1 hbase (o := lay.rowStride * v.lr.toNat + lay.pageStride * v.lp.toNat) ?_ ?_]
  · rw [Nat.mul_comm lay.rowStride, Nat.mul_comm lay.pageStride]; omega
  · rw [toNat_mad64, toNat_mul64, toNat_sx32 hpg.2, toNat_sx32 (by omega)]
    omega
  · rw [Nat.mul_comm lay.rowStride, Nat.mul_comm lay.pageStride]; omega

/-! ### The head bases -/

theorem mulhi6_W {h : Nat} (hh : h < 2 ^ 26) :
    mulhi (W h) 715827883 = W (h / 6) := by
  have h1 : toSigned 32 (r32 (W h)) = h := by rw [r32_W (by omega)]; exact toSigned_W (by omega)
  have h2 : toSigned 32 (i32 715827883) = 715827883 := by decide
  simp only [mulhi, h1, h2, beq_self_eq_true, ↓reduceIte]
  have h3 : (h : Int) * 715827883 / 2 ^ 32 = ((h / 6 : Nat) : Int) := by omega
  rw [h3]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.ofInt_natCast, BitVec.toNat_ofNat, W]
  have h4 : h / 6 < 2 ^ 26 := by omega
  generalize h / 6 = q at h4
  rw [Nat.mod_eq_of_lt (show q < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show q < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show q < 2 ^ 64 by omega)]

theorem r751_W {h : Nat} (hh : h < 2 ^ 26) {v : V} (hv : v.co.head = W h) :
    (setup p L g v).r751 = W (h / 6) := by
  have hm := mulhi6_W hh
  have hs : shru (W (h / 6)) 31 = W 0 := by
    have h31 : (i32 31).toNat = 31 := by decide
    apply BitVec.eq_of_toNat_eq
    simp only [shru, h31, show ¬ (31 ≥ 32) by decide, ↓reduceIte, BitVec.toNat_ushiftRight,
      r32_W (show h / 6 < 2 ^ 32 by omega), toNat_W (show h / 6 < 2 ^ 64 by omega),
      Nat.shiftRight_eq_div_pow]
    rw [toNat_W (by omega)]
    omega
  have h748 : (setup p L g v).r748 = W (h / 6) := by
    simp only [setup, hv, hm, hs]
    rw [add32_W (by omega)]; rfl
  have hlt : scmpi .lt .s (W h) 0 = false := by
    simp only [scmpi, PTX.compare]
    rw [r32_W (by omega), toSigned_W (by omega),
      show toSigned 32 (i32 0) = 0 by decide]
    simp
  have h109 : (setup p L g v).p109 = false := by
    simp only [setup, hv, hlt, Bool.false_and]
  have e : (setup p L g v).r751 = add32 (setup p L g v).r748
      (sel (setup p L g v).p109 (i32 (-1)) (i32 0)) := by simp only [setup]
  rw [e, h748, h109]
  rw [show sel false (i32 (-1)) (i32 0) = W 0 from rfl, add32_W (by omega)]
  rfl

/-- **The setup's head bases** are those of the chosen request's head. -/
theorem head_exact (hp : Pre p L m) {v : V} {h : Nat} (hh : h < p.heads)
    (hv : v.co.head = W h) {v' : V} (hs : v'.su = setup p L g v) :
    v'.su.rd12.toNat = p.kLayout.base + 2 * (h / 6 * p.kLayout.headStride) ∧
      v'.su.rd13.toNat = p.vLayout.base + 2 * (h / 6 * p.vLayout.headStride) := by
  have hh25 := Epilogue.heads_small hp
  have hk : h / 6 < p.kvHeads := by unfold Params.heads at hh; omega
  have hb := r751_W (p := p) (L := L) (g := g) (show h < 2 ^ 26 by omega) hv
  have h0 : 0 < p.pages := by have := hp.shape; omega
  have key : ∀ lay, lay = p.kLayout ∨ lay = p.vLayout → ∀ b : BitVec 64,
      b.toNat = lay.base → (add64 b (shl64 (mul64 (BitVec.ofNat 64 lay.headStride)
        (sext (W (h / 6)))) 1)).toNat = lay.base + 2 * (h / 6 * lay.headStride) := by
    intro lay hl b hbn
    have hroom := row_room hp hl h0 hk (show 0 < 16 by decide)
    have := add_shl1 (x := mul64 (BitVec.ofNat 64 lay.headStride) (sext (W (h / 6))))
      (o := h / 6 * lay.headStride) hbn (by
        rw [toNat_mul64, sext_W (by omega), toNat_W (by omega), Nat.mul_comm]) (by omega)
    exact this
  have hbase : ∀ lay, lay = p.kLayout ∨ lay = p.vLayout →
      (BitVec.ofNat 64 lay.base).toNat = lay.base := by
    intro lay hl
    have hroom := row_room hp hl h0 hk (show 0 < 16 by decide)
    rw [BitVec.toNat_ofNat]; omega
  refine ⟨?_, ?_⟩
  · rw [hs, show (setup p L g v).rd12 = add64 (BitVec.ofNat 64 p.kLayout.base)
      (shl64 (mul64 (BitVec.ofNat 64 p.kLayout.headStride) (sext (setup p L g v).r751)) 1) by
        simp only [setup], hb]
    exact key _ (.inl rfl) _ (hbase _ (.inl rfl))
  · rw [hs, show (setup p L g v).rd13 = add64 (BitVec.ofNat 64 p.vLayout.base)
      (shl64 (mul64 (BitVec.ofNat 64 p.vLayout.headStride) (sext (setup p L g v).r751)) 1) by
        simp only [setup], hb]
    exact key _ (.inr rfl) _ (hbase _ (.inr rfl))

/-- The setup's head bases are a head's. -/
theorem head_setup (hp : Pre p L m) {v : V} {h : Nat} (hh : h < p.heads)
    (hv : v.co.head = W h) {v' : V} (hs : v'.su = setup p L g v) : HeadOk p v' := by
  obtain ⟨h1, h2⟩ := head_exact hp hh hv hs
  exact ⟨h / 6, by unfold Params.heads at hh; omega, h1, h2⟩

/-- The loader's head coordinate is the output warp's. -/
theorem head_chosen (hp : Pre p L m) (hg : g < L.threads) {d : D} {R ns nv : Nat}
    {bal : BitVec 64} (hC : Epilogue.ChosenVals p L g R bal (toE d) ns nv) :
    ∃ h < p.heads, (coords p L g d.v.sc).head = W h := by
  obtain ⟨h, hh, hd⟩ := Epilogue.chosen_head hp hg hC
  exact ⟨h, hh, hd⟩

/-! ### The row word and the page word -/

/-- The page index of every 32-bit row. -/
theorem pgIdx_all {x : BitVec 64} (h : x.toNat < 2 ^ 32) : (pgIdx x).toNat = x.toNat / 16 := by
  have hx : r32 x = x := r32_of_lt (by omega)
  have hm : (mul64 (BitVec.ofNat 64 1) (zext x)).toNat < 2 ^ 32 := by
    unfold mul64 zext r64
    rw [toNat_trunc64, BitVec.toNat_mul, toNat_trunc64, toNat_trunc64, toNat_trunc64, hx,
      show (BitVec.ofNat 64 1).toNat = 1 from rfl]
    omega
  have hsub : sub32 x 0 = x := by
    apply BitVec.eq_of_toNat_eq
    unfold sub32
    have hz : x - (0 : BitVec 64) = x := by apply BitVec.eq_of_toNat_eq; simp
    rw [hx, show r32 (0 : BitVec 64) = 0 from rfl, hz, show truncBits 32 x = r32 x from rfl, hx]
  rw [pgIdx, hiWord_zero hm, hsub]
  have h1 := shrur_i32 x (n := 1) (by decide) (by decide)
  rw [show ((1 : Nat) : Int) = 1 from rfl, hx] at h1
  have h1' : (shrur x (i32 1)).toNat < 2 ^ 32 := by rw [h1]; omega
  have ha : add32 (shrur x (i32 1)) 0 = shrur x (i32 1) := by
    unfold add32
    have hz : r32 (shrur x (i32 1)) + (0 : BitVec 64) = r32 (shrur x (i32 1)) := by
      apply BitVec.eq_of_toNat_eq; simp
    rw [show r32 (0 : BitVec 64) = 0 from rfl, hz, show truncBits 32 (r32 (shrur x (i32 1))) =
      r32 (r32 (shrur x (i32 1))) from rfl, r32_of_lt (toNat_r32_lt _), r32_of_lt h1']
  rw [ha]
  have h3 := shrur_i32 (shrur x (i32 1)) (n := 3) (by decide) (by decide)
  rw [show ((3 : Nat) : Int) = 3 from rfl, r32_of_lt h1', h1] at h3
  rw [h3]
  omega

theorem tr32_nat (z : BitVec 64) : (truncBits 32 z).toNat = z.toNat % 2 ^ 32 := by
  simp only [truncBits, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))

theorem row_rem (x : BitVec 64) (h : x.toNat < 2 ^ 32) :
    (sub32 x (mul32 (pgIdx x) (i32 16))).toNat < 16 := by
  have hi := pgIdx_all h
  have h16 : (i32 16).toNat = 16 := by decide
  have hm : (mul32 (pgIdx x) (i32 16)).toNat = x.toNat / 16 * 16 := by
    simp only [mul32, r32, tr32_nat, BitVec.toNat_mul, hi, h16]
    omega
  simp only [sub32, r32, tr32_nat, BitVec.toNat_sub, hm]
  omega

/-- The row word a page round stores. -/
theorem rw_val (p : Params) (L : Launch) (g w : Nat) (per : Per) (it : Fin 2) (v : V)
    (kk : Fin 2) : RowV (rv p L g w ⟨.rwSt per it, v, kk⟩ (rwStV per)) := by
  have hrow : (row0 p L g v per it).toNat < 2 ^ 32 := by
    cases per <;> exact toNat_add32_lt _ _
  have e : rv p L g w ⟨.rwSt per it, v, kk⟩ (rwStV per) =
      sub32 (row0 p L g v per it) (mul32 (pgIdx (row0 p L g v per it)) (i32 16)) := by
    cases per <;> rfl
  rw [e]
  exact row_rem _ hrow

theorem pg_val (p : Params) (L : Launch) (g w : Nat) (per : Per) (it : Fin 2) (v : V)
    (kk : Fin 2) : rv p L g w ⟨.pgSt per it, v, kk⟩ (pgStV per) = v.pw := by
  cases per <;> rfl

/-- **The word a page-table load returns is a page.** -/
theorem pg_page (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {b : Bool} {d : D} {n : Cls → Nat} {e : Event} {ns nv nc : Nat} {per : Per} {it : Fin 2}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)))
    (hF : LFits p L g d ns nv nc) (hs : d.site = .pgLd per it) :
    ∀ a bs x, e.kind = .rd a bs → rebuild 3 bs = .ok (.bits 32 x) → PageW p x := by
  obtain ⟨i, hib, q, hq, h⟩ := pg_value hp hX he hσ hF hs
  intro a bs x hk hx
  rw [h a bs hk] at hx
  simp only [Except.ok.injEq, Value.bits.injEq, true_and] at hx
  subst hx
  obtain ⟨h1, h2⟩ := (hp.pageTable i hib).2 q hq
  have : (BitVec.ofNat 64 (p.page i q)).toNat = p.page i q := by
    rw [BitVec.toNat_ofNat]; omega
  exact ⟨by rw [this]; exact h1, by rw [this]; exact h2⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
