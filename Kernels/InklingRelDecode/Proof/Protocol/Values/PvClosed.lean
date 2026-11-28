-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.PvWords
public import Kernels.InklingRelDecode.Proof.Protocol.Values.LdoReal
import Kernels.InklingRelDecode.Proof.Protocol.Values.PvSum
import Kernels.InklingRelDecode.Proof.Lib.QkCell
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteStore
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdOrderO
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits

@[expose] public section

/-! # The PV accumulator is the closed form

By induction on the ordinal: the real of the last PV step of ordinal `n + 1` is the sum of the
products of block `n` plus the real the ordinal starts from. That is the real of step 7 of the
ordinal before (no rescale store covers the cell, the factor is one), or the word of the rescale
store of the round, the factor times the word of the load of the round, which is the real of step
7 of the ordinal before again (`ld_o_real`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem Lib.SoftRow Finset

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A rescale store has the static address and shape. -/
theorem rescale_static (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {t k a vals sh jj}
    (he : X.get (t, k) = some ⟨2328, .tc (.st a vals sh)⟩) (hj : jj < vals.length) :
    ∃ w, sh = .s16x32bx2 64 ∧ a = 256 + w * 2 ^ 21 := by
  obtain ⟨-, -, k1 | k2⟩ := st_write_cell hp hX hf base (x := (t, k))
    (cell := tcDataCell L t sh a jj) ⟨a, vals, sh, jj, ⟨2328, he⟩, hj, rfl⟩
  · obtain ⟨a1, v1, ba, w, j1, g1, -⟩ := k1
    rw [he] at g1
    simp at g1
  · obtain ⟨a2, v2, w, j2, g2, ha, -⟩ := k2
    rw [he] at g2
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at g2
    obtain ⟨-, rfl, rfl, rfl⟩ := g2
    exact ⟨w, rfl, ha⟩

/-- **A rescale store and the load before it cover the same cell with one register.** -/
theorem st_ld_cell (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {t k kl a vals sh a' ov sh' jj}
    (hs : X.get (t, k) = some ⟨2328, .tc (.st a vals sh)⟩)
    (hl : X.get (t, kl) = some ⟨2260, .tc (.ld a' ov sh')⟩) (hj : jj < vals.length)
    (hj' : jj < ov.length) : tcDataCell L t sh a jj = tcDataCell L t sh' a' jj := by
  obtain ⟨w, rfl, rfl⟩ := rescale_static hp hX hf base hs hj
  obtain ⟨kk, -, rfl, rfl, hj64, -⟩ := ld_o_cell hp hX hf base hl (.inl rfl) hj'
  rw [cell_split L t 256 64 w jj (by omega), cell_split L t 256 64 kk jj (by omega)]

/-- **The cell a PV step writes**: lane of its row, column of its column in the accumulator. -/
theorem pv_result_cell (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {g k d s acc mask row col cell} {j : Fin 8}
    (he : X.get (g, k) = some ⟨Lib.pvIssue j, .tc (.mma d s acc mask)⟩)
    (hw : writeCell s d mask row col = some cell) :
    row < 64 ∧ col < 128 ∧ cell = ⟨g / L.block, 32 * (row / 16) + row % 16, 256 + col⟩ := by
  obtain ⟨rfl, hD⟩ := pv_cols hp hX hf base he
  obtain ⟨hmask, lo, -⟩ := Mma.Export.columns hp hX hf base he
  obtain ⟨hr, hc, hcell⟩ := Lib.pv_cell hD hmask hw
  exact ⟨hr, hc, by rw [hcell, lo]⟩

/-- The accumulator after `n + 1` blocks from the one after `n`. -/
theorem closedAcc_succ (Q : Params) (L : Launch) (pw : Nat → Nat → Nat → Nat → ℝ)
    (al : Nat → Nat → Nat → ℝ) (c row col n : Nat) :
    closedAcc Q L pw al c row col (n + 1) =
      (∑ κ ∈ range 128, pw c n row κ * (keyPair Q (ctaZ L c) (row / 6)
        (ctaY L c * 6 + row % 6) col (128 * (Q.splits * n + ctaXc L c) + κ)).2) +
      al c n row * closedAcc Q L pw al c row col n := rfl

/-- **The last PV step of ordinal `n + 1` is the closed form** of its cell's row and column. -/
theorem pv_closed_form (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X) (hG : SyncGuarded L kernel X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) (hws : WritesSafe L X)
    (ht : Tmem.One.Tmem1Facts L X 0) (hmd : Tmem.AccessCp.AsyncDoneDealloc L X)
    (words : RoleBytes L X) (nub : ¬ Assumptions.inputReadOnly.ub L m X)
    (form : Iface.KvCopyForm Q L X) (W : Iface.PWords X)
    {pw : Nat → Nat → Nat → Nat → ℝ} {al : Nat → Nat → Nat → ℝ} (P : PWords Q L X pw)
    (hR : ∀ {src a vals sh}, X.get src = some ⟨2328, .tc (.st a vals sh)⟩ →
      ∀ v ∈ vals, ∃ r : ℝ, v = .float .f32 r)
    (tie : RescaleLd X) (ord : LdBeforeSt X) (RA : RescaleAl Q L X al) (NR : NoRescaleAl Q L X al) :
    ∀ n {g k cell R}, PvAt X g k 7 → pollRound 2510 ((X.tr g).take k) = n + 1 →
      n + 1 ≤ Lib.blocksOf Q L (g / L.block) →
      ResReal L X (pvA L X pw) (pvB Q L X) (svOf L X) (g, k) cell R →
      ∃ row col, row < 64 ∧ col < 128 ∧
        cell = ⟨g / L.block, 32 * (row / 16) + row % 16, 256 + col⟩ ∧
        (Lib.QRowValid Q L (g / L.block) row →
          R = closedAcc Q L pw al (g / L.block) row col (n + 1)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro g k cell R hat hn hlim hres
  obtain ⟨ks, hks, row, col, steps, r0, hsum, hbase⟩ :=
    pv_sum hp hX hf hu safe base rows init hG tie 7 rfl hat hres
  obtain ⟨-, -, d, s, acc, mask, hi7, hw7⟩ := steps 7 le_rfl
  obtain ⟨d0, s0, a0, m0, e0⟩ := hat
  have hk7 : ks (7 : Fin 8).val = k := hks
  rw [hk7] at hi7
  obtain ⟨pc7, e7⟩ := hi7
  have := Option.some.inj (e0.symm.trans e7)
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at this
  obtain ⟨-, rfl, rfl, rfl, rfl⟩ := this
  obtain ⟨hrow, hcol, hcell⟩ := pv_result_cell hp hX hf base e0 hw7
  have hgrid : g / L.block < L.grid := Nat.div_lt_of_lt_mul (by
    simpa [Launch.threads, Nat.mul_comm] using Frame.lt_of_get hX e0)
  refine ⟨row, col, hrow, hcol, hcell, fun valid => ?_⟩
  have blk : ∑ i ∈ range ((7 : Fin 8).val + 1), ∑ kk ∈ range 16,
      pvA L X pw (g, ks i) row kk * pvB Q L X (g, ks i) col kk =
      ∑ κ ∈ range 128, pw (g / L.block) n row κ * (keyPair Q (ctaZ L (g / L.block)) (row / 6)
        (ctaY L (g / L.block) * 6 + row % 6) col
          (128 * (Q.splits * n + ctaXc L (g / L.block)) + κ)).2 := by
    rw [← pv_block_sum Q L pw (g / L.block) n row col hcol]
    refine sum_congr rfl fun i hi => sum_congr rfl fun kk _ => ?_
    obtain ⟨⟨d1, s1, a1, m1, e1⟩, rd, -⟩ := steps ⟨i, mem_range.1 hi⟩ (by simp at hi ⊢; omega)
    have st : pvStepOf X (g, ks i) = i := by simp [pvStepOf, e1, pvStep_pvIssue]
    simp only [pvA, pvB, st, rd, hn, Nat.add_sub_cancel]
  rw [hsum, blk, closedAcc_succ]
  rw [hn] at hbase
  suffices hr0 : r0 = al (g / L.block) n row * closedAcc Q L pw al (g / L.block) row col n by
    rw [hr0]
  rcases hbase with ⟨h1, h0⟩ | ⟨h2, ⟨kR, pat, hord, rr, nost⟩ | ⟨st, hresc, hsv⟩⟩
  · obtain rfl : n = 0 := by omega
    rw [h0]
    simp [closedAcc, clAcc]
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨row', col', -, -, hcell', hv'⟩ := ih n' (by omega) pat (by omega) (by omega) rr
    obtain ⟨-, hl, hcl⟩ := Cell.mk.inj (hcell.symm.trans hcell')
    obtain rfl : row = row' := by omega
    obtain rfl : col = col' := by omega
    have one := NR (g / L.block) (n' + 1) row col hgrid hrow hcol valid (by omega)
      (show n' + 1 < Lib.blocksOf Q L (g / L.block) by omega)
      (fun st hst => nost st (by rw [hcell]; simpa using hst))
    rw [hv' valid, one, one_mul]
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨t, ks0⟩ := st
    obtain ⟨a, vals, sh, jj, hst, hjj, hcell2, hr2⟩ := hresc
    have r2 : pollRound 1257 ((X.tr t).take ks0) = n' + 1 + 1 := by simpa using hr2
    obtain ⟨kl, -, a', ov, sh', hld, same⟩ := tie t ks0 a vals sh hst
    have cta : g / L.block = t / L.block := by
      have := rescale_cta hp hX hf base (st := (t, ks0)) (r := n' + 1) (cell := cell)
        ⟨a, vals, sh, jj, hst, hjj, hcell2, by omega⟩
      rw [hcell] at this
      exact this
    have hlane : laneRow (tcDataCell L t sh a jj).lane = row := by
      rw [← hcell2, hcell]
      show 16 * ((32 * (row / 16) + row % 16) / 32) + (32 * (row / 16) + row % 16) % 32 = row
      omega
    obtain ⟨x, hov, hvals⟩ := RA t ks0 a vals sh kl a' ov sh' jj (by rw [hlane, ← cta]; exact valid)
      hst hld same hjj
    have hovlen := (List.getElem?_eq_some_iff.mp hov).1
    have hce := st_ld_cell hp hX hf base hst hld hjj hovlen
    have vld : Lib.QRowValid Q L (t / L.block) (laneRow (tcDataCell L t sh' a' jj).lane) := by
      rw [← hce, hlane, ← cta]
      exact valid
    obtain ⟨g', kR', r1, cy', pat', hord', rr', hovr⟩ := ld_o_real hp hX hf hu safe hG base rows
      init hws ht hmd words nub form W P hR ord hld hovlen (r := n' + 1) (by omega) vld
    have hx : x = r1 := by
      rw [hov] at hovr
      simpa using hovr
    obtain ⟨row', col', -, -, hcell', hv'⟩ := ih n' (by omega) pat' hord'
      (by rw [cy', ← cta]; omega) rr'
    obtain ⟨hg', hl, hcl⟩ := Cell.mk.inj (hcell.symm.trans (hcell2.trans (hce.trans hcell')))
    obtain rfl : row = row' := by omega
    obtain rfl : col = col' := by omega
    have hs := svOf_eq hp hX hf base (src := (t, ks0)) (cell := cell)
      (old := .float .f32 (al (t / L.block) (pollRound 1257 ((X.tr t).take ks0) - 1)
        (laneRow (tcDataCell L t sh a jj).lane) * x))
      (r := al (t / L.block) (pollRound 1257 ((X.tr t).take ks0) - 1)
        (laneRow (tcDataCell L t sh a jj).lane) * x)
      ⟨a, vals, sh, jj, ⟨2328, hst⟩, hvals, hcell2⟩ (by simp [valFloat, pure, Except.pure])
    rw [hsv, hs, hlane, r2, ← cta, hx, Nat.add_sub_cancel, hv' (hg' ▸ valid), ← hg']

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
