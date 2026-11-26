-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MmaSlot
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Reads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PWordVal
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Result.PvEnv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCode
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.PvAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QkPrev
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdExists
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvSource0
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.RsPin
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ArrBlock
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Block
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Rescale
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.RldRst

@[expose] public section

/-! # One block of the accumulator recursion

The chain of PV MMA `6 + p` of block `d` at the cell of lane `g` is its base plus the four slices'
products (`PvChain`). The base of block `d` is zero for the first block; for a later one it is the
chain of block `d - 1` at the cell times `2 ^ (M d - M (d + 1))`, `M n` the maximum lane `g` carries
after `n` blocks: through the rescale store of block `d` (its words are the previous chain ends
times the factor, `rst_store_words`) or, if the block did not rescale, through the MMA itself (the
vote is false, so the maximum is kept: `pv0_mma_noarm`, `w0_max_novote`). -/

/-! # The first PV MMA of a done chain is done

A done PV MMA `k` of a block reads its accumulator from PV MMA `k - 2` (`acc_source_pv`), which is
done (`acc_mma_done`); so the first MMA of the block (`k % 2`) is done (`pv_first_done`). Two PV
MMAs of the lane with the same issue count are the same event (`pv_issue_eq`). -/

/-! # The words a rescale store of warpgroup 0 writes

The two events before chunk `c`'s rescale store `y` of block `r ≥ 1` are its load and the load's
wait: the load has the store's counts of `qkDone` polls and `soReady` arrivals, so it is block
`r`'s load, and each of its 64 registers is the end of the PV chain of block `r - 1` at the cell
(`rs_ld_word`). So the words the store writes are those numbers times the block's factor
`s = 2 ^ (m - m')` (`w0_rst_vals`): `rst_store_words`. -/

/-! # The words a rescale load of warpgroup 0 reads

A register `j` of chunk `c`'s rescale load of block `r ≥ 1` holds the single-precision number
that PV MMA `6 + p` of block `r - 1` (`p = (64 c + j) / 128`) leaves at the cell of its lane and
column `64 c + j` (`ld_pin_rs`, `ld_word_pv`): the end of that block's PV chain. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **A rescale load's word is the end of the previous block's PV chain** (valid rows). -/
theorem rs_ld_word (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hR : Safe.W0TraceValid P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X)
    {h k a j r : Nat} {c : Fin 4} {vals : List Value} {sh : TcShape}
    (he : X.get (h, k) = some ⟨[716, 817, 918, 1019].getD c.val 0, .tc (.ld a vals sh)⟩)
    (hj : j < vals.length) (h1r : 1 ≤ r)
    (hr : ∀ b : Fin 2, okPolls (mbarLoc L (h / L.block) (.qkDone b)) ((X.tr h).take k) =
        ringUses 2 b.val (r + 1) ∧ arrivals (mbarLoc L (h / L.block) (.soReady b))
        ((X.tr h).take k) = ringUses 2 b.val r) :
    ∃ (i : Nat) (x : ℝ), vals[j]? = some (.float .f32 x) ∧
      mmaIssues ((X.tr (mmaLane L X (h / L.block))).take i) =
        24 * (r - 1) + 16 + (6 + (a + j) / 128) ∧
      X.async.mmaDone (mmaLane L X (h / L.block), i) = true ∧
      TmRace.PvChain L X (mmaLane L X (h / L.block)) i (6 + (a + j) / 128)
        (tcDataCell L h .s32x32b a j) (.float .f32 x) := by
  have E := pvEnv hp hIn hR hX hFw hnu
  have hld : X.TLd (h, k) a vals sh := ⟨_, he⟩
  obtain ⟨hat, hsh, ha', -⟩ := TmRace.ld_class hp hX hFw he
  subst hsh
  obtain ⟨hca, -⟩ := wg0_rld_addr hp hX hFw hat.1 he
  have hlen := ldLen hp hX he rfl
  have hc4 := c.isLt
  have hlc : TcMma.LoadCell L X (h, k) j (tcDataCell L h .s32x32b a j) :=
    ⟨a, vals, .s32x32b, hld, hj, rfl⟩
  obtain ⟨src, hs⟩ := TmRace.ld_source hp hX hFw E.hMb E.hI E.hB E.hN E.hBr E.hPS E.hG E.ht
    hlc (TmRace.ld_write hp hX hFw E.hMb E.hI E.hB E.hN hld hj rfl)
  obtain ⟨i, sx, mask, hsrc, hget, hiss, hdone, hmc⟩ :=
    TmRace.ld_pin_rs hp hX hFw E.hMb E.hI E.hB E.hG he hj rfl h1r hr hs
  obtain ⟨hcta, hlane, hcol⟩ := dataCell hp hat.1 ha' (j := j)
  rw [hcol] at hget hiss
  have hk6 : (6 + (a + j) / 128) % 2 = (a + j) / 128 := by omega
  obtain ⟨x, hx, hch⟩ := ld_word_pv hp hX hFw E (kk := 6 + (a + j) / 128) hld hlc hs hsrc
    (by omega) (by rw [hk6]; exact hget) hdone hmc
  exact ⟨i, x, hx, hiss, hsrc ▸ hdone, hch⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **A rescale store's words are the previous block's chain ends times the factor** (valid
rows). -/
theorem rst_store_words (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hR : Safe.W0TraceValid P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X)
    {g k a r : Nat} {c : Fin 4} {vals : List Value} {sh : TcShape}
    (hw : warp L g < 4) (hv0 : W0Trace P X g)
    (he : X.get (g, k) = some ⟨[814, 915, 1016, 1117].getD c.val 0, .tc (.st a vals sh)⟩)
    (h1r : 1 ≤ r)
    (hr : ∀ b : Fin 2, okPolls (mbarLoc L (g / L.block) (.qkDone b)) ((X.tr g).take k) =
        ringUses 2 b.val (r + 1) ∧ arrivals (mbarLoc L (g / L.block) (.soReady b))
        ((X.tr g).take k) = ringUses 2 b.val r) :
    ∃ (x : Nat → ℝ) (s : ℝ),
      s = (2 : ℝ) ^ ((w0Carry P.scale (w0Fin ((X.tr g).take k)).1).1 -
        w0Max P.scale (w0Carry P.scale (w0Fin ((X.tr g).take k)).1).1
          (w0Words (w0Fin ((X.tr g).take k)).2)) ∧
      vals.length = 64 ∧
      (∀ i < 64, vals[i]? = some (.float .f32 (x i * s))) ∧
      ∀ i < 64, ∃ i',
        mmaIssues ((X.tr (mmaLane L X (g / L.block))).take i') =
          24 * (r - 1) + 16 + (6 + (64 * c.val + i) / 128) ∧
        X.async.mmaDone (mmaLane L X (g / L.block), i') = true ∧
        TmRace.PvChain L X (mmaLane L X (g / L.block)) i' (6 + (64 * c.val + i) / 128)
        (tcDataCell L g .s32x32b (64 * c.val) i) (.float .f32 (x i)) := by
  obtain ⟨j, f0, f1, a0, vals0, sh0, hk2, hf0, hpc0, hk0, hf1, hpc1⟩ :=
    Wg0.w0_rst_prev hp hX hFw hw (hv0.take k) he (noUb_kind hnu he) rfl
  obtain ⟨j', f0', a0', vals0', sh0', hk2', hf0', hk0', hlen0, himp⟩ :=
    w0_rst_vals hp hX hFw hw (hv0.take k) he rfl rfl
  have hjj : j = j' := by omega
  subst hjj
  rw [hf0] at hf0'
  obtain rfl := Option.some.inj hf0'
  rw [hk0] at hk0'
  simp only [Kind.tc.injEq, TcKind.ld.injEq] at hk0'
  obtain ⟨rfl, rfl, rfl⟩ := hk0'
  obtain ⟨pc0, kd0⟩ := f0
  obtain ⟨pc1, kd1⟩ := f1
  simp only at hpc0 hk0 hpc1
  subst hk0
  have hkd1 : kd1 = .tc .waitLd := wg0_rldw_kind hp hX hFw hw (c := c) (hpc1 ▸ hf1)
    ((noUbWg0_of_noUb L hnu).kind hw hf1)
  subst hkd1
  have hf0'' : X.get (g, j) = some ⟨[716, 817, 918, 1019].getD c.val 0,
      .tc (.ld a0 vals0 sh0)⟩ := by rw [hf0, hpc0]
  have hlt : j + 2 = k := hk2.symm
  have htake : (X.tr g).take k = (X.tr g).take j ++ [⟨pc0, .tc (.ld a0 vals0 sh0)⟩,
      ⟨pc1, .tc .waitLd⟩] := by
    have h0 : (X.tr g)[j]? = some ⟨pc0, .tc (.ld a0 vals0 sh0)⟩ := hf0
    have h1 : (X.tr g)[j + 1]? = some ⟨pc1, .tc .waitLd⟩ := hf1
    rw [← hlt, show j + 2 = (j + 1) + 1 from rfl, List.take_add_one, List.take_add_one]
    simp [h0, h1]
  have hr' : ∀ b : Fin 2, okPolls (mbarLoc L (g / L.block) (.qkDone b)) ((X.tr g).take j) =
      ringUses 2 b.val (r + 1) ∧ arrivals (mbarLoc L (g / L.block) (.soReady b))
        ((X.tr g).take j) = ringUses 2 b.val r := by
    intro b
    have h := hr b
    rw [htake] at h
    simpa [okPolls, arrivals, List.countP_append, okPoll, sourceWaitSuccess, arrivesOn,
      sourceArrive] using h
  obtain ⟨hca, -⟩ := wg0_rld_addr hp hX hFw hw hf0''
  subst hca
  have hl64 : vals0.length = 64 := hlen0
  have hwords : ∀ i, ∃ x : ℝ, i < 64 → vals0[i]? = some (.float .f32 x) ∧
      ∃ i', mmaIssues ((X.tr (mmaLane L X (g / L.block))).take i') =
          24 * (r - 1) + 16 + (6 + (64 * c.val + i) / 128) ∧
        X.async.mmaDone (mmaLane L X (g / L.block), i') = true ∧
        TmRace.PvChain L X (mmaLane L X (g / L.block)) i' (6 + (64 * c.val + i) / 128)
        (tcDataCell L g .s32x32b (64 * c.val) i) (.float .f32 x) := by
    intro i
    by_cases hi : i < 64
    · obtain ⟨i', x, hx, hiss, hdn, hch⟩ :=
        rs_ld_word hp hIn hR hX hFw hnu hf0'' (j := i) (by omega) h1r hr'
      exact ⟨x, fun _ => ⟨hx, i', hiss, hdn, hch⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose x hx using hwords
  obtain ⟨y, s, hs, hyo, hvl, hvals⟩ := himp (fun v hv => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    refine ⟨x i, ?_⟩
    have := (hx i (by omega)).1
    rw [List.getElem?_eq_getElem hi] at this
    rw [Option.some.inj this]
    exact okF_float _)
  refine ⟨x, s, hs, hvl, fun i hi => ?_, fun i hi => ?_⟩
  · have h1 := hvals i (by omega)
    have h2 := (hyo i (by omega)).2
    have h3 := (hx i hi).1
    rw [List.getElem?_eq_getElem (by omega)] at h3
    rw [Option.some.inj h3] at h2
    simp only [valFloat] at h2
    have h4 : y i = x i := by
      have := Except.ok.inj h2
      exact this.symm
    rw [List.getElem?_eq_getElem (by omega), h1, h4]
  · exact ⟨(hx i hi).2.choose, (hx i hi).2.choose_spec⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0}

theorem pvPc_range {k : Nat} (hk : k < 8) : 1853 ≤ TmemRow.pvPc k ∧ TmemRow.pvPc k ≤ 2160 := by
  simp only [TmemRow.pvPc]
  split <;> omega

theorem pvPc_inj_f {k k' : Nat} (h : TmemRow.pvPc k = TmemRow.pvPc k') : k = k' := by
  simp only [TmemRow.pvPc] at h
  split_ifs at h <;> omega

/-- **Two PV MMAs of one lane with the same issue count are one event.** -/
theorem pv_issue_eq {X : Execution} {g j j' k k' : Nat} {a b : TcMma.OperandSpec} {c d : Bool}
    {mk mk' : List Nat} {x y : Nat}
    (hj : X.get (g, j) = some ⟨TmemRow.pvPc k, .tc (.mma x a c mk)⟩) (hk : k < 8)
    (hj' : X.get (g, j') = some ⟨TmemRow.pvPc k', .tc (.mma y b d mk')⟩) (hk' : k' < 8)
    (hiss : mmaIssues ((X.tr g).take j) = mmaIssues ((X.tr g).take j')) : j = j' := by
  rcases lt_trichotomy j j' with h | h | h
  · have := mmaIssues_lt hj (pvPc_range hk) h
    omega
  · exact h
  · have := mmaIssues_lt hj' (pvPc_range hk') h
    omega

/-- **The first MMA of the block of a done PV MMA is done.** -/
theorem pv_first_done (hp : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    (E : PvEnv P L mem0 X) {g : Nat} :
    ∀ n k, k / 2 = n → k < 8 → ∀ {i : Nat} {s : TcMma.OperandSpec} {acc : Bool}
      {mask : List Nat} {cell : TcMma.Cell},
      X.get (g, i) = some ⟨TmemRow.pvPc k, .tc (.mma (128 * (k % 2)) s acc mask)⟩ →
      X.async.mmaDone (g, i) = true → (2 ≤ k → X.MmaReadCell (g, i) cell) →
      ∃ j0 s0 a0 m0, X.get (g, j0) =
          some ⟨TmemRow.pvPc (k % 2), .tc (.mma (128 * (k % 2)) s0 a0 m0)⟩ ∧
        mmaIssues ((X.tr g).take j0) + (k - k % 2) = mmaIssues ((X.tr g).take i) ∧
        X.async.mmaDone (g, j0) = true := by
  intro n
  induction n with
  | zero =>
    intro k hkn hk i s acc mask cell he hd _
    have : k % 2 = k := by omega
    exact ⟨i, s, acc, mask, by simpa only [this] using he, by omega, hd⟩
  | succ n ih =>
    intro k hkn hk i s acc mask cell he hd hrd0
    have hk2 : 2 ≤ k := by omega
    have hacc : acc = true := by
      obtain ⟨k1, -, -, -, -, hon, -⟩ := TmRace.pv_pc E.hT hX he (by omega)
      obtain ⟨d1, k1', h1, h2, h3, h4, hiff, -⟩ := mma_pvAt hp hX hFw he hon.1 (by omega)
      obtain rfl := pvPc_inj_f h2
      exact hiff.mpr (Or.inl hk2)
    subst hacc
    have hrd := hrd0 hk2
    obtain ⟨j, hji, ⟨s2, a2, m2, hj⟩, ⟨r, hr1, hr2⟩, hmc, hsrc⟩ :=
      TmRace.acc_source_pv hp hX hFw E.hMb E.hI E.hB E.hT E.hO E.hPS E.hG E.ht E.hmd he hk2 hk hrd
    have hdj := TmRace.acc_mma_done hp hX E.hT E.hO E.hG hd hrd hsrc hmc
    obtain ⟨d, s3, a3, mk3, row, col, hi, hpos⟩ := id hmc
    have hmod : (k - 2) % 2 = k % 2 := by omega
    have hj' : X.get (g, j) =
        some ⟨TmemRow.pvPc (k - 2), .tc (.mma (128 * ((k - 2) % 2)) s2 a2 m2)⟩ := by
      rw [hmod]; exact hj
    have hrd' : 2 ≤ k - 2 → X.MmaReadCell (g, j) cell := by
      intro h2
      obtain ⟨k1, -, -, -, -, hon, -⟩ := TmRace.pv_pc E.hT hX hj' (by omega)
      obtain ⟨d1, k1', h1, h3, h5, h4, hiff, -⟩ := mma_pvAt hp hX hFw hj' hon.1 (by omega)
      obtain rfl := pvPc_inj_f h3
      have ha2 : a2 = true := hiff.mpr (Or.inl h2)
      subst ha2
      obtain ⟨pcx, hx⟩ := id hi
      rw [hj] at hx
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hx
      obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hx
      exact ⟨_, _, _, row, col, hi, TcMma.writeCell_resultCell hpos⟩
    obtain ⟨j0, s0, a0, m0, h0, hi0, hd0⟩ := ih (k - 2) (by omega) (by omega) hj' hdj hrd'
    refine ⟨j0, s0, a0, m0, by rw [← hmod]; exact h0, ?_, hd0⟩
    rw [hmod] at hi0
    omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- The maximum lane `g` carries after `n` blocks. -/
noncomputable def carryM (P : Params) (X : Execution) (g n : Nat) : ℝ :=
  (w0Carry P.scale ((w0Fin (X.tr g)).1.take n)).1

private theorem pvPc_inj_r {k k' : Nat} (h : TmemRow.pvPc k = TmemRow.pvPc k') : k = k' := by
  simp only [TmemRow.pvPc] at h
  split_ifs at h <;> omega

/-- **The base of the chain of block `d`** (valid rows): the chain of PV MMA `6 + p` of block `d`
at the cell `(64 c, jj)` of lane `g` is its base plus the four slices' terms, the base being `0`
(`d = 0`) or the chain of block `d - 1` at the cell times `2 ^ (M d - M (d + 1))`. -/
theorem pv_rec (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hR : Safe.W0TraceValid P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X)
    {g d c jj p i0 K : Nat} {x : ℝ}
    (hw : warp L g < 4) (hv0 : W0Trace P X g)
    (hKn : (w0Fin ((X.tr g).take K)).1.length = blocksOf P L (g / L.block))
    (hd : d < blocksOf P L (g / L.block)) (hc : c < 4) (hjj : jj < 64)
    (hp2 : p = (64 * c + jj) / 128)
    (hch : TmRace.PvChain L X (mmaLane L X (g / L.block)) i0 (6 + p)
      (tcDataCell L g .s32x32b (64 * c) jj) (.float .f32 x))
    (hiss : mmaIssues ((X.tr (mmaLane L X (g / L.block))).take i0) = 24 * d + 16 + (6 + p))
    (hdone : X.async.mmaDone (mmaLane L X (g / L.block), i0) = true) :
    ∃ (j : Nat → Nat) (a : Nat → ℝ) (base : ℝ),
      (∀ m ≤ 3, TmRace.PvTerm X (mmaLane L X (g / L.block)) (j m) (p + 2 * m)
        (tcDataCell L g .s32x32b (64 * c) jj) (a m)) ∧
      (∀ m ≤ 3, mmaIssues ((X.tr (mmaLane L X (g / L.block))).take (j m)) =
        24 * d + 16 + (p + 2 * m)) ∧
      x = base + ∑ m ∈ Finset.range 4, a m ∧
      ((d = 0 ∧ base = 0) ∨ (1 ≤ d ∧ ∃ i' x',
        mmaIssues ((X.tr (mmaLane L X (g / L.block))).take i') = 24 * (d - 1) + 16 + (6 + p) ∧
        X.async.mmaDone (mmaLane L X (g / L.block), i') = true ∧
        TmRace.PvChain L X (mmaLane L X (g / L.block)) i' (6 + p)
          (tcDataCell L g .s32x32b (64 * c) jj) (.float .f32 x') ∧
        base = (2 : ℝ) ^ (carryM P X g d - carryM P X g (d + 1)) * x')) := by
  have E := pvEnv hp hIn hR hX hFw hnu
  obtain ⟨hcta, hlane, hcol⟩ := stCell hp hw hc (j := jj)
  have hp2' : p < 2 := by omega
  obtain ⟨j, a, base, hj3, hbase, hterms, hmono, ⟨r, hr⟩, hv⟩ := hch
  have hk2 : (6 + p) % 2 = p := by omega
  have hk3 : (6 + p) / 2 = 3 := by omega
  simp only [hk2, hk3] at hj3 hbase hterms hr hv
  have hrd : d = r := by
    have := hr 3 le_rfl
    rw [hj3, hiss] at this
    omega
  subst hrd
  have hx : x = base + ∑ m ∈ Finset.range 4, a m := by
    have := Value.float.inj hv
    simpa using this
  refine ⟨j, a, base, hterms, hr, hx, ?_⟩
  obtain ⟨s0, acc0, mask0, hget0, hcases⟩ := hbase
  have hRead : ∀ m ≤ 3, (2 ≤ p + 2 * m ∨ 1 ≤ d) →
      X.MmaReadCell (mmaLane L X (g / L.block), j m) (tcDataCell L g .s32x32b (64 * c) jj) := by
    intro m hm hcond
    obtain ⟨s, acc, ops, row, col, xs, ys, hget, hops, hpos, -⟩ := hterms m hm
    obtain ⟨k0, -, -, -, -, hon, -⟩ := TmRace.pv_pc E.hT hX hget (by omega)
    obtain ⟨d1, k1, -, h2, -, h4, hiff, -⟩ := mma_pvAt hp hX hFw hget hon.1 (by omega)
    obtain rfl := pvPc_inj_r h2
    have hd1 : d = d1 := by have := hr m hm; omega
    subst hd1
    have hacc : acc = true := hiff.mpr hcond
    subst hacc
    exact ⟨_, _, _, row, col, ⟨_, hget⟩, TcMma.writeCell_resultCell hpos⟩
  have hd1 : acc0 = true → 1 ≤ d := by
    intro hacc
    obtain ⟨k0, -, -, -, -, hon, -⟩ := TmRace.pv_pc E.hT hX hget0 (by omega)
    obtain ⟨d1, k1, -, h2, -, h4, hiff, -⟩ := mma_pvAt hp hX hFw hget0 hon.1 (by omega)
    obtain rfl := pvPc_inj_r h2
    have := hr 0 (by omega)
    have h5 := hiff.mp hacc
    omega
  rcases hcases with ⟨hacc0, hb0⟩ | ⟨hacc0, src, old, hsrc, hres, hvf⟩
  · left
    refine ⟨?_, hb0⟩
    by_contra hne
    obtain ⟨k0, -, -, -, -, hon, -⟩ := TmRace.pv_pc E.hT hX hget0 (by omega)
    obtain ⟨d1, k1, -, h2, -, h4, hiff, -⟩ := mma_pvAt hp hX hFw hget0 hon.1 (by omega)
    obtain rfl := pvPc_inj_r h2
    have := hr 0 (by omega)
    have h5 : acc0 = true := hiff.mpr (Or.inr (by omega))
    rw [hacc0] at h5
    cases h5
  · right
    subst hacc0
    have hd1' := hd1 rfl
    refine ⟨hd1', ?_⟩
    have hrd0 := hRead 0 (by omega) (Or.inr hd1')
    have hget0' : X.get (mmaLane L X (g / L.block), j 0) =
        some ⟨TmemRow.pvPc p, .tc (.mma (128 * p) s0 true mask0)⟩ := by
      simpa only [Nat.mod_eq_of_lt hp2'] using hget0
    obtain ⟨d', hd'1, hiss', hbr⟩ := TmRace.acc_source_pv0 hp hX hFw E.hMb E.hI E.hB E.hT E.hO
      E.hG hget0' hp2' hrd0 hsrc
    have hdd : d = d' := by have := hr 0 (by omega); omega
    subst hdd
    have hno := w0_noEarly hp hX hFw hnu hw
    have hKd : d < (w0Fin ((X.tr g).take K)).1.length := by rw [hKn]; exact hd
    rcases hbr with ⟨jS, sS, mS, hsrcEq, hgetS, hissS, hmcS⟩ |
      ⟨h, is, a0, c', vals, hsrcEq, hh1, hh2, hwh, hc4, hgetS, ha0, hlen, hcc, harr, hpoll⟩
    · -- the source is the MMA of the previous block
      subst hsrcEq
      have hresS : TcMma.Result L Assumptions.all X (mmaLane L X (g / L.block), jS)
          (tcDataCell L g .s32x32b (64 * c) jj) old := by
        rcases hres with h1 | ⟨a', vals', sh', j', ⟨pcs, hst⟩, -⟩
        · exact h1
        · cases TmRace.get_tc_inj hgetS hst
      obtain ⟨s3, acc3, ops3, row3, col3, xs3, ys3, hget3, hops3, hpos3, hx3⟩ :=
        hterms 3 le_rfl
      have e63 : p + 2 * 3 = 6 + p := by omega
      rw [hj3, e63] at hget3
      have hrdI : 2 ≤ 6 + p → X.MmaReadCell (mmaLane L X (g / L.block), i0)
          (tcDataCell L g .s32x32b (64 * c) jj) := fun _ => by
        have := hRead 3 le_rfl (Or.inl (by omega))
        rwa [hj3] at this
      obtain ⟨j0, s0', a0', m0', h0get, h0iss, h0done⟩ :=
        pv_first_done hp hX hFw E 3 (6 + p) (by omega) (by omega) hget3 hdone hrdI
      rw [hk2] at h0get
      have hj0 : j0 = j 0 := pv_issue_eq h0get (by omega) hget0 (by omega)
        (by have := hr 0 (by omega); omega)
      rw [hj0] at h0done
      have hdoneS := TmRace.acc_mma_done hp hX E.hT E.hO E.hG h0done hrd0 hsrc hmcS
      have hgetS' : X.get (mmaLane L X (g / L.block), jS) =
          some ⟨TmemRow.pvPc (6 + p), .tc (.mma (128 * ((6 + p) % 2)) sS true mS)⟩ := by
        rw [hk2]; exact hgetS
      have hchS := TmRace.pv_chain hp hX hFw E.hMb E.hI E.hB E.hT E.hO E.hPS E.hG E.ht E.hmd
        (mmaLane L X (g / L.block), jS) (fun j _ => E.hE j)
        (fun i' src old cell _ hdep hh => E.hold i' src old cell hdep hh)
        3 (6 + p) (by omega) (by omega) hgetS' (fun _ => rfl) hdoneS hresS (Or.inl rfl)
      obtain ⟨x', rfl⟩ : ∃ x', old = .float .f32 x' := by
        obtain ⟨_, _, _, _, _, _, _, _, hvS⟩ := hchS
        exact ⟨_, hvS⟩
      have hbx : base = x' := by
        simp only [valFloat] at hvf
        exact (Except.ok.inj hvf).symm
      obtain ⟨ia, l, tx, cnt, rel, sc, hia, hcl, harrb⟩ := w0_block_arrive hp hX hFw hnu hw
        (K := K) (t := d) (by rw [← w0Fin_length (hno K)]; exact hKd)
      obtain ⟨q, mm, a1, h18, hvote, hAr⟩ := TmRace.pv0_mma_noarm hp hX hFw E.hMb E.hI E.hB E.hT
        E.hG hnu hget0' hp2' hrd0 hd1' (by have := hr 0 (by omega); omega) hsrc hgetS hissS
        hcta.symm hlane.symm hw hia harrb
      have hlenv : (w0Fin ((X.tr g).take (ia - 18))).1.length = d := by
        rw [w0Fin_length (hno (ia - 18))]
        have e1 := w0Closed_arrs hp hX hFw hw (k := ia - 18) hnu
        have e2 := w0Closed_arrs hp hX hFw hw (k := ia) hnu
        unfold arrs2 at e1 e2
        have h0 := hAr (loc L g (.soReady 0))
        have h1 := hAr (loc L g (.soReady 1))
        omega
      have hnov := w0_max_novote hp hX hFw hnu hw hv0 hvote hlenv hKd
      refine ⟨jS, x', hissS, hdoneS, hchS, ?_⟩
      rw [hbx]
      unfold carryM
      rw [hnov]
      simp
    · -- the source is the rescale store of the block
      have hb : L.block = 384 := by have := hp.block; omega
      have hhg : g = h := (thread_eq (by rw [hb]; omega) (hh1.trans hcta)).symm
      subst hsrcEq
      subst hhg
      have hcc' : c = c' := by omega
      subst hcc'
      subst ha0
      rcases hres with hr1 | ⟨a', vals', sh', j', ⟨pcs, hst⟩, hvj, hcj⟩
      · obtain ⟨d2, s2, ac2, mk2, pc2, hs2⟩ := hr1.mmaIssue
        cases TmRace.get_tc_inj hgetS hs2
      have hinj := TmRace.get_tc_inj hgetS hst
      simp only [TcKind.st.injEq] at hinj
      obtain ⟨rfl, rfl, rfl⟩ := hinj
      have hcc2 := congrArg TcMma.Cell.column hcj
      rw [(stCell hp hw hc (j := j')).2.2, hcol] at hcc2
      have hjj' : jj = j' := by omega
      subst hjj'
      have hr' : ∀ b : Fin 2, okPolls (mbarLoc L (g / L.block) (.qkDone b)) ((X.tr g).take is) =
          ringUses 2 b.val (d + 1) ∧ arrivals (mbarLoc L (g / L.block) (.soReady b))
            ((X.tr g).take is) = ringUses 2 b.val d := fun b => ⟨hpoll b, harr b⟩
      obtain ⟨xs, sf, hsf, hvl, hvals, hchs⟩ := rst_store_words hp hIn hR hX hFw hnu hw hv0
        (c := ⟨c, hc⟩) hgetS hd1' hr'
      have hold : old = .float .f32 (xs jj * sf) := by
        have := (hvals jj hjj).symm.trans hvj
        exact (Option.some.inj this).symm
      have hbx : base = xs jj * sf := by
        rw [hold] at hvf
        simp only [valFloat] at hvf
        exact (Except.ok.inj hvf).symm
      have hpp : (64 * (⟨c, hc⟩ : Fin 4).val + jj) / 128 = p := by
        show (64 * c + jj) / 128 = p
        omega
      obtain ⟨i', hissc, hdonec, hchc⟩ := hchs jj hjj
      rw [hpp] at hissc hchc
      have hpcs : 579 ≤ [814, 915, 1016, 1117].getD c 0 ∧
          [814, 915, 1016, 1117].getD c 0 < 1122 := by
        interval_cases c <;> simp
      have hlenis : (w0Fin ((X.tr g).take is)).1.length = d := by
        rw [w0Fin_length (hno is)]
        have e1 := w0Closed_arrs hp hX hFw hw (k := is) hnu
        unfold arrs2 at e1
        have h0 := harr 0
        have h1 := harr 1
        unfold ringUses at h0 h1
        simp only [Fin.val_zero, Fin.val_one] at h0 h1
        have l0 : loc L g (.soReady 0) = mbarLoc L (g / L.block) (.soReady 0) := rfl
        have l1 : loc L g (.soReady 1) = mbarLoc L (g / L.block) (.soReady 1) := rfl
        rw [l0, l1, h0, h1] at e1
        omega
      obtain ⟨sB, hsB, hws, htk, hcs⟩ := w0_max_at hp hX hFw hnu hw hv0 hgetS hpcs hlenis
        (K := K) hKd
      rw [hcs, htk] at hsf
      refine ⟨i', xs jj, hissc, hdonec, hchc, ?_⟩
      rw [hbx, hsf]
      unfold carryM
      ring

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
