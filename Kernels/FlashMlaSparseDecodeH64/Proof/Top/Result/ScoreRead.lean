-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Closed
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Reads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.QkPairSum
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Result.LoWords
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Result.ScoreWord
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.PExchange
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MaskRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PeerPair
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.OfPc
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SegEvent
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SldArm
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SldCol

@[expose] public section

/-! # The scores a lane read (valid rows)

`score_read`: at the lane's epilogue, every finished block `t` and every column `i` its mask keeps
read the high score word plus the peer's word as `score` of the block's slot. The high word is the
QK chain's sum of the lane's cell (`hi_word`), the peer's word the partner's low word at the
partner's store of the block (`peer_pair`, `lo_at_pst`), the sum of the other contraction half
(`QueryTile.pair_sum`): together the 512 features. -/

/-! # The high words of a finished block

The high half of a finished block `t` of a lane of warpgroup 0 is the register file of the lane's
high load (pc 278, or 285 for the warps 2 and 3), at the column `400 + 32 half`: its word `i` is a
single-precision number, and where the slot `32 half + i` of the block is valid, the QK chain's sum
of the lane's cell (`score_ld_word`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The high word of a finished block** (valid rows). -/
theorem hi_word (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hR : Safe.W0TraceValid P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X)
    (hw : warp L g < 4) (hv : W0Trace P X g) {K0 t i : Nat} (hi : i < 32)
    (hev : ∀ f ∈ (w0Fin ((X.tr g).take K0)).2, ∃ j < K0, X.get (g, j) = some f ∧
      w0Closed ((X.tr g).take j) = t)
    (hlen : ((w0Words (w0Fin ((X.tr g).take K0)).2).hi).length = 32) :
    ∃ S : ℝ, (w0Words (w0Fin ((X.tr g).take K0)).2).hi.getD i (.pred false) = .float .f32 S ∧
      (slotValid P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) t)
        (w0BlockSlot P (ctaidY L g) t (32 * w0Half L g + i)) →
        S = ∑ a ∈ Finset.range 16, ∑ b ∈ Finset.range 16,
          P.q (ctaidY L g) (ctaidX L g) (g % 384 % 64) (QueryTile.feature a (g % 384) b) *
            slotValue P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) t)
              (w0BlockSlot P (ctaidY L g) t (32 * w0Half L g + i))
              (QueryTile.feature a (g % 384) b)) := by
  obtain ⟨vals, hlast⟩ : ∃ vals, w0Last w0TcVals [278, 285] (w0Fin ((X.tr g).take K0)).2 =
      some vals := by
    cases h : w0Last w0TcVals [278, 285] (w0Fin ((X.tr g).take K0)).2 with
    | some v => exact ⟨v, rfl⟩
    | none => simp [w0Words, h] at hlen
  have hhi : (w0Words (w0Fin ((X.tr g).take K0)).2).hi = vals := by simp [w0Words, hlast]
  rw [hhi] at hlen ⊢
  obtain ⟨f, hfseg, hfpc, hfv⟩ := w0Last_event hlast
  obtain ⟨j, hjK, hget, hcl⟩ := hev f hfseg
  obtain ⟨pc, kd⟩ := f
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfpc
  obtain ⟨a, vals', sh, rfl⟩ : ∃ a vals' sh, kd = .tc (.ld a vals' sh) := by
    cases kd with
    | tc k' =>
      cases k' <;> simp [w0TcVals] at hfv
      exact ⟨_, _, _, rfl⟩
    | _ => simp [w0TcVals] at hfv
  simp only [w0TcVals, Option.some.injEq] at hfv
  subst hfv
  obtain ⟨hc4, hc3⟩ := wg0_sldCol hp hX hFw hget (by omega)
  have harm := w0_sld_arm hp hX hFw hw hget (noUb_kind hnu hget) (by simp only; omega) (hv.take j)
  simp only at hfpc harm
  have hat : Wg0At L g pc := ⟨hw, by omega, by omega⟩
  obtain ⟨r', hcnt, ⟨x, hx⟩, hval⟩ := score_ld_word hp hIn hR hX hFw hnu hget hat
    (by rcases hfpc with h1 | h1
        · have := hc4 (by omega); omega
        · have := hc3 (by omega); omega) (j := i) (by omega)
  have hr' : r' = t := by
    rw [← hcl]
    exact (w0Closed_of_ring hp hX hFw hw (fun b => (hcnt b).2) hnu).symm
  subst hr'
  refine ⟨x, by rw [List.getD_eq_getElem?_getD, hx]; rfl, fun hvalid => ?_⟩
  have ha : a + i - 400 = 32 * w0Half L g + i := by
    simp only [w0Half, MbarRow.warp] at harm hw ⊢
    rcases hfpc with h1 | h1
    · have := hc4 (by omega)
      have h2 : ¬ 2 ≤ (L.tidOf g).x / 32 := fun h3 => by have := harm.mpr h3; omega
      omega
    · have := hc3 (by omega)
      have h2 : 2 ≤ (L.tidOf g).x / 32 := harm.mp (by omega)
      omega
  rw [ha] at hval
  have := hval hvalid
  rw [hx] at this
  have h3 := Option.some.inj this
  simpa using h3

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The number a single-precision float value reads as. -/
theorem w0F_float (x : ℝ) : w0F (.float .f32 x) = x := by
  simp [w0F, valFloat]
  rfl

/-- **A peer word of a block is the partner's low word**: word `i` of a block whose peer pair
`i / 4` is the partner's pairs `4 (i / 4) .. 4 (i / 4) + 3`. -/
theorem w0PeerF_lo {w : W0Words} {lo : List Value} {i : Nat}
    (hp : w.pw (i / 4) =
      (.pair (lo.getD (4 * (i / 4)) (.pred false)) (lo.getD (4 * (i / 4) + 1) (.pred false)),
       .pair (lo.getD (4 * (i / 4) + 2) (.pred false))
         (lo.getD (4 * (i / 4) + 3) (.pred false)))) :
    w0PeerF w i = w0F (lo.getD i (.pred false)) := by
  unfold w0PeerF
  simp only [hp]
  have h4 : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  rcases h4 with h | h | h | h
  · have e1 : (i / 2) % 2 = 0 := by omega
    have e2 : i % 2 = 0 := by omega
    have e3 : 4 * (i / 4) = i := by omega
    simp [e1, e2, splitValue, e3]
  · have e1 : (i / 2) % 2 = 0 := by omega
    have e2 : i % 2 ≠ 0 := by omega
    have e3 : 4 * (i / 4) + 1 = i := by omega
    simp [e1, e2, splitValue, e3]
  · have e1 : (i / 2) % 2 ≠ 0 := by omega
    have e2 : i % 2 = 0 := by omega
    have e3 : 4 * (i / 4) + 2 = i := by omega
    simp [e1, e2, splitValue, e3]
  · have e1 : (i / 2) % 2 ≠ 0 := by omega
    have e2 : i % 2 ≠ 0 := by omega
    have e3 : 4 * (i / 4) + 3 = i := by omega
    simp [e1, e2, splitValue, e3]

/-- **The scores a lane read** (valid rows). -/
theorem score_read (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hR : Safe.W0TraceValid P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X)
    (hV : W0Rows P L X) : ScoreRead P L X hV := by
  intro g k e hg he hpc t seg hseg i hi hbit
  have hw : warp L g < 4 := wg0_warp_of_pc hp hX hFw hnu he (by omega)
  have hvg : W0Trace P X g := hV g hg (by simp only [warp] at hw; omega)
  have hmask := mask_read hp hX hFw (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw)
    (hIn.bar0 hp X hX hFw) (hIn.coord hp X hX hFw) hnu hV g k e hg he hpc t seg hseg i hi
  have hvalid := hmask.mp hbit
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨K0, c0, hc0, hpc0, hK0lt, hlen0, rfl, hev⟩ := w0_seg_events hp hX hFw hw hseg hnu
  have hW : W0Ok P.scale (w0Words (w0Fin ((X.tr g).take K0)).2) :=
    (hvg.1 k hk.le).1 _ (List.mem_of_getElem? hseg)
  obtain ⟨S, hS, hSv⟩ := hi_word hp hIn hR hX hFw hnu hw hvg hi
    (fun f hf => by
      obtain ⟨j, hj, hget, hcl⟩ := hev f hf
      exact ⟨j, hj, hget, hcl⟩) hW.hiLen
  have hno := w0_noEarly hp hX hFw hnu hw K0
  have hclg : w0Closed ((X.tr g).take K0) = t := by
    rw [← w0Fin_length hno]; exact hlen0
  obtain ⟨hs, hwh, hdiv, hmod⟩ := w0Partner_facts hp hw hg
  have hvp : W0Trace P X (w0Partner L g) := hV _ hs.1 (MemRow.wg0_tid hwh)
  have hne : ∀ j f, X.get (w0Partner L g, j) = some f → f.pc = 403 + 10 * (i / 4) →
      (w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo ≠ [] := fun j f hf hpcf =>
    (lo_at_pst hp hIn hR hX hFw hnu hwh hvp (k0 := i / 4) (by omega) hf hpcf).1
  have hfl : ∀ j f, X.get (w0Partner L g, j) = some f → f.pc = 403 + 10 * (i / 4) →
      ∀ c < 32, ∃ x : ℝ,
        (w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD c (.pred false) =
          .float .f32 x := fun j f hf hpcf =>
    (lo_at_pst hp hIn hR hX hFw hnu hwh hvp (k0 := i / 4) (by omega) hf hpcf).2.2.1
  obtain ⟨jp, fp, hfp, hfpc, hcl, hpeer⟩ := peer_pair hp hX hFw hnu (hIn.bar hp X hX hFw) hw hvg
    hvp (k0 := i / 4) (by omega) (hW.peer (i / 4) (by omega)) hne hfl
  obtain ⟨-, -, hflo, hlo⟩ := lo_at_pst hp hIn hR hX hFw hnu hwh hvp (k0 := i / 4) (by omega)
    hfp hfpc
  obtain ⟨T, hT⟩ := hflo i hi
  have hpw : (w0Words (w0Fin ((X.tr g).take K0)).2).pw (i / 4) =
      w0Peer (w0Fin ((X.tr g).take K0)).2 (i / 4) := by
    simp [w0Words, show i / 4 < 8 by omega]
  have hPF := w0PeerF_lo (w := w0Words (w0Fin ((X.tr g).take K0)).2) (i := i)
    (by rw [hpw, hpeer])
  rw [hS, w0F_float, hPF, hT, w0F_float]
  have hy : ctaidY L (w0Partner L g) = ctaidY L g := by simp only [ctaidY, ctaOf, hdiv]
  have hx : ctaidX L (w0Partner L g) = ctaidX L g := by simp only [ctaidX, ctaOf, hdiv]
  have hb : L.block = 384 := by have := hp.block; omega
  have hp384 : w0Partner L g % 384 = g % 384 ^^^ 64 := by rw [hb] at hmod; exact hmod
  have hr128 : g % 384 < 128 := by simp only [warp, tidOf_x_eq hp] at hw; omega
  have hkey : ∀ x < 128, (x ^^^ 64) % 64 = x % 64 ∧ (2 ≤ (x ^^^ 64) / 32 ↔ x / 64 = 0) := by
    decide
  obtain ⟨hk1, hk2⟩ := hkey _ hr128
  have hwp : warp L (w0Partner L g) = (g % 384 ^^^ 64) / 32 := by
    simp only [warp, tidOf_x_eq hp, hp384]
  have hhalf : w0Half L g = g % 384 / 64 := by simp [w0Half, tidOf_x_eq hp]
  have hidx : (if 2 ≤ warp L (w0Partner L g) then i else 32 + i) = 32 * w0Half L g + i := by
    rw [hwp, hhalf]
    by_cases h : g % 384 / 64 = 0
    · simp only [hk2.mpr h, ↓reduceIte, h]; omega
    · have : ¬ 2 ≤ (g % 384 ^^^ 64) / 32 := fun h3 => h (hk2.mp h3)
      have h1 : g % 384 / 64 = 1 := by omega
      simp only [this, ↓reduceIte, h1]
  have hvalid_p : slotValid P (ctaidY L (w0Partner L g)) (ctaidX L (w0Partner L g))
      (w0BlockExtra P (ctaidY L (w0Partner L g)) (w0Closed ((X.tr (w0Partner L g)).take jp)))
      (w0BlockSlot P (ctaidY L (w0Partner L g)) (w0Closed ((X.tr (w0Partner L g)).take jp))
        (if 2 ≤ warp L (w0Partner L g) then i else 32 + i)) := by
    rw [hy, hx, hcl, hclg, hidx]
    exact hvalid
  have hTv := hlo i hi hvalid_p
  rw [hT] at hTv
  have hTe := Option.some.inj (congrArg some hTv)
  simp only [Value.float.injEq, true_and] at hTe
  rw [hSv hvalid, hTe]
  simp only [hy, hx, hcl, hclg, hp384, hk1]
  have hpsum := QueryTile.pair_sum
    (fun t' => P.q (ctaidY L g) (ctaidX L g) (g % 384 % 64) t' *
      slotValue P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) t)
        (w0BlockSlot P (ctaidY L g) t (32 * w0Half L g + i)) t') hr128
  have hhead : w0Head L g = g % 384 % 64 := by simp [w0Head, tidOf_x_eq hp]
  unfold score
  rw [hidx, hhead]
  exact hpsum

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
