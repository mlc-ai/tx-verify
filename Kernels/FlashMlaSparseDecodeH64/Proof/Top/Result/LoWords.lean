-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Result.ScoreWord
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Closed
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.LoBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SldCol
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SldArm
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemLoad
import Lemmas.Order.OrderWaits

@[expose] public section

/-! # The low words at a peer store

At a peer store of a lane `h` of warpgroup 0 (pc `403 + 10 k0`) the low half of the block in
progress is the register file of the lane's low load: 32 words, each a single-precision number
(`score_ld_word`), and where the slot of the column is valid, the QK chain's sum of the cell of the
lane's row. The low load's column is `400 + 32 (1 - half)` (`wg0_sldCol`, `w0_sld_arm`), and its
block is the one of the store (ring counts, `w0Closed_of_ring`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {h : Nat}

/-- **The low words at a peer store** (valid rows): from the words of the events before the store
in the tcgen05 order and the validity of the lane's prefix before it. -/
theorem lo_at_pst_at (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    (hw : warp L h < 4) {j k0 : Nat} {e : Event} (hv : W0Valid P.scale ((X.tr h).take j))
    (hbelow : ∀ w e', X.get w = some e' → Relation.TransGen (TcMma.TcStep L X) w (h, j) →
      TmRace.TmClaim L X w ∧ TmRace.RfClaim L X w) (hk0 : k0 < 8)
    (he : X.get (h, j) = some e) (hub : ∀ f, e.kind ≠ .ub f) (hpc : e.pc = 403 + 10 * k0) :
    (w0Words (w0Fin ((X.tr h).take j)).2).lo ≠ [] ∧
    (w0Words (w0Fin ((X.tr h).take j)).2).lo.length = 32 ∧
    (∀ c < 32, ∃ x : ℝ,
      (w0Words (w0Fin ((X.tr h).take j)).2).lo.getD c (.pred false) = .float .f32 x) ∧
    ∀ c < 32, slotValid P (ctaidY L h) (ctaidX L h)
        (w0BlockExtra P (ctaidY L h) (w0Closed ((X.tr h).take j)))
        (w0BlockSlot P (ctaidY L h) (w0Closed ((X.tr h).take j))
          (if 2 ≤ warp L h then c else 32 + c)) →
      (w0Words (w0Fin ((X.tr h).take j)).2).lo.getD c (.pred false) =
        .float .f32 (∑ i ∈ Finset.range 16, ∑ t ∈ Finset.range 16,
          P.q (ctaidY L h) (ctaidX L h) (h % 384 % 64) (QueryTile.feature i (h % 384) t) *
            slotValue P (ctaidY L h) (ctaidX L h)
              (w0BlockExtra P (ctaidY L h) (w0Closed ((X.tr h).take j)))
              (w0BlockSlot P (ctaidY L h) (w0Closed ((X.tr h).take j))
                (if 2 ≤ warp L h then c else 32 + c))
              (QueryTile.feature i (h % 384) t)) := by
  obtain ⟨i, a, vals, sh, pc', hij, hget, hpc', hcl, hlo⟩ :=
    w0_lo_before_pst hp hX hFw hw hv hk0 he hub hpc
  have hbl : ∀ w e', X.get w = some e' → Relation.TransGen (TcMma.TcStep L X) w (h, i) →
      TmRace.TmClaim L X w ∧ TmRace.RfClaim L X w := fun w e' hw htc =>
    hbelow w e' hw (.tail htc (.inl (.single (.inl (po_of_source_not_access rfl hij
      (len_of_get he) (by simp [hget, Event.acc]))))))
  have hmem : pc' ∈ [278, 280, 283, 285] := by simp only [List.mem_cons]; omega
  have hlen : vals.length = 32 := scoreLdLen hp hX (i := (h, i)) hget rfl hmem
  obtain ⟨hc4, hc3⟩ := wg0_sldCol hp hX hFw hget (by omega)
  have harm := w0_sld_arm hp hX hFw hw hget (noUb_kind_of_lt hX hget hij (len_of_get he))
    (by simp only; omega)
    (Wg0.W0Valid.take_le hv hij.le)
  simp only at harm
  have hat : Wg0At L h pc' := ⟨hw, by omega, by omega⟩
  have hrr : ∀ c < 32, ∃ x : ℝ, vals[c]? = some (.float .f32 x) ∧
      (slotValid P (ctaidY L h) (ctaidX L h)
        (w0BlockExtra P (ctaidY L h) (w0Closed ((X.tr h).take j)))
        (w0BlockSlot P (ctaidY L h) (w0Closed ((X.tr h).take j))
          (if 2 ≤ warp L h then c else 32 + c)) →
        vals[c]? = some (.float .f32 (∑ i ∈ Finset.range 16, ∑ t ∈ Finset.range 16,
          P.q (ctaidY L h) (ctaidX L h) (h % 384 % 64) (QueryTile.feature i (h % 384) t) *
            slotValue P (ctaidY L h) (ctaidX L h)
              (w0BlockExtra P (ctaidY L h) (w0Closed ((X.tr h).take j)))
              (w0BlockSlot P (ctaidY L h) (w0Closed ((X.tr h).take j))
                (if 2 ≤ warp L h then c else 32 + c))
              (QueryTile.feature i (h % 384) t)))) := by
    intro c hc
    obtain ⟨r', hcnt, ⟨x, hx⟩, hval⟩ := score_ld_word_at hp hIn hX hFw hbl hget hat
      (by rcases hpc' with h1 | h1
          · have := hc3 (by omega); omega
          · have := hc4 (by omega); omega) (j := c) (by omega)
    have hr' : r' = w0Closed ((X.tr h).take j) := by
      rw [← hcl]
      exact (w0Closed_of_ring hp hX hFw hw (fun b => (hcnt b).2) (noUbBefore_of_get hX hget)).symm
    subst hr'
    refine ⟨x, hx, fun hvalid => ?_⟩
    have ha : a + c - 400 = if 2 ≤ warp L h then c else 32 + c := by
      rcases hpc' with h1 | h1
      · have := hc3 (by omega)
        have h2 : ¬ 2 ≤ warp L h := by
          intro h3
          have := harm.mpr h3
          omega
        simp only [h2, ↓reduceIte]; omega
      · have := hc4 (by omega)
        have h2 : 2 ≤ warp L h := by
          apply harm.mp
          omega
        simp only [h2, ↓reduceIte]; omega
    rw [ha] at hval
    exact hval hvalid
  refine ⟨by rw [hlo]; intro h0; rw [h0] at hlen; simp at hlen, by rw [hlo]; exact hlen,
    fun c hc => ?_, fun c hc hvalid => ?_⟩
  · obtain ⟨x, hx, -⟩ := hrr c hc
    exact ⟨x, by rw [hlo, List.getD_eq_getElem?_getD, hx]; rfl⟩
  · obtain ⟨x, hx, hv'⟩ := hrr c hc
    rw [hlo, List.getD_eq_getElem?_getD, hv' hvalid]
    rfl

/-- **The low words at a peer store** (valid rows), with the leaf of the trace. -/
theorem lo_at_pst (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hR : Safe.W0TraceValid P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X)
    (hw : warp L h < 4) (hv : W0Trace P X h) {j k0 : Nat} {e : Event} (hk0 : k0 < 8)
    (he : X.get (h, j) = some e) (hpc : e.pc = 403 + 10 * k0) :
    (w0Words (w0Fin ((X.tr h).take j)).2).lo ≠ [] ∧
    (w0Words (w0Fin ((X.tr h).take j)).2).lo.length = 32 ∧
    (∀ c < 32, ∃ x : ℝ,
      (w0Words (w0Fin ((X.tr h).take j)).2).lo.getD c (.pred false) = .float .f32 x) ∧
    ∀ c < 32, slotValid P (ctaidY L h) (ctaidX L h)
        (w0BlockExtra P (ctaidY L h) (w0Closed ((X.tr h).take j)))
        (w0BlockSlot P (ctaidY L h) (w0Closed ((X.tr h).take j))
          (if 2 ≤ warp L h then c else 32 + c)) →
      (w0Words (w0Fin ((X.tr h).take j)).2).lo.getD c (.pred false) =
        .float .f32 (∑ i ∈ Finset.range 16, ∑ t ∈ Finset.range 16,
          P.q (ctaidY L h) (ctaidX L h) (h % 384 % 64) (QueryTile.feature i (h % 384) t) *
            slotValue P (ctaidY L h) (ctaidX L h)
              (w0BlockExtra P (ctaidY L h) (w0Closed ((X.tr h).take j)))
              (w0BlockSlot P (ctaidY L h) (w0Closed ((X.tr h).take j))
                (if 2 ≤ warp L h then c else 32 + c))
              (QueryTile.feature i (h % 384) t)) :=
  lo_at_pst_at hp hIn hX hFw hw (hv.take (j := j))
    (fun w e' hw' _ => Safe.tmClaimsR hp hIn hR hX hFw hnu w e' hw') hk0 he (noUb_kind hnu he) hpc

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
