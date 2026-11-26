-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.TmEnv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.Completed
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.QkElem
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Reads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.QueryTile
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.QkCellSum
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.ResultFloat
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdPin
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdExists
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Writers
import Lemmas.Tcgen05.AccumulateStored

@[expose] public section

/-! # The words a score load of warpgroup 0 reads

A register `j` of a load of warpgroup 0 at a score column `a` (`400 ≤ a`) holds the single-precision
number the QK chain of its block `r` leaves at the cell of its lane and column `a + j` (`ld_pin`,
`load_word`, `qk_cell_sum`): the sum over the sixteen MMAs and elements of the query value times the
slot's value, at the features of the lane, when the block's slot `a + j - 400` is valid
(`score_ld_word`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **A score load's word is the QK chain's sum**, from the words of the events before the load in
the tcgen05 order (`TmClaim`, `RfClaim`). -/
theorem score_ld_word_at (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {h k pc a j : Nat} {vals : List Value} {sh : TcShape}
    (hbelow : ∀ w e', X.get w = some e' → Relation.TransGen (TcMma.TcStep L X) w (h, k) →
      TmRace.TmClaim L X w ∧ TmRace.RfClaim L X w)
    (he : X.get (h, k) = some ⟨pc, .tc (.ld a vals sh)⟩) (hat : Wg0At L h pc) (ha : 400 ≤ a)
    (hj : j < vals.length) :
    ∃ r, (∀ b : Fin 2, okPolls (mbarLoc L (h / L.block) (.qkDone b)) ((X.tr h).take k) =
        ringUses 2 b.val (r + 1) ∧ arrivals (mbarLoc L (h / L.block) (.soReady b))
        ((X.tr h).take k) = ringUses 2 b.val r) ∧
      (∃ x : ℝ, vals[j]? = some (.float .f32 x)) ∧
      (slotValid P (ctaidY L h) (ctaidX L h) (w0BlockExtra P (ctaidY L h) r)
        (w0BlockSlot P (ctaidY L h) r (a + j - 400)) →
        vals[j]? = some (.float .f32 (∑ i ∈ Finset.range 16, ∑ t ∈ Finset.range 16,
          P.q (ctaidY L h) (ctaidX L h) (h % 384 % 64) (QueryTile.feature i (h % 384) t) *
            slotValue P (ctaidY L h) (ctaidX L h) (w0BlockExtra P (ctaidY L h) r)
              (w0BlockSlot P (ctaidY L h) r (a + j - 400))
              (QueryTile.feature i (h % 384) t)))) := by
  have hT : TmemRows P L X := tmem_rows hp hX hFw
  have hO : MmaOne L X := mmaOne hp hX hFw
  have hb := Safe.tmBase hp hIn hX hFw
  have hQk := Safe.qkElements hp hIn hX hFw
  have hMb := hIn.mbar hp X hX hFw
  have hI := hIn.initRows hp X hX hFw
  have hB := hIn.bar0 hp X hX hFw
  have hN := hIn.dequant hp X hX hFw
  have hRaw := hIn.raw hp X hX hFw
  have hNc := hIn.coord hp X hX hFw
  have hBr := hIn.bar hp X hX hFw
  have hPS := Safe.pvStore hp hIn hX hFw
  have hG := Safe.guarded hp hIn hX hFw
  have ht := Safe.tmemOne hp hIn hX hFw
  have hold : ∀ i src old cell, (i = (h, k) ∨ Relation.TransGen (TcMma.TcStep L X) i (h, k)) →
      Relation.TransGen (TcMma.TcStep L X) src i →
      ((X.async.mmaDone src = true ∧ TcMma.Result L Assumptions.all X src cell old) ∨
        TcMma.StoreValue L X src cell old) → ∃ r : ℝ, valFloat .f32 old = .ok r := by
    intro i src old cell hi hdep hh
    have hdep' : Relation.TransGen (TcMma.TcStep L X) src (h, k) := by
      rcases hi with rfl | hi
      · exact hdep
      · exact hdep.trans hi
    rcases hh with ⟨hds, hres⟩ | hst
    · obtain ⟨d, s, ac, mk, pc', hsrc⟩ := hres.mmaIssue
      exact (hbelow src _ hsrc hdep').2 cell old hds hres
    · obtain ⟨a', vals', sh', j', ⟨pc', hsrc⟩, -⟩ := id hst
      obtain ⟨r, -, hr⟩ := (hbelow src _ hsrc hdep').1.2 cell old hst
      exact ⟨r, hr⟩
  have hld : X.TLd (h, k) a vals sh := ⟨pc, he⟩
  obtain ⟨-, hsh, ha', -⟩ := TmRace.ld_class hp hX hFw he
  subst hsh
  have hlc : TcMma.LoadCell L X (h, k) j (tcDataCell L h .s32x32b a j) :=
    ⟨a, vals, .s32x32b, hld, hj, rfl⟩
  obtain ⟨src, hs⟩ := TmRace.ld_source hp hX hFw hMb hI hB hN hBr hPS hG ht hlc
    (TmRace.ld_write hp hX hFw hMb hI hB hN hld hj rfl)
  obtain ⟨r, hcnt, i, sx, mask, hsrc, hget, hiss, hdone, hmc⟩ :=
    TmRace.ld_pin hp hX hFw hMb hI hB hG he hat ha hj rfl hs
  subst hsrc
  obtain ⟨hcta, hlane, hcol⟩ := dataCell hp hat.1 ha' (j := j)
  have hcw := (TmRace.writer_cases hp hX hT hs.2.1).1
  have hxc : mmaLane L X (h / L.block) / L.block = h / L.block := hcw.symm.trans hcta
  obtain ⟨d, s, acc, mk, row, col, hi, hpos⟩ := id hmc
  obtain ⟨rr, hres⟩ := (hbelow (mmaLane L X (h / L.block), i) _ hget hs.2.2.1.tcStep).1.1
    d s acc mk row col _ hi hdone hpos
  obtain ⟨word, hwd, hcont⟩ := TcMma.load_word hX.tcRead.1 hld hlc hs (.inl hres)
  have hy : ctaidY L (mmaLane L X (h / L.block)) = ctaidY L h := by simp only [ctaidY, ctaOf, hxc]
  have hx : ctaidX L (mmaLane L X (h / L.block)) = ctaidX L h := by simp only [ctaidX, ctaOf, hxc]
  have hfl : ∃ x : ℝ, vals[j]? = some (.float .f32 x) := by
    rcases hcont with ⟨-, rfl⟩ | ⟨h2, -⟩
    · exact ⟨rr, hwd⟩
    · simp [Value.bytes, FloatFmt.bytes] at h2
  refine ⟨r, hcnt, hfl, fun hvalid => ?_⟩
  have hv := TmRace.qk_cell_sum hp hX hFw hT hO hMb hI hB hN hRaw hNc hb.hv hPS hG ht hb.hmd
    hQk (h, k) hold hget hdone hres (.inr hs.2.2.1.tcStep) hiss (by rw [hy, hx, hcol]; exact hvalid)
  rw [hy, hx, hlane, hcol] at hv
  rcases hcont with ⟨-, rfl⟩ | ⟨h2, -⟩
  · rw [hwd, hv]
  · simp [Value.bytes, FloatFmt.bytes] at h2

/-- **The Tensor Memory words and float results of every event**, from the leaf of the warpgroup 0
trace (the claims of the induction `Safe.tmJoint`, as the old tree states them). -/
theorem Safe.tmClaimsR (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hR : Safe.W0TraceValid P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    ∀ w e', X.get w = some e' → TmRace.TmClaim L X w ∧ TmRace.RfClaim L X w := by
  have env := Safe.tmEnv hp hIn hR hX hFw hnu
  have hT : TmemRows P L X := tmem_rows hp hX hFw
  have hO : MmaOne L X := mmaOne hp hX hFw
  have hTV := TmRace.tmem_values hp hX hFw hT hO (Safe.pvStore hp hIn hX hFw)
    (Safe.guarded hp hIn hX hFw) (Safe.tmemOne hp hIn hX hFw) env.hmd (hIn.mbar hp X hX hFw)
    (hIn.initRows hp X hX hFw) (hIn.bar0 hp X hX hFw) (hIn.dequant hp X hX hFw)
    (hIn.bar hp X hX hFw) env.hE env.hS
  exact fun w e' hw => ⟨hTV w e' hw,
    fun cell old hd (hr : TcMma.Result L Assumptions.all X w cell old) => by
      obtain ⟨d, s, ac, mk, pc', hsrc⟩ := hr.mmaIssue
      exact TmRace.result_float hp hX hT hO (Safe.guarded hp hIn hX hFw) env.hE
        (fun w' e'' hw' cell' old' hst => (hTV w' e'' hw').2 cell' old' hst) hsrc hd hr⟩

/-- **A score load's word is the QK chain's sum** (valid rows). -/
theorem score_ld_word (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hR : Safe.W0TraceValid P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X)
    {h k pc a j : Nat} {vals : List Value} {sh : TcShape}
    (he : X.get (h, k) = some ⟨pc, .tc (.ld a vals sh)⟩) (hat : Wg0At L h pc) (ha : 400 ≤ a)
    (hj : j < vals.length) :
    ∃ r, (∀ b : Fin 2, okPolls (mbarLoc L (h / L.block) (.qkDone b)) ((X.tr h).take k) =
        ringUses 2 b.val (r + 1) ∧ arrivals (mbarLoc L (h / L.block) (.soReady b))
        ((X.tr h).take k) = ringUses 2 b.val r) ∧
      (∃ x : ℝ, vals[j]? = some (.float .f32 x)) ∧
      (slotValid P (ctaidY L h) (ctaidX L h) (w0BlockExtra P (ctaidY L h) r)
        (w0BlockSlot P (ctaidY L h) r (a + j - 400)) →
        vals[j]? = some (.float .f32 (∑ i ∈ Finset.range 16, ∑ t ∈ Finset.range 16,
          P.q (ctaidY L h) (ctaidX L h) (h % 384 % 64) (QueryTile.feature i (h % 384) t) *
            slotValue P (ctaidY L h) (ctaidX L h) (w0BlockExtra P (ctaidY L h) r)
              (w0BlockSlot P (ctaidY L h) r (a + j - 400))
              (QueryTile.feature i (h % 384) t)))) := by
  exact score_ld_word_at hp hIn hX hFw
    (fun w e' hw _ => Safe.tmClaimsR hp hIn hR hX hFw hnu w e' hw) he hat ha hj

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
