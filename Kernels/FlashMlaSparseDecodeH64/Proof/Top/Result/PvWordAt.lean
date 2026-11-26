-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.TmEnv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvChain
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvAProof
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MmaElem
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.ResultFloat
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Writers
import Lemmas.Tcgen05.AccumulateStored

@[expose] public section

/-! # The words of the PV chains, per event

The operand elements of the MMAs before an event in the tcgen05 order are numbers
(`Safe.mmaElemBelow`, from the validity of warpgroup 0's prefixes before the P stores), and a load
whose source is a done PV MMA reads the end of its chain from the words of the events before the
load (`ld_word_pv_at`), without the whole trace's validity. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **The operand elements of the MMAs below `b`** are numbers: the prefixes of warpgroup 0's
lanes before the events below `b` are valid. -/
theorem Safe.mmaElemBelow (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {b : EvId}
    (hv : ∀ h k2 ev, X.get (h, k2) = some ev →
      Relation.TransGen (TcMma.TcStep L X) (h, k2) b → warp L h < 4 →
      W0Valid P.scale ((X.tr h).take k2)) :
    ∀ w, (w = b ∨ Relation.TransGen (TcMma.TcStep L X) w b) → MmaElemAt X w := by
  intro w hw
  have hT : TmemRows P L X := tmem_rows hp hX hFw
  have hO : MmaOne L X := mmaOne hp hX hFw
  have hb := Safe.tmBase hp hIn hX hFw
  have hMb := hIn.mbar hp X hX hFw
  have hI := hIn.initRows hp X hX hFw
  have hB := hIn.bar0 hp X hX hFw
  have hN := hIn.dequant hp X hX hFw
  have hBr := hIn.bar hp X hX hFw
  have ht := Safe.tmemOne hp hIn hX hFw
  have hSi : ∀ i d s acc mask, X.MmaIssue i d s acc mask → TcMma.IssueShape L i d s mask :=
    fun _ _ _ _ _ hi => Safe.issueShape hp hX hFw hi
  refine TmRace.mma_elem_at hp hX hFw hMb hI hB hN hb.hv hSi hT hO ht hb.hmd w
    fun d s acc mask ops row col cell hi hd hops hc hd256 => ?_
  refine TmRace.pv_a_elem_at hp hX hFw hMb hI hB hBr hSi hT ?_ d s acc mask ops row col cell
    hi hd hops hc hd256
  intro h k2 ev hev htc hwh
  refine hv h k2 ev hev ?_ hwh
  rcases hw with rfl | hw
  · exact htc
  · exact htc.trans hw

/-- **A load register whose source is a done PV MMA reads the end of its chain**, from the words
of the events before the load (`TmClaim`, `RfClaim`) and the operand elements below it. -/
theorem ld_word_pv_at (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {h k a j kk i : Nat} {vals : List Value} {src : EvId}
    {sx : TcMma.OperandSpec} {mask : List Nat}
    (hbelow : ∀ w e', X.get w = some e' → Relation.TransGen (TcMma.TcStep L X) w (h, k) →
      TmRace.TmClaim L X w ∧ TmRace.RfClaim L X w)
    (hEb : ∀ w, (w = (h, k) ∨ Relation.TransGen (TcMma.TcStep L X) w (h, k)) →
      MmaElemAt X w)
    (hld : X.TLd (h, k) a vals .s32x32b)
    (hlc : TcMma.LoadCell L X (h, k) j (tcDataCell L h .s32x32b a j))
    (hs : TcMma.ReadSource L X .ld src (h, k) (tcDataCell L h .s32x32b a j))
    (hsrc : src = (mmaLane L X (h / L.block), i)) (hk8 : kk < 8)
    (hget : X.get src = some ⟨TmemRow.pvPc kk, .tc (.mma (128 * (kk % 2)) sx true mask)⟩)
    (hdone : X.async.mmaDone src = true)
    (hmc : X.MmaCell src (tcDataCell L h .s32x32b a j)) :
    ∃ x : ℝ, vals[j]? = some (.float .f32 x) ∧
      TmRace.PvChain L X (mmaLane L X (h / L.block)) i kk (tcDataCell L h .s32x32b a j)
        (.float .f32 x) := by
  subst hsrc
  have hT : TmemRows P L X := tmem_rows hp hX hFw
  have hO : MmaOne L X := mmaOne hp hX hFw
  have hb := Safe.tmBase hp hIn hX hFw
  have hMb := hIn.mbar hp X hX hFw
  have hI := hIn.initRows hp X hX hFw
  have hB := hIn.bar0 hp X hX hFw
  have hPS := Safe.pvStore hp hIn hX hFw
  have hG := Safe.guarded hp hIn hX hFw
  have ht := Safe.tmemOne hp hIn hX hFw
  have hold : ∀ i' src old cell,
      (i' = (h, k) ∨ Relation.TransGen (TcMma.TcStep L X) i' (h, k)) →
      Relation.TransGen (TcMma.TcStep L X) src i' →
      ((X.async.mmaDone src = true ∧ TcMma.Result L Assumptions.all X src cell old) ∨
        TcMma.StoreValue L X src cell old) → ∃ r : ℝ, valFloat .f32 old = .ok r := by
    intro i' src' old cell hi hdep hh
    have hdep' : Relation.TransGen (TcMma.TcStep L X) src' (h, k) := by
      rcases hi with rfl | hi
      · exact hdep
      · exact hdep.trans hi
    rcases hh with ⟨hds, hres⟩ | hst
    · obtain ⟨d, s, ac, mk, pc', hsrc'⟩ := hres.mmaIssue
      exact (hbelow src' _ hsrc' hdep').2 cell old hds hres
    · obtain ⟨a', vals', sh', j', ⟨pc', hsrc'⟩, -⟩ := id hst
      obtain ⟨r, -, hr⟩ := (hbelow src' _ hsrc' hdep').1.2 cell old hst
      exact ⟨r, hr⟩
  obtain ⟨d, s, acc, mk, row, col, hi, hpos⟩ := id hmc
  obtain ⟨rr, hres⟩ := (hbelow (mmaLane L X (h / L.block), i) _ hget hs.2.2.1.tcStep).1.1
    d s acc mk row col _ hi hdone hpos
  obtain ⟨word, hwd, hcont⟩ := TcMma.load_word hX.tcRead.1 hld hlc hs (.inl hres)
  have hch := TmRace.pv_chain hp hX hFw hMb hI hB hT hO hPS hG ht hb.hmd (h, k) hEb hold
    (kk / 2) kk rfl hk8 hget (fun _ => rfl) hdone hres
    (Or.inr hs.2.2.1.tcStep)
  rcases hcont with ⟨-, rfl⟩ | ⟨h2, -⟩
  · exact ⟨rr, hwd, hch⟩
  · simp [Value.bytes, FloatFmt.bytes] at h2

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
