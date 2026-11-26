-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.TmEnv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.Completed
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.ResultFloat
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MmaResults
import Lemmas.Tcgen05.AccumulateStored
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvChain
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Order

@[expose] public section

/-! # What the value chains of the Tensor Memory need, in one place

The facts the PV chain and the loads' sources are proved from (`pv_chain`, `ld_source`): the rows,
the single MMA lane, the orders and the Tensor Memory facts, the mbarrier facts, and `hold`: the
words an accumulator source holds are numbers (`result_float`, the rescale stores' words). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **The environment of the value chains** of an execution. -/
structure PvEnv (P : Params) (L : Launch) (mem0 : Mem0) (X : Execution) : Prop where
  hT : TmemRows P L X
  hO : MmaOne L X
  hPS : TmRace.PvStoreOrder L X
  hG : SyncGuarded L kernel X
  ht : Tmem.One.Tmem1Facts L X 0
  hMb : MbarRows P L X
  hI : InitRows L X
  hB : Bar0Rows L X
  hN : DequantInputs L X
  hBr : BarRows P L X
  hmd : Tmem.AccessCp.AsyncDoneDealloc L X
  hE : MmaElements X
  hS : RescaleStep L X
  hold : ∀ i src old cell, Relation.TransGen (TcMma.TcStep L X) src i →
    ((X.async.mmaDone src = true ∧ TcMma.Result L Assumptions.all X src cell old) ∨
      TcMma.StoreValue L X src cell old) → ∃ r : ℝ, valFloat .f32 old = .ok r

/-- **The environment of the value chains** (valid rows). -/
theorem pvEnv (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hR : Safe.W0TraceValid P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    PvEnv P L mem0 X := by
  have hT : TmemRows P L X := tmem_rows hp hX hFw
  have hO : MmaOne L X := mmaOne hp hX hFw
  have env := Safe.tmEnv hp hIn hR hX hFw hnu
  have hPS := Safe.pvStore hp hIn hX hFw
  have hG := Safe.guarded hp hIn hX hFw
  have ht := Safe.tmemOne hp hIn hX hFw
  have hMb := hIn.mbar hp X hX hFw
  have hI := hIn.initRows hp X hX hFw
  have hB := hIn.bar0 hp X hX hFw
  have hN := hIn.dequant hp X hX hFw
  have hBr := hIn.bar hp X hX hFw
  have hTV := TmRace.tmem_values hp hX hFw hT hO hPS hG ht env.hmd hMb hI hB hN hBr env.hE
    env.hS
  refine ⟨hT, hO, hPS, hG, ht, hMb, hI, hB, hN, hBr, env.hmd, env.hE, env.hS, ?_⟩
  intro i src old cell _ hh
  rcases hh with ⟨hds, hres⟩ | hst
  · obtain ⟨d, s, ac, mk, pc', hsrc⟩ := hres.mmaIssue
    exact TmRace.result_float hp hX hT hO hG env.hE
      (fun w e hw cell old hst => (hTV w e hw).2 cell old hst) hsrc hds hres
  · obtain ⟨a', vals', sh', j', ⟨pc', hsrc⟩, -⟩ := id hst
    obtain ⟨r, -, hr⟩ := (hTV src _ hsrc).2 cell old hst
    exact ⟨r, hr⟩

/-- **A load register whose source is a done PV MMA reads the end of its chain.** -/
theorem ld_word_pv (hp : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    (E : PvEnv P L mem0 X) {h k a j kk i : Nat} {vals : List Value} {src : EvId}
    {sx : TcMma.OperandSpec} {mask : List Nat}
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
  have hTV := TmRace.tmem_values hp hX hFw E.hT E.hO E.hPS E.hG E.ht E.hmd E.hMb E.hI E.hB
    E.hN E.hBr E.hE E.hS
  obtain ⟨d, s, acc, mk, row, col, hi, hpos⟩ := id hmc
  obtain ⟨rr, hres⟩ := (hTV (mmaLane L X (h / L.block), i) _ hget).1 d s acc mk row col _ hi hdone
    hpos
  obtain ⟨word, hwd, hcont⟩ := TcMma.load_word hX.tcRead.1 hld hlc hs (.inl hres)
  have hch := TmRace.pv_chain hp hX hFw E.hMb E.hI E.hB E.hT E.hO E.hPS E.hG E.ht E.hmd
    (mmaLane L X (h / L.block), i) (fun j _ => E.hE j)
    (fun i' src old cell _ hdep hh => E.hold i' src old cell hdep hh)
    (kk / 2) kk rfl hk8 hget (fun _ => rfl) hdone hres (Or.inl rfl)
  rcases hcont with ⟨-, rfl⟩ | ⟨h2, -⟩
  · exact ⟨rr, hwd, hch⟩
  · simp [Value.bytes, FloatFmt.bytes] at h2

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
