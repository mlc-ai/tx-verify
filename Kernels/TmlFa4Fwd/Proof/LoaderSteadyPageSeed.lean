-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyFirstObserved
import Kernels.TmlFa4Fwd.Flow.Code.Part021

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue Prologue

noncomputable section

/-- The steady loop keeps the selected page-table base, lane row offset, and column. -/
def steadyCacheFrame (p : Params) (l : Launch) (batch head trips warp tid : Nat) :
    List (Nat × Value) :=
  [(1116, b32 (trips - 2)), (2130, b32 (primingLaneRow 0 tid)),
    (1147, b32 (8 * (tid % 8))), (7781, b64 (16 * (tid % 8))),
    (7763, b64 (p.pageTableBase + 4 * (batch * p.pageTableStride)))] ++
      warmStartFrame p l batch head trips warp tid ++ [(1146,b32 (tid/8%8))]

set_option maxRecDepth 100000 in
private theorem steadyPageBaseCore {p : Params} {l : Launch} {m : Mem0} {g batch tid : Nat}
    (hp : Pre p l m) (hb : batch < p.batch) (hQ : 0 < p.qLength batch) :
    Seg kernel [] l g 5 1391
      [(7170, b32 batch), (7505, b64 p.pageTableStride), (7504, b64 p.pageTableBase),
        (1147, b32 (8 * (tid % 8)))] 1396
      [(7763, b64 (p.pageTableBase + 4 * (batch * p.pageTableStride))),
        (7781, b64 (16 * (tid % 8)))] := by
  let addr := p.pageTableBase + 4 * (batch * p.pageTableStride)
  have hRegion := hp.ranges ⟨p.pageTableBase, 4 * p.batch * p.pageTableStride⟩
    (by simp [Params.inputRegions])
  have hStride := (hp.pageTable batch hb).1
  have hKey := (hp.lengths batch hb).2.1
  have hSucc := Nat.mul_le_mul_right p.pageTableStride (show batch + 1 ≤ p.batch by omega)
  rw [Nat.add_mul, Nat.one_mul] at hSucc
  change p.pageTableBase + 4 * p.batch * p.pageTableStride ≤ 2 ^ 64 at hRegion
  rw [Nat.mul_assoc] at hRegion
  have hBig : addr < 2 ^ 64 := by dsimp [addr]; omega
  have hBatch31 : batch < 2 ^ 31 := hb.trans hp.shape.2.1
  have hBatch32 : batch < 2 ^ 32 := by omega
  have hBatch64 : batch < 2 ^ 64 := by omega
  have hBase : p.pageTableBase < 2 ^ 64 := by dsimp [addr] at hBig; omega
  have hStride64 : p.pageTableStride < 2 ^ 64 := by
    have hMon := Nat.mul_le_mul_right p.pageTableStride (show 1 ≤ p.batch by omega)
    rw [Nat.one_mul] at hMon
    omega
  have hProd : batch * p.pageTableStride < 2 ^ 64 := by dsimp [addr] at hBig; omega
  have hBytes : 4 * (batch * p.pageTableStride) < 2 ^ 64 := by dsimp [addr] at hBig; omega
  have hSigned : toSigned 32 (BitVec.ofNat 64 batch) = (batch : Int) := by
    simp only [toSigned, toNat_ofNat_lt hBatch64, Nat.mod_eq_of_lt hBatch32,
      ite_eq_left hBatch31]
  have hTwo : (truncBits 32 (BitVec.ofInt 64 2)).toNat = 2 := rfl
  have hCol : 8 * (tid % 8) < 2 ^ 32 := by omega
  have hColMul : 8 * (tid % 8) * 2 = 16 * (tid % 8) := by omega
  intro s hs
  seg_fp hs using first
    | solve
      | simp only [b64, cvtIntBits, intBits, intOf, intSat, Bool.not_false, hSigned, addr,
          hTwo, show ¬(2 : Nat) ≥ 64 by decide, ↓reduceIte, BitVec.ofInt_natCast,
          truncBits_ofNat hBatch32 (by decide), truncBits_ofNat hBatch64 (by decide),
          truncBits_ofNat hBase (by decide), truncBits_ofNat hStride64 (by decide),
          ← BitVec.ofNat_mul, Nat.mul_comm p.pageTableStride batch,
          truncBits_ofNat hProd (by decide), nf_shl, show (2 : Nat) ^ 2 = 4 from rfl,
          Nat.mul_comm (batch * p.pageTableStride) 4, truncBits_ofNat hBytes (by decide),
          ← BitVec.ofNat_add, truncBits_ofNat hBig (by decide)]
    | norm_bits [Nat.mod_eq_of_lt hCol, hColMul]

set_option maxRecDepth 100000 in
/-- The one-time steady prelude seeds the loop and preserves the launch-provided inputs. -/
theorem steadyPagePrelude {p : Params} {l : Launch} {m : Mem0} {g batch head trips warp tid : Nat}
    (hp : Pre p l m) (hb : batch < p.batch) (hQ : 0 < p.qLength batch) (hTid : tid < 512)
    {s : TState} (hs : At s 1386 ([(7181, b32 9), (1116, b32 (trips - 2))] ++
      warmStartFrame p l batch head trips warp tid)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 1396 ((7181, b32 9) :: steadyCacheFrame p l batch head trips warp tid) := by
  let F := [(7181, b32 9), (1116, b32 (trips - 2))] ++ warmStartFrame p l batch head trips warp tid
  obtain ⟨t, ht, hT⟩ := recurringLaneOffsetWithColumnAndRowCore (g := g) hTid 1 s
    (hs.mono ⟨holds_lookup hs.2.2.2.2 rfl, trivial⟩)
  obtain ⟨htA, htKeep⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) hs.1
    (by kernel_rfl) (by kernel_rfl) ht
  have hTF : Holds t.regs F :=
    holdsSchedulerFrame hs.2.2.2.2 htKeep (fun _ h => List.mem_map_of_mem h)
  obtain ⟨u, hu, hU⟩ := steadyPageBaseCore (g := g) (tid := tid) hp hb hQ t
    (hT.mono ⟨holds_lookup hTF rfl, holds_lookup hTF rfl, holds_lookup hTF rfl,
      hT.2.2.2.2.2.1, trivial⟩)
  let G := [(2130, b32 (primingLaneRow 0 tid)), (1147, b32 (8 * (tid % 8))),
    (1146,b32 (tid/8%8))] ++ F
  obtain ⟨huA, huKeep⟩ := loaderLinear (regs := G.map Prod.fst) (by decide) (by decide) hT.1
    (by kernel_rfl) (by kernel_rfl) hu
  have hUF := holdsSchedulerFrame
    (show Holds t.regs G from ⟨hT.2.2.2.2.1, hT.2.2.2.2.2.1, hT.2.2.2.2.2.2.1, hTF⟩)
    huKeep (fun _ h => List.mem_map_of_mem h)
  refine ⟨u, run_rtg (run_comp htA huA), hU.mono ?_⟩
  exact ⟨hUF.2.2.2.1, hUF.2.2.2.2.1, hUF.1, hUF.2.1, hU.2.2.2.2.2.1, hU.2.2.2.2.1,
    (holds_append ..).mpr ⟨hUF.2.2.2.2.2, hUF.2.2.1, trivial⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
