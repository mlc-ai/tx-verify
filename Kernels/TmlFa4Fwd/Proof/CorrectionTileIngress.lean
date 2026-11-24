-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionTileGeometry
public import Kernels.TmlFa4Fwd.Proof.CorrectionActiveCoordinates
public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
import Kernels.TmlFa4Fwd.Flow.Code.Part124

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue Prologue

noncomputable section

private theorem ptrSigned {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

private theorem cuQPointer {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {batch tile : Nat} (hb : batch < p.batch) :
    Seg kernel [] l g 2 7953
      [(7277, b32 batch), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase), (7276, b32 tile)]
      7955 (correctionInputFacts p batch tile) := by
  have hBatch : batch < 2 ^ 31 := hb.trans hp.shape.2.1
  have hRange := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRange
  have hBatch32 : batch % 4294967296 = batch := Nat.mod_eq_of_lt (by omega)
  have hFour : toSigned 32 (truncBits 32 (BitVec.ofInt 64 4)) = 4 := rfl
  intro t ht
  unfold correctionInputFacts
  seg_fp ht using
    norm_bits [hBatch32, ptrSigned hBatch, hFour, ← Int.natCast_mul, BitVec.ofInt_natCast]

set_option maxRecDepth 100000 in
private theorem ingressCore :
    ((kernel.code.drop 7932).take 23).all (fun ins => Assumptions.coreOp ins.op) = true := by
  kernel_rfl

private theorem ingressOut {l : Launch} {g : Nat} {t : TState}
    (hLo : 7932 ≤ t.pc) (hHi : t.pc < 7955) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  cases hc : kernel.code[t.pc]? with
  | none => simp only [out, hc]
  | some ins =>
    have hm : ins ∈ (kernel.code.drop 7932).take 23 := by
      apply List.mem_of_getElem? (i := t.pc - 7932)
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
      exact hc
    apply Assumptions.out_all_eq_nil _ _ _ hc (List.all_eq_true.mp ingressCore _ hm)
    all_goals
      simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites,
        Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
      omega

private theorem ingressLinear {l : Launch} {g pc n : Nat} {t u : TState} {regs : List Nat}
    (hLo : 7932 ≤ pc) (hHi : pc + n ≤ 7955) (ht : t.pc = pc)
    (hWrites : ((kernel.code.drop pc).take n).all
      (fun i => regs.all (fun r => !(writesRegs i.op).contains r)) = true)
    (hFallthrough : ((kernel.code.drop pc).take (n - 1)).all
      (fun i => schedulerFallsThrough i.op) = true)
    (hr : run kernel [] l g n t = some u) :
    run kernel Assumptions.all l g n t = some u ∧ ∀ r ∈ regs, u.regs r = t.regs r := by
  have hlo : pc ≤ t.pc := ht.ge
  have hhi : t.pc + n ≤ pc + n := by rw [ht]
  exact ⟨schedulerLocalTransport hFallthrough
    (fun ha hb => ingressOut (by omega) (by omega)) hr hlo hhi,
    fun _ h => schedulerLocalFrame hWrites hFallthrough hr hlo hhi h⟩

/-- A selected live tile retains the computed row geometry and ABI through the decoded
branch to its first cumulative-query read. -/
theorem correctionInputRun {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch lane : Nat} (hb : batch < p.batch)
    {t : TState} (ht : At t 7932 (correctionActiveTileFacts p l g batch lane)) :
    let thread := warpLane l g lane
    let tile := (assignedCoordinates p batch (g / l.block)).1
    ∃ u, run kernel Assumptions.all l thread 23 t = some u ∧
      At u 7955 (correctionInputFacts p batch tile ++ correctionTileGeometryFacts l thread true ++
        correctionActiveTileFacts p l g batch lane) := by
  dsimp only
  let thread := warpLane l g lane
  let tile := (assignedCoordinates p batch (g / l.block)).1
  let F := correctionActiveTileFacts p l g batch lane
  let G := correctionTileGeometryFacts l thread true
  have hCarry : Holds t.regs F := ht.2.2.2.2
  have hWarp := holds_lookup hCarry (show F.lookup 1062 = some (b32 (warpIndex l thread)) from rfl)
  have hTid := holds_lookup hCarry (show F.lookup 1612 = some (b32 (thread % l.block)) from rfl)
  have hRow := holds_lookup hCarry (show F.lookup 1613 = some (b32 (rowOf l thread)) from rfl)
  have hShared := holds_lookup hCarry (show F.lookup 2535 = some (b32 l.sharedBase) from rfl)
  obtain ⟨s, hs, hS⟩ := correctionTileGeometry hp thread true _
    (ht.mono ⟨hWarp, hTid, hRow, hShared, hCarry.2.2.2.1, trivial⟩)
  obtain ⟨hsAll, hFrame⟩ := ingressLinear (regs := F.map Prod.fst) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hs
  have hRemain := holdsSchedulerFrame hCarry hFrame (fun _ hm => List.mem_map_of_mem hm)
  have hAt : At s 7952 (G ++ F) := hS.mono ((holds_append _ _ _).2 ⟨hS.2.2.2.2, hRemain⟩)
  have hLive : s.regs 723 = some (.pred false) :=
    holds_lookup hAt.2.2.2.2 (show (G ++ F).lookup 723 = some (.pred false) from rfl)
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := thread)
    Flow.code_7952 false hAt hLive (by simp)
  obtain ⟨hvAll, _⟩ := ingressLinear (regs := []) (by decide) (by decide) hAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hv
  have hBatch := holds_lookup hV.2.2.2.2 (show (G ++ F).lookup 7277 = some (b32 batch) from rfl)
  have hBase := holds_lookup hV.2.2.2.2 (show (G ++ F).lookup 7502 = some (b64 p.cuQBase) from rfl)
  have hUsed := holds_lookup hV.2.2.2.2
    (show (G ++ F).lookup 7503 = some (b64 p.usedKBase) from rfl)
  have hTile := holds_lookup hV.2.2.2.2 (show (G ++ F).lookup 7276 = some (b32 tile) from rfl)
  have hEntryPc : v.pc = 7953 := hV.1
  obtain ⟨u, hu, hU⟩ := cuQPointer hp thread hb v (hV.mono ⟨hBatch, hBase, hUsed, hTile, trivial⟩)
  obtain ⟨huAll, huFrame⟩ := ingressLinear (regs := (G ++ F).map Prod.fst)
    (by decide) (by decide) hEntryPc (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hRemain' := holdsSchedulerFrame hV.2.2.2.2 huFrame
    (fun _ hm => List.mem_map_of_mem hm)
  refine ⟨u, run_comp (run_comp hsAll hvAll) huAll, hU.mono ?_⟩
  change Holds u.regs ((correctionInputFacts p batch tile ++ G) ++ F)
  rw [List.append_assoc]
  exact (holds_append _ _ _).2 ⟨hU.2.2.2.2, hRemain'⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
