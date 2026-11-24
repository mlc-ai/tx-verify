-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionSelectedPrefix
public import Lemmas.Flow.Local
import Kernels.TmlFa4Fwd.Flow.Code.Part123

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- Registers for the correction warp's selected batch, tile count and CTA offset. -/
def correctionCoordinateFacts (p : Params) (l : Launch) (g first batch lane : Nat) :
    List (Nat × Value) :=
  [(5918, b32 (g / l.block - tilePrefix p batch * p.heads)),
   (5916, b32 (requestTiles p batch)), (7152, b32 p.batch), (7158, b32 800)] ++
    correctionPrefixFacts p l g first batch lane

private theorem scalarLoad {l : Launch} {g pc r word arg : Nat} {t : TState}
    {F : List (Nat × Value)}
    (ht : At t pc F) (hp : l.params (param arg) = some (BitVec.ofNat 64 word))
    (hw : word < 2 ^ 32) (hc : kernel.code[pc]? = some ⟨none, .mem
      { kind := .load, space := some .param, sem := .weak, elem := .int .b 32,
        addr := ⟨.param (param arg) false, 0⟩, dsts := [some r] }⟩) :
    run kernel [] l g 1 t = some (next (setReg t r (b32 word))) := by
  apply run_local hc rfl ht
  rw [execLocalA_nil, execLocal_mem rfl]
  simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq, hp,
    DType.width, MemExt.extendBits_same, pure, Except.pure, truncBits_ofNat hw (by decide)]
  rfl

set_option maxRecDepth 3000 in
private theorem correctionCoordinateParams {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} {t : TState} {F : List (Nat × Value)} (ht : At t 7882 F)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ 7158 ∧ pair.1 ≠ 7152) :
    ∃ u, run kernel Assumptions.all l g 2 t = some u ∧
      At u 7884 ((7152, b32 p.batch) :: (7158, b32 800) :: F) := by
  obtain ⟨hCap, h22⟩ := hp.values (22, 800) (by simp [Params.scalarWords])
  obtain ⟨hBatch, h19⟩ := hp.values (19, p.batch) (by simp [Params.scalarWords])
  let v := next (setReg t 7158 (b32 800))
  let u := next (setReg v 7152 (b32 p.batch))
  have hv : At v 7883 ((7158, b32 800) :: F) := ht.set fun pair hm => (hFresh pair hm).1
  have hu : At u 7884 ((7152, b32 p.batch) :: (7158, b32 800) :: F) := hv.set (by
    intro pair hm
    rcases List.mem_cons.mp hm with rfl | hf
    · decide
    · exact (hFresh pair hf).2)
  change l.params (param 22) = some (BitVec.ofNat 64 800) at h22
  change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at h19
  have decimal22 : toString (22 : Nat) = "22" := by
    rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
    simp only [show (22 / 10 : Nat) = 2 by decide, show (22 % 10 : Nat) = 2 by decide,
      Nat.repr_of_lt (n := 2) (by decide), Nat.digitChar_eq_two.mpr rfl]
    rfl
  have decimal19 : toString (19 : Nat) = "19" := by
    rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
    simp only [show (19 / 10 : Nat) = 1 by decide, show (19 % 10 : Nat) = 9 by decide,
      Nat.repr_of_lt (n := 1) (by decide), Nat.repr_of_lt (n := 9) (by decide),
      Nat.digitChar_eq_one.mpr rfl, Nat.digitChar_eq_nine.mpr rfl]
    rfl
  have hr : run kernel [] l g 2 t = some u := run_comp
    (scalarLoad (r := 7158) ht h22 hCap (by rw [Flow.code_7882, param, decimal22]; rfl))
    (scalarLoad (r := 7152) hv h19 hBatch (by rw [Flow.code_7883, param, decimal19]; rfl))
  exact ⟨u, (groupLinear (regs := []) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hr).1, hu⟩

variable {p : Params} {l : Launch}

private theorem correctionTileCountTemplate {m : Mem0} (hp : Pre p l m) {g idx count : Nat}
    (hIdx : idx < 32) {t : TState} (ht : At t 7884 [(1624, b32 idx), (7270, b32 count)]) :
    out kernel Assumptions.all l g t = .ev (.shfl .idx (b32 count) idx 31
      (fun value _ => next (setReg t 5916 value))) := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  rw [groupCoreOut (by rw [ht.1]; decide) (by rw [ht.1]; decide)]
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_7884) rfl rfl]
  change Out.ev (shflTmpl l g t .idx 5916 none (.reg 7270) (.reg 1624)
    (.imm 31) (.imm (-1))) = _
  have hIndex := readBits_b32 (g := g) (L := l) ht.2.2.2.2.1 (show idx < 2 ^ 32 by omega)
  have hMask : readBits l g t 32 (.imm (-1)) = .ok 4294967295#64 := rfl
  have hClamp : readBits l g t 32 (.imm 31) = .ok 31#64 := rfl
  simp only [shflTmpl, readValue, readReg, ht.2.2.2.2.2.1, hBlock, hMask, hClamp, hIndex,
    pure, Except.pure, toNat_ofNat_lt (show idx < 2 ^ 64 by omega)]
  rfl

private theorem selectedOffset {m : Mem0} (hp : Pre p l m) {g cta first batch : Nat}
    (hFirst : first ≤ batch) (hGroup : batch < first + 31) (hBatch : batch < p.batch)
    (hCta : tilePrefix p batch * p.heads ≤ cta) (hCtaMax : cta < tilePrefix p (batch + 1) * p.heads)
    :
    Seg kernel [] l g 2 7885 [(1623, b32 (tilePrefix p first * p.heads)),
      (7275, b32 (selectedGroupPrefix p first batch)), (1618, b32 cta)] 7887
      [(5918, b32 (cta - tilePrefix p batch * p.heads))] := by
  have hs : tilePrefix p first * p.heads + selectedGroupPrefix p first batch =
      tilePrefix p batch * p.heads := precedingGroupWork p hFirst hBatch hGroup
  have hWorkMax := hp.prefixWork_signed (show batch + 1 ≤ p.batch by omega)
  have hBaseMax : tilePrefix p batch * p.heads < 4294967296 := by omega
  have hPart1 : (tilePrefix p first * p.heads) % 4294967296 = tilePrefix p first * p.heads :=
    Nat.mod_eq_of_lt (by omega)
  have hPart2 : selectedGroupPrefix p first batch % 4294967296 =
      selectedGroupPrefix p first batch := Nat.mod_eq_of_lt (by omega)
  have hBase := Nat.mod_eq_of_lt hBaseMax
  have hCtaWord : cta % 4294967296 = cta := Nat.mod_eq_of_lt (by omega)
  intro t ht
  seg_fp ht using norm_bits [hPart1, hPart2, hs, hBase, hCtaWord]

private theorem coordinateParamsLane {m : Mem0} (hp : Pre p l m) {g first batch lane : Nat}
    {t : TState} (ht : At t 7882 (correctionPrefixFacts p l g first batch lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u 7884 ((7152,b32 p.batch) :: (7158,b32 800) ::
        correctionPrefixFacts p l g first batch lane) := by
  let facts := correctionPrefixFacts p l g first batch
  obtain ⟨u, hu, hU⟩ := correctionCoordinateParams hp (ht) (by
    intro pair hm
    have hMem := List.mem_map_of_mem (f := Prod.fst) hm
    constructor <;> intro he <;> rw [he] at hMem
    · exact (of_decide_eq_true rfl : 7158 ∉ (facts lane).map Prod.fst) hMem
    · exact (of_decide_eq_true rfl : 7152 ∉ (facts lane).map Prod.fst) hMem)
  exact ⟨u, run_rtg hu, hU⟩

private theorem coordinateOffsetLane {m : Mem0} (hp : Pre p l m) {g first batch lane : Nat}
    (hFirst : first ≤ batch) (hGroup : batch < first+31) (hBatch : batch < p.batch)
    (hCta : tilePrefix p batch*p.heads ≤ g/l.block)
    (hCtaMax : g/l.block < tilePrefix p (batch+1)*p.heads) {t : TState}
    (ht : At t 7885 ((5916,b32 (groupLaneTiles p first
      (shflSource .idx lane (batch-first) 31).1)) :: (7152,b32 p.batch) :: (7158,b32 800) ::
        correctionPrefixFacts p l g first batch lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u 7887 (correctionCoordinateFacts p l g first batch lane) := by
  let facts := correctionPrefixFacts p l g first batch
  let carry := fun lane => (7152,b32 p.batch) :: (7158,b32 800) :: facts lane
  let idx := batch-first
  have hIdx : idx < 31 := by omega
  let thread := warpLane l g lane
  let readFacts := (5916, b32 (groupLaneTiles p first (shflSource .idx lane idx 31).1)) ::
    carry lane
  change At t (7884 + 1) readFacts at ht
  have hBase := holds_lookup ht.2.2.2.2 (show readFacts.lookup 1623 =
    some (b32 (tilePrefix p first * p.heads)) from rfl)
  have hPrefix := holds_lookup ht.2.2.2.2 (show readFacts.lookup 7275 =
    some (b32 (selectedGroupPrefix p first batch)) from rfl)
  have hCtaReg := holds_lookup ht.2.2.2.2 (show readFacts.lookup 1618 =
    some (b32 (g / l.block)) from rfl)
  obtain ⟨u, hu, hU⟩ := selectedOffset (g := thread) hp hFirst hGroup hBatch hCta hCtaMax _
    (ht.mono ⟨hBase, hPrefix, hCtaReg, trivial⟩)
  have hx : groupLaneTiles p first idx = requestTiles p batch := by
    have hi : first + idx = batch := by dsimp [idx]; omega
    simp [groupLaneTiles, hIdx, hi, hBatch]
  have hCarry :
      Holds t.regs ((5916, b32 (requestTiles p batch)) :: carry lane) := by
    simpa only [readFacts, shflSource_idx lane (show idx < 32 by omega), hx] using ht.2.2.2.2
  obtain ⟨huA, huFrame⟩ := groupLinear (regs := readFacts.map Prod.fst)
    (by decide) (by decide) ht.1 (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hs := holdsSchedulerFrame hCarry huFrame (fun pair hm => by
    have he : (((5916, b32 (requestTiles p batch)) :: carry lane).map Prod.fst) =
        readFacts.map Prod.fst := rfl
    exact he ▸ List.mem_map_of_mem hm)
  exact ⟨u, run_rtg huA, hU.mono ⟨hU.2.2.2.2.1, hs⟩⟩

/-- The selected request's cache cap, batch count and exact tile count reach the live
correction coordinate registers. The CTA offset is measured from that request's first CTA. -/
theorem correctionSelectedCoordinatesTo {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g first batch shuffles votes : Nat}
    (hg : g < l.threads) (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) (hCta : tilePrefix p batch * p.heads ≤ g / l.block)
    (hCtaMax : g / l.block < tilePrefix p (batch + 1) * p.heads) {ends : Nat → Option TState}
    {src index : Nat} {target : Event}
    (cur : SchedulerWarpAt l X g 7882 (correctionPrefixFacts p l g first batch) shuffles votes ends)
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hTarget : 7884 < target.pc) :
    ∃ next : SchedulerWarpAt l X g 7887 (correctionCoordinateFacts p l g first batch)
      (shuffles + 1) votes ends, WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g next.pos src index target := by
  let facts := correctionPrefixFacts p l g first batch
  let carry := fun lane => (7152, b32 p.batch) :: (7158, b32 800) :: facts lane
  let idx := batch - first
  have hIdx : idx < 31 := by omega
  obtain ⟨ready, hPos⟩ : ∃ ready : SchedulerWarpAt l X g 7884 carry shuffles votes ends,
      ready.pos = cur.pos := by
    apply cur.advanceLocalAt
    exact fun lane hl => coordinateParamsLane hp (cur.checkpoint lane hl)
  have hFresh (lane : Nat) (_ : lane < 32) (pair : Nat × Value) (hm : pair ∈ carry lane) :
      pair.1 ≠ 5916 := by
    intro he
    have hMem := List.mem_map_of_mem (f := Prod.fst) hm
    rw [he] at hMem
    exact (of_decide_eq_true rfl : 5916 ∉ (carry lane).map Prod.fst) hMem
  have hOut (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (warpLane l g lane) (ready.state lane) =
        .ev (.shfl .idx (b32 (groupLaneTiles p first lane)) idx 31
          (fun v _ => next (setReg (ready.state lane) 5916 v))) := by
    have ht := ready.checkpoint lane hl
    have hIdxReg := holds_lookup ht.2.2.2.2
      (show (carry lane).lookup 1624 = some (b32 idx) from rfl)
    have hCount := holds_lookup ht.2.2.2.2 (show (carry lane).lookup 7270 =
      some (b32 (groupLaneTiles p first lane)) from rfl)
    exact correctionTileCountTemplate hp (by omega) (ht.mono ⟨hIdxReg, hCount, trivial⟩)
  obtain ⟨read, hRead⟩ := ready.consumeShuffleTo hp hX hg .idx
    (fun lane => b32 (groupLaneTiles p first lane)) (fun _ => idx) (fun _ => 31) hFresh hOut
    (by rw [hPos]; exact hProgress) hTarget
  obtain ⟨next, hNext⟩ := read.advanceLocalAt (G := correctionCoordinateFacts p l g first batch)
    (pc' := 7887) (fun lane hl =>
      coordinateOffsetLane hp hFirst hGroup hBatch hCta hCtaMax (read.checkpoint lane hl))
  exact ⟨next, fun h => hNext.symm ▸ hRead (hPos.symm ▸ h)⟩

/-- A maximal correction warp performs the selected tile-count exchange. -/
theorem correctionSelectedCoordinatesOfMaximal {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g first batch shuffles votes : Nat}
    (hg : g < l.threads) (hFirst : first ≤ batch) (hGroup : batch < first+31)
    (hBatch : batch < p.batch) (hCta : tilePrefix p batch*p.heads ≤ g/l.block)
    (hCtaMax : g/l.block < tilePrefix p (batch+1)*p.heads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7882 (correctionPrefixFacts p l g first batch)
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 7887 (correctionCoordinateFacts p l g first batch)
      (shuffles+1) votes ends) := by
  let facts := correctionPrefixFacts p l g first batch
  let carry := fun lane => (7152,b32 p.batch) :: (7158,b32 800) :: facts lane
  let idx := batch-first
  obtain ⟨ready⟩ := cur.advanceLocal (G := carry) (fun lane hl =>
    coordinateParamsLane hp (cur.checkpoint lane hl))
  have hFresh (lane : Nat) (_ : lane < 32) (pair : Nat × Value) (hm : pair ∈ carry lane) :
      pair.1 ≠ 5916 := by
    intro he
    have hMem := List.mem_map_of_mem (f := Prod.fst) hm
    rw [he] at hMem
    exact (of_decide_eq_true rfl : 5916 ∉ (carry lane).map Prod.fst) hMem
  have hOut (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (warpLane l g lane) (ready.state lane) =
        .ev (.shfl .idx (b32 (groupLaneTiles p first lane)) idx 31
          (fun v _ => next (setReg (ready.state lane) 5916 v))) := by
    have ht := ready.checkpoint lane hl
    have hIdxReg := holds_lookup ht.2.2.2.2
      (show (carry lane).lookup 1624 = some (b32 idx) from rfl)
    have hCount := holds_lookup ht.2.2.2.2 (show (carry lane).lookup 7270 =
      some (b32 (groupLaneTiles p first lane)) from rfl)
    exact correctionTileCountTemplate hp (by omega) (ht.mono ⟨hIdxReg, hCount, trivial⟩)
  obtain ⟨read⟩ := ready.consumeShuffle hp hMax hg .idx
    (fun lane => b32 (groupLaneTiles p first lane)) (fun _ => idx) (fun _ => 31) hFresh hOut
  exact read.advanceLocal (fun lane hl =>
    coordinateOffsetLane hp hFirst hGroup hBatch hCta hCtaMax (read.checkpoint lane hl))

end
end PTX.Kernels.TmlFa4Fwd.Correction
