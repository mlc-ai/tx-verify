-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSelectedPrefix
public import Lemmas.Flow.Local

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- Registers for the loader's selected batch, tile count and CTA offset. -/
def loaderCoordinateFacts (p : Params) (l : Launch) (g warp first batch lane : Nat) :
    List (Nat × Value) :=
  [(1756, b32 (g / l.block - tilePrefix p batch * p.heads)),
   (1754, b32 (requestTiles p batch)), (7144, b32 p.batch), (7154, b32 800)] ++
    loaderPrefixFacts p l g warp first batch lane

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
private theorem loaderCoordinateParams {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} {t : TState} {F : List (Nat × Value)} (ht : At t 306 F)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ 7154 ∧ pair.1 ≠ 7144) :
    ∃ u, run kernel Assumptions.all l g 2 t = some u ∧
      At u 308 ((7144, b32 p.batch) :: (7154, b32 800) :: F) := by
  obtain ⟨hCap, h22⟩ := hp.values (22, 800) (by simp [Params.scalarWords])
  obtain ⟨hBatch, h19⟩ := hp.values (19, p.batch) (by simp [Params.scalarWords])
  let v := next (setReg t 7154 (b32 800))
  let u := next (setReg v 7144 (b32 p.batch))
  have hv : At v 307 ((7154, b32 800) :: F) := ht.set fun pair hm => (hFresh pair hm).1
  have hu : At u 308 ((7144, b32 p.batch) :: (7154, b32 800) :: F) := hv.set (by
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
    (scalarLoad (r := 7154) ht h22 hCap (by rw [Flow.code_306, param, decimal22]; rfl))
    (scalarLoad (r := 7144) hv h19 hBatch (by rw [Flow.code_307, param, decimal19]; rfl))
  exact ⟨u, (loaderLinear (regs := []) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hr).1, hu⟩

/-- The decoded indexed broadcast reads the known lane count. -/
theorem loaderTileCountTemplate {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g idx count : Nat} (hIdx : idx < 32) {t : TState}
    (ht : At t 308 [(1080, b32 idx), (7162, b32 count)]) :
    out kernel Assumptions.all l g t = .ev (.shfl .idx (b32 count) idx 31
      (fun value _ => next (setReg t 1754 value))) := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  rw [loaderOutCore (by rw [ht.1]; decide) (by rw [ht.1]; decide)]
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_308) rfl rfl]
  change Out.ev (shflTmpl l g t .idx 1754 none (.reg 7162) (.reg 1080)
    (.imm 31) (.imm (-1))) = _
  have hIndex := readBits_b32 (g := g) (L := l) ht.2.2.2.2.1 (show idx < 2 ^ 32 by omega)
  have hMask : readBits l g t 32 (.imm (-1)) = .ok 4294967295#64 := rfl
  have hClamp : readBits l g t 32 (.imm 31) = .ok 31#64 := rfl
  simp only [shflTmpl, readValue, readReg, ht.2.2.2.2.2.1, hBlock, hMask, hClamp, hIndex,
    pure, Except.pure, toNat_ofNat_lt (show idx < 2 ^ 64 by omega)]
  rfl

private theorem selectedOffset {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g cta first batch : Nat} (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) (hCta : tilePrefix p batch * p.heads ≤ cta)
    (hCtaMax : cta < tilePrefix p (batch + 1) * p.heads) :
    Seg kernel [] l g 2 309 [(1079, b32 (tilePrefix p first * p.heads)),
      (7167, b32 (selectedGroupPrefix p first batch)), (1072, b32 cta)] 311
      [(1756, b32 (cta - tilePrefix p batch * p.heads))] := by
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

/-- ABI additions retained while broadcasting the selected request's tile count. -/
def loaderCoordCarry (p : Params) (l : Launch) (g warp first batch lane : Nat) :
    List (Nat × Value) :=
  (7144,b32 p.batch) :: (7154,b32 800) :: loaderPrefixFacts p l g warp first batch lane

/-- Local parameter decoding prepares the selected-tile broadcast. -/
theorem loaderCoordinatesPrepare {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g warp first batch lane : Nat} {t : TState}
    (ht : At t 306 (loaderPrefixFacts p l g warp first batch lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u 308 (loaderCoordCarry p l g warp first batch lane) := by
  let facts := loaderPrefixFacts p l g warp first batch
  obtain ⟨u, hu, hU⟩ := loaderCoordinateParams hp ht (by
    intro pair hm
    have hMem := List.mem_map_of_mem (f := Prod.fst) hm
    constructor <;> intro he <;> rw [he] at hMem
    · exact (of_decide_eq_true rfl : 7154 ∉ (facts lane).map Prod.fst) hMem
    · exact (of_decide_eq_true rfl : 7144 ∉ (facts lane).map Prod.fst) hMem)
  exact ⟨u, run_rtg hu, hU⟩

/-- A returned tile-count broadcast determines the decoded offset relative to its request. -/
theorem loaderCoordinatesReturned {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g warp first batch lane : Nat} (hg : g < l.threads) (hl : lane < 32)
    (hFirst : first ≤ batch) (hGroup : batch < first + 31) (hBatch : batch < p.batch)
    (hCta : tilePrefix p batch * p.heads ≤ g/l.block)
    (hCtaMax : g/l.block < tilePrefix p (batch+1) * p.heads)
    {t : TState} (ht : At t 309
      ((1754,b32 (groupLaneTiles p first (shflSource .idx lane (batch-first) 31).1)) ::
        loaderCoordCarry p l g warp first batch lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u 311 (loaderCoordinateFacts p l g warp first batch lane) := by
  let carry := loaderCoordCarry p l g warp first batch
  let idx := batch-first
  have hIdx : idx < 31 := by omega
  let thread := warpLane l g lane
  let readFacts := (1754, b32 (groupLaneTiles p first (shflSource .idx lane idx 31).1)) ::
    carry lane
  change At t (308 + 1) readFacts at ht
  have hBase := holds_lookup ht.2.2.2.2 (show readFacts.lookup 1079 =
    some (b32 (tilePrefix p first * p.heads)) from rfl)
  have hPrefix := holds_lookup ht.2.2.2.2 (show readFacts.lookup 7167 =
    some (b32 (selectedGroupPrefix p first batch)) from rfl)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hThreadCta : thread / l.block = g / l.block :=
    (Step.sameWarp_lane hBlock hg hl).1.1.2.2.symm
  have hCtaReg := holds_lookup ht.2.2.2.2 (show readFacts.lookup 1072 =
    some (b32 (thread / l.block)) from rfl)
  rw [hThreadCta] at hCtaReg
  obtain ⟨u, hu, hU⟩ := selectedOffset (g := thread) hp hFirst hGroup hBatch hCta hCtaMax _
    (ht.mono ⟨hBase, hPrefix, hCtaReg, trivial⟩)
  have hx : groupLaneTiles p first idx = requestTiles p batch := by
    have hi : first + idx = batch := by dsimp [idx]; omega
    simp [groupLaneTiles, hIdx, hi, hBatch]
  have hCarry :
      Holds t.regs ((1754, b32 (requestTiles p batch)) :: carry lane) := by
    simpa only [readFacts, shflSource_idx lane (show idx < 32 by omega), hx] using ht.2.2.2.2
  obtain ⟨huA, huFrame⟩ := loaderLinear (regs := readFacts.map Prod.fst)
    (by decide) (by decide) ht.1 (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu
  have hs := holdsSchedulerFrame hCarry huFrame (fun pair hm => by
    have he : (((1754, b32 (requestTiles p batch)) :: carry lane).map Prod.fst) =
        readFacts.map Prod.fst := rfl
    exact he ▸ List.mem_map_of_mem hm)
  exact ⟨u, run_rtg huA, hU.mono ⟨hU.2.2.2.2.1, hs⟩⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g warp first batch shuffles votes : Nat}
    (hg : g < l.threads) (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) (hCta : tilePrefix p batch * p.heads ≤ g / l.block)
include hp hX hg hFirst hGroup hBatch hCta

/-- The selected request's cache cap, batch count and exact tile count reach the live
loader coordinate registers. The CTA offset is measured from that request's first CTA. -/
theorem loaderSelectedCoordinatesTo (hCtaMax : g / l.block < tilePrefix p (batch + 1) * p.heads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 306 (loaderPrefixFacts p l g warp first batch) shuffles votes ends)
    {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 308 < target.pc) :
    ∃ next : SchedulerWarpAt l X g 311 (loaderCoordinateFacts p l g warp first batch)
      (shuffles + 1) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g next.pos src index target := by
  let carry := loaderCoordCarry p l g warp first batch
  let idx := batch - first
  have hIdx : idx < 31 := by omega
  obtain ⟨ready, hReadyPos⟩ := cur.advanceLocalAt (pc' := 308) (G := carry) (fun lane hl =>
    loaderCoordinatesPrepare hp (cur.checkpoint lane hl))
  have hFresh (lane : Nat) (_ : lane < 32) (pair : Nat × Value) (hm : pair ∈ carry lane) :
      pair.1 ≠ 1754 := by
    intro he
    have hMem := List.mem_map_of_mem (f := Prod.fst) hm
    rw [he] at hMem
    exact (of_decide_eq_true rfl : 1754 ∉ (carry lane).map Prod.fst) hMem
  have hOut (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (warpLane l g lane) (ready.state lane) =
        .ev (.shfl .idx (b32 (groupLaneTiles p first lane)) idx 31
          (fun v _ => next (setReg (ready.state lane) 1754 v))) := by
    have ht := ready.checkpoint lane hl
    have hIdxReg := holds_lookup ht.2.2.2.2
      (show (carry lane).lookup 1080 = some (b32 idx) from rfl)
    have hCount := holds_lookup ht.2.2.2.2 (show (carry lane).lookup 7162 =
      some (b32 (groupLaneTiles p first lane)) from rfl)
    exact loaderTileCountTemplate hp (by omega) (ht.mono ⟨hIdxReg, hCount, trivial⟩)
  have hBefore : WarpFollowsEvent l X g cur.pos src index target →
      WarpFollowsEvent l X g ready.pos src index target := fun h => hReadyPos.symm ▸ h
  obtain ⟨read, hAdvance⟩ := ready.consumeShuffleTo hp hX hg .idx
    (fun lane => b32 (groupLaneTiles p first lane)) (fun _ => idx) (fun _ => 31) hFresh hOut
    (hProgress.imp_right hBefore) hPc
  obtain ⟨result, hPos⟩ := read.advanceLocalAt
    (pc' := 311) (G := loaderCoordinateFacts p l g warp first batch) (fun lane hl =>
      loaderCoordinatesReturned hp hg hl hFirst hGroup hBatch hCta hCtaMax
        (read.checkpoint lane hl))
  exact ⟨result, fun h => hPos.symm ▸ hAdvance (hBefore h)⟩

/-- The verified selected coordinates on a terminated trace. -/
theorem loaderSelectedCoordinates (hCtaMax : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (cur : SchedulerWarpAt l X g 306 (loaderPrefixFacts p l g warp first batch) shuffles votes) :
    Nonempty (SchedulerWarpAt l X g 311 (loaderCoordinateFacts p l g warp first batch)
      (shuffles + 1) votes) := by
  obtain ⟨next, _⟩ := loaderSelectedCoordinatesTo hp hX hg hFirst hGroup hBatch hCta hCtaMax cur
    (src := 0) (index := 0) (target := ⟨309, .exit⟩) (.inl (fun _ _ => rfl)) (by decide)
  exact ⟨next⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
