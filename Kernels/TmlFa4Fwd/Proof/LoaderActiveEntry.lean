-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderTileHead
public import Kernels.TmlFa4Fwd.Proof.LoaderSwizzleSetup
public import Kernels.TmlFa4Fwd.Flow.Code.Part005

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The live loader controls and byte addresses at the first selected-request read. -/
def loaderActiveFacts (p : Params) (l : Launch) (tid batch : Nat) : List (Nat × Value) :=
  [(7515, b64 (p.cuQBase + 4 * batch)), (7503, b64 p.usedKBase),
   (7514, b64 (4 * batch)), (7297, b64 batch), (1798, b32 16), (103, .pred false),
   (7179, b32 0), (7180, b32 1), (7192, b32 1),
   (1081, b32 (tid / 8 % 8)), (1082, b32 (kvCopyColumn tid false)),
   (1083, b32 (kvCopyAddress l.sharedBase 0 tid 0 false)),
   (1084, b32 (kvCopyAddress l.sharedBase 0 tid 1 false))]

private theorem activeMask {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch : Nat} (hb : batch < p.batch) :
    Seg kernel [] l g 2 354 [(7170, b32 batch), (7144, b32 p.batch), (1663, b32 16)] 356
      [(771, .pred true), (7296, b64 16)] := by
  have hm := hp.shape.2.1
  have signed {n : Nat} (hn : n < 2 ^ 31) : toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
    simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left hn]
  intro t ht
  seg_fp ht using first
    | decide
    | simp only [truncBits_ofNat (show batch < 2 ^ 32 by omega) (by decide),
        truncBits_ofNat (show p.batch < 2 ^ 32 by omega) (by decide),
        compare, Option.getD_some, signed (hb.trans hm), signed hm, Int.ofNat_lt,
        hb, decide_true]

private theorem activeBeforeBranch (l : Launch) (g : Nat) :
    Seg kernel [] l g 4 371 [(771, .pred true)] 375
      [(102, .pred false), (7179, b32 0), (7180, b32 1), (7192, b32 1)] := by
  intro t ht
  seg_fp ht using rfl

private theorem activeFirstReadAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch : Nat} (hb : batch < p.batch) :
    Seg kernel [] l g 5 376 [(7296, b64 16), (7170, b32 batch), (7502, b64 p.cuQBase)] 381
      [(7515, b64 (p.cuQBase + 4 * batch)), (7514, b64 (4 * batch)),
        (7297, b64 batch), (1798, b32 16), (103, .pred false)] := by
  have ha := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at ha
  have hm := hp.shape.2.1
  have hSigned : toSigned 32 (BitVec.ofNat 64 batch) = (batch : Int) := by
    simp only [toSigned, toNat_ofNat_lt (show batch < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show batch < 2 ^ 32 by omega), ite_eq_left (hb.trans hm)]
  have hSize : toSigned 32 (truncBits 32 (BitVec.ofInt 64 4)) = 4 := rfl
  have hOff : (batch : Int) * 4 = ↑(4 * batch) := by omega
  intro t ht
  seg_fp ht using first
    | rfl
    | simp only [b64, kind_s_beq_s, ↓reduceIte,
        MemExt.extendBits_same, cvtIntBits, intOf, intSat, intBits, Bool.not_false,

        truncBits_ofNat (show batch < 2 ^ 32 by omega) (by decide),
        truncBits_ofNat (show batch < 2 ^ 64 by omega) (by decide), hSigned,
        hSize, hOff, BitVec.ofInt_natCast,
        truncBits_ofNat (show 4 * batch < 2 ^ 64 by omega) (by decide),
        truncBits_ofNat (show p.cuQBase < 2 ^ 64 by omega) (by decide), ← BitVec.ofNat_add,
        truncBits_ofNat (show p.cuQBase + 4 * batch < 2 ^ 64 by omega) (by decide)]

def activeEntryInputs (p : Params) (l : Launch) (tid batch tile head : Nat) :
    List (Nat × Value) :=
  [(7170, b32 batch), (7144, b32 p.batch), (1663, b32 16),
   (1061, b32 tid), (2535, b32 l.sharedBase), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
   (7168, b32 tile), (7169, b32 head)]

private def swizzleFacts (l : Launch) (tid : Nat) : List (Nat × Value) :=
  [(1081, b32 (tid / 8 % 8)), (1082, b32 (kvCopyColumn tid false)),
   (1083, b32 (kvCopyAddress l.sharedBase 0 tid 0 false)),
   (1084, b32 (kvCopyAddress l.sharedBase 0 tid 1 false))]

private theorem activeFrameBlock {extra F : List (Nat × Value)} {pc n : Nat}
    (hLo : 354 ≤ pc) (hHi : pc + n ≤ 381)
    (hExtra : ((kernel.code.drop 354).take 27).all
      (fun ins => (extra.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hF : ((kernel.code.drop pc).take n).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true) :
    ((kernel.code.drop pc).take n).all
      (fun ins => ((F ++ extra).map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) =
      true := by
  apply List.all_eq_true.mpr
  intro ins hm
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hm
  have hIndex : j < n :=
    (List.getElem?_eq_some_iff.mp hj).1.trans_le (List.length_take_le _ _)
  rw [List.getElem?_take_of_lt hIndex, List.getElem?_drop] at hj
  have hWide : ((kernel.code.drop 354).take 27)[pc + j - 354]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le (by omega : 354 ≤ pc + j)]
    exact hj
  have h := List.all_eq_true.mp hExtra ins (List.mem_of_getElem? hWide)
  rw [List.map_append, List.all_append, List.all_eq_true.mp hF ins hm, h]
  rfl

/-- The decoded active path initializes the stage-zero swizzle, keeps its selected
coordinates, and reaches the exact first cuQ load address and parity inputs. -/
theorem loaderActiveEntryFrame {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g tid batch tile head : Nat} (hTid : tid < 512) (hb : batch < p.batch)
    {t : TState} {extra : List (Nat × Value)}
    (hExtra : ((kernel.code.drop 354).take 27).all
      (fun ins => (extra.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (ht : At t 354 (activeEntryInputs p l tid batch tile head ++ extra)) :
    ∃ u, run kernel Assumptions.all l g 27 t = some u ∧
      At u 381 ((loaderActiveFacts p l tid batch ++
        [(7168, b32 tile), (7169, b32 head), (7170, b32 batch), (7296, b64 16)]) ++ extra) := by
  let f0 := activeEntryInputs p l tid batch tile head
  let f := f0 ++ extra
  let fr := f.map Prod.fst
  have hKeep {s u : TState} (hs : Holds s.regs f)
      (hf : ∀ r ∈ fr, u.regs r = s.regs r) : Holds u.regs f :=
    holdsSchedulerFrame hs hf (fun _ hm => List.mem_map_of_mem hm)
  obtain ⟨v, hv, hV⟩ := activeMask (g := g) hp hb t
    (ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1, trivial⟩)
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := fr) (by decide) (by decide) ht.1
    (activeFrameBlock (F := f0) (pc := 354) (n := 2) (by decide) (by decide) hExtra
      (by set_option maxRecDepth 100000 in kernel_rfl)) rfl hv
  have hfV := hKeep ht.2.2.2.2 hvFrame
  obtain ⟨w, hw, hW⟩ := initialKvSwizzle l g hTid hp.shared.2.1 v
    (hV.mono ⟨hfV.2.2.2.1, hfV.2.2.2.2.1, trivial⟩)
  let frame0 := (771, .pred true) :: (7296, b64 16) :: f0
  let frame := frame0 ++ extra
  obtain ⟨hwA, hwFrame⟩ := loaderLinear (regs := frame.map Prod.fst)
    (by decide) (by decide) hV.1
    (activeFrameBlock (F := frame0) (pc := 356) (n := 15) (by decide) (by decide) hExtra
      (by set_option maxRecDepth 100000 in kernel_rfl)) rfl hw
  have hWFrame : Holds w.regs frame := holdsSchedulerFrame
    (show Holds v.regs frame from ⟨hV.2.2.2.2.1, hV.2.2.2.2.2.1, hfV⟩) hwFrame
    (fun _ hm => List.mem_map_of_mem hm)
  obtain ⟨x, hx, hX⟩ := activeBeforeBranch l g w
    (hW.mono ⟨hWFrame.1, trivial⟩)
  let more0 := swizzleFacts l tid ++ frame0
  let more := more0 ++ extra
  have hMore : Holds w.regs more :=
    (holds_append w.regs (swizzleFacts l tid) frame).mpr ⟨hW.2.2.2.2, hWFrame⟩
  obtain ⟨hxA, hxFrame⟩ := loaderLinear (regs := more.map Prod.fst)
    (by decide) (by decide) hW.1
    (activeFrameBlock (F := more0) (pc := 371) (n := 4) (by decide) (by decide) hExtra
      (by set_option maxRecDepth 100000 in kernel_rfl)) rfl hx
  have hxMore := holdsSchedulerFrame hMore hxFrame (fun _ hm => List.mem_map_of_mem hm)
  let save0 := [(102, .pred false), (7179, b32 0), (7180, b32 1), (7192, b32 1)] ++ more0
  let save := save0 ++ extra
  have hxAt : At x 375 save :=
    hX.mono ⟨hX.2.2.2.2.1, hX.2.2.2.2.2.1, hX.2.2.2.2.2.2.1, hX.2.2.2.2.2.2.2.1, hxMore⟩
  obtain ⟨y, hy, hY⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_375 false hxAt hxAt.2.2.2.2.1 (by simp)
  obtain ⟨hyA, _⟩ := loaderLinear (regs := [])
    (by decide) (by decide) hxAt.1 (by set_option maxRecDepth 100000 in kernel_rfl) rfl hy
  have hyArgs : At y 376 [(7296, b64 16), (7170, b32 batch), (7502, b64 p.cuQBase)] := by
    apply hY.mono
    repeat' apply And.intro
    all_goals first | trivial | (apply holds_lookup hY.2.2.2.2; rfl)
  obtain ⟨u, hu, hU⟩ := activeFirstReadAddress hp hb y hyArgs
  obtain ⟨huA, huFrame⟩ := loaderLinear (regs := save.map Prod.fst) (by decide) (by decide) hyArgs.1
    (activeFrameBlock (F := save0) (pc := 376) (n := 5) (by decide) (by decide) hExtra
      (by set_option maxRecDepth 100000 in kernel_rfl)) rfl hu
  have hUCarry := holdsSchedulerFrame hY.2.2.2.2 huFrame (fun _ hm => List.mem_map_of_mem hm)
  refine ⟨u, run_comp (run_comp (run_comp (run_comp hvA hwA) hxA) hyA) huA, hU.mono ?_⟩
  simp only [loaderActiveFacts, List.cons_append, List.nil_append, Holds]
  repeat' apply And.intro
  all_goals first
    | apply holds_lookup hU.2.2.2.2; rfl
    | apply holds_lookup hUCarry; rfl
    | exact ((holds_append ..).mp hUCarry).2

/-- The decoded active path initializes the stage-zero swizzle, keeps its selected
coordinates, and reaches the exact first cuQ load address and parity inputs. -/
theorem loaderActiveEntry {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g tid batch tile head : Nat} (hTid : tid < 512) (hb : batch < p.batch)
    {t : TState} (ht : At t 354 (activeEntryInputs p l tid batch tile head)) :
    ∃ u, run kernel Assumptions.all l g 27 t = some u ∧
      At u 381 (loaderActiveFacts p l tid batch ++
        [(7168, b32 tile), (7169, b32 head), (7170, b32 batch), (7296, b64 16)]) :=
  loaderActiveEntryFrame hp hTid hb (extra := [])
    (by set_option maxRecDepth 100000 in kernel_rfl) ht

/-- At the first selected-request read, each lane holds its own swizzle and the common
scheduler coordinates. -/
def loaderActiveLaneFacts (p : Params) (l : Launch) (g batch lane : Nat) : List (Nat × Value) :=
  let tid := warpLane l g lane % l.block
  let pos := assignedCoordinates p batch (g / l.block)
  loaderActiveFacts p l tid batch ++
    [(7168, b32 pos.1), (7169, b32 pos.2), (7170, b32 batch), (7296, b64 16)]

/-- From the actual selected CTA offset and request tile count, each lane reaches the
first active request load with the same reversed tile and head as the scalar scheduler. -/
theorem loaderActiveWarpEntryPreserving {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g warp first batch shuffles votes : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 311 (loaderCoordinateFacts p l g warp first batch)
      shuffles votes ends) :
    ∃ result : SchedulerWarpAt l X g 381 (loaderActiveLaneFacts p l g batch) shuffles votes ends,
      result.pos = cur.pos ∧ result.before = cur.before := by
  apply cur.advanceLocalPreserving
  intro lane hl
  let thread := warpLane l g lane
  let tid := thread % l.block
  let pos := assignedCoordinates p batch (g / l.block)
  let carry := [(1663, b32 16), (1061, b32 tid), (2535, b32 l.sharedBase),
    (7502, b64 p.cuQBase), (7503, b64 p.usedKBase)]
  have ht := cur.checkpoint lane hl
  have hArgs : At (cur.state lane) 311
      [(1754, b32 (requestTiles p batch)), (7136, b32 p.heads),
       (1756, b32 (g / l.block - tilePrefix p batch * p.heads)), (7154, b32 800),
       (7144, b32 p.batch), (7170, b32 batch)] := by
    apply ht.mono
    repeat' apply And.intro
    all_goals first | trivial | (apply holds_lookup ht.2.2.2.2; rfl)
  have hCarry : Holds (cur.state lane).regs carry := by
    dsimp only [carry, Holds]
    repeat' apply And.intro
    all_goals first | trivial | (apply holds_lookup ht.2.2.2.2; rfl)
  obtain ⟨v, hv, hV⟩ := loaderTileHead hp thread hb hLo hHi (cur.state lane) hArgs
  obtain ⟨hvA, hVFrame⟩ := loaderLinear (regs := carry.map Prod.fst)
    (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hf := holdsSchedulerFrame hCarry hVFrame (fun _ hm => List.mem_map_of_mem hm)
  have hVEntry : At v 354 (activeEntryInputs p l tid batch pos.1 pos.2) := by
    apply hV.mono
    simp only [activeEntryInputs, Holds]
    repeat' apply And.intro
    all_goals first
      | trivial
      | (apply holds_lookup hV.2.2.2.2; rfl)
      | (apply holds_lookup hf; rfl)
  have hTid : tid < 512 := by rw [← hp.block]; exact Nat.mod_lt _ (by rw [hp.block]; decide)
  obtain ⟨u, hu, hU⟩ := loaderActiveEntry hp hTid hb hVEntry
  exact ⟨u, run_rtg (run_comp hvA hu), hU⟩

/-- The selected loader coordinate entry on a terminated trace. -/
theorem loaderActiveWarpEntry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g warp first batch shuffles votes : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (cur : SchedulerWarpAt l X g 311 (loaderCoordinateFacts p l g warp first batch)
      shuffles votes) :
    Nonempty (SchedulerWarpAt l X g 381 (loaderActiveLaneFacts p l g batch) shuffles votes) := by
  obtain ⟨result,_,_⟩ := loaderActiveWarpEntryPreserving hp hb hLo hHi cur
  exact ⟨result⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
