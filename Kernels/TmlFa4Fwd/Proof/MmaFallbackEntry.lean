-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaScanCounter
import Kernels.TmlFa4Fwd.Proof.MmaFirstRoute
import Lemmas.Kernel.ReadValue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue

/-- Launch registers that survive the scheduler's group search. -/
def fallbackAbi (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(1180, b32 (laneOf l g)), (7139, b32 p.heads), (2535, b32 l.sharedBase),
    (7502, b64 p.cuQBase), (7506, b64 p.cuQBase), (7503, b64 p.usedKBase)]

private theorem fallbackSeedCore (l : Launch) (g : Nat) {cta total : Nat}
    (hCta : cta + 1 < 2 ^ 31) :
    Seg kernel [] l g 3 1985 [(1072, b32 cta), (7200, b32 total)] 1988
      [(1182, b32 (cta + 1)), (7199, b32 0), (7194, b32 total)] := by
  intro t ht
  seg_fp ht using norm_bits

/-- A CTA beyond the first cutoff seeds the fallback loop with the first group's work
and retains the launch arguments for all subsequent groups. -/
theorem initializeFallbackSearch {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (hg : g < l.threads) {t : TState} :
    let total := tilePrefix p (min p.batch 31) * p.heads
    let cta := g / l.block
    At t 1985 ([(1072, b32 cta), (7203, b32 p.batch), (7200, b32 total)] ++ fallbackAbi p l g) →
    ∃ u, run kernel Assumptions.all l g 3 t = some u ∧
      At u 1988 (groupScanFacts .select 0 p.batch cta ++
        (7194, b32 total) :: fallbackAbi p l g) := by
  dsimp only
  intro ht
  have hGrid : g / l.block < l.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
  have hCta := (Nat.succ_le_of_lt hGrid).trans_lt hp.grid.2.2
  let total := tilePrefix p (min p.batch 31) * p.heads
  let F := [(1072, b32 (g / l.block)), (7203, b32 p.batch)] ++ fallbackAbi p l g
  obtain ⟨u, hu, hU⟩ := fallbackSeedCore l g hCta t (by at_select ht)
  have hWrites : ((kernel.code.drop 1985).take 3).all
      (fun i => (F.map Prod.fst).all fun r => !(writesRegs i.op).contains r) = true := by
    change ((kernel.code.drop 1985).take 3).all (fun i =>
      [1072, 7203, 1180, 7139, 2535, 7502, 7506, 7503].all
        (fun r => !(writesRegs i.op).contains r)) = true
    decide +kernel
  have hStraight : ((kernel.code.drop 1985).take 2).all
      (fun i => schedulerFallsThrough i.op) = true := by decide +kernel
  have hAt : At t 1985 F := ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.2⟩
  have hKeep := holdsSchedulerFrame hAt.2.2.2.2
    (fun _ hr => schedulerLocalFrame hWrites hStraight hu ht.1.ge (by rw [ht.1]) hr)
    (fun _ hm => List.mem_map_of_mem hm)
  exact ⟨u, localRun (by decide) (by decide) ht.1 hStraight hu,
    hU.mono ⟨hU.2.2.2.2.2.1, hKeep.2.1, hU.2.2.2.2.1, hKeep.1,
      hU.2.2.2.2.2.2.1, hKeep.2.2⟩⟩

/-- A nonexhausted fallback group advances the cumulative-offset base for its
lane-indexed reads and retains the previous groups' work. -/
theorem advanceFallbackSearch {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g old : Nat} (hMore : old + 31 < p.batch) {t : TState} :
    let cutoff := tilePrefix p (old + 31) * p.heads
    let cta := g / l.block
    let frame := (7194, b32 cutoff) :: fallbackAbi p l g
    At t 1988 (groupScanFacts .select old p.batch cta ++ frame) →
    ∃ u, run kernel Assumptions.all l g 5 t = some u ∧
      At u 1993 ([(1183, b32 (old + 31)), (7200, b32 (cta + 1))] ++
        groupScanFacts .select (old + 31) p.batch cta ++ frame) := by
  dsimp only
  intro ht
  have hSigned := hMore.trans hp.shape.2.1
  have hFrame : ((kernel.code.drop 1988).take 5).all
      (fun i => [7194, 1180, 7139, 2535, 7502, 7506, 7503].all
        (fun r => !(writesRegs i.op).contains r)) = true := by decide +kernel
  let frame := (7194, b32 (tilePrefix p (old + 31) * p.heads)) :: fallbackAbi p l g
  obtain ⟨u, hu, hU⟩ := advanceGroupScanPreserving (l := l) (g := g) (F := frame)
    .select hSigned hp.shape.2.1 hFrame ht
  exact ⟨u, hu, by
    simpa only [List.cons_append, List.nil_append, scanSite, ite_eq_right (Nat.not_le_of_gt hMore),
      Nat.min_eq_left hMore.le] using hU⟩

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

/-- The fallback scheduler computes a lane's cumulative-offset index and masks
the read when its index exceeds the last offset supplied by the launch. -/
theorem fallbackCuQReadGate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {first lane : Nat} (hFirst : first ≤ p.batch) (hLane : lane < 32) :
    Seg kernel [] l g 3 1993 [(1183, b32 first), (1180, b32 lane), (7203, b32 p.batch)]
      1996 [(1184, b32 (first + lane)), (348, .pred (decide (p.batch < first + lane))),
        (7195, b32 0)] := by
  intro t ht
  have hShape := hp.shape.2.2.2.2.2
  have hb := hp.shape.2.1
  have hi : first + lane < 2 ^ 31 := by omega
  have hi32 : first + lane < 2 ^ 32 := by omega
  have hf32 : first < 2 ^ 32 := by omega
  have hl32 : lane < 2 ^ 32 := by omega
  have hb32 : p.batch < 2 ^ 32 := by omega
  seg_fp ht using
    first
    | rfl
    | simp only [b32, ← BitVec.ofNat_add, truncBits_ofNat hf32 (by decide),
        truncBits_ofNat hl32 (by decide), truncBits_ofNat hi32 (by decide),
        truncBits_ofNat hb32 (by decide), compare, Option.getD_some,
        signedWord hi, signedWord hb, Int.ofNat_lt, gt_iff_lt]

/-- A live fallback lane forms the protected global address of its cumulative Q offset. -/
theorem fallbackCuQReadAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {index : Nat} (hi : index ≤ p.batch) :
    Seg kernel [] l g 2 1997 [(1184, b32 index), (7506, b64 p.cuQBase)] 1999
      [(7879, b64 (p.cuQBase + 4 * index))] := by
  intro t ht
  have hb := hp.shape.2.1
  have hRegion := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRegion
  have h31 : index < 2 ^ 31 := by omega
  have h32 : index < 2 ^ 32 := by omega
  have hBase : p.cuQBase < 2 ^ 64 := by omega
  have hOff : 4 * index < 2 ^ 64 := by omega
  have hAddr : p.cuQBase + 4 * index < 2 ^ 64 := by omega
  have hFour : toSigned 32 (truncBits 32 (BitVec.ofInt 64 4)) = 4 := rfl
  have hProduct : (index : Int) * 4 = ((4 * index : Nat) : Int) := by push_cast; omega
  seg_fp ht using simp only [b64, kind_s_beq_s, ↓reduceIte, hFour, signedWord h31,
    truncBits_ofNat h32 (by decide), truncBits_ofNat hOff (by decide),
    truncBits_ofNat hBase (by decide), hProduct, BitVec.ofInt_natCast, ← BitVec.ofNat_add,
    truncBits_ofNat hAddr (by decide)]

/-- The active branch reads the actual cumulative-offset word at its decoded address. -/
theorem fallbackCuQReadOut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g index : Nat} {t : TState} (hi : index ≤ p.batch)
    (ht : At t 1999 [(7879, b64 (p.cuQBase + 4 * index))]) :
    out kernel Assumptions.all l g t =
      .ev (.read {loc := globalLoc (p.cuQBase + 4 * index), size := 4} (afterLoad t [7195])) := by
  have hRegion := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRegion
  have hSum : p.cuQBase + 4 * index < 2 ^ 64 := by omega
  have hAlign := hp.alignment.2.2.2.2.2.2.2.2.1
  rw [out_eq_core (by rw [ht.1]; decide) (by rw [ht.1]; decide),
    out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_1999) rfl rfl]
  change Out.ev (loadTmpl [] l g t .global false 32 [7195] 7879 0) = _
  exact congrArg Out.ev (loadTmpl_global (t := t) (w := 32)
    ht.2.1 ht.2.2.2.2.1 hSum (by decide) (by omega))

end PTX.Kernels.TmlFa4Fwd.Mma
