-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueExit
public import Kernels.TmlFa4Fwd.Proof.EpilogueSchedule
public import Kernels.TmlFa4Fwd.Proof.ScheduleGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

private theorem signedIndex {n : Nat} (hn : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left hn]

/-- The conditional jumps in the drain scan, in instruction order. -/
def drainBranchSite : Fin 6 → Nat × Nat × Nat
  | 0 => (2993, 268, 3004)
  | 1 => (3028, 316, 3086)
  | 2 => (3036, 317, 3083)
  | 3 => (3040, 318, 3044)
  | 4 => (3050, 321, 3061)
  | 5 => (3085, 330, 3032)

theorem drainBranchRun (site : Fin 6) (l : Launch) (g : Nat) {facts : List (Nat × Value)}
    (t : TState) (take : Bool) (ht : At t (drainBranchSite site).1 facts)
    (hp : t.regs (drainBranchSite site).2.1 = some (.pred take)) :
    ∃ u, run kernel [] l g 1 t = some u ∧
      At u (if take then (drainBranchSite site).2.2 else (drainBranchSite site).1 + 1) facts := by
  have hc : kernel.code[(drainBranchSite site).1]? = some
      ⟨some ((drainBranchSite site).2.1, false), .bra (drainBranchSite site).2.2 false⟩ := by
    fin_cases site
    · exact Flow.code_2993
    · exact Flow.code_3028
    · exact Flow.code_3036
    · exact Flow.code_3040
    · exact Flow.code_3050
    · exact Flow.code_3085
  exact run_bra hc take ht hp (by simp)

/-- The first group reuses the request eligibility from entry and initializes the inactive lanes. -/
theorem drainFirstLaneTiles (l : Launch) (g : Nat) {begin finish : Nat} (active : Bool)
    (hBegin : begin < 2 ^ 32) (hFinish : finish < 2 ^ 32)
    (hMono : active = true → begin ≤ finish) (hLen : finish - begin < 2 ^ 30)
    (t : TState) (ht : At t 2991 [(7229, b32 begin), (2401, b32 finish), (268, .pred (!active))]) :
    ∃ u, run kernel [] l g (if active then 13 else 3) t = some u ∧ At u 3004
      [(7232, b32 (if active then (finish - begin + 255) / 256 else 0))] := by
  have hGate : Seg kernel [] l g 2 2991
      [(7229, b32 begin), (2401, b32 finish), (268, .pred (!active))] 2993
      [(1209, .bits 32 (truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin))),
       (7232, b32 0), (268, .pred (!active))] := by
    intro s hs
    seg_fp hs using first | rfl |
      simp only [truncBits_ofNat hBegin (by decide), truncBits_ofNat hFinish (by decide)]
  obtain ⟨u, hRun, hu⟩ := hGate t ht
  have hp : u.regs 268 = some (.pred (!active)) := holds_mem hu.2.2.2.2 (by simp)
  obtain ⟨v, hBra, hv⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2993 _ hu hp (by simp)
  cases active with
  | false =>
    exact ⟨v, run_comp hRun hBra, by at_select hv⟩
  | true =>
    have hWord : truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin) =
        BitVec.ofNat 64 (finish - begin) := by
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (show begin < 2 ^ 64 by omega) (hMono rfl),
        truncBits_ofNat (show finish - begin < 2 ^ 32 by omega) (by decide)]
    have hV : At v 2994 [(1209, b32 (finish - begin))] := by
      refine ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, ?_⟩
      have hR := holds_mem hv.2.2.2.2 (by simp :
        (1209, .bits 32 (truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin))) ∈ _)
      simpa [Holds, b32, hWord] using hR
    obtain ⟨w, hRound, hw⟩ := laneTileCount 2 l g hLen v hV
    exact ⟨w, run_comp (run_comp hRun hBra) hRound, hw⟩

/-- The first group either enters the tail selection or enters the repeated scan with a
sentinel above the CTA index. -/
theorem enterDrainSearch (l : Launch) (g : Nat) {cta limit : Nat} (hCta : cta + 1 < 2 ^ 32) :
    Seg kernel [] l g 3 3029 [(1072, b32 cta), (7236, b32 limit)] 3032
      [(1210, b32 (cta + 1)), (7235, b32 0), (7230, b32 limit)] := by
  intro t ht
  seg_fp ht using first | rfl | norm_bits

/-- A repeated drain scan advances by one 31-request group, clipping at the batch sentinel. -/
theorem drainGroupAdvance (l : Launch) (g : Nat) {first batch stop : Nat}
    (hNext : first + 31 < 2 ^ 31) (hBatch : batch < 2 ^ 31) :
    Seg kernel [] l g 4 3032 [(7235, b32 first), (7147, b32 batch), (1210, b32 stop)] 3036
      [(1211, b32 (first + 31)), (317, .pred (decide (batch ≤ first + 31))),
       (7235, b32 (min (first + 31) batch)), (7236, b32 stop)] := by
  intro t ht
  have hFirst32 : first < 2 ^ 32 := by omega
  have hNext32 : first + 31 < 2 ^ 32 := by omega
  have hBatch32 : batch < 2 ^ 32 := by omega
  have hLit : truncBits 32 (BitVec.ofInt 64 31) = BitVec.ofNat 64 31 := rfl
  seg_fp ht using
    (simp only [b32, hLit, ← BitVec.ofNat_add, truncBits_ofNat hFirst32 (by decide),
        truncBits_ofNat hNext32 (by decide), truncBits_ofNat hBatch32 (by decide),
        compare, Option.getD_some, signedIndex hNext, signedIndex hBatch, Int.ofNat_le,
        ge_iff_le]
     all_goals
       (by_cases h : first + 31 < batch
        · simp [Nat.min_eq_left (Nat.le_of_lt h)]
          omega
        · simp [Nat.min_eq_right (Nat.le_of_not_lt h)]
          omega))

/-- Each lane reads its prefix offset only up to and including the batch sentinel. -/
theorem drainLaneGate (l : Launch) (g : Nat) {first lane batch : Nat}
    (hIndex : first + lane < 2 ^ 31) (hBatch : batch < 2 ^ 31) :
    Seg kernel [] l g 3 3037 [(1211, b32 first), (1201, b32 lane), (7147, b32 batch)] 3040
      [(1212, b32 (first + lane)), (318, .pred (decide (batch < first + lane))),
       (7231, b32 0)] := by
  intro t ht
  have hIdx32 : first + lane < 2 ^ 32 := by omega
  have hFirst32 : first < 2 ^ 32 := by omega
  have hLane32 : lane < 2 ^ 32 := by omega
  have hBatch32 : batch < 2 ^ 32 := by omega
  seg_fp ht using
    first
    | rfl
    | simp only [b32, ← BitVec.ofNat_add, truncBits_ofNat hFirst32 (by decide),
        truncBits_ofNat hLane32 (by decide), truncBits_ofNat hIdx32 (by decide),
        truncBits_ofNat hBatch32 (by decide), compare, Option.getD_some,
        signedIndex hIndex, signedIndex hBatch, Int.ofNat_lt, gt_iff_lt]

variable {p : Params} {l : Launch} {m : Mem0}

/-- The signed multiply in a later group computes the byte offset of its cuQ lane. -/
theorem drainLaterAddress (hp : Pre p l m) (g : Nat) {index : Nat} (hi : index ≤ p.batch) :
    Seg kernel [] l g 2 3041 [(1212, b32 index), (7506, b64 p.cuQBase)] 3043
      [(7875, b64 (p.cuQBase + 4 * index))] := by
  have hb := hp.shape.2.1
  have hi31 : index < 2 ^ 31 := by omega
  have hi32 : index < 2 ^ 32 := by omega
  have hRegion := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRegion
  have hSum : p.cuQBase + 4 * index < 2 ^ 64 := by omega
  have hFour : toSigned 32 (4#64) = 4 := rfl
  intro t ht
  seg_fp ht using
    (simp only [truncBits_ofNat hi32 (by decide), signedIndex hi31]
     nf_simp
     rw [hFour]
     omega)

theorem drainLaterRead (hp : Pre p l m) (g : Nat) {index : Nat} (hi : index ≤ p.batch) (t : TState)
    (ht : At t 3043 [(7875, b64 (p.cuQBase + 4 * index))]) :
    out kernel [] l g t =
      .ev (.read { loc := globalLoc (p.cuQBase + 4 * index), size := 4 } (afterLoad t [7231])) := by
  have hReg : t.regs 7875 = some (b64 (p.cuQBase + 4 * index)) :=
    holds_mem ht.2.2.2.2 (by simp)
  have hRegion := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRegion
  have hAl := hp.alignment.2.2.2.2.2.2.2.2.1
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_3043) rfl rfl]
  change Out.ev (loadTmpl [] l g t .global false 32 [7231] 7875 0) = _
  exact congrArg Out.ev
    (loadTmpl_global (t := t) (w := 32) ht.2.1 hReg (by omega) (by decide) (by omega))

theorem drainLaterLastLane (l : Launch) (g : Nat) {lane : Nat} (hl : lane < 32) :
    Seg kernel [] l g 1 3044 [(1201, b32 lane)] 3045 [(319, .pred (decide (lane = 31)))] := by
  have h : lane < 2 ^ 32 := by omega
  have h64 : lane < 2 ^ 64 := by omega
  have h31 : (truncBits 32 (BitVec.ofInt 64 31)).toNat = 31 := rfl
  intro t ht
  seg_fp ht using
    (simp only [compare, Option.getD_some, truncBits_ofNat h (by decide),
      toNat_ofNat_lt h64, h31, Value.pred.injEq, decide_eq_decide]
     all_goals omega)

theorem drainLaterShuffle (hp : Pre p l m) (g : Nat) (t : TState) (cuq : Nat) (hpc : t.pc = 3045)
    (hf : t.fault = none) (hVal : t.regs 7231 = some (b32 cuq)) :
    out kernel [] l g t =
      .ev (.shfl .down (b32 cuq) 1 31 (fun value _ => next (setReg t 2422 value))) := by
  rw [out_event hf (by rw [hpc]; exact Flow.code_3045) rfl rfl]
  change Out.ev (shflTmpl l g t .down 2422 none (.reg 7231) (.imm 1) (.imm 31) (.imm (-1))) = _
  have hb : l.block % 32 = 0 := by rw [hp.block]
  simp [shflTmpl, readValue, readReg, hVal, hb, Value.bytes, b32, readBits, pure, Except.pure]
  rfl

/-- The later group skips the tile count for its sentinel and the lanes beyond the batch. -/
theorem drainLaterTileGate (l : Launch) (g : Nat) {index batch begin finish : Nat} (last : Bool)
    (hi : index < 2 ^ 31) (hb : batch < 2 ^ 31)
    (hBegin : begin < 2 ^ 32) (hFinish : finish < 2 ^ 32) :
    Seg kernel [] l g 4 3046
      [(2422, b32 finish), (7231, b32 begin), (1212, b32 index),
       (7147, b32 batch), (319, .pred last)] 3050
      [(1213, .bits 32 (truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin))),
       (7232, b32 0), (321, .pred (last || decide (batch ≤ index)))] := by
  have hi32 : index < 2 ^ 32 := by omega
  have hb32 : batch < 2 ^ 32 := by omega
  intro t ht
  seg_fp ht using
    first
    | rfl
    | simp only [truncBits_ofNat hBegin (by decide), truncBits_ofNat hFinish (by decide)]
    | simp only [compare, Option.getD_some, truncBits_ofNat hi32 (by decide),
        truncBits_ofNat hb32 (by decide), signedIndex hi, signedIndex hb, Int.ofNat_le]

theorem drainLaterLaneTiles (l : Launch) (g : Nat) {begin finish : Nat} (active : Bool)
    (hBegin : begin < 2 ^ 32)
    (hMono : active = true → begin ≤ finish) (hLen : finish - begin < 2 ^ 30)
    (t : TState) (ht : At t 3050
      [(1213, .bits 32 (truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin))),
       (7232, b32 0), (321, .pred (!active))]) :
    ∃ u, run kernel [] l g (if active then 11 else 1) t = some u ∧ At u 3061
      [(7232, b32 (if active then (finish - begin + 255) / 256 else 0))] := by
  have hp : t.regs 321 = some (.pred (!active)) := holds_mem ht.2.2.2.2 (by simp)
  obtain ⟨v, hBra, hv⟩ := drainBranchRun 4 l g t (!active) ht hp
  cases active with
  | false => exact ⟨v, hBra, by at_select hv⟩
  | true =>
    have hWord : truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin) =
        BitVec.ofNat 64 (finish - begin) := by
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (show begin < 2 ^ 64 by omega) (hMono rfl),
        truncBits_ofNat (show finish - begin < 2 ^ 32 by omega) (by decide)]
    have hV : At v 3051 [(1213, b32 (finish - begin))] := by
      refine ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, ?_⟩
      have hR := holds_mem hv.2.2.2.2 (by simp :
        (1213, .bits 32 (truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin))) ∈ _)
      simpa [Holds, b32, hWord] using hR
    obtain ⟨w, hRound, hw⟩ := laneTileCount 3 l g hLen v hV
    exact ⟨w, run_comp hBra hRound, hw⟩

/-- The drain scans both obtain their total by shuffling lane 31's full prefix. -/
theorem drainGroupTotalTemplate (hp : Pre p l m) (later : Bool) (g : Nat) (t : TState) (sum : Nat)
    (hpc : t.pc = (if later then 3081 else 3024)) (hf : t.fault = none)
    (hv : t.regs 7233 = some (b32 sum)) :
    out kernel [] l g t = .ev (.shfl .idx (b32 sum) 31 31
      (fun value _ => next (setReg t 7234 value))) := by
  have hc : kernel.code[t.pc]? = some ⟨none,
      .warp ⟨.shfl .idx, some (.int .b 32), [some 7234], [.reg 7233, .imm 31, .imm 31],
        some (.imm (-1))⟩⟩ := by
    rw [hpc]
    cases later
    · exact Flow.code_3024
    · exact Flow.code_3081
  rw [out_event hf hc rfl rfl]
  change Out.ev (shflTmpl l g t .idx 7234 none (.reg 7233) (.imm 31) (.imm 31) (.imm (-1))) = _
  have hb : l.block % 32 = 0 := by rw [hp.block]
  simp [shflTmpl, readValue, readReg, hv, hb, Value.bytes, b32, readBits, pure, Except.pure]
  rfl

theorem drainFirstLimit (l : Launch) (g : Nat) {count heads cta : Nat}
    (hc : count < 2 ^ 31) (hh : heads < 2 ^ 31) (hg : cta < 2 ^ 31)
    (htotal : count * heads < 2 ^ 31) :
    Seg kernel [] l g 3 3025 [(7234, b32 count), (7138, b32 heads), (1072, b32 cta)] 3028
      [(7236, b32 (count * heads)), (316, .pred (decide (cta < count * heads))),
       (7235, b32 0)] := by
  intro t ht
  have hCount : count < 2 ^ 32 := by omega
  have hHeads : heads < 2 ^ 32 := by omega
  have hCta : cta < 2 ^ 32 := by omega
  have hTotal : count * heads < 2 ^ 32 := by omega
  seg_fp ht using
    first
    | rfl
    | (simp only [b32, ← BitVec.ofNat_mul,
        truncBits_ofNat hCount (by decide), truncBits_ofNat hHeads (by decide),
        truncBits_ofNat hCta (by decide), truncBits_ofNat hTotal (by decide),
        compare, Option.getD_some, signedIndex hg, signedIndex htotal, Int.ofNat_lt])

/-- A repeated group continues to the next interval only when its end is at or below the CTA. -/
theorem drainGroupCheck (l : Launch) (g : Nat) {limit cta : Nat}
    (hLimit : limit < 2 ^ 31) (hCTA : cta < 2 ^ 31) :
    Seg kernel [] l g 2 3083 [(7236, b32 limit), (1072, b32 cta)] 3085
      [(330, .pred (decide (limit ≤ cta))), (7230, b32 limit), (7236, b32 limit)] := by
  intro t ht
  have hLimit32 : limit < 2 ^ 32 := by omega
  have hCTA32 : cta < 2 ^ 32 := by omega
  seg_fp ht using
    simp only [compare, Option.getD_some, truncBits_ofNat hLimit32 (by decide),
      truncBits_ofNat hCTA32 (by decide), signedIndex hLimit, signedIndex hCTA, Int.ofNat_le]

/-- Finishing a later scan reads the correct ending offset and takes exactly the PTX backedge
when the CTA lies beyond it. -/
theorem drainLaterGroupLimit (hp : Pre p l m) (g : Nat) {first count cta : Nat} (hc : cta < l.grid)
    (hCount : tilePrefix p first + count = tilePrefix p (min p.batch (first + 31))) (t : TState)
    (ht : At t 3082 [(7230, b32 (tilePrefix p first * p.heads)), (7234, b32 count),
      (7138, b32 p.heads), (1072, b32 cta)]) :
    let limit := tilePrefix p (min p.batch (first + 31)) * p.heads
    ∃ u, run kernel [] l g 4 t = some u ∧
      At u (if limit ≤ cta then 3032 else 3086) [(7230, b32 limit), (7236, b32 limit)] := by
  dsimp only
  let limit := tilePrefix p (min p.batch (first + 31)) * p.heads
  have hL := hp.prefixWork_signed (Nat.min_le_left p.batch (first + 31))
  have hHead := hp.heads_signed
  have hEqu : tilePrefix p first * p.heads + count * p.heads = limit := by
    rw [← Nat.add_mul, hCount]
  have hs0 := hp.shape.2.2.1
  have hPos : 1 ≤ p.heads := by simp [Params.heads]; omega
  have hMul := Nat.mul_le_mul_left count hPos
  rw [Nat.mul_one] at hMul
  have hCount32 : count < 2 ^ 32 := by omega
  have hCTA : cta < 2 ^ 31 := lt_trans hc hp.grid.2.2
  have hBase32 : tilePrefix p first * p.heads < 2 ^ 32 := by omega
  have hHead32 : p.heads < 2 ^ 32 := by omega
  have hLimit32 : limit < 2 ^ 32 := by omega
  have hLimit' : count * p.heads + tilePrefix p first * p.heads = limit := by omega
  have hs' : Seg kernel [] l g 1 3082
      [(7230, b32 (tilePrefix p first * p.heads)), (7234, b32 count),
        (7138, b32 p.heads), (1072, b32 cta)] 3083
      [(7236, b32 limit), (1072, b32 cta)] := by
    intro v hv
    seg_fp hv using
      simp only [b32, ← BitVec.ofNat_mul, ← BitVec.ofNat_add,
        truncBits_ofNat hBase32 (by decide), truncBits_ofNat hCount32 (by decide),
        truncBits_ofNat hHead32 (by decide), hLimit', truncBits_ofNat hLimit32 (by decide)]
  obtain ⟨u, hr, hu⟩ := (hs'.comp (drainGroupCheck l g hL hCTA)) t ht
  have hPred : u.regs 330 = some (.pred (decide (limit ≤ cta))) :=
    holds_mem hu.2.2.2.2 (by simp)
  obtain ⟨v, hbra, hv⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_3085 _ hu hPred (by simp)
  refine ⟨v, run_comp hr hbra, ?_⟩
  have hp : v.pc = (if limit ≤ cta then 3032 else 3086) := by
    by_cases h : limit ≤ cta <;> simpa [h] using hv.1
  have hFinal : v.regs 7230 = some (b32 limit) := holds_mem hv.2.2.2.2 (by simp)
  exact ⟨hp, hv.2.1, hv.2.2.1, hv.2.2.2.1, hFinal, hv.2.2.2.2.2.2.1, trivial⟩

end

end PTX.Kernels.TmlFa4Fwd.Epilogue
