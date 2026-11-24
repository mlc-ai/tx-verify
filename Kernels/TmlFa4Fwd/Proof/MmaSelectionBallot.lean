-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaFirstRoute
import Kernels.TmlFa4Fwd.Proof.MmaGeometry
import Kernels.TmlFa4Fwd.Proof.LoaderBatchSelect
import Kernels.TmlFa4Fwd.Flow.Code.Part032

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left h]

/-- The decoded ballot comparison marks precisely the lanes preceding the selected batch. -/
theorem selectedGroupBallot {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {first batch lane cta : Nat} (hFirst : first ≤ batch)
    (hGroup : batch < first + 31) (hBatch : batch < p.batch) (hLane : lane < 32)
    (hLo : tilePrefix p batch * p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch + 1) * p.heads) :
    Seg kernel [] l g 4 2046
      [(7198, b32 (∑ i ∈ Finset.range 32, groupLaneTiles p first i)),
       (7197, b32 (∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i)),
       (7200, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)),
       (7139, b32 p.heads), (1072, b32 cta)] 2050
      [(1186, b32 (tilePrefix p first * p.heads)),
       (362, .pred (decide (first + lane < batch)))] := by
  let start := tilePrefix p first * p.heads
  let tail := tilePrefix p (min p.batch (first + 31)) * p.heads
  let total := ∑ i ∈ Finset.range 32, groupLaneTiles p first i
  let part := ∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i
  have hStart : start < 2 ^ 31 := hp.prefixWork_signed (by omega)
  have hTail : tail < 2 ^ 31 := hp.prefixWork_signed (Nat.min_le_left _ _)
  have hPart : part * p.heads + start < 2 ^ 31 := by
    have h := congrArg (fun n => n * p.heads) (groupTiles_eq p (by omega : first ≤ p.batch)
      (by omega : lane + 1 ≤ 32))
    change (tilePrefix p first + part) * p.heads = _ at h
    rw [Nat.add_mul, Nat.add_comm] at h
    exact h ▸ hp.prefixWork_signed (Nat.min_le_left _ _)
  have hTotal : total * p.heads + start = tail := by
    have h := congrArg (fun n => n * p.heads) (groupTiles_eq p (by omega : first ≤ p.batch)
      (by decide : 32 ≤ 32))
    change (tilePrefix p first + total) * p.heads = tail at h
    rw [Nat.add_mul, Nat.add_comm] at h
    exact h
  have hBallot : part * p.heads + start ≤ cta ↔ first + lane < batch := by
    simpa only [Nat.add_mul, Nat.add_comm, start] using
      groupBallot_iff p hFirst hGroup hBatch hLane hLo hHi
  have hHeads := hp.heads_signed
  have hCta : cta < 2 ^ 31 := lt_trans hHi (hp.prefixWork_signed (by omega))
  have hPos : 0 < p.heads := by unfold Params.heads; have := hp.shape.2.2.1; omega
  have hTotal32 : total < 2 ^ 32 := by have := Nat.le_mul_of_pos_right total hPos; omega
  have hPart32 : part < 2 ^ 32 := by have := Nat.le_mul_of_pos_right part hPos; omega
  have hTail32 : tail < 2 ^ 32 := by omega
  have hHeads32 : p.heads < 2 ^ 32 := by omega
  have hCta32 : cta < 2 ^ 32 := by omega
  have hTotalWork32 : total * p.heads < 2 ^ 32 := by omega
  have hStart32 : start < 2 ^ 32 := by omega
  have hPartWork32 : part * p.heads + start < 2 ^ 32 := by omega
  have hSub : tail - total * p.heads = start := by omega
  intro t ht
  change At t 2046
    [(7198, b32 total), (7197, b32 part), (7200, b32 tail), (7139, b32 p.heads), (1072, b32 cta)]
    at ht
  change ∃ u, run kernel [] l g 4 t = some u ∧
    At u 2050 [(1186, b32 start), (362, .pred (decide (first + lane < batch)))]
  seg_fp ht using
    simp only [b32, truncBits_ofNat hTotal32 (by decide), truncBits_ofNat hPart32 (by decide),
      truncBits_ofNat hTail32 (by decide), truncBits_ofNat hHeads32 (by decide),
      truncBits_ofNat hCta32 (by decide), truncBits_ofNat hStart32 (by decide),
      ← BitVec.ofNat_add, ← BitVec.ofNat_mul,
      truncBits_ofNat hTotalWork32 (by decide), truncBits_ofNat hPartWork32 (by decide),
      BitVec.ofNat_sub_ofNat_of_le _ _ (show total * p.heads < 2 ^ 64 by omega)
        (show total * p.heads ≤ tail by omega),
      hSub, compare, Option.getD_some, signedWord hPart, signedWord hCta,
      Int.ofNat_le, hBallot]

/-- The decoded selection ballot returns its mask in the loader scratch register. -/
theorem selectedGroupVote {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (hit : Bool)
    (hpc : t.pc = 2050) (hf : t.fault = none) (hv : t.regs 362 = some (.pred hit)) :
    out kernel [] l g t = .ev (.vote (2 ^ 32 - 1) hit
      (fun mask => next (setReg t 2500 (b32 mask.toNat)))) := by
  rw [out_event hf (by rw [hpc]; exact Flow.code_2050) rfl rfl]
  change Out.ev (voteTmpl l g t 2500 362 false (.imm (-1))) = _
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  simp [voteTmpl, readPred, readReg, hv, hBlock, bind, Except.bind, pure, Except.pure, b32]
  rfl

/-- The mask selects the first live request of the group, including lane zero. -/
theorem selectedGroupPopcount (l : Launch) (g : Nat) {first n : Nat}
    (hn : n < 32) (hbound : first + n < 2 ^ 31) :
    Seg kernel [] l g 4 2051 [(2500, b32 (2 ^ n - 1)), (7199, b32 first)] 2055
      [(1187, b32 n), (7203, b32 (first + n)), (363, .pred (decide (n = 0))),
       (7201, b32 0)] := by
  intro t ht
  have hp : 2 ^ n < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hn
  have hMask : 2 ^ n - 1 < 2 ^ 32 := by omega
  have hMask64 : 2 ^ n - 1 < 2 ^ 64 := by omega
  have hFirst : first < 2 ^ 32 := by omega
  have hSum : first + n < 2 ^ 32 := by omega
  have hn32 : n < 2 ^ 32 := by omega
  have hz : (↑(truncBits 32 (BitVec.ofInt 64 0)).toNat : Int) = 0 := rfl
  have hzMask : 2 ^ n - 1 = 0 ↔ n = 0 := by
    cases n with
    | zero => decide
    | succ n =>
      have hOne := Nat.one_lt_two_pow (Nat.succ_ne_zero n)
      omega
  have hc := ballotPrefixPopcount (Nat.le_of_lt hn)
  seg_fp ht using
    first
    | rfl
    | (simp only [b32, truncBits_ofNat hMask (by decide), truncBits_ofNat hFirst (by decide),
        toNat_ofNat_lt hMask64, hc, truncBits_ofNat hn32 (by decide), ← BitVec.ofNat_add,
        truncBits_ofNat hSum (by decide), Nat.add_comm,
        compare, Option.getD_some, hz, Int.natCast_eq_zero, hzMask])

/-- A nonexhausted MMA group reaches the computation of the selection predicate. -/
theorem selectedGroupAvailable (l : Launch) (g : Nat) {first batch : Nat}
    (hGroup : first < batch) (hBatch : batch < 2 ^ 31) :
    Seg kernel [] l g 4 2042 [(7199, b32 first), (7203, b32 batch)] 2046
      [(781, .pred false), (7202, b32 256)] := by
  intro t ht
  have hf : first < 2 ^ 31 := by omega
  obtain ⟨u, hu, hU⟩ : ∃ u, run kernel [] l g 3 t = some u ∧
      At u 2045 [(361, .pred false), (781, .pred false), (7202, b32 256)] := by
    seg_fp ht using
      first
      | rfl
      | simp only [compare, Option.getD_some, truncBits_ofNat (show first < 2 ^ 32 by omega)
          (by decide), truncBits_ofNat (show batch < 2 ^ 32 by omega) (by decide),
          signedWord hf, signedWord hBatch, ge_iff_le, Int.ofNat_le,
          decide_eq_false (Nat.not_le_of_lt hGroup)]
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2045 false hU hU.2.2.2.2.1 (by simp)
  exact ⟨v, run_comp hu hv, hV.mono hV.2.2.2.2.2⟩

/-- A nonfirst request takes its preceding inclusive prefix from the previous lane. -/
theorem selectedPreviousPrefixIndex (l : Launch) (g : Nat) {n : Nat}
    (hn : 0 < n) (hLane : n < 32) :
    Seg kernel [] l g 1 2056 [(1187, b32 n)] 2057 [(2501, b32 (n - 1))] := by
  intro t ht
  seg_fp ht using norm_bits

/-- The receiver's selected preceding prefix becomes its work offset within the group. -/
theorem selectedPreviousPrefixWork (l : Launch) (g : Nat) {sum heads : Nat}
    (hs : sum < 2 ^ 32) (hh : heads < 2 ^ 32) (hWork : sum * heads < 2 ^ 32) :
    Seg kernel [] l g 1 2058 [(2502, b32 sum), (7139, b32 heads)]
      2059 [(7201, b32 (sum * heads))] := by
  intro t ht
  seg_fp ht using
    simp only [b32, truncBits_ofNat hs (by decide), truncBits_ofNat hh (by decide),
      ← BitVec.ofNat_mul, truncBits_ofNat hWork (by decide)]

/-- Subtract the selected request's preceding work from the physical CTA index. -/
theorem selectedRelativeItem (l : Launch) (g : Nat) {start previous item : Nat}
    (hLo : start + previous ≤ item) (hItem : item < 2 ^ 31) :
    Seg kernel [] l g 2 2062 [(1186, b32 start), (7201, b32 previous), (1072, b32 item)]
      2064 [(2505, b32 (item - (start + previous)))] := by
  intro t ht
  have hs : start < 2 ^ 32 := by omega
  have hp : previous < 2 ^ 32 := by omega
  have hh : start + previous < 2 ^ 32 := by omega
  have hi : item < 2 ^ 32 := by omega
  have hRel : item - (start + previous) < 2 ^ 32 := by omega
  seg_fp ht using
    simp only [b32, truncBits_ofNat hs (by decide), truncBits_ofNat hp (by decide),
      truncBits_ofNat hh (by decide), truncBits_ofNat hi (by decide), ← BitVec.ofNat_add,
      BitVec.ofNat_sub_ofNat_of_le _ _ (show start + previous < 2 ^ 64 by omega) hLo,
      truncBits_ofNat hRel (by decide)]

/-- A live selected request takes the MMA body edge with the exclusive row bound. -/
theorem selectedTileEnter {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {batch tile : Nat} (hb : batch < p.batch) (htile : 256 * tile < p.qLength batch) :
    Seg kernel [] l g 6 2103
      [(7203, b32 batch), (7148, b32 p.batch), (2533, b32 tile), (2535, b32 l.sharedBase)]
      2109 [(7202, b32 (256 * (tile + 1))), (2562, b32 (l.sharedBase + 8))] := by
  have hB := hp.shape.2.1
  have hFits : p.kLength batch - p.qLength batch + 256 * (tile + 1) < 2 ^ 31 :=
    (trips_bounds hp hb htile).2.2
  have hEnd : 256 * (tile + 1) < 2 ^ 32 :=
    ((Nat.le_add_left _ _).trans_lt hFits).trans (by decide)
  have hShared := hp.shared.2.1
  have hBase : l.sharedBase + 8 < 2 ^ 32 := by omega
  intro t ht
  obtain ⟨u, hu, hAt⟩ : ∃ u, run kernel [] l g 5 t = some u ∧
      At u 2108 [(375, .pred false), (7202, b32 (256 * (tile + 1))),
        (2562, b32 (l.sharedBase + 8))] := by
    seg_fp ht using
      first
      | simp [compare, Option.getD_some, signedWord (show batch < 2 ^ 31 by omega),
          signedWord hB, truncBits_ofNat (show batch < 2 ^ 32 by omega) (by decide),
          truncBits_ofNat (show p.batch < 2 ^ 32 by omega) (by decide), hb, b32]; done
      | norm_bits
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2108 false hAt hAt.2.2.2.2.1 (by simp)
  exact ⟨v, run_comp hu hv, hV.mono hV.2.2.2.2.2⟩

end PTX.Kernels.TmlFa4Fwd.Mma
