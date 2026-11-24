-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderFirstScan

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left h]

/-- Advance to the next group, saturating its base at the batch sentinel. -/
theorem loaderAdvanceGroup (l : Launch) (g : Nat) {first batch stop : Nat}
    (hNext : first + 31 < 2 ^ 31) (hBatch : batch < 2 ^ 31) :
    Seg kernel [] l g 4 234 [(7165, b32 first), (7170, b32 batch), (1075, b32 stop)] 238
      [(1076, b32 (first + 31)), (74, .pred (decide (batch ≤ first + 31))),
       (7165, b32 (min (first + 31) batch)), (7166, b32 stop)] := by
  intro t ht
  have hFirst32 : first < 2 ^ 32 := by omega
  have hNext32 : first + 31 < 2 ^ 32 := by omega
  have hBatch32 : batch < 2 ^ 32 := by omega
  have hLit : truncBits 32 (BitVec.ofInt 64 31) = BitVec.ofNat 64 31 := rfl
  seg_fp ht using
    simp only [b32, hLit, ← BitVec.ofNat_add, truncBits_ofNat hFirst32 (by decide),
      truncBits_ofNat hNext32 (by decide), truncBits_ofNat hBatch32 (by decide), compare,
      Option.getD_some, signedWord hNext, signedWord hBatch, Int.ofNat_le, ge_iff_le]
    all_goals
      by_cases h : first + 31 < batch
      · simp [Nat.min_eq_left (Nat.le_of_lt h)]
        omega
      · simp [Nat.min_eq_right (Nat.le_of_not_lt h)]
        omega


/-- Stable facts at the loader fallback loop head. Only the past work limit and the group
index are carried between iterations. -/
def loaderFallbackFacts (p : Params) (l : Launch) (g warp first lane : Nat) : List (Nat × Value) :=
  [(1075, b32 (g / l.block + 1)), (7165, b32 first),
    (7160, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)),
    (7136, b32 p.heads)] ++ loaderCuQFacts p l (warpLane l g lane) warp

private theorem loaderFallbackEnter (l : Launch) (g : Nat) {cta limit : Nat}
    (hCta : cta + 1 < 2 ^ 31) :
    Seg kernel [] l g 3 231 [(1072, b32 cta), (7166, b32 limit)] 234
      [(1075, b32 (cta + 1)), (7165, b32 0), (7160, b32 limit)] := by
  intro t ht
  seg_fp ht using norm_bits

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Enter the fallback loop from its actual taken route, including the prior group's work
limit. -/
theorem loaderFallbackStartAtPreserving (hp : Pre p l m) {g warp shuffles votes : Nat}
    (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 231 (loaderFirstRouteFacts p l g warp) shuffles votes ends) :
    ∃ next : SchedulerWarpAt l X g 234 (loaderFallbackFacts p l g warp 0) shuffles votes ends,
      next.pos = cur.pos ∧ next.before = cur.before := by
  let cta := g / l.block
  let limit := tilePrefix p (min p.batch 31) * p.heads
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hCta : cta + 1 < 2 ^ 31 := by
    have h := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
    exact (Nat.succ_le_of_lt h).trans_lt hp.grid.2.2
  apply cur.advanceLocalPreserving
  intro lane hl
  let thread := warpLane l g lane
  let frame := (7136, b32 p.heads) :: loaderCuQFacts p l thread warp
  let regs := frame.map Prod.fst
  have ht := cur.checkpoint lane hl
  have h := ht.2.2.2.2
  have hABI : Holds (cur.state lane).regs (loaderCuQFacts p l thread warp) := h.2.2.2.2.2.2.2
  have hCtaWord := hABI.2.2.2.1
  have hSame : thread / l.block = cta := (Step.sameWarp_lane hBlock hg hl).1.1.2.2.symm
  rw [hSame] at hCtaWord
  have hAt : At (cur.state lane) 231 [(1072, b32 cta), (7166, b32 limit)] :=
    ht.mono ⟨hCtaWord, h.1, trivial⟩
  obtain ⟨u, hu, hU⟩ := loaderFallbackEnter l thread hCta _ hAt
  obtain ⟨huA, huFrame⟩ := loaderLinear (regs := regs) (by decide) (by decide) hAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hCarry : Holds (cur.state lane).regs frame := ⟨h.2.2.2.2.2.1, hABI⟩
  have hKeep := holdsSchedulerFrame hCarry huFrame (fun _ h => List.mem_map_of_mem h)
  exact ⟨u, run_rtg huA, hU.mono
    ⟨hU.2.2.2.2.1, hU.2.2.2.2.2.1, hU.2.2.2.2.2.2.1, hKeep⟩⟩

/-- The local transition keeps every trace index. -/
theorem loaderFallbackStartAt (hp : Pre p l m) {g warp shuffles votes : Nat} (hg : g < l.threads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 231 (loaderFirstRouteFacts p l g warp) shuffles votes ends) :
    ∃ next : SchedulerWarpAt l X g 234 (loaderFallbackFacts p l g warp 0) shuffles votes ends,
      next.pos = cur.pos := by
  obtain ⟨next,hPos,_⟩ := loaderFallbackStartAtPreserving hp hg cur
  exact ⟨next,hPos⟩

/-- The same fallback transition in a terminated execution. -/
theorem loaderFallbackStart (hp : Pre p l m) {g warp shuffles votes : Nat} (hg : g < l.threads)
    (cur : SchedulerWarpAt l X g 231 (loaderFirstRouteFacts p l g warp) shuffles votes) :
    Nonempty (SchedulerWarpAt l X g 234 (loaderFallbackFacts p l g warp 0) shuffles votes) := by
  obtain ⟨next, _⟩ := loaderFallbackStartAt hp hg cur
  exact ⟨next⟩

/-- Registers live after clipping or advancing the group. -/
def loaderAdvancedFacts (p : Params) (l : Launch) (g warp first lane : Nat) : List (Nat × Value) :=
  [(1076, b32 (first + 31)), (7165, b32 (min (first + 31) p.batch)),
    (7166, b32 (g / l.block + 1)), (1075, b32 (g / l.block + 1)),
    (7160, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)),
    (7136, b32 p.heads)] ++ loaderCuQFacts p l (warpLane l g lane) warp

/-- A full or partial subsequent group either reaches its first per-lane cuQ instruction or
clips to the batch sentinel while retaining the terminal CTA test. -/
theorem loaderFallbackAdvanceAtPreserving (hp : Pre p l m) {g warp first shuffles votes : Nat}
    (hFirst : first < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 234 (loaderFallbackFacts p l g warp first) shuffles votes ends) :
    ∃ next : SchedulerWarpAt l X g (if p.batch ≤ first + 31 then 285 else 239)
      (loaderAdvancedFacts p l g warp first) shuffles votes ends,
      next.pos = cur.pos ∧ next.before = cur.before := by
  have hSize := hp.shape.2.2.2.2.2
  have hNext : first + 31 < 2 ^ 31 := by omega
  apply cur.advanceLocalPreserving
  intro lane hl
  let thread := warpLane l g lane
  let stop := g / l.block + 1
  let stable := [(1075, b32 stop), (7160, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)),
    (7136, b32 p.heads)] ++ loaderCuQFacts p l thread warp
  let regs := stable.map Prod.fst
  have ht := cur.checkpoint lane hl
  have h := ht.2.2.2.2
  have hBatch : (cur.state lane).regs 7170 = some (b32 p.batch) := h.2.2.2.2.2.2.1
  have hAt : At (cur.state lane) 234 [(7165, b32 first), (7170, b32 p.batch), (1075, b32 stop)] :=
    ht.mono ⟨h.2.1, hBatch, h.1, trivial⟩
  obtain ⟨u, hu, hU⟩ := loaderAdvanceGroup l thread hNext hp.shape.2.1 _ hAt
  obtain ⟨huA, huFrame⟩ := loaderLinear (regs := regs) (by decide) (by decide) hAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hStable : Holds (cur.state lane).regs stable := ⟨h.1, h.2.2⟩
  have hKeep := holdsSchedulerFrame hStable huFrame (fun _ h => List.mem_map_of_mem h)
  let guard := decide (p.batch ≤ first + 31)
  have hBranch : At u 238 ((74, .pred guard) :: (1076, b32 (first + 31)) ::
      (7165, b32 (min (first + 31) p.batch)) :: (7166, b32 stop) :: stable) :=
    hU.mono ⟨hU.2.2.2.2.2.1, hU.2.2.2.2.1, hU.2.2.2.2.2.2.1, hU.2.2.2.2.2.2.2.1, hKeep⟩
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := thread)
    Flow.code_238 guard hBranch hBranch.2.2.2.2.1 (by simp)
  obtain ⟨hvA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hBranch.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hv
  have hFinal : Holds v.regs (loaderAdvancedFacts p l g warp first lane) :=
    hV.2.2.2.2.2
  exact ⟨v, run_rtg (run_comp huA hvA), by
    simpa only [guard, decide_eq_true_eq, Nat.reduceAdd] using hV.mono hFinal⟩

/-- The local transition keeps every trace index. -/
theorem loaderFallbackAdvanceAt (hp : Pre p l m) {g warp first shuffles votes : Nat}
    (hFirst : first < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 234 (loaderFallbackFacts p l g warp first) shuffles votes ends) :
    ∃ next : SchedulerWarpAt l X g (if p.batch ≤ first + 31 then 285 else 239)
      (loaderAdvancedFacts p l g warp first) shuffles votes ends,
      next.pos = cur.pos := by
  obtain ⟨next,hPos,_⟩ := loaderFallbackAdvanceAtPreserving hp hFirst cur
  exact ⟨next,hPos⟩

/-- The same fallback transition in a terminated execution. -/
theorem loaderFallbackAdvance (hp : Pre p l m) {g warp first shuffles votes : Nat}
    (hFirst : first < p.batch)
    (cur : SchedulerWarpAt l X g 234 (loaderFallbackFacts p l g warp first) shuffles votes) :
    Nonempty (SchedulerWarpAt l X g (if p.batch ≤ first + 31 then 285 else 239)
      (loaderAdvancedFacts p l g warp first) shuffles votes) := by
  obtain ⟨next, _⟩ := loaderFallbackAdvanceAt hp hFirst cur
  exact ⟨next⟩

private theorem loaderFallbackStop (l : Launch) (g : Nat) {cta : Nat}
    (hCta : cta + 1 < 2 ^ 31) :
    Seg kernel [] l g 3 285 [(7166, b32 (cta + 1)), (1072, b32 cta)] 288
      [(7160, b32 (cta + 1)), (87, .pred false)] := by
  intro t ht
  have hCta32 : cta < 2 ^ 32 := by omega
  have hEnd32 : cta + 1 < 2 ^ 32 := by omega
  have hCta31 : cta < 2 ^ 31 := by omega
  obtain ⟨u, hu, hU⟩ : ∃ u, run kernel [] l g 2 t = some u ∧
      At u 287 [(87, .pred false), (7160, b32 (cta + 1))] := by
    seg_fp ht using
      simp only [compare, Option.getD_some, truncBits_ofNat hCta32 (by decide),
          truncBits_ofNat hEnd32 (by decide), signedWord hCta31, signedWord hCta,
          Int.ofNat_le, decide_eq_false (show ¬cta + 1 ≤ cta by omega)]
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_287 false hU hU.2.2.2.2.1 (by simp)
  exact ⟨v, run_comp hu hv, hV.mono ⟨hV.2.2.2.2.2.1, hV.2.2.2.2.1, trivial⟩⟩

private theorem loaderNoBatch (l : Launch) (g : Nat) {batch : Nat} (hBatch : batch < 2 ^ 31) :
    Seg kernel [] l g 5 288 [(7165, b32 batch), (7170, b32 batch)] 355
      [(771, .pred false), (7168, b32 0), (7169, b32 0)] := by
  intro t ht
  have hBatch32 : batch < 2 ^ 32 := by omega
  obtain ⟨u, hu, hU⟩ : ∃ u, run kernel [] l g 4 t = some u ∧
      At u 292 [(88, .pred true), (771, .pred false), (7168, b32 0), (7169, b32 0)] := by
    seg_fp ht using
      first
      | rfl
      | simp only [compare, Option.getD_some, truncBits_ofNat hBatch32 (by decide),
          signedWord hBatch, ge_iff_le, le_refl, decide_true]
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_292 true hU hU.2.2.2.2.1 (by simp)
  exact ⟨v, run_comp hu hv, hV.mono hV.2.2.2.2.2⟩

/-- The decoded exhausted fallback bypasses request selection and leaves the work
predicate false. -/
theorem loaderFallbackExhaustedAtPreserving (hp : Pre p l m) {g warp first shuffles votes : Nat}
    (hg : g < l.threads) (hExhausted : p.batch ≤ first + 31) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 285 (loaderAdvancedFacts p l g warp first) shuffles votes ends) :
    ∃ next : SchedulerWarpAt l X g 355
      (fun lane => [(771, .pred false), (7168, b32 0), (7169, b32 0),
        (7165, b32 p.batch)] ++ loaderCuQFacts p l (warpLane l g lane) warp) shuffles votes ends,
      next.pos = cur.pos ∧ next.before = cur.before := by
  let cta := g / l.block
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hCTA : cta + 1 < 2 ^ 31 := by
    have h := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
    exact (Nat.succ_le_of_lt h).trans_lt hp.grid.2.2
  apply cur.advanceLocalPreserving
  intro lane hl
  let thread := warpLane l g lane
  let stable := (7165, b32 p.batch) :: loaderCuQFacts p l thread warp
  let regs := stable.map Prod.fst
  have ht := cur.checkpoint lane hl
  have h := ht.2.2.2.2
  have hABI : Holds (cur.state lane).regs (loaderCuQFacts p l thread warp) := h.2.2.2.2.2.2
  have hCtaWord := hABI.2.2.2.1
  have hSame : thread / l.block = cta := (Step.sameWarp_lane hBlock hg hl).1.1.2.2.symm
  rw [hSame] at hCtaWord
  have hAt : At (cur.state lane) 285 [(7166, b32 (cta + 1)), (1072, b32 cta)] :=
    ht.mono ⟨h.2.2.1, hCtaWord, trivial⟩
  obtain ⟨u, hu, hU⟩ := loaderFallbackStop l thread hCTA _ hAt
  obtain ⟨huA, huFrame⟩ := loaderLinear (regs := regs) (by decide) (by decide) hAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hFirst := h.2.1
  change (cur.state lane).regs 7165 = some (b32 (min (first + 31) p.batch)) at hFirst
  rw [Nat.min_eq_right hExhausted] at hFirst
  have hKeep := holdsSchedulerFrame (show Holds (cur.state lane).regs stable from ⟨hFirst, hABI⟩)
    huFrame (fun _ h => List.mem_map_of_mem h)
  have hAt' : At u 288 [(7165, b32 p.batch), (7170, b32 p.batch)] :=
    hU.mono ⟨hKeep.1, hKeep.2.2.2.1, trivial⟩
  obtain ⟨v, hv, hV⟩ := loaderNoBatch l thread hp.shape.2.1 _ hAt'
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := regs) (by decide) (by decide) hAt'.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hSaved := holdsSchedulerFrame hKeep hvFrame (fun _ h => List.mem_map_of_mem h)
  exact ⟨v, run_rtg (run_comp huA hvA), hV.mono
    ⟨hV.2.2.2.2.1, hV.2.2.2.2.2.1, hV.2.2.2.2.2.2.1, hSaved⟩⟩

/-- The local transition keeps every trace index. -/
theorem loaderFallbackExhaustedAt (hp : Pre p l m) {g warp first shuffles votes : Nat}
    (hg : g < l.threads) (hExhausted : p.batch ≤ first + 31) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 285 (loaderAdvancedFacts p l g warp first) shuffles votes ends) :
    ∃ next : SchedulerWarpAt l X g 355
      (fun lane => [(771, .pred false), (7168, b32 0), (7169, b32 0),
        (7165, b32 p.batch)] ++ loaderCuQFacts p l (warpLane l g lane) warp) shuffles votes ends,
      next.pos = cur.pos := by
  obtain ⟨next,hPos,_⟩ := loaderFallbackExhaustedAtPreserving hp hg hExhausted cur
  exact ⟨next,hPos⟩

theorem loaderFallbackExhausted (hp : Pre p l m) {g warp first shuffles votes : Nat}
    (hg : g < l.threads) (hExhausted : p.batch ≤ first + 31)
    (cur : SchedulerWarpAt l X g 285 (loaderAdvancedFacts p l g warp first) shuffles votes) :
    Nonempty (SchedulerWarpAt l X g 355
      (fun lane => [(771, .pred false), (7168, b32 0), (7169, b32 0),
        (7165, b32 p.batch)] ++ loaderCuQFacts p l (warpLane l g lane) warp) shuffles votes) := by
  obtain ⟨next, _⟩ := loaderFallbackExhaustedAt hp hg hExhausted cur
  exact ⟨next⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
