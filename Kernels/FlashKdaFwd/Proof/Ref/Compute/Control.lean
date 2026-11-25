-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Compute.StepLib

@[expose] public section

/-! # The control steps of the Compute phase

The steps of the phase's invariant that are not a straight step inside a tile, each as a
statement about the transition function of the thread machine:

* `tl_entry`: from the entry (`bar_5`) a compute thread reaches the first poll of tile 0, or,
  when its sequence has no token, the exit (`bar_7`);
* `tl_pollE`: a successful poll of the "empty" output mbarrier (instruction 2144) leads to the
  second poll and assigns the thread-dependent registers of the tile;
* `tl_pollF`: a successful poll of the "full" input mbarrier (2186) leads to the first matrix
  instruction;
* `tl_fence`: the proxy fence (2914) leads to the first arrival;
* `tl_arriveF`: the arrival on the "full" output mbarrier (2920) leads to the second arrival
  through `mapa`, which returns the address it is given (`mapaPeer_own`), so the transition is a
  state and not the end of the thread;
* `tl_arriveE`: the arrival on the "empty" input mbarrier (2928) leads to the first poll of the
  next tile or, after the last tile, to the exit.

In every case the successor is not one of the five breakpoint sites of the phase (2138, 2148,
2916, 2922, 2930): the flags that guard them hold by the invariant. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 8000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g t : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}

/-- A compute thread is outside the load warp, as instructions 1403 and 1404 test it. -/
theorem notLoadWarp (hc : tid g < 128) : scmpi .ne .b (andi (W (tid g)) 224) 128 = true := by
  rw [tid_and224]
  exact decide_eq_true (fun h => by have := (warp_eq4_iff g).mp h; omega)

theorem lt128 (hc : tid g < 128) : scmpi .lt .u (W (tid g)) 128 = true := by
  rw [tid_lt128]; exact decide_eq_true hc

theorem lt160 (hc : tid g < 128) : scmpi .lt .u (W (tid g)) 160 = true := by
  rw [tid_lt160]; exact decide_eq_true (by omega)

theorem gt127 (hc : tid g < 128) : scmpi .gt .u (W (tid g)) 127 = false := by
  rw [scmpi_gt_u_W (by omega) (by decide) (by decide)]
  exact decide_eq_false (by simp only [Int.reduceToNat]; omega)

/-- `setp.lt.s32 %p69, %r8, 1`: the sequence has no token. -/
theorem lenLt1 (hpre : Pre P L mem0) (g : Nat) :
    scmpi .lt .s (W (P.length (seqOf P g))) 1 = decide (P.length (seqOf P g) = 0) := by
  have h1 := first_le hpre g
  have h2 := Startup.total_lt hpre
  rw [scmpi_s_W .lt (by decide) (by decide), scmp_lt_W (by omega) (by decide)]
  exact decide_eq_decide.mpr (by simp only [Int.reduceToNat]; omega)

set_option hygiene false in
/-- A register after the transition of `bar_5`, for a compute thread whose sequence has a
token (the facts and decided conditions are the caller's hypotheses). -/
macro "entry_reg" : tactic => `(tactic| (
  (try file_simp [after_bar_5, tail_2117, htid, hlen, htiles, hfirst, hel, c1, c2, c3, c4, e1,
    e2, e3, e4, e5, e6, Arith32.sel, cmpLit, ↓reduceIte, Bool.true_or, Bool.false_eq_true]) <;>
  (try w32_norm) <;>
  first
    | (congr 1; omega)
    | rfl))

/-- **From the entry**: the transition of `bar_5` leads a compute thread whose sequence has no
token to the exit, and any other compute thread to the first poll of tile 0. -/
theorem tl_entry (hpre : Pre P L mem0) (hg : g < L.threads)
    (h : Entry P g ⟨.bar 5, w, p, x⟩) :
    (tilesOf P g = 0 ∧ Exit P g (after_bar_5 L g ⟨.bar 5, w, p, x⟩)) ∨
    (0 < tilesOf P g ∧ (after_bar_5 L g ⟨.bar 5, w, p, x⟩).site = .mbarWait 7 ∧
      Tile P L g 0 0 (after_bar_5 L g ⟨.bar 5, w, p, x⟩).w (after_bar_5 L g ⟨.bar 5, w, p, x⟩).p
        (after_bar_5 L g ⟨.bar 5, w, p, x⟩).x) := by
  obtain ⟨-, hc, htid, h83, h84, h85, hlen, htiles, hfirst, hel⟩ := h
  dsimp only at htid h83 h84 h85 hlen htiles hfirst hel
  have hs := shared_lt hpre
  have e1 := tidWord (g := g) hpre
  have c1 := notLoadWarp hc
  have c2 := lt128 hc
  have c3 := lt160 hc
  have c4 := lenLt1 hpre g
  by_cases h0 : P.length (seqOf P g) = 0
  · left
    have hT : tilesOf P g = 0 := by simp only [tilesOf, tiles, h0]
    rw [decide_eq_true h0] at c4
    refine ⟨hT, ?_, hc, ?_, ?_, ?_⟩ <;>
      file_simp [after_bar_5, htid, hlen, c1, c2, c3, c4, e1, Arith32.sel, cmpLit, ↓reduceIte,
        Bool.true_or, Bool.false_eq_true, gt127 hc, hel]
  · right
    have hT : 0 < tilesOf P g := (tiles_pos_iff P g).mpr (by omega)
    have hTlt := tiles_lt hpre g
    rw [decide_eq_false h0] at c4
    have e2 := gate_word hpre hg (P := P)
    have e3 := gateOff_word (P := P) hc
    have e4 := counter_word hT hTlt
    have e5 := sharedWord hpre
    have e6 : shl (i32 0) 3 = W 0 := by decide
    have hsite : (after_bar_5 L g ⟨.bar 5, w, p, x⟩).site = .mbarWait 7 := by
      file_simp [after_bar_5, tail_2117, htid, hlen, c1, c2, c3, c4, e1, Arith32.sel, cmpLit,
        ↓reduceIte, Bool.true_or, Bool.false_eq_true]
    refine ⟨hT, hsite, hc, hT, by decide, ?_, ?_, ?_, fun h => by omega, fun h => by omega⟩
    · have hk : regKeys.take (cntOf 0) = [2106, 2107, 2108, 2109, 2110, 1947, 486, 1151, 1152] :=
        rfl
      rw [hk]
      have f1 : (after_bar_5 L g ⟨.bar 5, w, p, x⟩).w 2106 =
          W (4294967296 - (tilesOf P g - 0)) := by entry_reg
      have f2 : (after_bar_5 L g ⟨.bar 5, w, p, x⟩).w 2107 = W 0 := by entry_reg
      have f3 : (after_bar_5 L g ⟨.bar 5, w, p, x⟩).w 2108 = W 0 := by entry_reg
      have f4 : (after_bar_5 L g ⟨.bar 5, w, p, x⟩).w 2109 = W 1 := by entry_reg
      have f5 : (after_bar_5 L g ⟨.bar 5, w, p, x⟩).w 2110 = W 0 := by entry_reg
      have f6 : (after_bar_5 L g ⟨.bar 5, w, p, x⟩).w 1947 = W (gateOff P g) := by entry_reg
      have f7 : (after_bar_5 L g ⟨.bar 5, w, p, x⟩).w 486 = W (if lane g = 0 then 1 else 0) := by
        entry_reg
      have f8 : (after_bar_5 L g ⟨.bar 5, w, p, x⟩).w 1151 =
          W (P.sharedBase + 8 * (0 % 2) + 98368) := by
        have e7 : P.sharedBase + 8 * (0 % 2) + 98368 = P.sharedBase + 98368 := by omega
        rw [e7]
        entry_reg
      have f9 : (after_bar_5 L g ⟨.bar 5, w, p, x⟩).w 1152 = W 10000000 := by entry_reg
      exact Regs.cons f1 (Regs.cons f2 (Regs.cons f3 (Regs.cons f4 (Regs.cons f5 (Regs.cons f6
        (Regs.cons f7 (Regs.cons f8 (Regs.one f9))))))))
    · file_simp [after_bar_5, tail_2117, htid, hlen, c1, c2, c3, c4, e1, Arith32.sel, cmpLit,
        ↓reduceIte, Bool.true_or, Bool.false_eq_true, h83, Bool.not_false]
    · file_simp [after_bar_5, tail_2117, htid, hlen, c1, c2, c3, c4, e1, Arith32.sel, cmpLit,
        ↓reduceIte, Bool.true_or, Bool.false_eq_true, h84, h85, Bool.or_self, Bool.not_false]

/-! ### The two polls -/

/-- A failed poll leaves the state where it is. -/
theorem pollE_fail {s : Site} :
    after_mbarWait_7 L g ⟨s, w, p, x⟩ false = ⟨.mbarWait 7, w, p, x⟩ := rfl

theorem pollF_fail {s : Site} :
    after_mbarWait_8 L g ⟨s, w, p, x⟩ false = ⟨.mbarWait 8, w, p, x⟩ := rfl

/-- **The first poll succeeds** (instruction 2144): the code up to the second poll
(instructions 2149 to 2185) assigns the thread's own registers of the tile; the breakpoint at
2148 is not reached because `%p71` holds. -/
theorem tl_pollE (hpre : Pre P L mem0) {s : Site} (h : Tile P L g t 0 w p x) :
    (after_mbarWait_7 L g ⟨s, w, p, x⟩ true).site = .mbarWait 8 ∧
      Tile P L g t 1 (after_mbarWait_7 L g ⟨s, w, p, x⟩ true).w
        (after_mbarWait_7 L g ⟨s, w, p, x⟩ true).p (after_mbarWait_7 L g ⟨s, w, p, x⟩ true).x := by
  have hc := h.compute
  have hs := shared_lt hpre
  have h71 := h.p71
  have h73 := h.p73
  have h2108 : w 2108 = W (t % 3) := h.regs 2108 (by decide)
  have e1 := tidWord (g := g) hpre
  have e5 := sharedWord hpre
  have b1 := accOff_le hc
  have b2 : t % 3 < 3 := Nat.mod_lt _ (by decide)
  refine ⟨by file_simp [after_mbarWait_7, h71, ↓reduceIte], hc, h.lt, by decide, ?_, ?_, ?_, ?_,
    fun h => by omega⟩
  · rw [take_split regKeys (show cntOf 0 ≤ cntOf 1 by decide)]
    refine Regs.append ?_ ?_
    · intro r hr
      rw [← h.regs r hr]
      have hk : regKeys.take (cntOf 0) = [2106, 2107, 2108, 2109, 2110, 1947, 486, 1151, 1152] :=
        rfl
      rw [hk] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        file_simp [after_mbarWait_7, h71, ↓reduceIte]
    · have hk : (regKeys.take (cntOf 1)).drop (cntOf 0) = [1923, 1924, 1932, 1935, 1938, 1160,
          1916, 1887, 1857, 1827, 1797, 1767, 1737, 1467, 1416, 1365, 1314, 1263, 1212, 1177,
          1161, 1939, 1940, 1156, 1157] := rfl
      rw [hk]
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        rv_simp
        file_simp [after_mbarWait_7, h71, ↓reduceIte, e1, e5, h2108, tid_warp hc, tid_bit3 hc,
          tid_pair hc, tid_acc hc, shl3_3]
      all_goals (try w32_norm)
      all_goals try (congr 1; omega)
  · file_simp [after_mbarWait_7, h71, ↓reduceIte]
  · file_simp [after_mbarWait_7, h71, ↓reduceIte, h73]
  · intro _
    file_simp [after_mbarWait_7, h71, ↓reduceIte, e1, lt128 hc]

/-- **The second poll succeeds** (instruction 2186): the code up to the first `ldmatrix`
(instructions 2189 to 2193) assigns the base of the input stage and the lane's row. -/
theorem tl_pollF (hpre : Pre P L mem0) {s : Site} (h : Tile P L g t 1 w p x) :
    (after_mbarWait_8 L g ⟨s, w, p, x⟩ true).site = .matrixLoad 0 ∧
      Tile P L g t 2 (after_mbarWait_8 L g ⟨s, w, p, x⟩ true).w
        (after_mbarWait_8 L g ⟨s, w, p, x⟩ true).p (after_mbarWait_8 L g ⟨s, w, p, x⟩ true).x := by
  have hc := h.compute
  have hs := shared_lt hpre
  have h2108 : w 2108 = W (t % 3) := h.regs 2108 (by decide)
  have h1940 : w 1940 = W (P.sharedBase + 8 * (t % 3)) := h.regs 1940 (by decide)
  have h1923 : w 1923 = W (tid g) := h.regs 1923 (by decide)
  have b1 := laneOff_le g
  have b2 : t % 3 < 3 := Nat.mod_lt _ (by decide)
  have e1 : mad32 (w 2108) (i32 18040) (w 1940) = W (P.sharedBase + 18048 * (t % 3)) := by
    rw [h2108, h1940]
    exact mad18040 hs t
  have e2 : andi (shl (w 1923) 4) 496 = W (laneOff g) := by rw [h1923]; exact tid_lane hc
  have e3 : add32 (mad32 (w 2108) (i32 18040) (w 1940)) (andi (shl (w 1923) 4) 496) =
      W (P.sharedBase + 18048 * (t % 3) + laneOff g) := by
    rw [e1, e2]
    exact add32_W (by omega)
  have e4 : addi (add32 (mad32 (w 2108) (i32 18040) (w 1940)) (andi (shl (w 1923) 4) 496)) 36992 =
      W (P.sharedBase + 18048 * (t % 3) + laneOff g + 36992) := by
    rw [e3]
    w32_norm
  exact ⟨rfl, h.step (l := [(1941, _), (1943, _), (1944, _), (1158, _)])
    (lk := [1941, 1943, 1944, 1158]) rfl (by decide) (by decide) (by decide) (by decide)
    (Regs.cons e1 (Regs.cons e2 (Regs.cons e3 (Regs.one e4))))⟩

/-! ### The end of a tile -/

/-- **The proxy fence** (instruction 2914): the breakpoint at 2916 is not reached because
`%p72` holds, and the code up to the first arrival computes the address of the "full" mbarrier
of the tile's output stage. -/
theorem tl_fence (hpre : Pre P L mem0) {s : Site} (h : Tile P L g t 265 w p x) :
    (after_fenceProxy_2 L g ⟨s, w, p, x⟩).site = .mbarArrive 4 ∧
      Tile P L g t 266 (after_fenceProxy_2 L g ⟨s, w, p, x⟩).w
        (after_fenceProxy_2 L g ⟨s, w, p, x⟩).p (after_fenceProxy_2 L g ⟨s, w, p, x⟩).x := by
  have hs := shared_lt hpre
  have h72 := h.p72 (by decide)
  have h2005 : w 2005 = W (8 * (t % 2)) := h.regs 2005 (by decide)
  have b2 : t % 2 < 2 := Nat.mod_lt _ (by decide)
  have e5 := sharedWord hpre
  have e1 : addi (add32 (sreg L.sharedBase) (w 2005)) 98352 =
      W (P.sharedBase + 8 * (t % 2) + 98352) := by
    rw [e5, h2005]
    w32_norm
  have ha : after_fenceProxy_2 L g ⟨s, w, p, x⟩ = ⟨.mbarArrive 4,
      setW [(2031, addi (add32 (sreg L.sharedBase) (w 2005)) 98352)] w, p, x⟩ := by
    simp only [after_fenceProxy_2, h72, ↓reduceIte]
  rw [ha]
  exact ⟨rfl, h.step (lk := [2031]) rfl (by decide) (by decide) (by decide) (by decide)
    (Regs.one e1)⟩

/-- **The arrival on the "full" output mbarrier** (instruction 2920): the breakpoint at 2922
is not reached because `%p71` holds; `mapa` (2927) returns the address of the "empty" mbarrier
of the tile's input stage, so the successor is the state at the second arrival. -/
theorem tl_arriveF (hpre : Pre P L mem0) (hg : g < L.threads) {s : Site}
    (h : Tile P L g t 266 w p x) :
    ∃ d', after_mbarArrive_4 L g ⟨s, w, p, x⟩ = some (some d') ∧ d'.site = .mbarArrive 5 ∧
      Tile P L g t 267 d'.w d'.p d'.x := by
  have hs := shared_lt hpre
  have h71 := h.p71
  have h1939 : w 1939 = W (8 * (t % 3)) := h.regs 1939 (by decide)
  have b2 : t % 3 < 3 := Nat.mod_lt _ (by decide)
  have e5 := sharedWord hpre
  have e1 : addi (add32 (sreg L.sharedBase) (w 1939)) 98328 =
      W (P.sharedBase + 8 * (t % 3) + 98328) := by
    rw [e5, h1939]
    w32_norm
  have e2 : (i32 0 : BitVec 64) = W 0 := rfl
  have hm := mapaPeer_own hpre hg (a := P.sharedBase + 8 * (t % 3) + 98328) (by omega)
  refine ⟨⟨.mbarArrive 5, setW [(2034, addi (add32 (sreg L.sharedBase) (w 1939)) 98328),
    (2035, i32 0)] w, p, valueEx x [(3434, remPtr P L g t)]⟩, ?_, rfl, ?_⟩
  · simp only [after_mbarArrive_4, h71, ↓reduceIte, tail_2927, mapaThen, setW_apply, lookupLit,
      Option.getD_some, e1, e2, hm, remPtr]
  · refine ⟨h.compute, h.lt, by decide, ?_, h.p71, h.p73, fun _ => h.p72 (by decide), fun _ => rfl⟩
    rw [take_split regKeys (show cntOf 266 ≤ cntOf 267 by decide)]
    exact (h.regs.frame (lk := [2034, 2035]) rfl (by decide)).append
      (Regs.cons e1 (Regs.one e2))

/-- **The arrival on the "empty" input mbarrier** (instruction 2928): the breakpoint at 2930 is
not reached because `%p73` holds; the code after it advances the two stages, flips a parity
when its stage wraps, and counts the loop counter up. After the last tile the counter is zero
and the thread goes to the exit; otherwise it goes to the first poll of the next tile (the
breakpoint at 2138 is not reached: the thread index is below 128). -/
theorem tl_arriveE (hpre : Pre P L mem0) {s : Site} (h : Tile P L g t 267 w p x) :
    (t + 1 = tilesOf P g ∧ Exit P g (after_mbarArrive_5 L g ⟨s, w, p, x⟩)) ∨
    (t + 1 < tilesOf P g ∧ (after_mbarArrive_5 L g ⟨s, w, p, x⟩).site = .mbarWait 7 ∧
      Tile P L g (t + 1) 0 (after_mbarArrive_5 L g ⟨s, w, p, x⟩).w
        (after_mbarArrive_5 L g ⟨s, w, p, x⟩).p (after_mbarArrive_5 L g ⟨s, w, p, x⟩).x) := by
  have hc := h.compute
  have hs := shared_lt hpre
  have hT := tiles_lt hpre g (P := P)
  have hlt := h.lt
  have h71 := h.p71
  have h73 := h.p73
  have h2106 : w 2106 = W (4294967296 - (tilesOf P g - t)) := h.regs 2106 (by decide)
  have h2107 : w 2107 = W (t / 3 % 2) := h.regs 2107 (by decide)
  have h2108 : w 2108 = W (t % 3) := h.regs 2108 (by decide)
  have h2109 : w 2109 = W ((t / 2 + 1) % 2) := h.regs 2109 (by decide)
  have h2110 : w 2110 = W (t % 2) := h.regs 2110 (by decide)
  have h1947 : w 1947 = W (gateOff P g) := h.regs 1947 (by decide)
  have h486 : w 486 = W (if lane g = 0 then 1 else 0) := h.regs 486 (by decide)
  have e1 := tidWord (g := g) hpre
  have e5 := sharedWord hpre
  have c2 := lt128 hc
  have c3 := gt127 hc
  have b2 : (t + 1) % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases hlast : t + 1 = tilesOf P g
  · left
    have e6 := counter_last hlast
    have c6 : scmpi .eq .b (W 0) 0 = true := by decide
    refine ⟨hlast, ?_, hc, ?_, ?_, ?_⟩ <;>
      file_simp [after_mbarArrive_5, h73, ↓reduceIte, h2106, e6, c6, e1, c3, h486]
  · right
    have hnext : t + 1 < tilesOf P g := by omega
    have e6 := counter_next hnext hT
    have c6 := counter_ne hnext hT
    have e7 : (i32 10000000 : BitVec 64) = W 10000000 := rfl
    have hsite : (after_mbarArrive_5 L g ⟨s, w, p, x⟩).site = .mbarWait 7 := by
      file_simp [after_mbarArrive_5, h73, ↓reduceIte, h2106, e6, c6, e1, c2, Bool.false_eq_true]
    refine ⟨hnext, hsite, hc, hnext, by decide, ?_, ?_, ?_, fun h => by omega, fun h => by omega⟩
    · have hk : regKeys.take (cntOf 0) = [2106, 2107, 2108, 2109, 2110, 1947, 486, 1151, 1152] :=
        rfl
      rw [hk]
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        rv_simp
        file_simp [after_mbarArrive_5, h73, ↓reduceIte, h2106, h2107, h2108, h2109, h2110,
          h1947, h486, e6, c6, e1, c2, e5, e7, Bool.false_eq_true, stage3_next, par3_next,
          stage2_next, par2_next, shl3_2]
      all_goals (try w32_norm)
      all_goals try (congr 1; omega)
    · file_simp [after_mbarArrive_5, h73, ↓reduceIte, h2106, e6, c6, e1, c2, Bool.false_eq_true,
        h71]
    · file_simp [after_mbarArrive_5, h73, ↓reduceIte, h2106, e6, c6, e1, c2, Bool.false_eq_true]

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
