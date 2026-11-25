-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Compute.Reach
public import Kernels.FlashKdaFwd.Proof.Schedule.Sites

@[expose] public section

/-! # The Compute phase: static facts about the sites of the 268 positions of a tile

Helper of `ExportsProgress.lean` (the Compute share of the progress contract
`Proof/Schedule/Contract.lean: RefProgress`). The contract speaks of a state of the thread
machine through its *site* (the event instruction the state is at): the instruction index
`Site.pc`, the sub-step `Site.sub` (1 at the second event of an `ldmatrix` or a `stmatrix`), the
kind `Site.kind` and the class `siteCls` (poll, warp collective, matrix event, free). The
invariant of the Compute phase (`Inv.lean`) speaks of the *position* `n < 268` of the state in
the straight line of the 268 events of a tile, whose site is of the kind `skOf n` (table
`skTab`). This file reads the first off the second, by evaluated checks over the 268 positions:

* `SK.site k`: one site of each kind `k` (the second event of an `ldmatrix` or a `stmatrix`
  carries the bytes of the first event; the instruction, the sub-step and the kind do not depend
  on them: `SK.at_site`). `pcOf n`, `kindOf n`: the instruction index and the kind of the site
  of position `n`.
* `pc_tab`: the instructions of the positions are 2144 to 2928 (inside the compute loop, 2106 to
  2944), and those after the named barrier (instruction 2913) are the positions from 265 on.
* `mxPcs`: the instruction indices of the 182 warp matrix instructions, a literal list;
  `mxPcs_eq`: it is the list of `Top.matrixSites` (the consumer's table). `matBefore_at`: the
  consumer's count `matBefore` of a site of position `n` is the invariant's `matOf n`.
* `mx_tab`: a position whose event is a matrix event is at least 3, has fewer than 182 matrix
  events of its tile before it, is at the instruction of that ordinal in `mxPcs`, and neither it
  nor the position before it is a `bar.sync`.
* `wait_tab`, `bar_tab`, `kind_tab`: the polls are the positions 0 and 1; the one `bar.sync` is
  position 264; no position is a shuffle, an election, the exit or a bulk-group wait.
* `posOf s`: the position read off a site (`posOf_eq`); `matrixSites_op`, `mxPcs_site`: an
  entry of `Top.matrixSites` is a warp matrix instruction of the code with its operation.
* `matrix_tmpl`: the event template of a warp matrix instruction at the sub-step of its matrix
  event is undefined behaviour or a matrix event with the instruction's operation.
* `unblocking_of_fired`: an event fired at a site that is no `bar.sync` and no bulk-group wait
  never blocks its thread (`Sched.Unblocking`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
open PTX PTX.Proof PTX.Flow PTX.Sched
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX.Kernels.FlashKdaFwd.Proof.Progress (siteCls kindCls siteCls_kind matBefore
  matBefore_eq op_of_matrix_kind)

noncomputable section

/-! ### One site of each kind -/

/-- A site of kind `k`: the one whose carried bytes (at the second event of an `ldmatrix` or a
`stmatrix`) are the empty list. -/
def SK.site : SK → Site
  | .wait j => .mbarWait j
  | .ld j => .matrixLoad j
  | .ldMx j => .matrixLoadMx j []
  | .mma j => .warpMma j
  | .mv j => .matrixMove j
  | .st j => .matrixStore j
  | .stWr j => .matrixStoreWr j []
  | .load j => .load j
  | .bar j => .bar j
  | .fence j => .fenceProxy j
  | .arrive j => .mbarArrive j

/-- The instruction, the sub-step and the kind of a site of kind `k` are those of `k.site`. -/
theorem SK.at_site {k : SK} {s : Site} (h : k.At s) :
    s.pc = k.site.pc ∧ s.sub = k.site.sub ∧ s.kind = k.site.kind := by
  cases k <;> simp only [SK.At] at h <;> first
    | (subst h; exact ⟨rfl, rfl, rfl⟩)
    | (obtain ⟨row, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩)

/-- The instruction index of position `n` of a tile. -/
def pcOf (n : Nat) : Nat := (skOf n).site.pc

/-- The kind of the site of position `n` of a tile. -/
def kindOf (n : Nat) : SiteKind := (skOf n).site.kind

/-- The instruction of the site of a position. -/
theorem pc_at {n : Nat} {s : Site} (h : (skOf n).At s) : s.pc = pcOf n := (SK.at_site h).1

/-- The kind of the site of a position. -/
theorem kind_at {n : Nat} {s : Site} (h : (skOf n).At s) : s.kind = kindOf n :=
  (SK.at_site h).2.2

/-- The class of the site of a position, by its kind. -/
theorem cls_at {n : Nat} {s : Site} (h : (skOf n).At s) : siteCls s = kindCls (kindOf n) := by
  rw [siteCls_kind, kind_at h]

/-! ### The instructions of the positions -/

/-- **The instructions of the positions**: from 2144 (the first poll) to 2928 (the second
arrival), and after the named barrier (instruction 2913) exactly from position 265 on. -/
theorem pc_tab : ∀ n < 268, 2144 ≤ pcOf n ∧ pcOf n ≤ 2928 ∧ (2913 < pcOf n ↔ 265 ≤ n) := by
  decide +kernel

/-- The instruction indices of the 182 warp matrix instructions of the tile loop (44
`ldmatrix`, 104 `mma.sync`, 16 `movmatrix`, 18 `stmatrix`), in program order. -/
def mxPcs : List Nat :=
  [2194, 2196, 2197, 2198, 2200, 2201, 2202, 2203, 2205, 2207, 2208, 2209, 2210, 2211, 2212, 2213,
   2214, 2215, 2216, 2217, 2219, 2221, 2222, 2223, 2224, 2225, 2226, 2227, 2228, 2229, 2230, 2231,
   2233, 2235, 2236, 2237, 2238, 2239, 2240, 2241, 2242, 2243, 2244, 2245, 2247, 2249, 2250, 2251,
   2252, 2253, 2254, 2255, 2256, 2257, 2258, 2259, 2261, 2263, 2264, 2265, 2266, 2267, 2268, 2269,
   2270, 2271, 2272, 2273, 2275, 2277, 2278, 2279, 2280, 2281, 2282, 2283, 2284, 2285, 2286, 2287,
   2289, 2291, 2292, 2293, 2294, 2295, 2296, 2297, 2298, 2299, 2300, 2301, 2302, 2303, 2304, 2305,
   2309, 2311, 2313, 2375, 2376, 2377, 2378, 2379, 2380, 2441, 2442, 2443, 2444, 2445, 2446, 2460,
   2461, 2462, 2463, 2464, 2465, 2466, 2479, 2480, 2481, 2482, 2483, 2484, 2503, 2505, 2510, 2515,
   2516, 2517, 2518, 2520, 2543, 2564, 2565, 2566, 2567, 2568, 2570, 2593, 2614, 2615, 2616, 2617,
   2618, 2620, 2643, 2664, 2665, 2666, 2667, 2668, 2670, 2693, 2714, 2715, 2716, 2717, 2718, 2720,
   2743, 2764, 2765, 2766, 2767, 2768, 2770, 2793, 2814, 2815, 2816, 2817, 2818, 2820, 2843, 2864,
   2865, 2866, 2867, 2868, 2889, 2910]

/-- `mxPcs` is the list of the instruction indices of the consumer's table of the warp matrix
instructions (one evaluated scan of the code). -/
theorem mxPcs_eq : Top.matrixSites.map (·.1) = mxPcs := by decide +kernel

/-- **The matrix events of the tile before a position**, counted as the consumer counts them
(the matrix instructions below the position's instruction, and its own at the row write of a
`stmatrix`), are the invariant's `matOf`. -/
theorem mat_tab : ∀ n < 268, (mxPcs.filter (· < pcOf n)).length +
    (if kindOf n = .matrixStoreWr then 1 else 0) = matOf n := by
  decide +kernel

/-- **The consumer's count `matBefore` of the site of a position is `matOf`.** -/
theorem matBefore_at {n : Nat} {s : Site} (hn : n < 268) (h : (skOf n).At s) :
    matBefore s = matOf n := by
  have hp := pc_tab n hn
  rw [matBefore_eq (by rw [pc_at h]; omega), pc_at h, kind_at h, ← mat_tab n hn, ← mxPcs_eq,
    List.filter_map, List.length_map]
  rfl

/-- **The positions of the matrix events**: at least 3; fewer than 182 matrix events of the tile
before them; at the instruction of that ordinal among the warp matrix instructions; and neither
the position nor the one before it is a `bar.sync`. -/
theorem mx_tab : ∀ n < 268, kindCls (kindOf n) = .matrix →
    3 ≤ n ∧ matOf n < 182 ∧ mxPcs[matOf n]? = some (pcOf n) ∧ kindOf n ≠ .bar ∧
      kindOf (n - 1) ≠ .bar := by
  decide +kernel

/-- The polls of a tile are its positions 0 and 1. -/
theorem wait_tab : ∀ n < 268, kindOf n = .mbarWait → n ≤ 1 := by decide +kernel

/-- The one `bar.sync` of a tile is its position 264. -/
theorem bar_tab : ∀ n < 268, kindOf n = .bar → n = 264 := by decide +kernel

/-- No position of a tile is a shuffle or an election, the exit or a bulk-group wait. -/
theorem kind_tab : ∀ n < 268,
    kindCls (kindOf n) ≠ .coll ∧ kindOf n ≠ .exit ∧ kindOf n ≠ .bulkWait := by
  decide +kernel

/-! ### The position, read off the site -/

/-- The position in the tile of a site of the tile loop: the index of its kind in the table
`skTab` (0 for a site of another kind). -/
def posOf (s : Site) : Nat :=
  match SK.ofSite s with
  | some k => skTab.idxOf k
  | none => 0

/-- **The position read off the site of a state at position `n` is `n`.** -/
theorem posOf_eq {n : Nat} {s : Site} (hn : n < 268) (h : (skOf n).At s) : posOf s = n := by
  have h' := SK.at_iff.mp h
  simp only [posOf, h']
  exact pos_idx n hn

/-! ### The consumer's table of the warp matrix instructions -/

/-- **An entry of `Top.matrixSites` is a warp matrix instruction of the code, with its
operation.** -/
theorem matrixSites_op {j pc : Nat} {op : MatrixOp} (h : Top.matrixSites[j]? = some (pc, op)) :
    ∃ ins i, kernel.code[pc]? = some ins ∧ ins.op = .matrix i ∧ i.op = op := by
  have hm := List.mem_of_getElem? h
  unfold Top.matrixSites at hm
  obtain ⟨⟨ins, pc'⟩, hz, hf⟩ := List.mem_filterMap.mp hm
  have hc := List.mem_zipIdx_iff_getElem?.mp hz
  dsimp only at hf
  split at hf
  · rename_i m hop
    cases hf
    exact ⟨ins, m, hc, hop, rfl⟩
  · cases hf

/-- The instruction at an index of `mxPcs` is the warp matrix instruction of the same ordinal
in `Top.matrixSites`. -/
theorem mxPcs_site {j pc : Nat} (h : mxPcs[j]? = some pc) :
    ∃ op, Top.matrixSites[j]? = some (pc, op) := by
  rw [← mxPcs_eq, List.getElem?_map] at h
  cases hj : Top.matrixSites[j]? with
  | none => rw [hj] at h; cases h
  | some e =>
    rw [hj] at h
    obtain ⟨pc', op⟩ := e
    cases h
    exact ⟨op, rfl⟩

/-! ### The template of a matrix event -/

variable {L : Launch} {g : Nat} {t : TState}

/-- **The template of a warp matrix instruction at the sub-step of its matrix event** (the
first event of a `stmatrix`, the second of an `ldmatrix`, the one event of an `mma` or a
`movmatrix`) is undefined behaviour or a matrix event with the instruction's operation. -/
theorem matrix_tmpl {i : MatrixInstr} {κ : SiteKind}
    (hκ : Ref.opKind t.sub (.matrix i) = some κ) (hm : kindCls κ = .matrix) :
    (∃ f, matrixTmpl L g t i = .ub f) ∨ ∃ own k, matrixTmpl L g t i = .matrix i.op own k := by
  unfold matrixTmpl
  split
  · split
    · -- a matrix load or store
      rename_i m hrule hop
      simp only [Ref.opKind, hop] at hκ
      rw [hop]
      unfold matrixMoveTmpl
      dsimp only
      split
      · -- `stmatrix`
        rename_i hst
        simp only [hst, ↓reduceIte, Option.some.injEq] at hκ
        split
        · split
          · exact .inl ⟨_, rfl⟩
          · exact .inr ⟨_, _, rfl⟩
        · rename_i hs
          simp only [hs, ↓reduceIte] at hκ
          subst hκ
          cases hm
      · -- `ldmatrix`
        rename_i hst
        simp only [hst, Bool.false_eq_true, ↓reduceIte] at hκ
        split at hκ
        · rename_i h32
          simp only [Option.some.injEq] at hκ
          split
          · rename_i hs
            simp only [hs.2, ↓reduceIte] at hκ
            subst hκ
            cases hm
          · exact .inr ⟨_, _, rfl⟩
        · cases hκ
    · -- `movmatrix`
      rename_i d a hrule hop hd hs
      rw [hop]
      split
      · exact .inl ⟨_, rfl⟩
      · exact .inr ⟨_, _, rfl⟩
    · -- `mma`
      rename_i s hrule hop
      rw [hop]
      split
      · exact .inl ⟨_, rfl⟩
      · exact .inr ⟨_, _, rfl⟩
    · exact .inl ⟨_, rfl⟩
  · exact .inl ⟨_, rfl⟩

/-! ### Events that never block -/

/-- **An event fired at a site that is no `bar.sync` and no bulk-group wait never blocks its
thread**: by the table `firedAt` of the kinds of events of each kind of site, it is no barrier
arrival and no bulk-group wait, and the program has no other blocking kind of event. -/
theorem unblocking_of_fired {k : Kind} {κ : SiteKind} (h : firedAt k κ = true)
    (hb : κ ≠ .bar) (hw : κ ≠ .bulkWait) : Unblocking k := by
  cases k <;> first
    | trivial
    | (cases κ <;> first | exact absurd rfl hb | exact absurd rfl hw | cases h)

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
