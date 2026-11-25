-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Compute.Trace
public import Kernels.FlashKdaFwd.Proof.Ref.Compute.Access

@[expose] public section

/-! # The Compute phase: from sites to positions, and the control side of "not dead"

What the exports of the phase share, beyond the phase theorem (`Trace.lean: inv_at`, `traces`)
and the closed forms of the events (`Events.lean`, `Access.lean`):

* **From a site to its position.** `SK.ofSite s` is the kind (`SK`) of a site of the tile
  loop; `SK.at_iff` says `k.At s ↔ SK.ofSite s = some k`; `pos_unique`: two positions below 268
  with the same kind of site are the same position, so the site of a state of the invariant
  determines its position in the tile (`skTab.idxOf`: `pos_idx`).
* **The exit site.** No position of the invariant is at `bar_7` (`RefAt.ne_bar7`); a followed
  state at `bar_7` after the entry has the exit condition at an earlier or the same position
  (`out_of_bar7`).
* **The successor is a state at the seven control positions** (`ok_control`): from the
  invariant and the event actually fired at the entry, a poll, the named barrier, the fence or
  an arrival, `Thread.next` is `some (some _)`: no breakpoint, no address out of range, and
  `mapa` succeeds. At the 262 other positions the successor function is one of the forms of
  `StepLib.lean` (`mxNext`, `rdNext`, `stNext`, `wrNext`, with `ldRow`, `stRecv`, `across`),
  whose only outcomes other than a state are data conditions: bytes that are unknown or do not
  form values, and the conditions of the floating-point runs.
* **The operation of a matrix event** (`matrix_op`): a `.matrix op own recv` event fired by the
  instruction `.matrix i` has `op = i.op`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Bar uses)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g t : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}
  {tt : TState} {ins : Instr} {e : Event} {o : Option TState}

/-! ### From a site to its position -/

/-- The kind of a site of the tile loop (none for the sites of other kinds). -/
def SK.ofSite : Site → Option SK
  | .mbarWait j => some (.wait j)
  | .matrixLoad j => some (.ld j)
  | .matrixLoadMx j _ => some (.ldMx j)
  | .warpMma j => some (.mma j)
  | .matrixMove j => some (.mv j)
  | .matrixStore j => some (.st j)
  | .matrixStoreWr j _ => some (.stWr j)
  | .load j => some (.load j)
  | .bar j => some (.bar j)
  | .fenceProxy j => some (.fence j)
  | .mbarArrive j => some (.arrive j)
  | _ => none

theorem SK.at_iff {k : SK} {s : Site} : k.At s ↔ SK.ofSite s = some k := by
  constructor
  · intro h
    cases k <;> simp only [SK.At] at h <;> first
      | (subst h; rfl)
      | (obtain ⟨row, rfl⟩ := h; rfl)
  · intro h
    cases s <;> simp only [SK.ofSite, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      first
        | rfl
        | exact ⟨_, rfl⟩

/-- The positions of a tile have pairwise different kinds of sites. -/
theorem pos_idx : ∀ n < 268, skTab.idxOf (skOf n) = n := by decide +kernel

/-- **The kind of the site determines the position.** -/
theorem pos_unique {n m : Nat} (hn : n < 268) (hm : m < 268) (h : skOf n = skOf m) : n = m := by
  rw [← pos_idx n hn, ← pos_idx m hm, h]

/-- The position of a state of the invariant whose site is of kind `k`. -/
theorem pos_of_site {k : SK} {n : Nat} {s : Site} (hn : n < 268) (hat : (skOf n).At s)
    (hk : SK.ofSite s = some k) : n = skTab.idxOf k := by
  have h := SK.at_iff.mp hat
  rw [hk] at h
  rw [← pos_idx n hn, Option.some.inj h]

/-! ### The exit site -/

/-- No position of the invariant is at `bar_7`. -/
theorem RefAt.ne_bar7 {pos : Pos} {s : D} (h : RefAt P L g pos s) : s.site ≠ .bar 7 := by
  intro hs
  cases pos with
  | entry =>
    have h5 : s.site = .bar 5 := h.site
    rw [hs] at h5
    exact absurd (Site.bar.inj h5) (by decide)
  | tile t n =>
    have hn : n < 268 := h.facts.pos
    have hat : (skOf n).At s.site := h.site
    rw [hs] at hat
    have hi := pos_of_site hn hat (k := .bar 7) rfl
    have hbad : skTab.idxOf (SK.bar 7) = 268 := by decide +kernel
    omega

/-- **A followed state at `bar_7`** of a thread that was at the entry at `k0`: the exit
condition held at a followed state between the entry and it. -/
theorem out_of_bar7 (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) {k0 k : Nat} {s0 s : D} (h0 : At (code L) X g k0 s0)
    (hin : In P L X g k0 s0) (hk0 : k0 ≤ k) (hk : k ≤ (X.tr g).length)
    (hs : At (code L) X g k s) (h7 : s.site = .bar 7) :
    ∃ j s1, k0 ≤ j ∧ j ≤ k ∧ At (code L) X g j s1 ∧ Out P L X g k0 j s1 := by
  rcases inv_at hpre hX hg h0 hin hk0 hk hs with ⟨pos, hR, -⟩ | h
  · exact absurd h7 hR.ne_bar7
  · exact h

/-! ### The successor is a state at the control positions -/

/-- The control positions: the entry, the two polls, the named barrier, the fence and the two
arrivals. -/
def Pos.control : Pos → Prop
  | .entry => True
  | .tile _ n => n ≤ 1 ∨ 264 ≤ n

/-- **No dead control transition**: at a control position the successor of the event actually
fired is a state. -/
theorem ok_control (hpre : Pre P L mem0) (hg : g < L.threads) {pos : Pos} {s : D}
    (h : RefAt P L g pos s) (hctl : pos.control) (hat : (code L g).AtD s tt)
    (hc : kernel.code[s.site.pc]? = some ins)
    (hf : Fires s.site.pc (eventTmpl Assumptions.all L g tt ins.op) e o) :
    ∃ s', Thread.next L g s e = some (some s') := by
  obtain ⟨site, w, p, x⟩ := s
  cases pos with
  | entry =>
    obtain rfl : site = .bar 5 := h.site
    exact ⟨_, next_bar_5 _ _ _ _⟩
  | tile t n =>
    have hn : n < 268 := h.facts.pos
    have hctl' : n ≤ 1 ∨ 264 ≤ n := hctl
    obtain rfl | rfl | rfl | rfl | rfl | rfl :
        n = 0 ∨ n = 1 ∨ n = 264 ∨ n = 265 ∨ n = 266 ∨ n = 267 := by omega
    · obtain rfl : site = .mbarWait 7 := h.site
      obtain ⟨ok, rfl⟩ := ev_pollE hpre h.facts hat hc hf
      exact ⟨after_mbarWait_7 L g ⟨.mbarWait 7, w, p, x⟩ ok, next_mbarWait_7 _ _ _ _⟩
    · obtain rfl : site = .mbarWait 8 := h.site
      obtain ⟨ok, rfl⟩ := ev_pollF hpre h.facts hat hc hf
      exact ⟨after_mbarWait_8 L g ⟨.mbarWait 8, w, p, x⟩ ok, next_mbarWait_8 _ _ _ _⟩
    · obtain rfl : site = .bar 6 := h.site
      exact ⟨_, next_bar_6 _ _ _ _⟩
    · obtain rfl : site = .fenceProxy 2 := h.site
      exact ⟨_, next_fenceProxy_2 _ _ _ _⟩
    · obtain rfl : site = .mbarArrive 4 := h.site
      obtain ⟨d', hd, -, -⟩ := tl_arriveF (s := .mbarArrive 4) hpre hg h.facts
      exact ⟨d', by rw [next_mbarArrive_4, hd]⟩
    · obtain rfl : site = .mbarArrive 5 := h.site
      exact ⟨_, next_mbarArrive_5 _ _ _ _⟩

/-! ### The operation of a matrix event -/

/-- **A matrix event has the operation of its instruction.** -/
theorem matrix_op {i : MatrixInstr} {pc : Nat} {op : MatrixOp} {own recv : List (Option Byte)}
    (hf : Fires pc (matrixTmpl L g tt i) e o) (hk : e.kind = .matrix op own recv) :
    op = i.op := by
  unfold matrixTmpl at hf
  split at hf
  · split at hf
    · rename_i m hrule hop
      unfold matrixMoveTmpl at hf
      dsimp only at hf
      rw [hop]
      repeat' split at hf
      all_goals first
        | (obtain ⟨recv', rfl, -⟩ := hf; cases hk; rfl)
        | (obtain ⟨bs, -, rfl, -⟩ := hf; cases hk)
        | (obtain ⟨rfl, -⟩ := hf; cases hk)
    · rename_i d a hrule hop hd hs
      rw [hop]
      split at hf
      · obtain ⟨rfl, -⟩ := hf
        cases hk
      · obtain ⟨recv', rfl, -⟩ := hf
        cases hk
        rfl
    · rename_i s hrule hop
      rw [hop]
      split at hf
      · obtain ⟨rfl, -⟩ := hf
        cases hk
      · obtain ⟨recv', rfl, -⟩ := hf
        cases hk
        rfl
    · obtain ⟨rfl, -⟩ := hf
      cases hk
  · obtain ⟨rfl, -⟩ := hf
    cases hk

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
