-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Time
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.RefNext
public import Lemmas.Flow.Arith32Interval
public import Lemmas.Kernel.FailCounts

@[expose] public section

/-! # The index warp's termination measure

The measure of a state is its place capped at `top` (`measure`). A step the machine follows
(`place_step`) stays (a failed poll, the same block) or moves to a later place: inside a block a
step moves to a later site or element; the arrival on `valid_coord_ready` counts one more arrival
(`blockOf_arr`), so the next block's sites are one stride later; the barrier is past every block
(`endAt`). The block of the counts moves only at the arrival (`blockOf_quiet`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

attribute [local simp] placeAt ord endAt ixEndPlace endSlot ixOrg ixBlk0 loopBase ixOff stride
  ixSpan blockCap

/-- The largest place before the cap. -/
def top : Nat := ixEndPlace + 1

/-- **The index warp's measure.** -/
def measure (L : Launch) (g : Nat) (d : D) (n : Cnt → Nat) : Nat := min (place L g d n) top

theorem measure_le (d : D) (n : Cnt → Nat) : measure L g d n ≤ top := Nat.min_le_right _ _

/-! ### The block of the counts across a step -/

theorem loc_eq_iff {f f' : MbarFam} : MbarRow.loc L g f = MbarRow.loc L g f' ↔ f = f' :=
  ⟨loc_inj, congrArg _⟩

/-- An event that is no arrival keeps the block. -/
theorem blockOf_quiet {e : Event} (hq : ∀ l, kindOf e ≠ some (.arrive l)) (n : Cnt → Nat) :
    blockOf L g (Code.bump cls n e) = blockOf L g n := by
  simp only [blockOf, bump_eq (hq _)]

/-- The arrival on a slot of `valid_coord_ready` counts one more block. -/
theorem blockOf_arr {e : Event} {s : Fin 4} (hin : inRole e = true)
    (hk : kindOf e = some (.arrive (MbarRow.loc L g (.coordReady s)))) (n : Cnt → Nat) :
    blockOf L g (Code.bump cls n e) = blockOf L g n + 1 := by
  have h : ∀ j : Fin 4, Code.bump cls n e (.arrive (MbarRow.loc L g (.coordReady j))) =
      n (.arrive (MbarRow.loc L g (.coordReady j))) + if s = j then 1 else 0 := fun j => by
    by_cases hj : s = j
    · subst hj; rw [bump_self hin hk]; simp
    · rw [bump_eq (by rw [hk]; simp [loc_eq_iff, hj])]; simp [hj]
  simp only [blockOf, h]
  fin_cases s <;> simp <;> omega

/-! ### The transitions' sites -/

theorem mem_sub {a : IxSite} {l l' : List IxSite} (h : ∀ x ∈ l, x ∈ l') (ha : a ∈ l) : a ∈ l' :=
  h a ha

theorem mainTop_site (c : IxCtl) : (mainTop c).1 ∈ [.wA, .pf] := by
  unfold mainTop; dsimp only; split <;> simp

theorem mainDone_site (c : IxCtl) : (ixMainDone c).1 ∈ [.bar, .xpre] := by
  unfold ixMainDone; split <;> simp

theorem xTop_site (c : IxCtl) : (xTop c).1 ∈ [.wB, .xpf] := by
  unfold xTop; dsimp only; split <;> simp

theorem afterPre_site (c : IxCtl) : (afterPre P L g c).1 ∈ [.bar, .xpre, .wA, .pf] := by
  unfold afterPre; split
  · unfold ixNoMain; exact mem_sub (by decide) (mainDone_site _)
  · unfold mainEntry; exact mem_sub (by decide) (mainTop_site _)

theorem afterXpre_site (c : IxCtl) : (afterXpre L g c).1 ∈ [.bar, .wB, .xpf] := by
  unfold afterXpre; split
  · simp
  · exact mem_sub (by decide) (xTop_site _)

theorem mainEnd_site (c : IxCtl) : (mainEnd c).1 ∈ [.bar, .xpre, .wA, .pf] := by
  unfold mainEnd; dsimp only; split
  · exact mem_sub (by decide) (mainTop_site _)
  · exact mem_sub (by decide) (mainDone_site _)

theorem xEnd_site (c : IxCtl) : (xEnd c).1 ∈ [.bar, .wB, .xpf] := by
  unfold xEnd; dsimp only; split
  · exact mem_sub (by decide) (xTop_site _)
  · simp

theorem lens_site (c : IxCtl) : (ixLens c).1 ∈ [.bar, .xpre, .pre] := by
  unfold ixLens; dsimp only; split
  · unfold ixNoMain; exact mem_sub (by decide) (mainDone_site _)
  · simp

theorem afterA_site (c : IxCtl) : (ixAfterA P c).1 ∈ [.bar, .xpre, .pre, .lenB] := by
  unfold ixAfterA; split
  · exact mem_sub (by decide) (lens_site _)
  · simp

/-! ### The step -/

/-- An event counted as an arrival is one. -/
theorem kindOf_arrive {e : Event} {l : Loc} (h : kindOf e = some (.arrive l)) :
    ∃ tx cn r sc, e.kind = .arrive l tx cn r sc := by
  obtain ⟨pc, kd⟩ := e
  unfold kindOf at h
  split at h <;> simp_all

/-- An event of a site other than the arrivals is no arrival. -/
theorem quiet_of {d : D} {e : Event} (hk : EvK P L g d e) (ha : d.site ≠ .arrA)
    (hb : d.site ≠ .arrB) : ∀ l, kindOf e ≠ some (.arrive l) := by
  intro l h
  obtain ⟨tx, cn, r, sc, he⟩ := kindOf_arrive h
  unfold EvK at hk
  cases hs : d.site <;> simp [hs, NcEv, NcAt, PollEv, ShflEv, StoreEv, he] at hk ha hb

theorem ldNext_or (d : D) (y : BitVec 64) (n : BitVec 64 → BitVec 64 → D) :
    (d.el + 1 < 2 ∧ (ldNext d y n).site = d.site ∧ (ldNext d y n).el = d.el + 1) ∨
      ∃ y0 y1, ldNext d y n = n y0 y1 := by
  unfold ldNext; split
  · exact .inl ⟨by omega, rfl, rfl⟩
  · exact .inr ⟨_, _, rfl⟩

theorem stNext_or (d n : D) : (d.el + 1 < 2 ∧ (stNext d n).site = d.site ∧
    (stNext d n).el = d.el + 1) ∨ stNext d n = n := by
  unfold stNext; split
  · exact .inl ⟨by omega, rfl, rfl⟩
  · exact .inr rfl

/-- **Every step the machine follows** stays (the same state and block) or moves to a later
place. -/
theorem place_step (hp : Pre P L m) {d d' : D} {n : Cnt → Nat} {e : Event} (hev : Ev P L g d e)
    (hs : succ P L g d e = some (some d')) :
    (d' = d ∧ blockOf L g (Code.bump cls n e) = blockOf L g n) ∨
      place L g d n < place L g d' (Code.bump cls n e) := by
  obtain ⟨site, el, ac, c⟩ := d
  obtain ⟨hpc, hk⟩ := hev
  have hx : site ≠ .exit := by rintro rfl; simp [succ] at hs
  have hin : inRole e = true := by
    have := site_inRole site hx
    simp only [inRole, hpc, decide_eq_true_eq]; exact this
  by_cases harr : site = .arrA ∨ site = .arrB
  · right
    have hk' : kindOf e = some (.arrive (MbarRow.loc L g (.coordReady c.slot))) := by
      rcases harr with rfl | rfl <;> simp only [EvK] at hk <;> simp [kindOf, hk, ready_loc hp]
    simp only [place]
    rw [blockOf_arr hin hk' n]
    rcases harr with rfl | rfl <;> simp only [succ, Option.some.injEq] at hs <;> subst hs
    · have h := mainEnd_site c
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h <;> simp [h] <;> omega
    · have h := xEnd_site c
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h <;> simp [h] <;> omega
  have hb := blockOf_quiet (L := L) (g := g)
    (quiet_of hk (fun h => harr (.inl h)) (fun h => harr (.inr h))) n
  simp only [place]
  rw [hb]
  generalize blockOf L g n = i
  have hsite : ∀ (p : IxSite × IxCtl) (l : List IxSite), p.1 ∈ l → (∀ t ∈ l,
      placeAt i site el < placeAt i t 0) → d' = ofC p →
      (d' = ⟨site, el, ac, c⟩ ∧ i = i) ∨ placeAt i site el < placeAt i d'.site d'.el :=
    fun p l hm ht hd => .inr (by rw [hd]; exact ht _ hm)
  cases site with
  | exit | arrA | arrB => simp at hx harr
  | lenA =>
    rcases hk with ⟨a, bs, hk⟩ | ⟨f, hk⟩ <;> simp only [succ, lenNext, hk] at hs
    · obtain ⟨x, rfl⟩ := ncNext_some hs
      exact hsite _ _ (afterA_site _) (by
        intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl <;> simp) rfl
    · cases hs
  | lenB =>
    rcases hk with ⟨a, bs, hk⟩ | ⟨f, hk⟩ <;> simp only [succ, lenNext, hk] at hs
    · obtain ⟨x, rfl⟩ := ncNext_some hs
      exact hsite _ _ (lens_site _) (by
        intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl
        all_goals first | (simp; done) | (simp; omega)) rfl
    · cases hs
  | pre | pf | xpre | xpf =>
    rcases hk with ⟨a, bs, hk⟩ | ⟨f, hk⟩ <;> simp only [succ] at hs
    · obtain ⟨y, rfl⟩ := ncPair_some hs
      rcases ldNext_or ⟨_, el, ac, c⟩ y _ with ⟨h1, h2, h3⟩ | ⟨y0, y1, h⟩
      · right; rw [h2, h3]; simp only at h1 ⊢; simp; omega
      · first
        | exact hsite _ _ (afterPre_site _) (by
            intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
            rcases ht with rfl | rfl | rfl | rfl <;> simp) h
        | exact hsite _ _ (afterXpre_site _) (by
            intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
            rcases ht with rfl | rfl | rfl <;> simp <;> omega) h
        | exact hsite (.wA, { c with n0 := y0, n1 := y1 }) [.wA] (by simp) (by
            intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
            subst ht; simp; omega) h
        | exact hsite (.wB, { c with f0 := y0, f1 := y1 }) [.wB] (by simp) (by
            intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
            subst ht; simp; omega) h
    · simp only [ncPair, hk] at hs; cases hs
  | wA | wB =>
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩ <;> simp only [succ, poll, hk] at hs
    · cases ok <;> simp only [Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at hs <;>
        subst hs
      · exact .inl ⟨rfl, rfl⟩
      · right; simp
    · cases hs
  | sA1 | sA2 | sB1 | sB2 =>
    simp only [succ] at hs
    obtain ⟨r, rfl⟩ := shflNext_some hs
    right; simp
  | bA | bB | bar =>
    simp only [succ, Option.some.injEq] at hs
    subst hs
    right; simp
  | stA | stB =>
    simp only [succ, Option.some.injEq] at hs
    subst hs
    rcases stNext_or ⟨_, el, ac, c⟩ (ofC (afterSt L g _ _, c)) with ⟨h1, h2, h3⟩ | h
    · right; rw [h2, h3]; simp only at h1 ⊢; simp; omega
    · refine hsite _ [.bA, .arrA, .bB, .arrB] ?_ (by
        intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl <;> simp <;> omega) h
      rcases afterSt_cases (L := L) (g := g) (.bA : IxSite) .arrA with h | h <;>
        rcases afterSt_cases (L := L) (g := g) (.bB : IxSite) .arrB with h' | h' <;>
        simp [h, h']

/-! ### The bound measure: the loops ranked by their counters

The place above is read from the counts and is bounded only for at most `2 ^ 26 + 3` blocks,
which the reference invariant does not say. The bound measure (`bplace`) ranks the loops by
their own counters instead, as a loop ranked above its trip counter: the main loop's `neg` and
the extra loop's `xn` (32-bit words) each grow by one per block, and the loop leaves exactly when
the increment wraps to `0`, so a block's counter is below `2 ^ 32` and the next block's is one
more (`ctr_next`). It holds of every state (`bplace_le`) and every step stays at a failed poll or
raises it (`bplace_step`), with no invariant. -/

open PTX.Flow.Arith32 in
/-- The counter of a block, as a number below `2 ^ 32`. -/
def ctr (x : BitVec 64) : Nat := (r32 x).toNat

theorem ctr_lt (x : BitVec 64) : ctr x < 2 ^ 32 := by
  simp only [ctr, Arith32.r32, truncBits, BitVec.toNat_ofNat]
  omega

open PTX.Flow.Arith32 in
/-- **A loop's counter after a block that is not the last** is one more. -/
theorem ctr_next {x : BitVec 64} (h : scmpi .ne .b (addi x 1) 0 = true) :
    ctr (addi x 1) = ctr x + 1 := by
  simp only [ctr, scmpi, PTX.compare, addi, r32, i32, truncBits, BitVec.toNat_ofNat,
    BitVec.toNat_add, BitVec.toNat_ofInt, ne_eq, decide_eq_true_eq] at h ⊢
  omega

/-- The first place of the extra loop's region. -/
def xBase : Nat := 4 + 16 * 2 ^ 32

/-- The barrier's bound place. -/
def bEnd : Nat := xBase + 16 * 2 ^ 32 + 2

/-- **The bound place of a state.** -/
def bplace (d : D) : Nat :=
  match d.site with
  | .lenA => 0
  | .lenB => 1
  | .pre => 2 + min d.el 1
  | .pf | .wA | .sA1 | .sA2 | .stA | .bA | .arrA => 4 + 16 * ctr d.c.neg + ord d.site + min d.el 1
  | .xpre => xBase + min d.el 1
  | .xpf | .wB | .sB1 | .sB2 | .stB | .bB | .arrB =>
    xBase + 2 + 16 * ctr d.c.xn + ord d.site + min d.el 1
  | .bar => bEnd
  | .exit => bEnd + 1

/-- The largest bound place. -/
def btop : Nat := bEnd + 1

/-- The bound places' constants, for `omega`. -/
theorem bconsts : xBase = 4 + 16 * 2 ^ 32 ∧ bEnd = xBase + 16 * 2 ^ 32 + 2 ∧ btop = bEnd + 1 :=
  ⟨rfl, rfl, rfl⟩

/-- **Every state's bound place is at most `btop`.** -/
theorem bplace_le (d : D) : bplace d ≤ btop := by
  have h1 := ctr_lt d.c.neg
  have h2 := ctr_lt d.c.xn
  have := bconsts
  obtain ⟨s, el, ac, c⟩ := d
  cases s <;> simp only [bplace, ord] at h1 h2 ⊢ <;> omega

/-! #### The places the control words enter -/

theorem b_mainTop (c : IxCtl) : 8 + 16 * ctr c.neg ≤ bplace (ofC (mainTop c)) := by
  unfold mainTop; dsimp only; split <;> simp only [bplace, ord] <;> omega

theorem b_mainDone (c : IxCtl) : xBase ≤ bplace (ofC (ixMainDone c)) := by
  have := bconsts
  unfold ixMainDone; split <;> simp only [bplace] <;> omega

theorem b_noMain (c : IxCtl) : xBase ≤ bplace (ofC (ixNoMain c)) := by
  unfold ixNoMain; exact b_mainDone _

theorem b_afterPre (c : IxCtl) : 8 ≤ bplace (ofC (afterPre P L g c)) := by
  unfold afterPre; split
  · exact le_trans (by have := bconsts; omega) (b_noMain _)
  · unfold mainEntry; exact le_trans (by omega) (b_mainTop _)

theorem b_mainEnd (c : IxCtl) : 18 + 16 * ctr c.neg ≤ bplace (ofC (mainEnd c)) := by
  have hl := ctr_lt c.neg
  unfold mainEnd; dsimp only; split
  · rename_i h
    refine le_trans ?_ (b_mainTop _)
    dsimp only
    rw [ctr_next h]
    omega
  · refine le_trans ?_ (b_mainDone _)
    have := bconsts
    omega

theorem b_lens (c : IxCtl) : 2 ≤ bplace (ofC (ixLens c)) := by
  unfold ixLens; dsimp only; split
  · exact le_trans (by have := bconsts; omega) (b_noMain _)
  · simp only [bplace]; omega

theorem b_afterA (P : Params) (c : IxCtl) : 1 ≤ bplace (ofC (ixAfterA P c)) := by
  unfold ixAfterA; split
  · exact le_trans (by omega) (b_lens _)
  · simp only [bplace]; omega

theorem b_xTop (c : IxCtl) : xBase + 6 + 16 * ctr c.xn ≤ bplace (ofC (xTop c)) := by
  unfold xTop; dsimp only; split <;> simp only [bplace, ord] <;> omega

theorem b_afterXpre (c : IxCtl) : xBase + 2 ≤ bplace (ofC (afterXpre L g c)) := by
  unfold afterXpre; split
  · have := bconsts; simp only [bplace]; omega
  · exact le_trans (by omega) (b_xTop _)

theorem b_xEnd (c : IxCtl) : xBase + 16 + 16 * ctr c.xn ≤ bplace (ofC (xEnd c)) := by
  have hl := ctr_lt c.xn
  unfold xEnd; dsimp only; split
  · rename_i h
    refine le_trans ?_ (b_xTop _)
    dsimp only
    rw [ctr_next h]
    omega
  · have := bconsts
    simp only [bplace]
    omega

/-- **Every step of the machine stays at a failed poll (which does not count) or raises the
bound place.** -/
theorem bplace_step {d d' : D} {e : Event} (hs : succ P L g d e = some (some d')) :
    (d' = d ∧ e.counts = false) ∨ bplace d < bplace d' := by
  obtain ⟨site, el, ac, c⟩ := d
  have hn := ctr_lt c.neg
  have hx := ctr_lt c.xn
  have hb := bconsts
  have hpair : ∀ {n : BitVec 64 → BitVec 64 → D} {y : BitVec 64},
      (∀ y0 y1, bplace ⟨site, el, ac, c⟩ < bplace (n y0 y1)) →
      (el + 1 < 2 → bplace ⟨site, el, ac, c⟩ < bplace ⟨site, el + 1, [.bits 32 y], c⟩) →
      bplace ⟨site, el, ac, c⟩ < bplace (ldNext ⟨site, el, ac, c⟩ y n) := fun h1 h2 => by
    unfold ldNext; split
    · exact h2 ‹_›
    · exact h1 _ _
  have hst : ∀ {n : D}, bplace ⟨site, el, ac, c⟩ < bplace n →
      (el + 1 < 2 → bplace ⟨site, el, ac, c⟩ < bplace ⟨site, el + 1, [], c⟩) →
      bplace ⟨site, el, ac, c⟩ < bplace (stNext ⟨site, el, ac, c⟩ n) := fun h1 h2 => by
    unfold stNext; split
    · exact h2 ‹_›
    · exact h1
  cases site with
  | exit => simp [succ] at hs
  | lenA =>
    simp only [succ, lenNext] at hs
    split at hs
    · obtain ⟨x, rfl⟩ := ncNext_some hs
      exact .inr (lt_of_lt_of_le (by simp only [bplace]; omega) (b_afterA P _))
    · cases hs
  | lenB =>
    simp only [succ, lenNext] at hs
    split at hs
    · obtain ⟨x, rfl⟩ := ncNext_some hs
      exact .inr (lt_of_lt_of_le (by simp only [bplace]; omega) (b_lens _))
    · cases hs
  | pre =>
    simp only [succ] at hs
    obtain ⟨y, rfl⟩ := ncPair_some hs
    refine .inr (hpair (fun y0 y1 => lt_of_lt_of_le ?_
      (b_afterPre { c with m0 := y0, m1 := y1 })) fun h => ?_) <;>
      simp only [bplace] <;> omega
  | xpre =>
    simp only [succ] at hs
    obtain ⟨y, rfl⟩ := ncPair_some hs
    refine .inr (hpair (fun y0 y1 => lt_of_lt_of_le ?_
      (b_afterXpre { c with e0 := y0, e1 := y1 })) fun h => ?_) <;>
      simp only [bplace] <;> omega
  | pf | xpf =>
    simp only [succ] at hs
    obtain ⟨y, rfl⟩ := ncPair_some hs
    refine .inr (hpair (fun y0 y1 => ?_) fun h => ?_) <;> simp only [bplace, ord] <;> omega
  | wA | wB =>
    simp only [succ, poll] at hs
    split at hs
    next l q ok a sc hk =>
      cases ok <;> simp only [Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at hs <;>
        subst hs
      · exact .inl ⟨rfl, Event.counts_of_fail hk (by simp)⟩
      · right; simp only [bplace, ord]; omega
    · cases hs
  | sA1 | sA2 | sB1 | sB2 =>
    simp only [succ] at hs
    obtain ⟨r, rfl⟩ := shflNext_some hs
    right; simp only [bplace, ord]; omega
  | bA | bB | bar =>
    simp only [succ, Option.some.injEq] at hs
    subst hs
    right; simp only [bplace, ord]; omega
  | stA | stB =>
    simp only [succ, Option.some.injEq] at hs
    subst hs
    refine .inr (hst ?_ fun h => ?_)
    · rcases afterSt_cases (L := L) (g := g) (.bA : IxSite) .arrA with h | h <;>
        rcases afterSt_cases (L := L) (g := g) (.bB : IxSite) .arrB with h' | h' <;>
        simp only [h, h', bplace, ord] <;> omega
    · simp only [bplace, ord]
      omega
  | arrA =>
    simp only [succ, Option.some.injEq] at hs
    subst hs
    exact .inr (lt_of_lt_of_le (by simp only [bplace, ord]; omega) (b_mainEnd c))
  | arrB =>
    simp only [succ, Option.some.injEq] at hs
    subst hs
    exact .inr (lt_of_lt_of_le (by simp only [bplace, ord]; omega) (b_xEnd c))

/-- **The bound measure along a step**: it never falls and a counted event raises it. -/
theorem bplace_mono {d d' : D} {e : Event} (hs : succ P L g d e = some (some d')) :
    bplace d ≤ bplace d' ∧ (e.counts = true → bplace d < bplace d') := by
  rcases bplace_step hs with ⟨rfl, hc⟩ | hlt
  · exact ⟨Nat.le_refl _, fun h => by rw [hc] at h; cases h⟩
  · exact ⟨Nat.le_of_lt hlt, fun _ => hlt⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
