-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Tracked
public import Kernels.FlashKdaFwd.Proof.Ref.Compute.Reach
public import Kernels.FlashKdaFwd.Proof.Values.TileClaim
public import Kernels.FlashKdaFwd.Proof.Values.TileAlgebra
public import Kernels.FlashKdaFwd.Proof.Values.Ends.Bridge
public import Kernels.FlashKdaFwd.Proof.Values.Ends.CarryLoad

@[expose] public section

/-!
# The carry registers before the first tile and after the last

A compute thread (a thread with index below 128 in its thread block of 192 threads) holds 128
entries of the 128 x 128 state of its block in 128 data registers, its *carry registers*,
across the tile loop. The value induction over the tiles (`Proof/Values/TileClaim.lean`) says
what these registers hold inside the loop. This file proves the two facts at the ends of the
loop that connect it to the rest of the kernel:

* `tileBase` (the field `base` of `Values.TileHyps`, the base case of the induction): when a
  compute thread arrives at the first `ldmatrix` of the first tile (the site `matrixLoad 0`,
  having made no warp matrix event), its carry registers hold the initial state of its block,
  in the form the induction uses (the register table of ordinal 0 on the real arrays of
  tile 0).
* `finalCarries` (`Values.Ends.FinalCarries`): at the first of the 128 final stores (the site
  `store 18`, instruction 3132) the carry registers hold the state after the last token of the
  block's sequence. For a sequence with at least one tile this is the conclusion of the
  induction at the exit of the loop (`Values.TileClaim.exit`); for an empty sequence it is the
  initial state, which the thread still holds.

## Words

A *site* is an instruction of the kernel at which a thread makes an event; the state of the
generated thread machine (`Proof/Thread/`) is `d = ⟨site, w, p, x⟩`: the site the thread is
at, its integer registers `w`, its predicates `p`, and its *data slots* `x` (the values of the
data registers by register id, which the machine does not interpret). The carry registers are
128 of the data slots, with ids from 2118 to 2245. `stateAt (code L) X g k = some (some d)`
says that `d` is the state of the machine of thread `g` before position `k` of its trace
(event number `k`) in the execution `X`: a *followed* state. `ordinal X g k` is the number of
warp matrix events of the thread before position `k`. `tid g` is the index of thread `g` in
its block (`g % L.block`, and the block has 192 threads).

## The path of a compute thread around the tile loop

Before the loop: the 128 carry loads, the proxy fence at instruction 1401 (site
`fenceProxy 1`), the `bar.sync 0` at 1402 (site `bar 5`), then per tile a poll of the "empty"
mbarrier of the tile's output buffer (2144, site `mbarWait 7`), a poll of the "full" mbarrier
of its input buffer (2186, site `mbarWait 8`) and the first `ldmatrix` (2194, `matrixLoad 0`).
After the last tile, or directly from 1402 when the sequence has no token: the `bar.sync 0` at
3113 (site `bar 7`), then the first final store (3132, `store 18`).

## The proof

1. **Frame lemmas** (`frame_fence`, `frame_bar5`, `frame_pollE`, `frame_pollF`, `frame_row`,
   `frame_bar7`): the transition function of the machine at each of the six control sites of
   the path leaves the carry registers as they are. Five of them leave all data slots
   unchanged; the transition of `bar 7` runs the pointer arithmetic of the first final store,
   which writes three pointer registers (ids 2896, 2897, 2901) and no slot below 2246.
2. **Where the thread is.** The chain of the phases (`Assembly/Stage.lean: stage`) says in
   which phase a followed state is, with the history of the earlier phases:
   * the state at 1402 is the entry state of the Compute phase, and the state one position
     before it is at the fence 1401 (the last position of the CarryLoad phase);
   * the invariant of the Compute phase counts the events since 1402 (`Compute.counted`; a
     failed poll is not counted), so a state with at most three counted events is at 1402, at
     one of the two polls of tile 0 or at its first `ldmatrix`;
   * the exit state of the Compute phase is at 3113 with `182 * tiles` matrix events, and the
     state at the first final store is one position later (`Epilogue.InvW`).
3. **The values.** At the fence 1401 the carries hold the initial state
   (`Values.Ends.carries_initial`); the frame lemmas carry this to the first `ldmatrix`
   (`base_at`) and, for an empty sequence, to 3113 (`exit_empty`). For a sequence with tiles,
   `Values.TileClaim.exit` gives the table of ordinal 0 on the arrays of entry `tiles` of the
   family at the first visit of 3113, which is the exit state (`exit_tiles`); these arrays
   carry the final state (`Values.tileInputs_last`). `frame_bar7` carries either to 3132.

`Values.Ends.carriesHold_iff_holds` translates between "the carry registers hold the state
`S`" (`CarriesHold`) and the induction's register table of ordinal 0.

## Hypotheses of the two final theorems

The precondition `Pre P L mem0`, consistency of the execution, and the two contracts of the
value ends that `carries_initial` takes: `Values.Ends.CarryRef L X` (where the carry loads are
and what they read: the CarryLoad phase, `Ref/CarryLoad/CarryRef.lean: carryRef_of`) and
`Values.Ends.EarlyRead P L X` (what a read of the FP32 state buffer returns before the tile
loop: the protocol layer's read-back, `Values/Ends/Contract.lean: earlyRead`). `finalCarries`
also takes the conclusion of the induction, `Values.TileClaim P L mem0 X`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.TileEnds
open PTX PTX.Proof PTX.Flow PTX.Frame PTX.WarpMatrix
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Proof.Values (Followed TileClaim tableAt blockInputs)
open PTX.Kernels.FlashKdaFwd.Proof.Values.Ends (CarryRef EarlyRead CarriesHold carryReg
  initState finalState finalSite)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : ℕ}

/-! ## The frame: the control sites leave the carry registers as they are -/

/-- Two equal followed states are the same state (in the direction `subst` wants). -/
theorem some_some_inj {α : Type} {a b : α} (h : some (some a) = some (some b)) : b = a :=
  (Option.some.inj (Option.some.inj h)).symm

/-- A transition that continues under a condition and is a state: the condition holds and the
transition is that state. -/
theorem under_eq_some {α : Type} {Q : Prop} {o : Option (Option α)} {d' : α}
    (h : under Q o = some (some d')) : Q ∧ o = some (some d') := by
  by_cases hQ : Q
  · rw [under_pos hQ] at h
    exact ⟨hQ, h⟩
  · rw [under_neg hQ] at h
    cases h

/-- **The proxy fence at 1401** leaves every data slot unchanged. -/
theorem frame_fence {d d' : D} {e : Event} (hs : d.site = .fenceProxy 1)
    (hn : Thread.next L g d e = some (some d')) : d'.x = d.x := by
  obtain ⟨s, w, p, x⟩ := d
  cases hs
  rw [next_fenceProxy_1] at hn
  obtain rfl := some_some_inj hn
  rfl

/-- The transition function of `bar.sync 0` at 1402 keeps the data slots, on each of its
branches (the three roles; a sequence with or without tokens). -/
theorem after_bar_5_x (d : D) : (after_bar_5 L g d).x = d.x := by
  unfold after_bar_5 tail_2117 tail_2949 tail_1412 tail_1436
  dsimp only
  split_ifs <;> rfl

/-- **The `bar.sync 0` at 1402** leaves every data slot unchanged. -/
theorem frame_bar5 {d d' : D} {e : Event} (hs : d.site = .bar 5)
    (hn : Thread.next L g d e = some (some d')) : d'.x = d.x := by
  obtain ⟨s, w, p, x⟩ := d
  cases hs
  rw [next_bar_5] at hn
  obtain rfl := some_some_inj hn
  exact after_bar_5_x _

/-- The transition function of the poll at 2144 keeps the data slots (the code after a
successful poll, instructions 2149 to 2185, writes integer registers and a predicate). -/
theorem after_mbarWait_7_x (d : D) (ok : Bool) : (after_mbarWait_7 L g d ok).x = d.x := by
  unfold after_mbarWait_7
  dsimp only
  split_ifs <;> rfl

/-- The transition function of the poll at 2186 keeps the data slots (the code after a
successful poll, instructions 2189 to 2193, writes integer registers). -/
theorem after_mbarWait_8_x (d : D) (ok : Bool) : (after_mbarWait_8 L g d ok).x = d.x := by
  unfold after_mbarWait_8
  dsimp only
  split_ifs <;> rfl

/-- **The poll at 2144** (of the "empty" mbarrier of the output buffer), failed or successful,
leaves every data slot unchanged. -/
theorem frame_pollE {d d' : D} {e : Event} (hs : d.site = .mbarWait 7)
    (hn : Thread.next L g d e = some (some d')) : d'.x = d.x := by
  obtain ⟨s, w, p, x⟩ := d
  cases hs
  rw [next_mbarWait_7] at hn
  split at hn
  · obtain rfl := some_some_inj hn
    exact after_mbarWait_7_x _ _
  · cases hn

/-- **The poll at 2186** (of the "full" mbarrier of the input buffer), failed or successful,
leaves every data slot unchanged. -/
theorem frame_pollF {d d' : D} {e : Event} (hs : d.site = .mbarWait 8)
    (hn : Thread.next L g d e = some (some d')) : d'.x = d.x := by
  obtain ⟨s, w, p, x⟩ := d
  cases hs
  rw [next_mbarWait_8] at hn
  split at hn
  · obtain rfl := some_some_inj hn
    exact after_mbarWait_8_x _ _
  · cases hn

/-- **The row read of the first `ldmatrix`** (2194, first event) leaves every data slot
unchanged: the machine only remembers the row in its site. -/
theorem frame_row {d d' : D} {e : Event} (hs : d.site = .matrixLoad 0)
    (hn : Thread.next L g d e = some (some d')) : d'.x = d.x := by
  obtain ⟨s, w, p, x⟩ := d
  cases hs
  rw [next_matrixLoad_0] at hn
  obtain ⟨a, bs, -, hf⟩ := Compute.rdNext_some hn
  obtain rfl := Compute.ldRow_some hf
  rfl

/-- **The `bar.sync 0` at 3113** leaves every data slot below 2246 unchanged, the 128 carry
registers among them: for a compute thread the transition runs the pointer arithmetic of the
first final store (instructions 3115 to 3131), which writes the pointer slots 2896, 2897 and
2901 only; for the other threads it writes no data slot. -/
theorem frame_bar7 {d d' : D} {e : Event} (hs : d.site = .bar 7)
    (hn : Thread.next L g d e = some (some d')) : ∀ r < 2246, d'.x r = d.x r := by
  obtain ⟨s, w, p, x⟩ := d
  cases hs
  rw [next_bar_7] at hn
  unfold after_bar_7 at hn
  dsimp only at hn
  split at hn
  · obtain rfl := some_some_inj hn
    exact fun _ _ => rfl
  · unfold tail_3126 at hn
    obtain ⟨-, hn⟩ := under_eq_some hn
    unfold tail_3127 at hn
    obtain ⟨-, rfl⟩ := across_eq_some hn
    intro r hr
    dsimp only
    have hr1 : ∀ V, r ∉ (Run.r3127_facts1 V).map Prod.fst := by
      intro V hm
      have hm' : r ∈ [2897, 2901] := hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
      omega
    rw [valueEx_of_not_mem (hr1 _), Values.Ends.valueEx_ne (by omega)]

/-! ## Along a trace -/

/-- The thread layer's contract, from the precondition and consistency. -/
theorem followedOf (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) :
    Followed L mem0 X :=
  ⟨by rw [hpre.block], hX, fun _ h => Thread.sound hpre h, tracked hpre hX⟩

/-- A position beyond the end of a thread's trace has the state after its last event. -/
theorem at_min {k : ℕ} {d : D} (hσ : stateAt (code L) X g k = some (some d)) :
    stateAt (code L) X g (min k (X.tr g).length) = some (some d) := by
  rcases Nat.le_total k (X.tr g).length with hk | hk
  · rw [Nat.min_eq_left hk]
    exact hσ
  · rw [Nat.min_eq_right hk, ← stateAt_of_le hk]
    exact hσ

/-- The number of matrix events does not decrease along a trace. -/
theorem ordinal_mono {i k : ℕ} (h : i ≤ k) : ordinal X g i ≤ ordinal X g k :=
  (List.take_prefix_take_left h).sublist.countP_le

/-- A position beyond the end of a thread's trace has the matrix events of the whole trace. -/
theorem ordinal_min (k : ℕ) : ordinal X g (min k (X.tr g).length) = ordinal X g k := by
  rcases Nat.le_total k (X.tr g).length with hk | hk
  · rw [Nat.min_eq_left hk]
  · rw [Nat.min_eq_right hk]
    simp only [ordinal, List.take_of_length_le hk, List.take_of_length_le (Nat.le_refl _)]

/-- The number of counted events since a position does not decrease along a trace. -/
theorem counted_mono {j0 i k : ℕ} (h : i ≤ k) :
    Compute.counted X g j0 i ≤ Compute.counted X g j0 k :=
  ((List.take_prefix_take_left h).sublist.drop j0).countP_le

/-- An unlaunched thread makes no event. -/
theorem tr_nil (hX : Consistent L kernel Assumptions.all mem0 X) (hg : ¬ g < L.threads) :
    X.tr g = [] := by
  by_contra h
  obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil h
  refine hg (lt_of_get hX (g := g) (k := 0) (e := e) ?_)
  show (X.tr g)[0]? = some e
  rw [he]
  rfl

/-- **A followed state beyond the startup is a state of a launched thread**: the machine of an
unlaunched thread stays in its initial state, which is at an instruction of the startup. -/
theorem launched_of_site (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) {k : ℕ} {d : D}
    (hσ : stateAt (code L) X g k = some (some d)) (hpc : 384 < d.site.pc) : g < L.threads := by
  by_contra hg
  have hnil := tr_nil hX hg
  have h0 : stateAt (code L) X g k = stateAt (code L) X g 0 := by
    rw [stateAt_of_le (k := k) (by rw [hnil]; exact Nat.zero_le _), hnil]
    rfl
  have hi : (code L g).init = init L g := by with_reducible rfl
  rw [h0, stateAt_zero, hi] at hσ
  have hd : init L g = d := Option.some.inj (Option.some.inj hσ)
  have hle := pc_startup (Startup.invE_init (X := X) (g := g) hpre).inv
  rw [hd] at hle
  exact absurd (Nat.lt_of_lt_of_le hpc hle) (Nat.lt_irrefl _)

/-! ## Before the first tile -/

/-- **At the entry of the Compute phase the carries hold the initial state.** The entry state
of a compute thread (the state at the `bar.sync 0` of instruction 1402, before its event) is
the successor of the state at the proxy fence 1401, where the 128 carry loads are complete
(`Values.Ends.carries_initial`); the fence changes no data slot. -/
theorem entry_carries (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (R : CarryRef L X) (hrd : EarlyRead P L X) (hg : g < L.threads) (hc : tid g < 128)
    {j0 : ℕ} {s0 : D} (past : CarryLoadDone P L X g j0 s0) (hj0 : j0 ≤ (X.tr g).length) :
    CarriesHold (initState P (g / L.block)) (g % L.block) s0.x := by
  have F := followedOf hpre hX
  obtain ⟨j1, s1, -, hlen, hall⟩ := past.entry
  have hl : CarryLoad.len g = 129 := by simp only [CarryLoad.len, hc, ↓reduceIte]
  rw [hl] at hlen
  obtain ⟨sf, hσf⟩ := Values.Ends.state_before F hg past.state (show j0 - 1 ≤ j0 by omega)
  obtain ⟨pos, hr, -, hk⟩ := hall (j0 - 1) sf (by omega) (by omega) hσf
  have hsite : sf.site = .fenceProxy 1 := by
    cases pos with
    | ld j =>
      have hj := j.isLt
      have hd : CarryLoad.done g (.ld j) = j.val := rfl
      omega
    | fence => exact hr.site
  obtain ⟨e, he⟩ := Values.Ends.get_of_lt_length (X := X) (g := g) (k := j0 - 1) (by omega)
  have hσ0 : stateAt (code L) X g (j0 - 1 + 1) = some (some s0) := by
    rw [show j0 - 1 + 1 = j0 by omega]
    exact past.state
  have hx := frame_fence hsite (Values.Ends.next_some he hσf hσ0)
  have hb : L.sharedBase % 32 = 0 := by
    have h1 := hpre.sharedBase
    have h2 := hpre.sharedAlignment
    omega
  have hcar := Values.Ends.carries_initial F R hrd hb
    (by rw [block_mod hpre]; exact hc) (show j0 - 1 ≤ (X.tr g).length by omega) hσf hsite
  rw [hx]
  exact hcar

/-- **From the entry of the Compute phase to the first `ldmatrix`, no data slot changes.**
`s0` is the entry state at position `j0`; every state from `j0` to before `k` is a state of
the phase's invariant; at most three counted events lie between `j0` and `k`. Then every state
between the two has the data slots of the entry: it is at the `bar.sync 0` of 1402, at one of
the two polls of tile 0 or at the row read of its first `ldmatrix`, and the transitions of
these four sites keep the data slots. -/
theorem early_frame (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) {j0 k : ℕ} {s0 : D} (h0 : At (code L) X g j0 s0)
    (hall : ∀ i si, j0 ≤ i → i < k → At (code L) X g i si → Compute.Inv P L X g j0 i si)
    (hk : k ≤ (X.tr g).length) (hcnt : Compute.counted X g j0 k ≤ 3) :
    ∀ n s, j0 + n ≤ k → At (code L) X g (j0 + n) s → s.x = s0.x := by
  have F := followedOf hpre hX
  intro n
  induction n with
  | zero =>
    intro s _ hσ
    rw [Nat.add_zero] at hσ
    obtain rfl := some_some_inj (h0.symm.trans hσ)
    rfl
  | succ n ih =>
    intro s' hle hσ'
    obtain ⟨e, he⟩ := Values.Ends.get_of_lt_length (X := X) (g := g) (k := j0 + n) (by omega)
    obtain ⟨s, hσ⟩ := Values.Ends.state_before F hg hσ' (Nat.le_succ (j0 + n))
    have hx := ih s (by omega) hσ
    have hn := Values.Ends.next_some he hσ hσ'
    obtain ⟨pos, hR, -, -, hc⟩ := hall (j0 + n) s (by omega) (by omega) hσ
    have hle3 : pos.idx ≤ 3 := by
      rw [← hc]
      exact (counted_mono (by omega)).trans hcnt
    rw [← hx]
    cases pos with
    | entry => exact frame_bar5 hR.site hn
    | tile t m =>
      have hm : 1 + 268 * t + m ≤ 3 := hle3
      obtain rfl : t = 0 := by omega
      have hm2 : m ≤ 2 := by omega
      have hat : (Compute.skOf m).At s.site := hR.site
      interval_cases m
      · exact frame_pollE hat hn
      · exact frame_pollF hat hn
      · exact frame_row hat hn

/-- **The base case at one state**: a followed state of a launched thread at the first
`ldmatrix` of the tile loop, with no matrix event before it, holds the initial state of its
block in its carry registers. -/
theorem base_at (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (R : CarryRef L X) (hrd : EarlyRead P L X) (hg : g < L.threads) {k : ℕ} {d : D}
    (ho : ordinal X g k = 0) (hσ : stateAt (code L) X g k = some (some d))
    (hs : d.site = .matrixLoad 0) :
    CarriesHold (initState P (g / L.block)) (g % L.block) d.x := by
  -- a position within the trace
  have hσ' := at_min hσ
  have ho' : ordinal X g (min k (X.tr g).length) = 0 := by rw [ordinal_min]; exact ho
  have hkl : min k (X.tr g).length ≤ (X.tr g).length := Nat.min_le_right _ _
  generalize min k (X.tr g).length = k' at hσ' ho' hkl
  -- the state is in the Compute phase
  have hpc : d.site.pc = 2194 := by rw [hs]; rfl
  obtain ⟨hc, j0, s0, past, hj, hin, hI⟩ :=
    (stage hpre hX hg hkl hσ').of_pc_compute (by omega) (by omega)
  obtain ⟨pos, hR, hled, -, hcnt⟩ := hI
  cases pos with
  | entry =>
    have h5 : d.site = .bar 5 := hR.site
    rw [hs] at h5
    cases h5
  | tile t n =>
    -- position 2 of tile 0
    have hn : n = 2 := by
      rw [Compute.pos_of_site (k := .ld 0) hR.facts.pos hR.site (by rw [hs]; rfl)]
      decide
    subst hn
    have hm : ordinal X g k' = 182 * t + Compute.matOf 2 := congrArg Compute.Led.mats hled
    have hm0 : Compute.matOf 2 = 0 := by decide
    obtain rfl : t = 0 := by omega
    -- no exit of the phase before `k'`: after it the thread is in the epilogue
    have hall : ∀ i si, j0 ≤ i → i < k' → At (code L) X g i si →
        Compute.Inv P L X g j0 i si := by
      intro i si hji hik hσi
      rcases Compute.inv_at hpre hX hg past.state hin hji (by omega) hσi with
        h | ⟨j, s1, -, hj1, hσ1, hout⟩
      · exact h
      · have := (pc_epilogue (Epilogue.epilogue_weak hpre hX hg hσ1
          (Epilogue.in_of_compute hout) (by omega) hkl hσ')).1
        omega
    have hc3 : Compute.counted X g j0 k' ≤ 3 := by
      rw [hcnt]
      exact Nat.le_refl 3
    have hx := early_frame hpre hX hg past.state hall hkl hc3 (k' - j0) d (by omega)
      (by rw [show j0 + (k' - j0) = k' by omega]; exact hσ')
    rw [hx]
    exact entry_carries hpre hX R hrd hg hc past (by omega)

/-! ## After the last tile -/

/-- The position of the epilogue at the site of the first final store. -/
theorem pos_of_final {pos : Epilogue.Pos} (h : finalSite 0 = pos.site) : pos = .st 0 := by
  cases pos <;> simp only [finalSite, Epilogue.Pos.site, Site.store.injEq, Fin.mk.injEq,
    reduceCtorEq] at h
  congr 1
  exact Fin.ext (by simpa using h.symm)

/-- **The exit of the tile loop of an empty sequence**: the thread went from the `bar.sync 0`
of 1402 directly to the one of 3113, and still holds the initial state, which is the final
state of a sequence without tokens. -/
theorem exit_empty (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (R : CarryRef L X) (hrd : EarlyRead P L X) (hg : g < L.threads) (hc : tid g < 128)
    {j0 j1 : ℕ} {s0 s1 : D} (past : CarryLoadDone P L X g j0 s0) (hσ1 : At (code L) X g j1 s1)
    (hout : Compute.Out P L X g j0 j1 s1)
    (hall : ∀ i si, j0 ≤ i → i < j1 → At (code L) X g i si → Compute.Inv P L X g j0 i si)
    (hj1 : j1 ≤ (X.tr g).length) (hT : Compute.tilesOf P g = 0) :
    CarriesHold (initState P (g / L.block)) (g % L.block) s1.x := by
  obtain ⟨-, -, hj, hcnt⟩ := hout
  have hc3 : Compute.counted X g j0 j1 ≤ 3 := by
    rw [hcnt, hT]
    decide
  have hx := early_frame hpre hX hg past.state hall hj1 hc3 (j1 - j0) s1 (by omega)
    (by rw [show j0 + (j1 - j0) = j1 by omega]; exact hσ1)
  rw [hx]
  exact entry_carries hpre hX R hrd hg hc past (by omega)

/-- **The exit of the tile loop is the first visit of the `bar.sync 0` of 3113**: an earlier
followed state with the same number of matrix events, at least 182, is a state of the Compute
phase's invariant (no position of which is at that site) or precedes the phase (where the
thread has made no matrix event). -/
theorem exit_first {j0 j1 k' : ℕ} {s0 d' : D} (hin : Compute.In P L X g j0 s0)
    (hall : ∀ i si, j0 ≤ i → i < j1 → At (code L) X g i si → Compute.Inv P L X g j0 i si)
    (hk' : k' ≤ j1) (hσ' : At (code L) X g k' d') (hs' : d'.site = .bar 7)
    (ho : 1 ≤ ordinal X g k') : k' = j1 := by
  by_contra hne
  rcases Nat.lt_or_ge k' j0 with hlt | hge
  · have h0 : ordinal X g j0 = 0 := congrArg Compute.Led.mats hin.2
    have := ordinal_mono (X := X) (g := g) hlt.le
    omega
  · obtain ⟨pos, hR, -⟩ := hall k' d' hge (by omega) hσ'
    exact hR.ne_bar7 hs'

/-- **A sequence without tiles ends in its initial state**: the real arrays of entry 0 of the
family of a block carry the initial state (`Values.tileInputs_first`) and, when the sequence
has no tile, the final state (`Values.tileInputs_last`). The launch memory `mem0` only names
the family. -/
theorem final_eq_init (mem0 : Mem0) {c : ℕ} (hT : tiles (P.length (c % P.sequences)) = 0) :
    finalState P c = initState P c := by
  funext v k
  have h1 := Values.tileInputs_last P mem0 (c % P.sequences) (c / P.sequences) k.isLt v.isLt
  have h2 := Values.tileInputs_first P mem0 (c % P.sequences) (c / P.sequences) k.isLt v.isLt
  rw [hT] at h1
  exact h1.symm.trans h2

/-- **The exit of the tile loop of a sequence with tiles**: at the exit state (the state at
the `bar.sync 0` of 3113 that the Compute phase's exit condition describes) the carries hold
the state after the last token. The value induction gives the register table of ordinal 0 on
the arrays of entry `tiles` of the block's family at the first visit of that site
(`Values.TileClaim.exit`); the exit state is that first visit (`exit_first`), and these arrays
carry the final state (`Values.tileInputs_last`). Thread `g` is lane `l` of warp `w` of block
`c`. -/
theorem exit_tiles (hpre : Pre P L mem0) (T : TileClaim P L mem0 X) {c w l : ℕ}
    (hc : c < L.grid) (hw : w < 4) (hl : l < 32) (hgc : g = c * L.block + 32 * w + l)
    {j0 j1 : ℕ} {s0 s1 : D} (hin : Compute.In P L X g j0 s0) (hσ1 : At (code L) X g j1 s1)
    (hout : Compute.Out P L X g j0 j1 s1)
    (hall : ∀ i si, j0 ≤ i → i < j1 → At (code L) X g i si → Compute.Inv P L X g j0 i si)
    (hT : 0 < Compute.tilesOf P g) :
    CarriesHold (finalState P (g / L.block)) (g % L.block) s1.x := by
  have hb := hpre.block
  obtain ⟨hx, hled, -, -⟩ := hout
  have ho : ordinal X g j1 = 182 * Compute.tilesOf P g := congrArg Compute.Led.mats hled
  -- the conclusion of the induction, for the thread `g`
  have hE : ∀ k d, stateAt (code L) X g k = some (some d) → d.site = .bar 7 →
      1 ≤ ordinal X g k / 182 → ∃ k' ≤ k, ∃ d', stateAt (code L) X g k' = some (some d') ∧
        d'.site = .bar 7 ∧ ordinal X g k' = ordinal X g k ∧
        (tableAt 0).Holds (blockInputs P mem0 c (ordinal X g k / 182)) w l d'.x := by
    subst hgc
    exact T.exit hc hw hl
  obtain ⟨k', hk', d', hσ', hs', ho', hH⟩ := hE j1 s1 hσ1 hx.site (by rw [ho]; omega)
  obtain rfl : j1 = k' := (exit_first hin hall hk' hσ' hs' (by rw [ho', ho]; omega)).symm
  obtain rfl := some_some_inj (hσ1.symm.trans hσ')
  -- the block, the warp and the lane of `g`
  have hgc' : g = c * 192 + 32 * w + l := by rw [hgc, hb]
  have hq : g / 192 = c := by omega
  have hr : g % 192 = 32 * w + l := by omega
  have hdiv : ordinal X g j1 / 182 = tiles (P.length (c % P.sequences)) := by
    rw [ho, Nat.mul_div_cancel_left _ (by decide)]
    show tiles (P.length (g / 192 % P.sequences)) = _
    rw [hq]
  rw [hdiv] at hH
  rw [hb, hq, hr]
  refine (Values.Ends.carriesHold_iff_holds (S := finalState P c) (tid := 32 * w + l)
    (val := d'.x) (by omega) (x := blockInputs P mem0 c (tiles (P.length (c % P.sequences))))
    (fun k ch hk hch =>
      Values.tileInputs_last P mem0 (c % P.sequences) (c / P.sequences) hk hch)).mpr ?_
  rw [show (32 * w + l) / 32 = w by omega, show (32 * w + l) % 32 = l by omega]
  exact hH

/-- **The final carries at one state**: a followed state of a compute thread at the first
final store holds the state after the last token of its block's sequence in its carry
registers. The state is the successor of the exit state of the tile loop (the epilogue's
invariant puts it one position after the `bar.sync 0` of 3113), whose carries are known
(`exit_tiles`, `exit_empty`), and the transition of that barrier keeps them (`frame_bar7`).
Thread `g` is lane `l` of warp `w` of block `c`. -/
theorem final_at (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (R : CarryRef L X) (hrd : EarlyRead P L X) (T : TileClaim P L mem0 X) {c w l : ℕ}
    (hc : c < L.grid) (hw : w < 4) (hl : l < 32) (hgc : g = c * L.block + 32 * w + l)
    (hg : g < L.threads) {k : ℕ} {d : D} (hσ : stateAt (code L) X g k = some (some d))
    (hs : d.site = finalSite 0) :
    CarriesHold (finalState P (g / L.block)) (g % L.block) d.x := by
  have hb := hpre.block
  have hct : tid g < 128 := by
    unfold tid
    rw [hgc, hb]
    omega
  -- a position within the trace
  have hσ' := at_min hσ
  have hkl : min k (X.tr g).length ≤ (X.tr g).length := Nat.min_le_right _ _
  generalize min k (X.tr g).length = k' at hσ' hkl
  -- the state is in the epilogue, one position after the exit state of the tile loop
  have hpc : d.site.pc = 3132 := by rw [hs]; rfl
  obtain ⟨j1, s1, past, hj1, ⟨pos, hR, -, hkp, -⟩, -⟩ :=
    (stage hpre hX hg hkl hσ').of_pc_epilogue (by omega) (.inr (by omega))
  obtain rfl := pos_of_final (hs.symm.trans hR.site)
  obtain rfl : k' = j1 + 1 := hkp
  have hσ1 := past.state
  have hs1 : s1.site = .bar 7 := past.into.1.site
  obtain ⟨e, he⟩ := Values.Ends.get_of_lt_length (X := X) (g := g) (k := j1) (by omega)
  have hfr := frame_bar7 hs1 (Values.Ends.next_some he hσ1 hσ')
  -- the carries at the exit state
  have hS : CarriesHold (finalState P (g / L.block)) (g % L.block) s1.x := by
    obtain ⟨j0, s0, cld, hj0, h | h | h⟩ := past.entry
    · obtain ⟨-, hin, hout, hall⟩ := h
      rcases Nat.eq_zero_or_pos (Compute.tilesOf P g) with hT | hT
      · have h1 := exit_empty hpre hX R hrd hg hct cld hσ1 hout hall (by omega) hT
        have hT' : tiles (P.length (g / L.block % P.sequences)) = 0 := by
          rw [hb]
          exact hT
        rw [final_eq_init mem0 hT']
        exact h1
      · exact exit_tiles hpre T hc hw hl hgc hin hσ1 hout hall hT
    · have := (warp_eq4_iff g).mp h.1
      omega
    · have := (warp_eq5_iff g).mp h.1
      omega
  intro j hj
  rw [hfr _ (Values.Ends.carryRow_ok hj).2.2.2.2.2.2]
  exact hS j hj

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.TileEnds

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow PTX.Frame PTX.WarpMatrix
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The base case of the value induction over the tiles** (the field `base` of
`Values.TileHyps`, verbatim): for every compute warp `w < 4` of every thread block `c`, when a
lane arrives at the first `ldmatrix` of the first tile (a followed state at the site
`matrixLoad 0` with no matrix event before it), its data slots satisfy the register table of
ordinal 0 on the real arrays of tile 0 of the block: the 128 carry registers hold the binary32
payloads of the lane's entries of the initial state.

Hypotheses: the precondition, consistency, and the two contracts of the carry loads
(`Values.Ends.CarryRef`: where the loads are and what they read, from the CarryLoad phase;
`Values.Ends.EarlyRead`: what a read of the FP32 state buffer returns before the tile loop,
from the protocol layer's read-back). -/
theorem tileBase (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (R : Values.Ends.CarryRef L X) (hrd : Values.Ends.EarlyRead P L X) :
    ∀ c w, c < L.grid → w < 4 →
      Values.Base (L := L) (Values.blockInputs P mem0 c) w X (c * L.block + 32 * w) := by
  intro c w hc hw l hl k d ho hσ hs
  have hb := hpre.block
  have hg : c * L.block + 32 * w + l < L.threads := by
    have h1 : (c + 1) * L.block ≤ L.grid * L.block := Nat.mul_le_mul_right _ hc
    rw [Launch.threads]
    rw [hb] at h1 ⊢
    omega
  have hC := TileEnds.base_at hpre hX R hrd hg ho hσ hs
  rw [show (c * L.block + 32 * w + l) / L.block = c by rw [hb]; omega,
    show (c * L.block + 32 * w + l) % L.block = 32 * w + l by rw [hb]; omega] at hC
  have hH := (Values.Ends.carriesHold_iff_holds (S := Values.Ends.initState P c)
    (tid := 32 * w + l) (val := d.x) (by omega) (x := Values.blockInputs P mem0 c 0)
    (fun k ch hk hch =>
      Values.tileInputs_first P mem0 (c % P.sequences) (c / P.sequences) hk hch)).mp hC
  rw [show (32 * w + l) / 32 = w by omega, show (32 * w + l) % 32 = l by omega] at hH
  exact hH

/-- **The carries after the last tile** (`Values.Ends.FinalCarries`, the hypothesis of the
value ends' theorems about the final stores): at the first of its 128 final stores (the site
`store 18`, instruction 3132) a compute thread holds, in its 128 carry registers, the binary32
payloads of its entries of the state after the last token of its block's sequence (the initial
state when the sequence is empty).

Hypotheses: the precondition, consistency, the two contracts of the carry loads (used for a
sequence without tiles, whose final state is the initial state the thread loaded) and the
conclusion `T` of the value induction over the tiles (used for a sequence with tiles). -/
theorem finalCarries (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (R : Values.Ends.CarryRef L X) (hrd : Values.Ends.EarlyRead P L X)
    (T : Values.TileClaim P L mem0 X) : Values.Ends.FinalCarries P L X := by
  intro g k d hc hσ hs
  have hb := hpre.block
  have hg : g < L.threads := TileEnds.launched_of_site hpre hX hσ (by rw [hs]; decide)
  have hg' : g < L.grid * 192 := by
    rw [← hb]
    exact hg
  rw [hb] at hc
  exact TileEnds.final_at hpre hX R hrd T (c := g / 192) (w := g % 192 / 32)
    (l := g % 192 % 32) (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg')) (by omega)
    (Nat.mod_lt _ (by decide)) (by rw [hb]; omega) hg hσ hs

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
