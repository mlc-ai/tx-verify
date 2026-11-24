-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WtBar0One

@[expose] public section

/-!
# `Bar0Facts.lock`: the lanes of a warp agree on the ordinal of their last-generation arrival

`¬ BarMismatch` (a disjunct of `Unsafe`): the lanes of a warp agree on the barrier and the count at
each barrier position (the `k`-th barrier event of each, over every barrier id). Let `bl y` be the
list of the barrier events of thread `y`. The first `p` entries of `bl y` and `bl y'` then have the
same ids, so the barrier-0 events among them are as many (`countP_take_congr`); the barrier-0
events before the event at index `j` are those among the first `p = #(barrier events before j)`
entries of `bl y` (`countP_take_filter`). A last-generation arrival of `y` at position `p` is a
barrier-0 event without a count with at least two earlier barrier-0 events, and a lane `y'` that has
a barrier event at position `p` has the same event there, with the same number of earlier barrier-0
events: a last-generation arrival too, so at its only one (`bar0_one`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Progress

noncomputable section
set_option maxRecDepth 100000

/-! ### Lists -/

theorem filter_getElem?_take {α : Type} (p : α → Bool) :
    ∀ (l : List α) (i : Nat) (e : α), l[i]? = some e → p e = true →
      (l.filter p)[(l.take i).countP p]? = some e := by
  intro l
  induction l with
  | nil => intro i e h; simp at h
  | cons a t ih =>
    intro i e h hp
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [hp]
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      by_cases ha : p a = true
      · simp [List.take_succ_cons, ha, ih i e h hp]
      · simp [List.take_succ_cons, ha, ih i e h hp]

theorem countP_take_filter {α : Type} (p q : α → Bool) (hq : ∀ a, q a = true → p a = true) :
    ∀ (l : List α) (j : Nat),
      (l.take j).countP q = ((l.filter p).take ((l.take j).countP p)).countP q := by
  intro l
  induction l with
  | nil => intro j; simp
  | cons a t ih =>
    intro j
    cases j with
    | zero => simp
    | succ j =>
      by_cases ha : p a = true
      · simp [List.take_succ_cons, List.countP_cons, ha, ih j]
      · have hqa : q a = false := by
          cases h : q a
          · rfl
          · exact absurd (hq a h) ha
        simp [List.take_succ_cons, ha, hqa, ih j]

theorem countP_take_congr {α : Type} (u v : List α) (q : α → Bool) :
    ∀ p : Nat, p ≤ u.length → p ≤ v.length →
      (∀ m < p, (u[m]?).map q = (v[m]?).map q) →
      (u.take p).countP q = (v.take p).countP q := by
  intro p
  induction p with
  | zero => intros; simp
  | succ p ih =>
    intro hu hv h
    have hu' : p < u.length := hu
    have hv' : p < v.length := hv
    rw [List.take_add_one, List.take_add_one, List.countP_append, List.countP_append,
      ih (by omega) (by omega) (fun m hm => h m (by omega))]
    have := h p (by omega)
    rw [List.getElem?_eq_getElem hu', List.getElem?_eq_getElem hv'] at this ⊢
    simp only [Option.map_some, Option.some.injEq] at this
    simp [this]

/-! ### The barrier events of a thread -/

/-- The barrier and count of a barrier event. -/
def bsig : Event → Option (Nat × Option Nat)
  | ⟨_, .bar id cnt _⟩ => some (id, cnt)
  | _ => none

theorem isBarId_bsig (id : Nat) (e : Event) :
    Execution.isBarId id e =
      (match bsig e with | some (i, _) => decide (i = id) | none => false) := by
  obtain ⟨pc, kd⟩ := e
  cases kd <;> simp [Execution.isBarId, bsig]
  rename_i i' c m'
  by_cases h : i' = id <;> simp [h]

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The lanes of a warp agree on the barrier and count at each barrier position**, from
`¬ BarMismatch`. -/
theorem bar_sig_align (hX : Consistent L kernel asms mem0 X) (hbm : ¬ BarMismatch L X)
    {y y' i j : Nat} {e e' : Event} (hw : SameWarp L y y') (h1 : X.get (y, i) = some e)
    (h2 : X.get (y', j) = some e') (hb1 : Execution.isBar e = true)
    (hb2 : Execution.isBar e' = true)
    (hc : ((X.tr y).take i).countP Execution.isBar = ((X.tr y').take j).countP Execution.isBar) :
    bsig e = bsig e' := by
  obtain ⟨pc, kd⟩ := e
  obtain ⟨pc', kd'⟩ := e'
  cases kd <;> simp [Execution.isBar] at hb1
  rename_i id cnt mode
  cases kd' <;> simp [Execution.isBar] at hb2
  rename_i id' cnt' mode'
  have hm : mode = .sync := by
    cases mode
    · rfl
    · exact (Consistent.noBarArrive Safety.kernel_noBarArrive hX (y, i) pc id cnt h1).elim
  have hm' : mode' = .sync := by
    cases mode'
    · rfl
    · exact (Consistent.noBarArrive Safety.kernel_noBarArrive hX (y', j) pc' id' cnt' h2).elim
  subst hm hm'
  by_contra hne
  apply hbm
  left
  refine ⟨y, y', i, j, id, id', cnt, cnt', pc, pc', hw, h1, h2, hc, ?_⟩
  by_cases hid : id = id'
  · right
    intro hcnt
    exact hne (by simp [bsig, hid, hcnt])
  · left
    exact hid

/-- **Barrier positions of two lanes of a warp carry the same barrier and count**: the `m`-th
barrier event of each, for each `m` below both lengths. -/
theorem bl_align (hX : Consistent L kernel asms mem0 X) (hbm : ¬ BarMismatch L X) {y y' : Nat}
    (hw : SameWarp L y y') {m : Nat} (h1 : m < ((X.tr y).filter Execution.isBar).length)
    (h2 : m < ((X.tr y').filter Execution.isBar).length) :
    ((X.tr y).filter Execution.isBar)[m]?.map bsig = ((X.tr y').filter Execution.isBar)[m]?.map bsig
    := by
  rw [← List.countP_eq_length_filter] at h1 h2
  obtain ⟨j, e, hj, he, hjm⟩ := NamedBar.exists_ordinal Execution.isBar (X.tr y) h1
  obtain ⟨j', e', hj', he', hjm'⟩ := NamedBar.exists_ordinal Execution.isBar (X.tr y') h2
  have g1 := filter_getElem?_take Execution.isBar (X.tr y) j e hj he
  have g2 := filter_getElem?_take Execution.isBar (X.tr y') j' e' hj' he'
  rw [hjm] at g1
  rw [hjm'] at g2
  rw [g1, g2]
  simp only [Option.map_some, Option.some.injEq]
  exact bar_sig_align hX hbm hw hj hj' he he' (hjm.trans hjm'.symm)

/-- The barrier-0 events of two lanes' lists of barrier events agree entrywise below both
lengths. -/
theorem bl_isBarId_align (hX : Consistent L kernel asms mem0 X) (hbm : ¬ BarMismatch L X)
    {y y' : Nat} (hw : SameWarp L y y') {m : Nat}
    (h1 : m < ((X.tr y).filter Execution.isBar).length)
    (h2 : m < ((X.tr y').filter Execution.isBar).length) :
    (((X.tr y).filter Execution.isBar)[m]?).map (Execution.isBarId 0) =
      (((X.tr y').filter Execution.isBar)[m]?).map (Execution.isBarId 0) := by
  have h := bl_align hX hbm hw h1 h2
  rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at h ⊢
  simp only [Option.map_some, Option.some.injEq] at h ⊢
  rw [isBarId_bsig, isBarId_bsig, h]

/-- The barrier-0 events before index `j` of a thread are those among its first
`#(barrier events before j)` barrier events. -/
theorem b0_count_eq (X : Execution) (y j : Nat) :
    ((X.tr y).take j).countP (Execution.isBarId 0) =
      (((X.tr y).filter Execution.isBar).take
        (((X.tr y).take j).countP Execution.isBar)).countP (Execution.isBarId 0) :=
  countP_take_filter Execution.isBar (Execution.isBarId 0)
    (fun _ h => NamedBar.isBar_of_isBarId h) (X.tr y) j

/-- The position of an event that is a barrier event is below the number of barrier events. -/
theorem bpos_lt {y j : Nat} {e : Event} (he : X.get (y, j) = some e)
    (hb : Execution.isBar e = true) :
    ((X.tr y).take j).countP Execution.isBar < ((X.tr y).filter Execution.isBar).length := by
  rw [← List.countP_eq_length_filter]
  have h1 := countP_take_succ (p := Execution.isBar) he hb
  have h2 := countP_take_mono Execution.isBar (X.tr y) (show j + 1 ≤ (X.tr y).length from by
    have := (List.getElem?_eq_some_iff.mp he).1
    simp only at this
    omega)
  rw [List.take_length] at h2
  omega

/-- **The ordinal of the last-generation arrival, for the lane with the earlier position.** -/
theorem lock_le (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    (hbm : ¬ BarMismatch L X) {y y' j j' : Nat} (hy' : y' < L.threads) (hw : SameWarp L y y')
    (h1 : FinalArr X 0 2 y j) (h2 : FinalArr X 0 2 y' j')
    (hle : ((X.tr y).take j).countP Execution.isBar ≤ ((X.tr y').take j').countP Execution.isBar) :
    ((X.tr y).take j).countP (Execution.isBarId 0) =
      ((X.tr y').take j').countP (Execution.isBarId 0) := by
  obtain ⟨pc, m, hj, hk⟩ := h1
  obtain ⟨pc', m', hj', hk'⟩ := h2
  have hbj : Execution.isBar ⟨pc, .bar 0 none m⟩ = true := rfl
  have hbj' : Execution.isBar ⟨pc', .bar 0 none m'⟩ = true := rfl
  set p := ((X.tr y).take j).countP Execution.isBar with hp
  set p' := ((X.tr y').take j').countP Execution.isBar with hp'
  have hlt := bpos_lt hj hbj
  have hlt' := bpos_lt hj' hbj'
  have hlt'' : p < ((X.tr y').filter Execution.isBar).length := by omega
  have halign := bl_align hX hbm hw hlt hlt''
  have g1 := filter_getElem?_take Execution.isBar (X.tr y) j _ hj hbj
  rw [← hp] at g1
  rw [g1] at halign
  simp only [Option.map_some] at halign
  obtain ⟨e', hg', hsig⟩ : ∃ e', ((X.tr y').filter Execution.isBar)[p]? = some e' ∧
      bsig e' = some (0, none) := by
    rw [List.getElem?_eq_getElem hlt''] at halign ⊢
    exact ⟨_, rfl, by simpa [bsig] using halign.symm⟩
  -- the lane's own event at position `p`
  have hlt3 : p < ((X.tr y').countP Execution.isBar) := by
    rw [List.countP_eq_length_filter]; exact hlt''
  obtain ⟨j'', e'', hj'', hb'', hjo⟩ := NamedBar.exists_ordinal Execution.isBar (X.tr y') hlt3
  have g2 := filter_getElem?_take Execution.isBar (X.tr y') j'' e'' hj'' hb''
  rw [hjo, hg'] at g2
  obtain rfl := Option.some.inj g2
  obtain ⟨pc'', mode'', rfl⟩ : ∃ pc'' mode'', e' = ⟨pc'', .bar 0 none mode''⟩ := by
    obtain ⟨pcx, kd⟩ := e'
    cases kd <;> simp [bsig] at hsig
    rename_i i' c md
    obtain ⟨rfl, rfl⟩ := hsig
    exact ⟨_, _, rfl⟩
  -- its ordinal is that of `y`'s arrival
  have hcount : ((X.tr y').take j'').countP (Execution.isBarId 0) =
      ((X.tr y).take j).countP (Execution.isBarId 0) := by
    rw [b0_count_eq X y' j'', hjo, b0_count_eq X y j, ← hp]
    symm
    refine countP_take_congr _ _ _ p (by omega) (by omega) fun mm hmm => ?_
    exact bl_isBarId_align hX hbm hw (by omega) (by omega)
  have hfin : FinalArr X 0 2 y' j'' := ⟨pc'', mode'', hj'', by omega⟩
  have hjj := bar0_one hpre hX hS ht hy' hfin ⟨pc', m', hj', hk'⟩
  subst hjj
  rw [← hcount]

/-- A safe execution has no barrier mismatch. -/
theorem not_barMismatch (hs : ¬ Unsafe L kernel asms mem0 X) : ¬ BarMismatch L X :=
  fun h => hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

/-- **`Bar0Facts.lock`**: the lanes of a warp agree on the ordinal of their last-generation
arrival. -/
theorem bar0_lock (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    (hs : ¬ Unsafe L kernel asms mem0 X) {y y' j j' : Nat} (hy : y < L.threads)
    (hy' : y' < L.threads) (hdiv : y / L.block = y' / L.block)
    (hw : y % L.block / 32 = y' % L.block / 32) (h1 : FinalArr X 0 2 y j)
    (h2 : FinalArr X 0 2 y' j') :
    ((X.tr y).take j).countP (Execution.isBarId 0) =
      ((X.tr y').take j').countP (Execution.isBarId 0) := by
  have hsw : SameWarp L y y' := ⟨⟨hy, hy', hdiv⟩, hw⟩
  have hbm := not_barMismatch hs
  rcases le_total (((X.tr y).take j).countP Execution.isBar)
      (((X.tr y').take j').countP Execution.isBar) with h | h
  · exact lock_le hpre hX hS ht hbm hy' hsw h1 h2 h
  · exact (lock_le hpre hX hS ht hbm hy (sameWarp_symm hsw) h2 h1 h).symm

end

end PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
